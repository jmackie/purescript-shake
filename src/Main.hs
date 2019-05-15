{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}

{-# OPTIONS_GHC -Wall #-}

module Main (main) where

import Prelude

import qualified Data.Aeson as Aeson
import qualified Data.List as List
import qualified Data.Text as Text

import Control.Monad (when, guard, mapAndUnzipM)
import Control.Monad.Except (MonadError)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Writer (MonadWriter, runWriterT)
import Data.Foldable (foldl')
import Data.Text (Text)
import Data.Traversable (for)
import Data.Version (showVersion)
import System.Directory (createDirectoryIfMissing)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath (takeDirectory)
import System.FilePath.Glob (glob)
import System.IO (hPutStrLn, stderr)

-- shake
import qualified Development.Shake as Shake
import Development.Shake ((&%>))
import Development.Shake.FilePath ((</>))

-- purescript
import qualified Language.PureScript as PureScript (version)
import qualified Language.PureScript.AST as AST
import qualified Language.PureScript.CST as CST
import qualified Language.PureScript.CoreFn as CoreFn
import qualified Language.PureScript.CoreFn.ToJSON as CoreFn (moduleToJSON)
import qualified Language.PureScript.Errors as Errors
import qualified Language.PureScript.Renamer as Renamer
import qualified Language.PureScript.Sugar as Sugar
import qualified Language.PureScript.TypeChecker as TypeChecker
import Language.PureScript.Environment (initEnvironment)
import Language.PureScript.Externs (ExternsFile(..), applyExternsFileToEnvironment, moduleToExternsFile)
import Language.PureScript.ModuleDependencies (sortModules, moduleSignature)
import Language.PureScript.Names (ModuleName, runModuleName)
import Control.Monad.Supply (runSupplyT)
import System.IO.UTF8 (readUTF8FileT)

main :: IO ()
main = do
  moduleFiles <- readInput =<< globWarningOnMisses =<< getArgs
  case parseModuleGraphFromFiles moduleFiles of
    Left errors -> do
      hPutStrLn stderr $ Errors.prettyPrintMultipleErrors Errors.defaultPPEOptions errors
      exitFailure

    Right graph ->
      compile graph

readInput :: [FilePath] -> IO [(FilePath, Text)]
readInput = traverse (\inFile -> (inFile, ) <$> readUTF8FileT inFile)

parseModuleGraphFromFiles
  :: MonadError Errors.MultipleErrors m
  => [(FilePath, Text)]
  -> m [(AST.Module, [ModuleName])]
parseModuleGraphFromFiles inputFiles = do
  pathsAndModules <- CST.parseModulesFromFiles id inputFiles
  let modules = fmap (CST.resPartial . snd) pathsAndModules
  (sorted, graph) <- sortModules moduleSignature modules
  for sorted $ \m ->
    maybe (error "wat") pure $ do
      let moduleName = AST.getModuleName m
      deps <- List.lookup moduleName graph
      pure (m, deps)

compile :: [(AST.Module, [ModuleName])] -> IO ()
compile graph =
  runShake $ do
    wants <- concat <$> traverse (uncurry compileModule) graph
    Shake.want wants

runShake :: Shake.Rules () -> IO ()
runShake =
  Shake.shakeArgs Shake.shakeOptions
    { Shake.shakeLint = Just Shake.LintBasic
    , Shake.shakeVerbosity = Shake.Diagnostic
    }

compileModule :: AST.Module -> [ModuleName] -> Shake.Rules [FilePath]
compileModule m deps = do
  let wants = [ outputFor (AST.getModuleName m) corefnPath
              , outputFor (AST.getModuleName m) externsPath
              ]

  wants &%> \[coreFnPath, externsFilePath] -> do
    (needs, externsFiles) <- flip mapAndUnzipM deps $ \dep -> do
      let need = outputFor dep externsPath
      mbExternsFile <- liftIO (readExternsFile need)
      case mbExternsFile of
        Nothing -> fail ("missing externs file: " <> need)
        Just externsFile -> pure (need, externsFile)

    -- Should we `need` the *.purs file path here?
    let moduleName = AST.spanName (AST.getModuleSourceSpan m)
    Shake.need (moduleName : needs)

    case runWriterT (compileCoreFn externsFiles m) of
      Left _errors ->
        fail "TODO: compilation errors"

      Right ((coreFn, externsFile), _warnings) ->
        liftIO $ do
          createDirectoryIfMissing True (takeDirectory externsFilePath)
          Aeson.encodeFile externsFilePath externsFile
          Aeson.encodeFile coreFnPath
            (CoreFn.moduleToJSON PureScript.version coreFn)

  pure wants

-- | Mostly copied from @Language.PureScript.Make.rebuildModule@.
compileCoreFn
  :: ( MonadError Errors.MultipleErrors m
     , MonadWriter Errors.MultipleErrors m
     )
  => [ExternsFile]
  -> AST.Module
  -> m (CoreFn.Module CoreFn.Ann, ExternsFile)
compileCoreFn externs m = do
  let moduleName = AST.getModuleName m
  let env = foldl' (flip applyExternsFileToEnvironment) initEnvironment externs
  let withPrim = AST.importPrim m
  ((AST.Module ss coms _ elaborated exps, env'), nextVar) <-
    runSupplyT 0 $
      Sugar.desugar externs [withPrim] >>= \case
        [desugared] ->
          TypeChecker.runCheck' (TypeChecker.emptyCheckState env) $
            TypeChecker.typeCheckModule desugared

        _ -> error "desugar did not return a singleton"

  (deguarded, _) <- runSupplyT nextVar $
    Sugar.desugarCaseGuards elaborated

  regrouped <- Sugar.createBindingGroups moduleName . Sugar.collapseBindingGroups $ deguarded
  let mod' = AST.Module ss coms moduleName regrouped exps
  let corefn = CoreFn.moduleToCoreFn env' mod'
  let optimized = CoreFn.optimizeCoreFn corefn
  let [renamed] = Renamer.renameInModules [optimized]
  pure (renamed, moduleToExternsFile mod' env')

outputFor :: ModuleName -> FilePath -> FilePath
outputFor moduleName base =
  outputDir </> Text.unpack (runModuleName moduleName) </> base

readExternsFile :: FilePath -> IO (Maybe ExternsFile)
readExternsFile path = do
  result <- Aeson.decodeFileStrict path
  case result of
    Nothing -> pure Nothing
    Just externs -> do
      guard $ Text.unpack (efVersion externs) == showVersion PureScript.version
      pure (Just externs)

globWarningOnMisses :: [FilePath] -> IO [FilePath]
globWarningOnMisses = concatMapM globWithWarning
  where
  globWithWarning :: String -> IO [FilePath]
  globWithWarning pattern' = do
    paths <- glob pattern'
    when (null paths) $
      hPutStrLn stderr $
        "purs compile: No files found using pattern: " <> pattern'
    pure paths

concatMapM :: (a -> IO [b]) -> [a] -> IO [b]
concatMapM f = fmap concat . mapM f

-- CONSTANTS

outputDir :: FilePath
outputDir = "output"

externsPath :: FilePath
externsPath = "externs.json"

corefnPath :: FilePath
corefnPath = "corefn.json"
