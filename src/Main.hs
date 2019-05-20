{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}

module Main (main) where

import Prelude

import qualified Data.Aeson as Aeson
import qualified Data.List as List
import qualified Data.Text as Text

import Control.Monad (when, guard)
import Control.Monad.Except (MonadError, throwError)
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
import qualified Language.PureScript.Environment as Environment
import Language.PureScript.Externs (ExternsFile(..), applyExternsFileToEnvironment, moduleToExternsFile)
import Language.PureScript.ModuleDependencies (sortModules, moduleSignature)
import Language.PureScript.Names (ModuleName, runModuleName)
import Control.Monad.Supply (runSupplyT)
import System.IO.UTF8 (readUTF8FileT)

main :: IO ()
main = do
  moduleFiles <- readInput =<< concatMapM glob =<< getArgs
  when (null moduleFiles) $ do
    hPutStrLn stderr "purs-shake: No input files"
    exitFailure

  case parseModuleGraphFromFiles moduleFiles of
    Left errors -> do
      hPutStrLn stderr $
        Errors.prettyPrintMultipleErrors Errors.defaultPPEOptions errors
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
    (m,) <$> allModuleDependencies graph (AST.getModuleName m)

  --for sorted $ \m -> do
  --  let moduleName = AST.getModuleName m
  --  let err =  Errors.errorMessage (AST.ModuleNotFound moduleName)
  --  maybe (throwError err) pure $ do
  --    deps <- List.lookup moduleName graph
  --    pure (m, deps)

-- | Collect all dependencies (including transitive) from a 'ModuleGraph'.
allModuleDependencies
  :: forall m
   . MonadError Errors.MultipleErrors m
  => [(ModuleName, [ModuleName])]
  -> ModuleName
  -> m [ModuleName]
allModuleDependencies graph moduleName =
  case List.lookup moduleName graph of
    Nothing   -> throwError (Errors.errorMessage (AST.ModuleNotFound moduleName))
    Just []   -> pure []
    Just deps -> mappend deps <$> concatMapM (allModuleDependencies graph) deps

compile :: [(AST.Module, [ModuleName])] -> IO ()
compile graph =
  runShake $ do
    wants <- concatMapM (uncurry compileModule) graph
    Shake.want wants

runShake :: Shake.Rules () -> IO ()
runShake =
  Shake.shake Shake.shakeOptions
    { Shake.shakeLint = Just Shake.LintBasic
    , Shake.shakeVerbosity = Shake.Silent
    , Shake.shakeChange = Shake.ChangeModtimeAndDigest
    }

compileModule :: AST.Module -> [ModuleName] -> Shake.Rules [FilePath]
compileModule m@(AST.Module sourceSpan _ moduleName _ _) deps = do
  let wants = [ outputFor moduleName corefnPath
              , outputFor moduleName externsPath
              ]
  wants &%> \[coreFnPath, externsFilePath] -> do
    let depExternsFiles = fmap (`outputFor` externsPath) deps
    Shake.need (AST.spanName sourceSpan : depExternsFiles)

    externsFiles <- for depExternsFiles $ \depExternsFile -> do
      mbExternsFile <- liftIO (readExternsFile depExternsFile)
      case mbExternsFile of
        Nothing -> fail ("missing externs file: " <> depExternsFile)
        Just externsFile -> pure externsFile

    -- FIXME
    -- `efExports = []` (i.e. no explicit exports) causes compilation to fail
    -- with UnknownImport...what's going on?
    liftIO $ print externsFiles

    case runWriterT (compileCoreFn externsFiles m) of
      Left errors ->
        fail $ Errors.prettyPrintMultipleErrors Errors.defaultPPEOptions errors

      Right ((coreFn, externsFile), _warnings) ->
        liftIO $ do
          createDirectoryIfMissing True (takeDirectory externsFilePath)
          Aeson.encodeFile externsFilePath externsFile
          Aeson.encodeFile coreFnPath
            (CoreFn.moduleToJSON PureScript.version coreFn)

          putStrLn ("Compiled " <> Text.unpack (runModuleName moduleName))

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
  let env = foldl' (flip applyExternsFileToEnvironment)
              Environment.initEnvironment
              externs
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

concatMapM :: Applicative m => (a -> m [b]) -> [a] -> m [b]
concatMapM f = fmap concat . traverse f

-- CONSTANTS

outputDir :: FilePath
outputDir = "output"

externsPath :: FilePath
externsPath = "externs.json"

corefnPath :: FilePath
corefnPath = "corefn.json"
