#!/usr/bin/env bash
test -d .psc-package || psc-package install
rm -rf output .shake
stack build
stack exec purs-shake -- ".psc-package/*/*/*/src/**/*.purs"
