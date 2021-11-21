module Compiler.Lisp.Emacs.Main

import Core.Context
import Compiler.Common
import Idris.Driver
import Libraries.Data.NameMap
import Libraries.Data.Version
import Compiler.Lisp.Emacs
import System
import System.Directory
import System.File
import System.Info

main : IO ()
main = mainWithCodegens [("emacs", codegenEmacs)]
