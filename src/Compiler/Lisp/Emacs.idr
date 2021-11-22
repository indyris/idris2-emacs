module Compiler.Lisp.Emacs

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Generated
import Compiler.Scheme.Common

import Core.Context
import Core.Context.Log
import Core.Directory
import Core.Name
import Core.Options
import Core.TT
import Libraries.Utils.Hex
import Libraries.Utils.Path

import Data.List
import Data.List1
import Data.Maybe
import Data.String
import Data.Vect

import Idris.Env

import System
import System.Directory
import System.Info

import Libraries.Data.Version
import Libraries.Utils.String

%default covering

emacsHeader : List String -> Bool -> String
emacsHeader libs whole
  = """
    ;; \{ generatedString "Emacs" }

    \{ ifThenElse whole
                  "(let ()"
                  "(source-directories (cons (getenv \"IDRIS2_INC_SRC\") (source-directories)))"
     }

    """

emacsFooter : Bool -> String
emacsFooter whole = """
    (collect 4)
    (blodwen-run-finalisers)
    \{ ifThenElse whole ")" "" }
  """

showEmacsChar : Char -> String -> String
showEmacsChar '\\' = ("\\\\" ++)
showEmacsChar c
   = if c < chr 32 || c > chr 126
        then (("\\x" ++ asHex (cast c) ++ ";") ++)
        else strCons c

showEmacsString : List Char -> String -> String
showEmacsString [] = id
showEmacsString ('"'::cs) = ("\\\"" ++) . showEmacsString cs
showEmacsString (c ::cs) = (showEmacsChar c) . showEmacsString cs

export
emacsString : String -> String
emacsString cs = strCons '"' (showEmacsString (unpack cs) "\"")

mutual
  handleRet : String -> String -> String
  handleRet "void" op = op ++ " " ++ mkWorld (schConstructor emacsString (UN $ Basic "") (Just 0) [])
  handleRet _ op = mkWorld op

  getFArgs : NamedCExp -> Core (List (NamedCExp, NamedCExp))
  getFArgs (NmCon fc _ _ (Just 0) _) = pure []
  getFArgs (NmCon fc _ _ (Just 1) [ty, val, rest]) = pure $ (ty, val) :: !(getFArgs rest)
  getFArgs arg = throw (GenericMsg (getFC arg) ("Badly formed c call argument list " ++ show arg))

  export
  emacsExtPrim : Int -> ExtPrim -> List NamedCExp -> Core String
  emacsExtPrim i GetField [NmPrimVal _ (Str s), _, _, struct,
                          NmPrimVal _ (Str fld), _]
      = do structsc <- schExp emacsExtPrim emacsString 0 struct
           pure $ "(ftype-ref " ++ s ++ " (" ++ fld ++ ") " ++ structsc ++ ")"
  emacsExtPrim i GetField [_,_,_,_,_,_]
      = pure "(blodwen-error-quit \"bad getField\")"
  emacsExtPrim i SetField [NmPrimVal _ (Str s), _, _, struct,
                          NmPrimVal _ (Str fld), _, val, world]
      = do structsc <- schExp emacsExtPrim emacsString 0 struct
           valsc <- schExp emacsExtPrim emacsString 0 val
           pure $ mkWorld $
              "(ftype-set! " ++ s ++ " (" ++ fld ++ ") " ++ structsc ++
              " " ++ valsc ++ ")"
  emacsExtPrim i SetField [_,_,_,_,_,_,_,_]
      = pure "(blodwen-error-quit \"bad setField\")"
  emacsExtPrim i SysCodegen []
      = pure $ "\"emacs\""
  emacsExtPrim i OnCollect [_, p, c, world]
      = do p' <- schExp emacsExtPrim emacsString 0 p
           c' <- schExp emacsExtPrim emacsString 0 c
           pure $ mkWorld $ "(blodwen-register-object " ++ p' ++ " " ++ c' ++ ")"
  emacsExtPrim i OnCollectAny [p, c, world]
      = do p' <- schExp emacsExtPrim emacsString 0 p
           c' <- schExp emacsExtPrim emacsString 0 c
           pure $ mkWorld $ "(blodwen-register-object " ++ p' ++ " " ++ c' ++ ")"
  emacsExtPrim i MakeFuture [_, work]
      = do work' <- schExp emacsExtPrim emacsString 0 work
           pure $ "(blodwen-make-future " ++ work' ++ ")"
  emacsExtPrim i prim args
      = schExtCommon emacsExtPrim emacsString i prim args

-- Label for noting which struct types are declared
export
data Structs : Type where

lispCall : FC -> (sfn : String) ->
             List Name -> CFType -> Core String
lispCall fc sfn argns ret
  = let call = "(" ++ sfn ++ " " ++ showSep " " (map schName argns) ++ ")" in
    case ret of
      CFIORes _ => pure $ mkWorld call
      _ => pure call

-- Use a calling convention to compile a foreign def.
-- Returns any preamble needed for loading libraries, and the body of the
-- function call.
useCC : {auto c : Ref Ctxt Defs} ->
        FC -> List String -> List (Name, CFType) -> CFType ->
        Core (Maybe String, String)
useCC fc ccs args ret = case parseCC ["emacs"] ccs of
  Just ("emacs", [sfn]) => do
    body <- lispCall fc sfn (map fst args) ret
    pure (Nothing, body)
  _ => throw (NoForeignCC fc ccs)

notWorld : CFType -> Bool
notWorld CFWorld = False
notWorld _ = True

cftySpec : FC -> CFType -> Core String
cftySpec fc CFUnit = pure "void"
cftySpec fc CFInt = pure "int"
cftySpec fc CFInt8 = pure "char"
cftySpec fc CFInt16 = pure "short"
cftySpec fc CFInt32 = pure "int"
cftySpec fc CFInt64 = pure "long"
cftySpec fc CFUnsigned8 = pure "unsigned-char"
cftySpec fc CFUnsigned16 = pure "unsigned-short"
cftySpec fc CFUnsigned32 = pure "unsigned-int"
cftySpec fc CFUnsigned64 = pure "unsigned-long"
cftySpec fc CFString = pure "UTF-8-string"
cftySpec fc CFDouble = pure "double"
cftySpec fc CFChar = pure "char"
cftySpec fc CFPtr = pure "(pointer void)"
cftySpec fc (CFIORes t) = cftySpec fc t
cftySpec fc (CFStruct n t) = pure $ n ++ "*/nonnull"
cftySpec fc (CFFun s t) = funTySpec [s] t
  where
    funTySpec : List CFType -> CFType -> Core String
    funTySpec args (CFFun CFWorld t) = funTySpec args t
    funTySpec args (CFFun s t) = funTySpec (s :: args) t
    funTySpec args retty
        = do rtyspec <- cftySpec fc retty
             argspecs <- traverse (cftySpec fc) (reverse . filter notWorld $ args)
             pure $ "(function (" ++ showSep " " argspecs ++ ") " ++ rtyspec ++ ")"
cftySpec fc t = throw (GenericMsg fc ("Can't pass argument of type " ++ show t ++
                         " to foreign function"))

-- For every foreign arg type, return a name, and whether to pass it to the
-- foreign call (we don't pass '%World')
mkArgs : Int -> List CFType -> List (Name, Bool)
mkArgs i [] = []
mkArgs i (CFWorld :: cs) = (MN "farg" i, False) :: mkArgs i cs
mkArgs i (c :: cs) = (MN "farg" i, True) :: mkArgs (i + 1) cs

mkStruct : {auto s : Ref Structs (List String)} ->
           CFType -> Core String
mkStruct (CFStruct n flds)
    = do defs <- traverse mkStruct (map snd flds)
         strs <- get Structs
         if n `elem` strs
            then pure (concat defs)
            else do put Structs (n :: strs)
                    pure $ concat defs ++ "(define-ftype " ++ n ++ " (struct\n\t"
                           ++ showSep "\n\t" !(traverse showFld flds) ++ "))\n"
  where
    showFld : (String, CFType) -> Core String
    showFld (n, ty) = pure $ "[" ++ n ++ " " ++ !(cftySpec emptyFC ty) ++ "]"
mkStruct (CFIORes t) = mkStruct t
mkStruct (CFFun a b) = do ignore (mkStruct a); mkStruct b
mkStruct _ = pure ""

schFgnDef : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Structs (List String)} ->
            FC -> Name -> NamedDef ->
            Core (Maybe String, String)
schFgnDef fc n (MkNmForeign cs args ret)
    = do let argns = mkArgs 0 args
         let allargns = map fst argns
         let useargns = map fst (filter snd argns)
         argStrs <- traverse mkStruct args
         retStr <- mkStruct ret
         (load, body) <- useCC fc cs (zip useargns args) ret
         defs <- get Ctxt
         pure (load,
                concat argStrs ++ retStr ++
                "(define " ++ schName !(full (gamma defs) n) ++
                " (lambda (" ++ showSep " " (map schName allargns) ++ ") " ++
                body ++ "))\n")
schFgnDef _ _ _ = pure (Nothing, "")

export
getFgnCall : {auto c : Ref Ctxt Defs} ->
             {auto s : Ref Structs (List String)} ->
             (Name, FC, NamedDef) ->
             Core (Maybe String, String)
getFgnCall (n, fc, d) = schFgnDef fc n d

||| Compile a TT expression to Emacs Lisp
compileToElisp : Ref Ctxt Defs -> String -> ClosedTerm -> (outfile : String) -> Core ()
compileToElisp c appdir tm outfile
    = do ds <- getDirectives (Other "Emacs")
         let libs = []
         -- libs <- findLibs ds
         -- traverse_ copyLib libs
         cdata <- getCompileData False Cases tm
         let ndefs = namedDefs cdata
         let ctm = forget (mainExpr cdata)

         defs <- get Ctxt
         s <- newRef {t = List String} Structs []
         fgndefs <- traverse getFgnCall ndefs
         -- loadlibs <- traverse (loadLib appdir) (mapMaybe fst fgndefs)

         compdefs <- traverse (getScheme emacsExtPrim emacsString) ndefs
         let code = fastConcat (map snd fgndefs ++ compdefs)
         main <- schExp emacsExtPrim emacsString 0 ctm
         support <- readDataFile "emacs/idris2-emacs-support.el"
         extraRuntime <- getExtraRuntime ds
         let scm = emacsHeader libs True ++
                   support ++ extraRuntime ++ code ++
                   -- concat loadlibs ++
                   "(collect-request-handler (lambda () (collect) (blodwen-run-finalisers)))\n" ++
                   main ++ emacsFooter True
         Right () <- coreLift $ writeFile outfile scm
            | Left err => throw (FileErr outfile err)
         coreLift_ $ chmodRaw outfile 0o755

||| Compile a TT expression to Emacs Scheme using incremental module builds
compileToElispInc : Ref Ctxt Defs -> List String -> String -> ClosedTerm -> (outfile : String) -> Core ()
compileToElispInc c libs appdir tm outfile
    = do tmcexp <- compileTerm tm
         let ctm = forget tmcexp

         -- loadlibs <- traverse (loadLib appdir) (nub libs)

         main <- schExp emacsExtPrim emacsString 0 ctm
         support <- readDataFile "emacs/idris2-emacs-support.el"

         let scm = emacsHeader libs False ++
                   support ++
                   -- concat loadlibs ++
                   "(collect-request-handler (lambda () (collect) (blodwen-run-finalisers)))\n" ++
                   main ++ emacsFooter False

         Right () <- coreLift $ writeFile outfile scm
            | Left err => throw (FileErr outfile err)
         coreLift_ $ chmodRaw outfile 0o755
         pure ()

compileExprWhole : Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String) ->
                   ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExprWhole c tmpDir outputDir tm outfile
    = do let appDirRel = outfile ++ "_app" -- relative to build dir
         let appDirGen = outputDir </> appDirRel -- relative to here
         coreLift_ $ mkdirAll appDirGen
         Just cwd <- coreLift currentDir
              | Nothing => throw (InternalError "Can't get current directory")
         let outElFile = appDirRel </> outfile <.> "el"
         let outElAbs = cwd </> outputDir </> outElFile
         compileToElisp c appDirGen tm outElAbs
         let outShRel = outputDir </> outfile
         pure (Just outShRel)

compileExprInc : Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String) ->
                 ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExprInc c tmpDir outputDir tm outfile
    = do defs <- get Ctxt
         let Just (mods, libs) = lookup (Other "Emacs") (allIncData defs)
           | Nothing =>
              do coreLift $ putStrLn $ "Missing incremental compile data, reverting to whole program compilation"
                 compileExprWhole c tmpDir outputDir tm outfile
         let appDirRel = outfile ++ "_app" -- relative to build dir
         let appDirGen = outputDir </> appDirRel -- relative to here
         coreLift_ $ mkdirAll appDirGen
         Just cwd <- coreLift currentDir
           | Nothing => throw (InternalError "Can't get current directory")
         let outFile = appDirRel </> outfile <.> "el"
         let outAbs = cwd </> outputDir </> outFile
         compileToElispInc c mods appDirGen tm outAbs
         pure (Just $ outputDir </> outFile)

||| Emacs lisp implementation of the `compileExpr` interface.
compileExpr : Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String) ->
              ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr c tmpDir outputDir tm outfile = do
  s <- getSession
  if not (wholeProgram s) && (Other "Emacs" `elem` incrementalCGs !getSession)
    then compileExprInc c tmpDir outputDir tm outfile
    else compileExprWhole c tmpDir outputDir tm outfile

||| We don't really support execution, but we can compile.
executeExpr : Ref Ctxt Defs -> (tmpDir : String) -> ClosedTerm -> Core ()
executeExpr c tmpDir tm
    = do Just sh <- compileExpr c tmpDir tmpDir tm "_tmpemacs"
           | Nothing => throw (InternalError "compileExpr returned Nothing")
         throw (InternalError "emacs lisp backend cannot execute expressions yet!")

-- incCompile : Ref Ctxt Defs ->
--              (sourceFile : String) -> Core (Maybe (String, List String))
-- incCompile c sourceFile
--     = do
--          elFile <- getTTCFileName sourceFile "el"
--          cdata <- getIncCompileData False Cases
--          d <- getDirs
--          let outputDir = build_dir d </> "ttc"

--          let ndefs = namedDefs cdata
--          if isNil ndefs
--             then pure (Just ("", []))
--                       -- ^ no code to generate, but still recored that the
--                       -- module has been compiled, with no output needed.
--             else do
--                s <- newRef {t = List String} Structs []
--                fgndefs <- traverse getFgnCall ndefs
--                compdefs <- traverse (getScheme emacsExtPrim emacsString) ndefs
--                let code = fastConcat (map snd fgndefs ++ compdefs)
--                Right () <- coreLift $ writeFile ssFile code
--                   | Left err => throw (FileErr ssFile err)

--                -- Compile to .so
--                let tmpFileAbs = outputDir </> "compileEmacs"
--                let build = "(parameterize ([optimize-level 3] " ++
--                            "[compile-file-message #f]) (compile-file " ++
--                           show ssFile ++ "))"
--                Right () <- coreLift $ writeFile tmpFileAbs build
--                   | Left err => throw (FileErr tmpFileAbs err)
--                coreLift_ $ system (emacs ++ " --script \"" ++ tmpFileAbs ++ "\"")
--                pure (Just (soFilename, mapMaybe fst fgndefs))

||| Codegen wrapper for Emacs lisp implementation.
export
codegenEmacs : Codegen
codegenEmacs = MkCG compileExpr executeExpr Nothing (Just "el")
-- when incremental works:
-- codegenEmacs = MkCG compileExpr executeExpr (Just incCompile) (Just "el")
