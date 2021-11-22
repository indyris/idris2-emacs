module Emacs

%foreign "emacs:eval"
eval : AnyPtr -> PrimIO AnyPtr

