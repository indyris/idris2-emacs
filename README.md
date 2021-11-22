# idris2-emacs -  a (WIP) emacs codegen for idris 2.

This is an adaptation of the built-in idris 2 chez backend.

## Status: pre-alpha

Does not work yet. Doesn't even comnpile yet.

## Building

You must have installed the idris compiler api (the `idris` package)
corresponding to your idris compiler with `make install-api` after
installing idris.

## TODO

- [ ] Finish porting scheme support library to emacs lisp
  - [ ] What to do about `box`?

## Notes

* We do not support compiling and loading shared objects. Emacs isn't
  really built for this sort of thing.
