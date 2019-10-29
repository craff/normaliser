
*************************************************************************
*                                                                       *
*           A normaliser for pure and typed lambda-calculus             *
*                                                                       *
*                            C. Raffalli                                *
*                                                                       *
*************************************************************************


  This program provides a useful environment to write programs in pure
lambda-calculus. Given a term, the program will compute and print its
normal form. This means that, unlike most functional languages,
computation is done under function abstractions (or lambdas).

  This software might be used for teaching lambda-calculus or just to
play with it.

  It has some interesting features :

   - Three modes of evaluation:
       lazy: call-by-name with some sharing
       left: call-by-name with no sharing
       trace: call-by-name and printing of each beta-reduction step or
              tracing of particular functions.

   - It is implemented in Objective-Caml (a ML dialect) so easily portable
     to many machines, even very small ones.

   - It is quite efficient. It uses a High-Order-Abstract-Syntax
     representation of terms which help to benefit from ML management
     of closure. This is specially optimised to give both reasonable
     performance in speed and memory. It's possible to terminate
     computation of factorial 100 with a binary encoding of natural
     numbers !

   - You can define terms (even using recursive definitions) or
     include files. This gives enough modularity to write fairly large
     terms.

   - You can use a typing algorithm for system F (with or without
     inductive type) to program more ``safely''.

INSTALLATION:

- On a Unix Machine:

  get and install Objective-Caml : The ftp site is
        host:       ftp.inria.fr (192.93.2.54)
        directory:  lang/caml-light

  Go into the directory Src and type make. This should produce an
  executable file lambda which is the normalizator.

  You can also type make lambdaopt. This produce an executable file
  lambdaopt compiled by the native code compiler (ocamlopt).


DOCUMENTATION:

  A documentation Doc.txt and a TeX version is available in the Doc
directory.


EXAMPLES:

  See in the Examples directory.

HISTORY:

  Version 2.3 (Novembre 97): Changes from version 2.2

  - fixed bug in printing of typing error messages for terms that
    were defined untyped but used later in a typed context
  - port to Objective-Caml 1.06 required minor changes
  - uses the new bindlib library version 2.0

  Version 2.2 (November 96): Changes from version 2.1

  - fixed bug in printing (there could be clashes in variable names)
  - changed for compatibility with ocaml 1.02 ("=" can not compare
    channels anymore)

  Version 2.1: Changes from version 2.0

  - port to Objective Caml
  - Corrected a bug that could result in raising "Binlib error" when
    parsing a term with some unbound variables

  Version 2.0: Changes from version 1.0

  - Added a type system (off by default).
  - In trace mode, only beta-reduction are traced (not function call).
  - function call can be traced in lazy and left mode.
  - The "def" command has been renamed "let".
  - "let" can be mutually recursive and/or local.
  - The fix-point combinator ! has been removed (let rec are better).
  - Error messages have been improved.
  - The characters "_" and "'" are not allowed as first characters
    of identifiers.
  - Keywords (like "let" or "and") can not be used as identifiers.
  - Parser and lexer have been rewritten in camlyacc and camllex.
  - Terms are now "pretty-printed" using the format library.
  - This version cannot be compiled with caml-light 0.6.

  Version 1.0: First public version
