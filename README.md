
## A normaliser for pure and typed lambda-calculus

  This program provides a useful environment to write programs in pure
lambda-calculus. Given a term, the program will compute and print its
normal form. This means that, unlike most functional languages,
computation is done under function abstractions (or lambdas).

  This software might be used for teaching lambda-calculus or just to
play with it.

  It has some interesting features :

 - It is maintained (compile with latest OCaml) but not changed anymore.
   If you use it for teaching, you files will probably still work in 10 or
   20 years

 - Three modes of evaluation:
       lazy: call-by-name with some sharing
       left: call-by-name with no sharing
       trace: call-by-name and printing of each beta-reduction step or
              tracing of particular functions.

 - It is implemented in OCaml (a ML dialect) so easily portable
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

### INSTALLATION:

Get and install Objective-Caml

```bash
cd Src
make
make lambdaopt
```

### DOCUMENTATION:

  A latex documentation is available in the Doc directory.


### EXAMPLES:

  See in the Examples directory.
