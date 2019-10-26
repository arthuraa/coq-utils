# Coq Utils: a handful of useful Coq libraries

This package contains miscellaneous useful Coq libraries:

- `nominal`: a simple theory of [nominal sets][1] with computable support,
  including the formalization of name restriction and [binding operators][2].

- `word`: theory of finite bit vectors.

- `hseq`: heterogeneous lists.

- `string`: basic infrastructure for some types in the Coq standard library.


The development is based on the [SSReflect][3] proof language and on the
[Mathematical Components libraries][4], and tries to follow their conventions
and philosophy (for example, the use of canonical structures to define types
with structure).

## Installation

The package currently needs to be compiled by hand.  It requires Coq v8.10 as
well as the following [OPAM][5] packages:

- `coq-mathcomp-ssreflect`, `coq-mathcomp-fingroup`, `coq-mathcomp-algebra` v1.9
- `coq-extructures` v0.2.1
- `coq-void` v0.1
- `coq-deriving` (available in the `extra-dev` repository)

To compile the package, simply run

    make

After compilation, you can install the package by running

    make install

## Usage

Documentation for the libraries is currently scarce, but will be progressively
added as comments in the headers of the files.  Once the package is installed,
it can be required using the `CoqUtils` qualifier.  For example:

    From CoqUtils Require Import hseq nominal.


  [1]: https://link.springer.com/article/10.1007/s001650200016
  [2]: http://www.sciencedirect.com/science/article/pii/S1571066116300743
  [3]: https://coq.inria.fr/distrib/current/refman/ssreflect.html
  [4]: https://github.com/math-comp/math-comp
  [5]: https://coq.inria.fr/opam/www/using.html
