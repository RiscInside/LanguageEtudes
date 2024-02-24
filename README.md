# Language etudes ♫

Repository accomodating a bunch of single-file typechecker/interpreter/compiler implementations.
## Table of contents

### Interpreters

| File | Description |
|------|-------------|
| [scala/nbe.sc](scala/nbe.sc) | Plain and CPS-transformed NbE lambda calculus interpreters in Scala, along with a performance comparison. Run with `scala-cli run nbe.sc -- 1000 5`. |
| [ocaml/nbe.ml](scala/nbe.sc) | Same thing in OCaml. Run with `ocamlbuild ocaml/cps.native --`. |

### Typecheckers

| File | Description |
|------|-------------|
| [scala/holes/holes.scala](scala/holes/holes.scala) | Basic typechecker for a bare bones dependently typed language using NbE. Based on [elaboration-zoo/03-holes](https://github.com/AndrasKovacs/elaboration-zoo/tree/master/03-holes). Has no frontend yet, but you can run tests with `scala-cli test holes.scala` |

## Resources

- [Elaboration Zoo](https://github.com/AndrasKovacs/elaboration-zoo)
- [Checking Dependent Types with Normalization by Evaluation: A Tutorial (Haskell Version)](https://davidchristiansen.dk/tutorials/implementing-types-hs.pdf)
