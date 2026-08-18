# Cube

Cube is an experimental proof assistant for the formalization of constructive mathematics as developed in the informal cubically-flavored style advocated by Bentzen <a id="1">[1]</a>. It implements a version of the cubical type theory with reflection-free extensional equality proposed by Sterling, Angiuli, and Gratzer <a id="1">[2]</a><a id="1">[3]</a>, facilitating formalization with proof irrelevance while maintaining core cubical features. 

## Installation

To install and use Cube, you need OCaml version 4.14.2 or greater. We also recommend relying on the [opam](https://opam.ocaml.org/) package manager for installation. You will also need [menhir](https://opam.ocaml.org/packages/menhir/) for the LR(1) parser generator, and [dune](https://github.com/ocaml/dune) for building the project. Both can be installed using opam. It is best to ensure that your opam is up-to-date before installing the dependencies:

```
$ opam update && opam upgrade
$ opam install menhir dune base
```

Next, clone the repository and build the project using dune:

```
$ git clone https://github.com/bbentzen/cube.git
$ cd cube
$ dune build
```

This will create the executable `main.exe` which you can run on any `.cube` file to typecheck its contents with Cube. Since this compiled executable is typically be found under a subfolder such as `_build/default/bin`, you can run it as follows:

```
$ dune exec _build/default/bin/main.exe <filename>.cube
```

However, we recommend using the cube-vscode extension for verification support. More information can be found at [cube-vscode/README.md](https://github.com/bbentzen/cube/blob/master/cube-vscode/README.md).

## Usage

Please see the reference manual on [doc/README.md](https://github.com/bbentzen/cube/blob/master/doc/README.md).

## Support

This work was partly supported by the US Air Force Office of Scientific Research (AFOSR) grant FA9550-18-1-0120. Any opinions, findings and conclusions, or recommendations expressed in this material are those of the author and do not necessarily reflect the views of the AFOSR.

## References

<a id="1">[1]</a> 
Bruno Bentzen. Naive cubical type theory. 
Mathematical Structures in Computer Science, 31, pp. 1205–1231, 2021.
[doi:10.1017/S096012952200007X](https://doi.org/10.1017/S096012952200007X), [arXiv:1911.05844](https://arxiv.org/abs/1911.05844).

<a id="1">[2]</a> 
Jonathan Sterling, Carlo Angiuli, Daniel Gratzer. 
Cubical syntax for reflection-free extensional equality. 
In Herman Geuvers (ed.), 4th International Conference on Formal Structures for Computation and Deduction (FSCD 2019), volume 131 of Leibniz International Proceedings in Informatics (LIPIcs), pages 31:1-31:25.
[doi:10.4230/LIPIcs.FSCD.2019.31](https://doi.org/10.4230/LIPIcs.FSCD.2019.31), [arXiv:1904.08562](https://arxiv.org/abs/1904.08562).

<a id="1">[3]</a> 
Jonathan Sterling, Carlo Angiuli, Daniel Gratzer. 
A Cubical Language for Bishop Sets. 
Logical Methods in Computer Science, 18 (1), 2022.
[doi:10.46298/lmcs-18(1:43)2022](https://doi.org/10.46298/lmcs-18(1:43)2022), [arXiv:2003.01491](https://arxiv.org/abs/2003.01491).