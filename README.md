## Acknowledgments

Based on the [work](https://gitlab.inria.fr/cambium/cosmo) of Glen Mével, Jacques-Henri Jourdan and François Pottier.

## Building

First, you need to install [`opam`](https://opam.ocaml.org/) (>= 2.0).

To make sure it is up-to-date, run:

```
opam update --all --repositories
```

Then, create a new local `opam` switch and install dependencies with:

```
opam switch create . --deps-only --repos default,coq-released=https://coq.inria.fr/opam/released,iris-dev=git+https://gitlab.mpi-sws.org/iris/opam.git --yes
eval $(opam env --switch=. --set-switch)
```

Finally, to compile Coq proofs, run:

```
make -j
```
