Odefa
=====

Artifact for the paper **Higher-Order Demand-Driven Symbolic Evaluation**.


Install
-------

sudo apt upgrade opam
opam update
opam switch create 4.09.0+flambda

Install
-------


```
# dune external-lib-deps --missing @@default
opam install shexp core batteries gmap jhupllib monadlib ocaml-monadic pds-reachability ppx_deriving ppx_deriving_yojson -y
opam pin z3 4.8.1 -y
```

```
export LD_LIBRARY_PATH=`opam config var z3:lib`
````


```
make
make test
make benchmark
```
