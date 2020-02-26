
# install

```shell
sudo apt upgrade opam
sudo apt autoremove

opam update
opam switch list-available
# opam switch create 4.09.0
opam switch create 4.09.0+flambda

git clone https://github.com/JHU-PL-Lab/odefa.git`
cd odefa
git checkout test-generation

# dune external-lib-deps --missing @@default
opam install batteries gmap jhupllib monadlib ocaml-monadic pds-reachability ppx_deriving ppx_deriving_yojson -y
opam pin z3 4.8.1 -y

export LD_LIBRARY_PATH=`opam config var z3:lib`

make
make test

# two error cases which should be fixed
```

# prepare stats

```shell

#mac
#sysctl -n machdep.cpu.brand_string
#vm_stat


#linux
lscpu
cat /proc/cpuinfo
#vmstat
free -m
uname -a

git rev-parse HEAD

ocaml -version
opam --version


sudo ln -s `opam config var z3:lib`/dllz3ml /usr/local/lib/dllz3ml
```

# prepare testing
