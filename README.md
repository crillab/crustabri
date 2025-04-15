# Crustabri

Crustabri is a RUST ABstract argumentation Reasoner Implementation.

This project contains both a library and from one to three binaries, depending on the selected features.
The library allows to create and modify static and dynamic argumentation frameworks, and to execute queries on them.
The first binary, `crustabri`, allows various operations on input argumentation frameworks. Type `crustabri -h` to get the description of the available subcommands and `crustabri <SUBCOMMAND> -h` for the help for a given subcommand.

If the `iccma` feature is present, e.g. by compiling with `cargo build --release --features iccma`, two additional binaries will be present.
The binary named `crustabri_iccma23` is a wrapper for Crustabri to be compatible with the [ICCMA'23 competition](https://argumentationcompetition.org/2023/index.html) requirements.
The binary named `crustabri_iccma25` is its counterpart for the 2025 edition of the competition;
the main difference with the `crustabri_iccma23` is its ability to use an IPASIR-compatible SAT solver pointed by the `IPASIR_LIBRARY` environment variable.

## Using an IPASIR SAT solver library

IPASIR is a simple C interface to incremental SAT solvers (it stands for Reentrant Incremental Sat solver API, in reverse.)
This interface is supported by a few different solvers because it is used in the SAT competition's incremental track.
Crustabri is able to use any SAT solver following the IPASIR interface in place of its builtin solver.

For example, download the latest version of Cadical from its [homepage](https://fmv.jku.at/cadical/) (the most recent one is cadical-sc2020-45029f8.tar.xz at the time of writing).
Extract the archive, then compile it with the flags required to build a shared library:

```
./configure CXXFLAGS=-fPIC
make -j
cd build
g++ -shared -o libcadical.so $(ls *.o | grep -v mobical.o)
IPASIR_LIBRARY=$(realpath libcadical.so)
```

This will create `libcadical.so` in the build directory of Cadical and set its path into the `IPASIR_LIBRARY` variable.
Then, you can use this solver instead of the builtin using the dedicated CLI option:

```
crustabri solve -f test.af -p SE-PR --ipasir-library "$IPASIR_LIBRARY"
```

## Using an external SAT solver

Any SAT solver following the input/output format of SAT competitions can be used to replace the builtin one.
Note that using an external SAT solver may decrease the performances of Crustabri, especially when dealing with complex semantics.

```
crustabri solve -f test.af -p SE-PR --external-sat-solver "$PATH_TO_SOLVER"
```

## License

Crustabri is developed at CRIL (Univ. Artois & CNRS).
It is made available under the terms of the GNU GPLv3 license.
