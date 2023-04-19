# Crustabri

Crustabri is a RUST ABstract argumentation Reasoner Implementation.

## Compiling

Compiling Crustabri requires a recent version of the Rust toolchain; see the [get started page](https://www.rust-lang.org/learn/get-started) on rust-lang.org.
Once installed, a call to `cargo build --release` should be sufficient to download the dependencies and to build the binaries in the `target/release` directory.
Note that compiling on the machine on which Crustabri will be launched (or at least on an identical system) may prevent some compatibility issues.

The `cargo` tool will download and compile the dependencies, including the CaDiCaL SAT solver.
This means that the machine on which Crustabri is built requires an internet connection and a recent C/C++ compiler.
In case a network connection is not available on the machine, `cargo vendor` should be the solution.
A call to this command should download the dependencies, put them in the `vendor` directory, and give the content of a `.cargo/config.toml` file.
Putting both the `vendor` directory and the populated `.cargo/config.toml` file in the root folder of Crustabri should be sufficient to prevent the use of the internet connection.

Compiling the project produces three binaries in the `target/release` directory:

  * `crustabri`, the main program with its own command line arguments usage
  * `crustabri_iccma23`, a wrapper which command line usage fits the ICCMA'23 main track competition requirements
  * `crustabri_iccma23_aba`, a wrapper which command line usage fits the ICCMA'23 ABA track competition requirements

## License

Crustabri is developed at CRIL (Univ. Artois & CNRS).
It is made available under the terms of the GNU GPLv3 license.
