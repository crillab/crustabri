# Crustabri

Crustabri is a RUST ABstract argumentation Reasoner Implementation.

This project contains both a library and from one to three binaries, depending on the selected features.
The library allows to create and modify static and dynamic argumentation frameworks, and to execute queries on them.
The first binary, `crustabri`, allows various operations on input argumentation frameworks. Type `crustabri -h` to get the description of the available subcommands and `crustabri <SUBCOMMAND> -h` for the help for a given subcommand.

If the `iccma` feature is present, e.g. by compiling with `cargo build --release --features iccma`, two additional bianries will be present.
The binary named `crustabri_iccma23` is a wrapper for Crustabri to be compatible with the [ICCMA'23 competition](https://argumentationcompetition.org/2023/index.html) requirements.
The binary named `crustabri_iccma25` is its counterpart for the 2025 edition of the competition;
the main difference with the `crustabri_iccma23` is its ability to use an IPASIR-compatible SAT solver pointed by the `IPASIR_LIBRARY` environment variable.

## License

Crustabri is developed at CRIL (Univ. Artois & CNRS).
It is made available under the terms of the GNU GPLv3 license.
