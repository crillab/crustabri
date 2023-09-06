# Crustabri

Crustabri is a RUST ABstract argumentation Reasoner Implementation.

This project contains both a library and two binaries.
The library allows to create and modify static and dynamic argumentation frameworks, and to execute queries on them.
The first binary, `crustabri`, allows various operations on input argumentation frameworks. Type `crustabri -h` to get the description of the available subcommands and `crustabri <SUBCOMMAND> -h` for the help for a given subcommand.
The second binary, `crustabri_iccma23`, is a wrapper for Crustabri to be compatible with the [ICCMA'23 competition](https://argumentationcompetition.org/2023/index.html) requirements.

## License

Crustabri is developed at CRIL (Univ. Artois & CNRS).
It is made available under the terms of the GNU GPLv3 license.
