# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [2.0.0] - 2025-07-17

### Added

- Added reasoning on Flat ABA frameworks (ICCMA'25 queries)
- Added a command to produce the SAT encoding for a query
- Added the ability to use any IPASIR-compatible SAT solver library as an external solver
- A binary is now produce for the ICCMA'25 competition when compiling with the `iccma` feature
- Implemented SE-ST queries in a dynamic context

### Changed

- Renamed the project from Crustabri to Scalop
- Improved performance for DS-PR and SE-ID queries

### Fixed

- Fixed an issue that could prevent compilation on Windows

### Removed

- Removed inefficient dynamic-AF encodings where SAT assumptions are set on attacks

## [1.1.1] - 2024-01-24

### Fixed

- Added missing files.


## [1.1.0] - 2024-01-24

### Added

- Added other computation methods for dynamic track.


## [1.0.0] - 2023-09-06

### Added

- Added the content required for ICCMA'23 main track.
- Added the content required for ICCMA'23 dynamic track.
