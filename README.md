# Rust-SMT-LIB-API  [![Build Status](https://travis-ci.com/facebookincubator/Rust-SMT-LIB-API.svg?token=eGmra6RUfZeknKfxxdBS&branch=master)](https://travis-ci.com/facebookincubator/Rust-SMT-LIB-API) [![codecov](https://codecov.io/gh/facebookincubator/Rust-SMT-LIB-API/branch/master/graph/badge.svg?token=ZvGjkOKO5l)](https://codecov.io/gh/facebookincubator/Rust-SMT-LIB-API)


This crate provides a generic high-level API for interacting with SMT
solvers.  The aim of this interface is to be solver-agnostic (i.e. the
user can switch between back-end SMT solvers by modifying a single
line of code) and to mimic the SMT-LIB standard commands as closely as
possible.  Currently, Z3 is supported as a back-end.  See links below
for more information on SMT-LIB and Z3.  See tests/test.rs for
examples of how to use the interface.

## Installing z3
* For linux systems with apt: sudo apt install libz3-dev
* For all other systems, follow the install instructions on the Z3 website (see below)

## Building
* Download or clone Rust-SMT-LIB-API
* cd to the root directory of Rust-SMT-LIB-API and run: cargo test

## Additional links
* [SMT-LIB standard and documentation](http://smtlib.org).
* [Z3 SMT solver](https://github.com/Z3Prover/z3).

## License
Rust-SMT-LIB-API is MIT licensed, as found in the [LICENSE](https://github.com/facebookincubator/Rust-SMT-LIB-API/blob/master/LICENSE) file.
