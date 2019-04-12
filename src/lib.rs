// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// An abstract interface for SMT solvers, parameterized by implementations of
// Sort, Term, and UninterpretedFunction.  This interface aims to mimic the
// SMT-LIB commands as closely as possible.  See  http:://www.smtlib.org for
// documentation on the SMT standard and interface.  See tests/test.rs for
// examples of how to use the interface.

pub mod smt_err;
pub mod smt_ops;

// Most functions return an SMTResult.  If an error is returned, there are three
// possibilities:
//   APIError - this results when the API is misused.
//   UnsupportedError - this results when the solver doesn't support a feature
//   InternalError - this results when the solver or a library call fails.
// See smt_err.rs for more details.
type SMTResult<T> = Result<T, smt_err::SMTError>;

// The result of calling check_sat is either satisfiable (Sat), unsatisfiable
// (Unsat), or unknown (Unknown).
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum CheckSatResult {
    Sat,
    Unsat,
    Unknown,
}

// An abstract data type for SMT sorts.
pub trait Sort: std::fmt::Debug + std::clone::Clone + Sized {
    // Get a string representing the SMT-LIB name for the Sort.  The only
    // possible error is InternalError.
    fn to_string(&self) -> SMTResult<String>;
}

// An abstract data type for uninterpreted function symbols.
pub trait UninterpretedFunction: std::fmt::Debug + std::clone::Clone + Sized {
    // Get the name of the uninterpreted function.  The only possible error is
    // InternalError.
    fn to_string(&self) -> SMTResult<String>;
}

// A Function is either a built-in operator or an uninterpreted function.
pub enum Function<F: UninterpretedFunction> {
    Op(smt_ops::Fn),
    UF(F),
}

// An abstract data type for SMT terms.
pub trait Term: std::fmt::Debug + std::clone::Clone + Sized {
    // Get a string for the SMT-LIB representation of the term.  The only
    // possible error is InternalError.
    fn to_string(&self) -> SMTResult<String>;

    // For terms that are constant values representable as i64, return the
    // corresponding i64 value.  Returns APIError if term is not a constant of
    // real, int, or bitvector type, or if it is a non-integral real constant,
    // or if the integral value doesn't fit in 64 bits.
    fn to_int(&self) -> SMTResult<i64>;
}

// An abstract data type for SMT solvers.
pub trait SMTSolver {
    type S: Sort;
    type T: Term;
    type F: UninterpretedFunction;

    // Return a new solver object.
    fn new() -> Self;

    ///////////////////////////////////////////////////////////////////////////
    // Sorts                                                                 //
    ///////////////////////////////////////////////////////////////////////////

    // Declare a new uninterpreted sort with the given name.  Only
    // InternalError errors are possible.
    fn declare_sort(&self, name: &str) -> SMTResult<Self::S>;

    // Lookup a built-in sort belonging to an SMT-LIB theory.  Returns an
    // APIError if s is a sort constructor (e.g. Array).
    fn lookup_sort(&self, s: smt_ops::Sorts) -> SMTResult<Self::S>;

    // Apply a built-in sort constructor of arity 2.  Returns an APIError if s
    // is not a sort constructor of arity 2.
    fn apply_sort(&self, s: smt_ops::Sorts, s1: &Self::S, s2: &Self::S) -> SMTResult<Self::S>;

    ///////////////////////////////////////////////////////////////////////////
    // Functions                                                             //
    ///////////////////////////////////////////////////////////////////////////

    // Declare a new uninterpreted function with the given name.  args specifies
    // the argument sorts, and sort specifies the return sort.  Returns an
    // UninterpretedFunction object.  Only InternalError errors are possible.
    fn declare_fun(&self, name: &str, args: &[&Self::S], sort: &Self::S) -> SMTResult<Self::F>;

    ///////////////////////////////////////////////////////////////////////////
    // Terms                                                                 //
    ///////////////////////////////////////////////////////////////////////////

    // Declare a new constant with a given name and sort.  Only InternalError
    // errors are possible.
    fn declare_const(&self, name: &str, sort: &Self::S) -> SMTResult<Self::T>;

    // Lookup a built-in constant belonging to an SMT-LIB theory.  Returns an
    // APIError if f is not a built-in constant.
    fn lookup_const(&self, f: smt_ops::Fn) -> SMTResult<Self::T>;

    // Construct a constant from a 64-bit integer of a given sort.  Supported
    // sorts are integer, real, and bitvector (for bitvector the value must be
    // non-negative and fit in the bit-width).  If an invalid sort is used or
    // an invalid value is used with a bitvector sort, the result is an
    // APIError.
    fn const_from_int(&self, value: i64, sort: &Self::S) -> SMTResult<Self::T>;

    // Construct a constant of a given sort from a numeric string.  Supported
    // sorts are integer, real, and bitvector.  Expects only digits
    // (non-bitvectors can also have a single unary minus at the beginning, and
    // reals can have at most one decimal point).  Currently does not check if
    // value fits within the bitwidth for bitvector sorts.  Behavior in that
    // case is dependent on the solver.
    fn const_from_string(&self, value: &str, sort: &Self::S) -> SMTResult<Self::T>;

    // Apply a function f to a vector of arguments to get a Term object.  f can
    // be either a built-in function operator or the result of an earlier call
    // to declare_fun.  The number and sorts of the terms in args should match
    // the arity and argument sorts of the function f.  Behavior if the
    // arguments are incorrect is solver-dependent.  If a solver does not
    // support an SMT-LIB operation, an UnsupportedError is returned.
    fn apply_fun(&self, f: &Function<Self::F>, args: &[Self::T]) -> SMTResult<Self::T>;

    // Sams as above, except the arguments are in a vector of references to
    // terms rather than a vector of terms.
    fn apply_fun_refs(&self, f: &Function<Self::F>, args: &[&Self::T]) -> SMTResult<Self::T>;

    ///////////////////////////////////////////////////////////////////////////
    // Solving                                                               //
    ///////////////////////////////////////////////////////////////////////////

    // Returns the current level of the solver.  Initially the level is 0.  The
    // level increases with each push and decreases with each pop.
    fn level(&self) -> u32;

    // A push sets a checkpoint in the state of the solver.  This method pushes
    // n times.  Returns Ok(true) if successful.  Otherwise, returns
    // InternalError.
    fn push(&mut self, n: u32) -> SMTResult<bool>;

    // A pop restores the solver to the state it had at the last checkpoint.
    // This method pops n times.  n must be less than or equal to the current
    // level.  If it is not, returns an APIError.  Otherwise, returns
    // InternalError if unsuccessful.
    fn pop(&mut self, n: u32) -> SMTResult<bool>;

    // Add an assertion t to the solver context.  The sort of the assertion must
    // be Boolean.  Returns Ok(true) if successful.  Otherwise returns
    // InternalError.
    fn assert(&mut self, t: &Self::T) -> SMTResult<bool>;

    // Check the satisfiability of all the assertions in the current solver
    // context.  Returns a CheckSatResult (see above).
    fn check_sat(&mut self) -> CheckSatResult;

    // After a call to check_sat that returns Sat, if the solver has model
    // production enabled, then it can report a concrete constant value for any
    // term t.  get_value returns that value, given a term t.  If check_sat has
    // not been called or if the most recent call returned unsat, an APIError
    // is returned.
    fn get_value(&mut self, t: &Self::T) -> SMTResult<Self::T>;
}

// Needed by z3.
#[macro_use]
extern crate lazy_static;
pub mod z3;

// A factory function for generating an instance of SMTSolver.
// Currently, it supports only z3, but the plan is to add other
// solvers eventually.
pub fn new_smt_solver(solver: &str) -> impl SMTSolver {
    match solver {
        "z3" => z3::Z3SMTSolver::new(),
        _ => panic!("Unknown solver"),
    }
}
