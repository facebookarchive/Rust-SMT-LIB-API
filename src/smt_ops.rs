// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

pub enum Sorts {
    // Core theory
    Bool,

    // Arithmetic
    Int,
    Real,

    // Arrays
    Array,

    // Bitvectors
    BitVec(u32),
}

pub enum Fn<'a> {
    // Core theory
    False,
    True,
    Not,
    Implies,
    And,
    Or,
    Xor,
    Eq,
    Neq, // abbreviation for Not o Eq
    Ite,
    Distinct,

    // Arithmetic
    Uminus,
    Minus,
    Plus,
    Times,
    Divide,
    Div,
    Mod,
    Abs,
    LE,
    LT,
    GE,
    GT,
    ToReal,
    ToInt,
    IsInt,

    // Arrays
    Select,
    Store,

    // Records
    RecordSelect(&'a str),
    RecordUpdate(&'a str),

    // Bitvectors
    Concat,
    Extract(u32, u32),
    Bvnot,
    Bvand,
    Bvor,
    Bvneg,
    Bvadd,
    Bvmul,
    Bvudiv,
    Bvurem,
    Bvshl,
    Bvlshr,
    Bvult,
    Bvnand,
    Bvnor,
    Bvxor,
    Bvxnor,
    Bvcomp,
    Bvsub,
    Bvsdiv,
    Bvsrem,
    Bvsmod,
    Bvashr,
    Repeat(u32),
    ZeroExtend(u32),
    SignExtend(u32),
    RotateLeft(u32),
    RotateRight(u32),
    Bvule,
    Bvugt,
    Bvuge,
    Bvslt,
    Bvsle,
    Bvsgt,
    Bvsge,
}
