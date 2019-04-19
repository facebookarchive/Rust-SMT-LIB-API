// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use rust_smt::smt_err::*;
use rust_smt::smt_ops::*;
use rust_smt::Function::*;
use rust_smt::*;

#[test]
fn test_create_solver() {
    let _smt = new_z3_solver();
}

#[test]
fn test_declare_sort() {
    let smt = new_z3_solver();
    let s = smt.declare_sort("s").unwrap();
    assert_eq!(s.to_string().unwrap(), "s");
}

#[test]
fn test_lookup_sort_bool() {
    let smt = new_z3_solver();
    let bool_sort = smt.lookup_sort(Sorts::Bool).unwrap();
    assert_eq!(bool_sort.to_string().unwrap(), "Bool");
}

#[test]
fn test_lookup_sort_int() {
    let smt = new_z3_solver();
    let int_sort = smt.lookup_sort(Sorts::Int).unwrap();
    assert_eq!(int_sort.to_string().unwrap(), "Int");
}

#[test]
fn test_lookup_sort_real() {
    let smt = new_z3_solver();
    let real_sort = smt.lookup_sort(Sorts::Real).unwrap();
    assert_eq!(real_sort.to_string().unwrap(), "Real");
}

#[test]
fn test_lookup_sort_bitvec8() {
    let smt = new_z3_solver();
    let bv8_sort = smt.lookup_sort(Sorts::BitVec(8)).unwrap();
    assert_eq!(bv8_sort.to_string().unwrap(), "(_ BitVec 8)");
}

#[test]
fn test_lookup_sort_array_error() {
    let smt = new_z3_solver();
    assert_eq!(
        smt.lookup_sort(Sorts::Array).unwrap_err(),
        SMTError::new_api("Use apply_sort to create Array sorts")
    );
}

#[test]
fn test_apply_sort_array_int_int() {
    let smt = new_z3_solver();
    let int_sort = smt.lookup_sort(Sorts::Int).unwrap();
    let array_sort = smt.apply_sort(Sorts::Array, &int_sort, &int_sort).unwrap();
    assert_eq!(array_sort.to_string().unwrap(), "(Array Int Int)");
}

#[test]
fn test_apply_sort_error() {
    let smt = new_z3_solver();
    let int_sort = smt.lookup_sort(Sorts::Int).unwrap();
    assert_eq!(
        smt.apply_sort(Sorts::Int, &int_sort, &int_sort)
            .unwrap_err(),
        SMTError::new_api("apply_sort called with non-sort constructor")
    );
}

#[test]
fn test_declare_record_sort() {
    let smt = new_z3_solver();
    let int_sort = smt.lookup_sort(Sorts::Int).unwrap();
    let record_sort = smt.declare_record_sort(&[&int_sort, &int_sort]).unwrap();
    assert_eq!(record_sort.to_string().unwrap(), "Record");
}

#[test]
fn test_declare_fun() {
    let smt = new_z3_solver();
    let int_sort = smt.lookup_sort(Sorts::Int).unwrap();
    let f = smt.declare_fun("f", &[&int_sort], &int_sort).unwrap();
    assert_eq!(f.to_string().unwrap(), "f");
}

#[test]
fn test_declare_const() {
    let smt = new_z3_solver();
    let s = smt.lookup_sort(Sorts::Int).unwrap();
    let x = smt.declare_const("x", &s).unwrap();
    assert_eq!(x.to_string().unwrap(), "x");
}

#[test]
fn test_clone_term() {
    let smt = new_z3_solver();
    let s = smt.lookup_sort(Sorts::Int).unwrap();
    let x = smt.declare_const("x", &s).unwrap();
    let x_prime = x.clone();
    assert_eq!(x.to_string().unwrap(), x_prime.to_string().unwrap());
}

#[test]
fn test_lookup_const_true() {
    let smt = new_z3_solver();
    let t = smt.lookup_const(Fn::True).unwrap();
    assert_eq!(t.to_string().unwrap(), "true");
}

#[test]
fn test_lookup_const_false() {
    let smt = new_z3_solver();
    let f = smt.lookup_const(Fn::False).unwrap();
    assert_eq!(f.to_string().unwrap(), "false");
}

#[test]
fn test_lookup_nonconst_error() {
    let smt = new_z3_solver();
    assert_eq!(
        smt.lookup_const(Fn::Uminus).unwrap_err(),
        SMTError::new_api("lookup_const called with non-constant")
    );
}

#[test]
fn test_symbolic_const_to_int_error() {
    let smt = new_z3_solver();
    let int_sort = smt.lookup_sort(Sorts::Int).unwrap();
    let x = smt.declare_const("x", &int_sort).unwrap();
    assert_eq!(
        x.to_int().unwrap_err(),
        SMTError::new_api("Term::to_int: term is not a numeric constant")
    );
}

#[test]
fn test_bad_sorted_const_to_int_error() {
    let smt = new_z3_solver();
    let bool_sort = smt.lookup_sort(Sorts::Bool).unwrap();
    let b = smt.declare_const("b", &bool_sort).unwrap();
    assert_eq!(
        b.to_int().unwrap_err(),
        SMTError::new_api("Term::to_int: sort of term is not int, real, or bitvector")
    );
}

#[test]
fn test_non_int_real_const_to_int_error() {
    let smt = new_z3_solver();
    let real_sort = smt.lookup_sort(Sorts::Real).unwrap();
    let x = smt.const_from_string("0.5", &real_sort).unwrap();
    assert_eq!(
        x.to_int().unwrap_err(),
        SMTError::new_api("Term::to_int: unable to convert to 64-bit integer")
    );
}

#[test]
fn test_const_from_int_to_int() {
    let smt = new_z3_solver();
    let int_sort = smt.lookup_sort(Sorts::Int).unwrap();
    assert_eq!(
        smt.const_from_int(0, &int_sort).unwrap().to_int().unwrap(),
        0
    );
    assert_eq!(
        smt.const_from_int(-1000, &int_sort)
            .unwrap()
            .to_int()
            .unwrap(),
        -1000
    );
    assert_eq!(
        smt.const_from_int(32768, &int_sort)
            .unwrap()
            .to_int()
            .unwrap(),
        32768
    );
}

#[test]
fn test_const_from_int_to_real() {
    let smt = new_z3_solver();
    let real_sort = smt.lookup_sort(Sorts::Real).unwrap();
    assert_eq!(
        smt.const_from_int(1, &real_sort)
            .unwrap()
            .to_string()
            .unwrap(),
        "1.0"
    );
    assert_eq!(
        smt.const_from_int(-1234, &real_sort)
            .unwrap()
            .to_string()
            .unwrap(),
        "(- 1234.0)"
    );
    assert_eq!(
        smt.const_from_int(100000, &real_sort)
            .unwrap()
            .to_string()
            .unwrap(),
        "100000.0"
    );
}

#[test]
fn test_const_from_int_to_bv() {
    let smt = new_z3_solver();
    let bv8_sort = smt.lookup_sort(Sorts::BitVec(8)).unwrap();
    assert_eq!(
        smt.const_from_int(1, &bv8_sort)
            .unwrap()
            .to_string()
            .unwrap(),
        "#x01"
    );
    assert_eq!(
        smt.const_from_int(123, &bv8_sort)
            .unwrap()
            .to_string()
            .unwrap(),
        "#x7b"
    );
    assert_eq!(
        smt.const_from_int(0xFF, &bv8_sort)
            .unwrap()
            .to_string()
            .unwrap(),
        "#xff"
    );
}

#[test]
fn test_const_from_int_to_bv_to_int() {
    let smt = new_z3_solver();
    let bv8_sort = smt.lookup_sort(Sorts::BitVec(8)).unwrap();
    assert_eq!(
        smt.const_from_int(1, &bv8_sort).unwrap().to_int().unwrap(),
        1
    );
    assert_eq!(
        smt.const_from_int(123, &bv8_sort)
            .unwrap()
            .to_int()
            .unwrap(),
        123
    );
    assert_eq!(
        smt.const_from_int(0xFF, &bv8_sort)
            .unwrap()
            .to_int()
            .unwrap(),
        255
    );
}

#[test]
fn test_const_from_int_bad_sort_error() {
    let smt = new_z3_solver();
    let bool_sort = smt.lookup_sort(Sorts::Bool).unwrap();
    assert_eq!(
        smt.const_from_int(1, &bool_sort).unwrap_err(),
        SMTError::new_api("const_from_int: sort of term is not int, real, or bitvector")
    );
}

#[test]
fn test_const_from_int_negative_bv_error() {
    let smt = new_z3_solver();
    let bv16_sort = smt.lookup_sort(Sorts::BitVec(16)).unwrap();
    assert_eq!(
        smt.const_from_int(-1, &bv16_sort).unwrap_err(),
        SMTError::new_api(
            "const_from_int: bitvector requires non-negative value representable in the bit-width"
        )
    );
}

#[test]
fn test_const_from_int_bv_too_large_error() {
    let smt = new_z3_solver();
    let bv16_sort = smt.lookup_sort(Sorts::BitVec(16)).unwrap();
    assert_eq!(
        smt.const_from_int(65535, &bv16_sort)
            .unwrap()
            .to_string()
            .unwrap(),
        "#xffff"
    );
    assert_eq!(
        smt.const_from_int(65536, &bv16_sort).unwrap_err(),
        SMTError::new_api(
            "const_from_int: bitvector requires non-negative value representable in the bit-width"
        )
    );
}

#[test]
fn test_const_from_string_to_int() {
    let smt = new_z3_solver();
    let int_sort = smt.lookup_sort(Sorts::Int).unwrap();
    assert_eq!(
        smt.const_from_string("0", &int_sort)
            .unwrap()
            .to_string()
            .unwrap(),
        "0"
    );
    assert_eq!(
        smt.const_from_string("-1000000000000000", &int_sort)
            .unwrap()
            .to_string()
            .unwrap(),
        "(- 1000000000000000)"
    );
    assert_eq!(
        smt.const_from_string("123456789012345678901234567890", &int_sort)
            .unwrap()
            .to_string()
            .unwrap(),
        "123456789012345678901234567890"
    );
}

#[test]
fn test_const_from_string_to_real() {
    let smt = new_z3_solver();
    let real_sort = smt.lookup_sort(Sorts::Real).unwrap();
    assert_eq!(
        smt.const_from_string("100", &real_sort)
            .unwrap()
            .to_string()
            .unwrap(),
        "100.0"
    );
    assert_eq!(
        smt.const_from_string("0.25", &real_sort)
            .unwrap()
            .to_string()
            .unwrap(),
        "(/ 1.0 4.0)"
    );
    assert_eq!(
        smt.const_from_string("123456789012345678901234567890", &real_sort)
            .unwrap()
            .to_string()
            .unwrap(),
        "123456789012345678901234567890.0"
    );
}

#[test]
fn test_const_from_string_to_bv() {
    let smt = new_z3_solver();
    let bv256_sort = smt.lookup_sort(Sorts::BitVec(256)).unwrap();
    assert_eq!(
        smt.const_from_string("100", &bv256_sort)
            .unwrap()
            .to_string()
            .unwrap(),
        "#x0000000000000000000000000000000000000000000000000000000000000064"
    );
    assert_eq!(
        smt.const_from_string("65536", &bv256_sort)
            .unwrap()
            .to_string()
            .unwrap(),
        "#x0000000000000000000000000000000000000000000000000000000000010000"
    );
    assert_eq!(
        smt.const_from_string("123456789012345678901234567890", &bv256_sort)
            .unwrap()
            .to_string()
            .unwrap(),
        "#x00000000000000000000000000000000000000018ee90ff6c373e0ee4e3f0ad2"
    );
}

#[test]
fn test_const_from_string_bad_sort_error() {
    let smt = new_z3_solver();
    let bool_sort = smt.lookup_sort(Sorts::Bool).unwrap();
    assert_eq!(
        smt.const_from_string("1", &bool_sort).unwrap_err(),
        SMTError::new_api("const_from_string: sort must be int, real or bitvector")
    );
}

#[test]
fn test_const_from_string_decimal_in_int_error() {
    let smt = new_z3_solver();
    let int_sort = smt.lookup_sort(Sorts::Int).unwrap();
    assert_eq!(
        smt.const_from_string("1.0", &int_sort).unwrap_err(),
        SMTError::new_api("const_from_string: decimal not allowed in non-real")
    );
}

#[test]
fn test_const_from_string_too_many_decimals_error() {
    let smt = new_z3_solver();
    let real_sort = smt.lookup_sort(Sorts::Real).unwrap();
    assert_eq!(
        smt.const_from_string("1.0.", &real_sort).unwrap_err(),
        SMTError::new_api("const_from_string: no more than one decimal place allowed")
    )
}

#[test]
fn test_const_from_string_neg_bitvector_error() {
    let smt = new_z3_solver();
    let bv32_sort = smt.lookup_sort(Sorts::BitVec(32)).unwrap();
    assert_eq!(
        smt.const_from_string("-1", &bv32_sort).unwrap_err(),
        SMTError::new_api("const_from_string: negative value not allowed for bitvectors")
    );
}

#[test]
fn test_const_from_string_invalid_char_error() {
    let smt = new_z3_solver();
    let bv32_sort = smt.lookup_sort(Sorts::BitVec(32)).unwrap();
    assert_eq!(
        smt.const_from_string("1234567890ABCDEF", &bv32_sort)
            .unwrap_err(),
        SMTError::new_api("const_from_string: string contains invalid character: digit expected")
    );
}

#[test]
fn test_apply_fun_uf() {
    let smt = new_z3_solver();
    let int_sort = smt.lookup_sort(Sorts::Int).unwrap();
    let f = UF(smt.declare_fun("f", &[&int_sort], &int_sort).unwrap());
    let x = smt.declare_const("x", &int_sort).unwrap();
    let fx = smt.apply_fun(&f, &[x]).unwrap();
    assert_eq!(fx.to_string().unwrap(), "(f x)");
}

#[test]
fn test_apply_fun_core() {
    let smt = new_z3_solver();
    let bool_sort = smt.lookup_sort(Sorts::Bool).unwrap();
    let p = smt.declare_const("p", &bool_sort).unwrap();
    let q = smt.declare_const("q", &bool_sort).unwrap();
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Not), &[&p])
            .unwrap()
            .to_string()
            .unwrap(),
        "(not p)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Implies), &[&p, &q])
            .unwrap()
            .to_string()
            .unwrap(),
        "(=> p q)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::And), &[&p, &q])
            .unwrap()
            .to_string()
            .unwrap(),
        "(and p q)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Or), &[&p, &q])
            .unwrap()
            .to_string()
            .unwrap(),
        "(or p q)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Xor), &[&p, &q])
            .unwrap()
            .to_string()
            .unwrap(),
        "(xor p q)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Eq), &[&p, &q])
            .unwrap()
            .to_string()
            .unwrap(),
        "(= p q)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Ite), &[&p, &q, &p])
            .unwrap()
            .to_string()
            .unwrap(),
        "(ite p q p)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Distinct), &[&p, &q])
            .unwrap()
            .to_string()
            .unwrap(),
        "(distinct p q)"
    );
}

#[test]
fn test_apply_fun_arith() {
    let smt = new_z3_solver();
    let int_sort = smt.lookup_sort(Sorts::Int).unwrap();
    let real_sort = smt.lookup_sort(Sorts::Real).unwrap();
    let x = smt.declare_const("x", &int_sort).unwrap();
    let y = smt.declare_const("y", &int_sort).unwrap();
    let z = smt.declare_const("z", &int_sort).unwrap();
    let a = smt.declare_const("a", &real_sort).unwrap();
    let b = smt.declare_const("b", &real_sort).unwrap();
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Uminus), &[&x])
            .unwrap()
            .to_string()
            .unwrap(),
        "(- x)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Minus), &[&a, &b])
            .unwrap()
            .to_string()
            .unwrap(),
        "(- a b)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Plus), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(+ x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Times), &[&x, &y, &z])
            .unwrap()
            .to_string()
            .unwrap(),
        "(* x y z)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Divide), &[&a, &b])
            .unwrap()
            .to_string()
            .unwrap(),
        "(/ a b)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Div), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(div x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Mod), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(mod x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Abs), &[&x, &y]).unwrap_err(),
        SMTError::new_unsupported("Z3 does not support abs")
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::LE), &[&a, &b])
            .unwrap()
            .to_string()
            .unwrap(),
        "(<= a b)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::LT), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(< x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::GE), &[&a, &b])
            .unwrap()
            .to_string()
            .unwrap(),
        "(>= a b)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::GT), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(> x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::ToReal), &[&x])
            .unwrap()
            .to_string()
            .unwrap(),
        "(to_real x)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::ToInt), &[&a])
            .unwrap()
            .to_string()
            .unwrap(),
        "(to_int a)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::IsInt), &[&b])
            .unwrap()
            .to_string()
            .unwrap(),
        "(is_int b)"
    );
}

#[test]
fn test_apply_fun_array() {
    let smt = new_z3_solver();
    let index_sort = smt.declare_sort("A").unwrap();
    let element_sort = smt.declare_sort("B").unwrap();
    let array_sort = smt
        .apply_sort(Sorts::Array, &index_sort, &element_sort)
        .unwrap();
    let a = smt.declare_const("a", &array_sort).unwrap();
    let i = smt.declare_const("i", &index_sort).unwrap();
    let x = smt.declare_const("x", &element_sort).unwrap();
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Select), &[&a, &i])
            .unwrap()
            .to_string()
            .unwrap(),
        "(select a i)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Store), &[&a, &i, &x])
            .unwrap()
            .to_string()
            .unwrap(),
        "(store a i x)"
    );
}

#[test]
fn test_apply_fun_bitvec() {
    let smt = new_z3_solver();
    let bv32_sort = smt.lookup_sort(Sorts::BitVec(32)).unwrap();
    let x = smt.declare_const("x", &bv32_sort).unwrap();
    let y = smt.declare_const("y", &bv32_sort).unwrap();
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Concat), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(concat x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvnot), &[&x])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvnot x)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvand), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvand x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvor), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvor x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvneg), &[&x])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvneg x)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvadd), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvadd x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvmul), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvmul x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvudiv), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvudiv x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvurem), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvurem x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvshl), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvshl x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvlshr), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvlshr x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvult), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvult x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvnand), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvnand x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvnor), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvnor x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvxor), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvxor x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvcomp), &[&x, &y]).unwrap_err(),
        SMTError::new_unsupported("Z3 does not support bvcomp")
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvxnor), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvxnor x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvsub), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvsub x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvsdiv), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvsdiv x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvsrem), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvsrem x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvsmod), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvsmod x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvashr), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvashr x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvule), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvule x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvugt), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvugt x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvuge), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvuge x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvslt), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvslt x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvsle), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvsle x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvsgt), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvsgt x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Bvsge), &[&x, &y])
            .unwrap()
            .to_string()
            .unwrap(),
        "(bvsge x y)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Repeat(2)), &[&x])
            .unwrap()
            .to_string()
            .unwrap(),
        "((_ repeat 2) x)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::ZeroExtend(2)), &[&x])
            .unwrap()
            .to_string()
            .unwrap(),
        "((_ zero_extend 2) x)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::SignExtend(3)), &[&x])
            .unwrap()
            .to_string()
            .unwrap(),
        "((_ sign_extend 3) x)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::RotateLeft(4)), &[&x])
            .unwrap()
            .to_string()
            .unwrap(),
        "((_ rotate_left 4) x)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::RotateRight(5)), &[&x])
            .unwrap()
            .to_string()
            .unwrap(),
        "((_ rotate_right 5) x)"
    );
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::Extract(7, 0)), &[&x])
            .unwrap()
            .to_string()
            .unwrap(),
        "((_ extract 7 0) x)"
    );
}

#[test]
fn test_apply_fun_record_select() {
    let smt = new_z3_solver();
    let int_sort = smt.lookup_sort(Sorts::Int).unwrap();
    let record_sort = smt.declare_record_sort(&[&int_sort, &int_sort]).unwrap();
    let r = smt.declare_const("r", &record_sort).unwrap();
    assert_eq!(
        smt.apply_fun_refs(&Op(Fn::RecordSelect(0)), &[&r])
            .unwrap()
            .to_string()
            .unwrap(),
        "(Record_sel_0 r)"
    );
}

#[test]
fn test_level() {
    let smt = new_z3_solver();
    assert_eq!(smt.level(), 0);
}

#[test]
fn test_push_pop() {
    let mut smt = new_z3_solver();
    smt.push(1).unwrap();
    assert_eq!(smt.level(), 1);
    smt.pop(1).unwrap();
    assert_eq!(smt.level(), 0);
}

#[test]
fn test_pop_too_far_error() {
    let mut smt = new_z3_solver();
    smt.push(1).unwrap();
    assert_eq!(
        smt.pop(2).unwrap_err(),
        SMTError::new_api("pop: called with n > level")
    );
}

#[test]
fn test_assert() {
    let mut smt = new_z3_solver();
    smt.assert(&smt.lookup_const(Fn::True).unwrap()).unwrap();
}

#[test]
fn test_check_sat_true() {
    let mut smt = new_z3_solver();
    smt.assert(&smt.lookup_const(Fn::True).unwrap()).unwrap();
    assert_eq!(smt.check_sat(), CheckSatResult::Sat);
}

#[test]
fn test_check_sat_false() {
    let mut smt = new_z3_solver();
    smt.assert(&smt.lookup_const(Fn::False).unwrap()).unwrap();
    assert_eq!(smt.check_sat(), CheckSatResult::Unsat);
}

#[test]
fn test_check_sat_xlty() {
    let mut smt = new_z3_solver();
    let int_sort = smt.lookup_sort(Sorts::Int).unwrap();
    let x = smt.declare_const("x", &int_sort).unwrap();
    let y = smt.declare_const("y", &int_sort).unwrap();
    let x_lt_y = smt.apply_fun_refs(&Op(Fn::LT), &[&x, &y]).unwrap();
    smt.assert(&x_lt_y).unwrap();
    let smt_result = smt.check_sat();
    assert_eq!(smt_result, CheckSatResult::Sat);
}

#[test]
fn test_check_sat_xnoteqx() {
    let mut smt = new_z3_solver();
    let s = smt.declare_sort("s").unwrap();
    let x = smt.declare_const("x", &s).unwrap();
    let xeqx = smt.apply_fun_refs(&Op(Fn::Eq), &[&x, &x]).unwrap();
    let xnoteqx = smt.apply_fun_refs(&Op(Fn::Not), &[&xeqx]).unwrap();
    smt.assert(&xnoteqx).unwrap();
    let smt_result = smt.check_sat();
    assert_eq!(smt_result, CheckSatResult::Unsat);
}

#[test]
fn test_check_sat_with_push() {
    let mut smt = new_z3_solver();
    let int_sort = smt.lookup_sort(Sorts::Int).unwrap();
    let x = smt.declare_const("x", &int_sort).unwrap();
    let y = smt.declare_const("y", &int_sort).unwrap();
    let f = UF(smt.declare_fun("f", &[&int_sort], &int_sort).unwrap());
    let fx = smt.apply_fun_refs(&f, &[&x]).unwrap();
    let fy = smt.apply_fun_refs(&f, &[&y]).unwrap();
    let fx_eq_fy = smt.apply_fun_refs(&Op(Fn::Eq), &[&fx, &fy]).unwrap();
    smt.assert(&smt.apply_fun_refs(&Op(Fn::Not), &[&fx_eq_fy]).unwrap())
        .unwrap();
    smt.push(1).unwrap();
    smt.assert(&smt.apply_fun_refs(&Op(Fn::Eq), &[&x, &y]).unwrap())
        .unwrap();
    assert_eq!(smt.check_sat(), CheckSatResult::Unsat);
    smt.pop(1).unwrap();
    assert_eq!(smt.check_sat(), CheckSatResult::Sat);
}

#[test]
fn test_get_value() {
    let mut smt = new_z3_solver();
    let int_sort = smt.lookup_sort(Sorts::Int).unwrap();
    let x = smt.declare_const("x", &int_sort).unwrap();
    let xeq0 = smt
        .apply_fun_refs(
            &Op(Fn::Eq),
            &[&x, &smt.const_from_int(0, &int_sort).unwrap()],
        )
        .unwrap();
    smt.assert(&xeq0).unwrap();
    assert_eq!(smt.check_sat(), CheckSatResult::Sat);
    let value = smt.get_value(&x).unwrap();
    assert_eq!(value.to_string().unwrap(), "0");
}

#[test]
fn test_get_value_after_unsat_error() {
    let mut smt = new_z3_solver();
    let s = smt.declare_sort("s").unwrap();
    let x = smt.declare_const("x", &s).unwrap();
    let xeqx = smt.apply_fun_refs(&Op(Fn::Eq), &[&x, &x]).unwrap();
    let xnoteqx = smt.apply_fun_refs(&Op(Fn::Not), &[&xeqx]).unwrap();
    smt.assert(&xnoteqx).unwrap();
    let smt_result = smt.check_sat();
    assert_eq!(smt_result, CheckSatResult::Unsat);
    assert_eq!(
        smt.get_value(&x).unwrap_err(),
        SMTError::new_api(
            "get_value: can only be called after a call to check_sat that returns Sat"
        )
    );
}

#[test]
fn test_push_pop_get_model() {
    let mut smt = new_z3_solver();
    let x = smt
        .declare_const("x", &smt.lookup_sort(Sorts::Int).unwrap())
        .unwrap();
    smt.push(1).unwrap();
    let smt_result = smt.check_sat();
    assert_eq!(smt_result, CheckSatResult::Sat);
    let _value = smt.get_value(&x).unwrap();
    smt.pop(1).unwrap();
}
