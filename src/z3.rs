// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// This file contains an implementation of the SMTSolver trait using
// the Z3 SMT solver.  We use the z3-sys crate for bindings to Z3.

use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::error::Error;
use std::ffi::{CStr, CString};

extern crate z3_sys;
use z3_sys::*;

use crate::smt_err::SMTError;
use crate::smt_ops::*;
use crate::Function::*;
use crate::*;

// Z3 is not thread-safe, so we guard each call to Z3 using the
// following semaphore.  This imposes some overhead, so if
// thread-safety is not required, it can be disabled (see below).
use std::sync::Mutex;
lazy_static! {
    static ref Z3_MUTEX: Mutex<()> = Mutex::new(());
}

// Macro for thread-safety.  If not needed, comment this out and
// replace with the line below it.
macro_rules! mutex {
    () => {
        let _mutex = Z3_MUTEX.lock().unwrap();
    };
}
// macro_rules! mutex { () => { }; }

// Implementation of Sort for Z3.
#[derive(Debug, Eq, Hash, PartialEq)]
pub struct Z3Sort {
    context: Z3_context,
    sort: Z3_sort,
}

fn new_z3_sort(context: Z3_context, sort: Z3_sort, mutex: bool) -> Z3Sort {
    unsafe {
        if mutex {
            mutex!();
        }
        Z3_inc_ref(context, Z3_sort_to_ast(context, sort));
    }
    Z3Sort { context, sort }
}

impl Clone for Z3Sort {
    fn clone(&self) -> Z3Sort {
        new_z3_sort(self.context, self.sort, true)
    }
}

impl Drop for Z3Sort {
    fn drop(&mut self) {
        unsafe {
            mutex!();
            Z3_dec_ref(self.context, Z3_sort_to_ast(self.context, self.sort));
        }
    }
}

impl Sort for Z3Sort {
    fn to_string(&self) -> SMTResult<String> {
        unsafe {
            mutex!();
            let ptr = Z3_sort_to_string(self.context, self.sort) as *mut i8;
            if ptr.is_null() {
                Err(SMTError::new_internal("Unable to convert Sort to string"))
            } else {
                let cstr = CStr::from_ptr(ptr);
                match cstr.to_str() {
                    Ok(s) => Ok(String::from(s)),
                    Err(e) => Err(SMTError::new_internal(e.description())),
                }
            }
        }
    }
}

// Implementation of UninterpretedFunction for Z3.
#[derive(Debug, Eq, Hash, PartialEq)]
pub struct Z3UninterpretedFunction {
    context: Z3_context,
    decl: Z3_func_decl,
}

fn new_z3_uninterpreted_function(
    context: Z3_context,
    decl: Z3_func_decl,
    mutex: bool,
) -> Z3UninterpretedFunction {
    unsafe {
        if mutex {
            mutex!();
        }
        Z3_inc_ref(context, Z3_func_decl_to_ast(context, decl));
        Z3UninterpretedFunction { context, decl }
    }
}

impl Clone for Z3UninterpretedFunction {
    fn clone(&self) -> Z3UninterpretedFunction {
        new_z3_uninterpreted_function(self.context, self.decl, true)
    }
}

impl Drop for Z3UninterpretedFunction {
    fn drop(&mut self) {
        unsafe {
            mutex!();
            Z3_dec_ref(self.context, Z3_func_decl_to_ast(self.context, self.decl));
        }
    }
}

impl UninterpretedFunction for Z3UninterpretedFunction {
    fn to_string(&self) -> SMTResult<String> {
        unsafe {
            mutex!();
            let ptr = Z3_get_decl_name(self.context, self.decl);
            if ptr.is_null() {
                Err(SMTError::new_internal(
                    "Unable to get name for UninterpretedFunction",
                ))
            } else {
                let ptr = Z3_get_symbol_string(self.context, ptr);
                if ptr.is_null() {
                    Err(SMTError::new_internal(
                        "Unable to convert UninterpretedFunction name to string",
                    ))
                } else {
                    let cstr = CStr::from_ptr(ptr);
                    match cstr.to_str() {
                        Ok(s) => Ok(String::from(s)),
                        Err(e) => Err(SMTError::new_internal(e.description())),
                    }
                }
            }
        }
    }
}

// Implementation of Term for Z3.
#[derive(Debug, Eq, Hash, PartialEq)]
pub struct Z3Term {
    context: Z3_context,
    ast: Z3_ast,
}

fn new_z3_term(context: Z3_context, ast: Z3_ast, mutex: bool) -> Z3Term {
    unsafe {
        if mutex {
            mutex!();
        }
        Z3_inc_ref(context, ast);
    }
    Z3Term { context, ast }
}

impl Clone for Z3Term {
    fn clone(&self) -> Z3Term {
        new_z3_term(self.context, self.ast, true)
    }
}

impl Drop for Z3Term {
    fn drop(&mut self) {
        unsafe {
            mutex!();
            Z3_dec_ref(self.context, self.ast);
        }
    }
}

impl Term for Z3Term {
    fn to_string(&self) -> SMTResult<String> {
        unsafe {
            mutex!();
            let ptr = Z3_ast_to_string(self.context, self.ast) as *mut i8;
            if ptr.is_null() {
                Err(SMTError::new_internal("Unable to convert Term to string"))
            } else {
                let cstr = CStr::from_ptr(ptr);
                match cstr.to_str() {
                    Ok(s) => Ok(String::from(s)),
                    Err(e) => Err(SMTError::new_internal(e.description())),
                }
            }
        }
    }
    fn to_int(&self) -> SMTResult<i64> {
        unsafe {
            mutex!();
            let z3sort = Z3_get_sort(self.context, self.ast);
            let ok = match Z3_get_sort_kind(self.context, z3sort) {
                SortKind::Int => true,
                SortKind::Real => true,
                SortKind::BV => true,
                _ => false,
            };
            if !ok {
                Err(SMTError::new_api(
                    "Term::to_int: sort of term is not int, real, or bitvector",
                ))
            } else {
                let ok = match Z3_get_ast_kind(self.context, self.ast) {
                    AstKind::Numeral => true,
                    _ => false,
                };
                if !ok {
                    Err(SMTError::new_api(
                        "Term::to_int: term is not a numeric constant",
                    ))
                } else {
                    let mut tmp: ::std::os::raw::c_longlong = 0;
                    let res = Z3_get_numeral_int64(self.context, self.ast, &mut tmp);
                    if res {
                        Ok(tmp)
                    } else {
                        Err(SMTError::new_api(
                            "Term::to_int: unable to convert to 64-bit integer",
                        ))
                    }
                }
            }
        }
    }
}

// Used to keep track of declared record sorts.
struct RecordInfo {
    field_map: HashMap<String, u32>,
    cons_decl: Z3UninterpretedFunction,
}

// Implementation of SMTSolver for Z3.
pub struct Z3Solver {
    config: Z3_config,
    context: Z3_context,
    solver: Z3_solver,
    level: u32,
    model: Option<Z3_model>,
    last_result: CheckSatResult,
    record_map: HashMap<Z3_sort, RecordInfo>,
}

impl Drop for Z3Solver {
    fn drop(&mut self) {
        unsafe {
            self.record_map.clear();
            mutex!();
            if let Some(m) = self.model {
                Z3_model_dec_ref(self.context, m);
            }
            Z3_solver_dec_ref(self.context, self.solver);
            Z3_del_context(self.context);
            Z3_del_config(self.config);
        }
    }
}

impl SMTSolver for Z3Solver {
    type S = Z3Sort;
    type T = Z3Term;
    type F = Z3UninterpretedFunction;
    fn new() -> Z3Solver {
        unsafe {
            mutex!();
            let cfg = Z3_mk_config();
            let cxt = Z3_mk_context(cfg);
            let s = Z3_mk_solver(cxt);
            Z3_solver_inc_ref(cxt, s);
            Z3Solver {
                config: cfg,
                context: cxt,
                solver: s,
                level: 0,
                model: None,
                last_result: CheckSatResult::Unknown,

                record_map: HashMap::new(),
            }
        }
    }
    fn declare_sort(&self, name: &str) -> SMTResult<Z3Sort> {
        unsafe {
            match CString::new(name) {
                Err(e) => Err(SMTError::new_internal(e.description())),
                Ok(str) => {
                    let sort = {
                        mutex!();
                        let sym = Z3_mk_string_symbol(self.context, str.as_ptr());
                        Z3_mk_uninterpreted_sort(self.context, sym)
                    };
                    Ok(new_z3_sort(self.context, sort, true))
                }
            }
        }
    }
    fn lookup_sort(&self, s: Sorts) -> SMTResult<Z3Sort> {
        unsafe {
            mutex!();
            match s {
                Sorts::Bool => Ok(new_z3_sort(
                    self.context,
                    Z3_mk_bool_sort(self.context),
                    false,
                )),
                Sorts::Int => Ok(new_z3_sort(
                    self.context,
                    Z3_mk_int_sort(self.context),
                    false,
                )),
                Sorts::Real => Ok(new_z3_sort(
                    self.context,
                    Z3_mk_real_sort(self.context),
                    false,
                )),
                Sorts::Array => Err(SMTError::new_api("Use apply_sort to create Array sorts")),
                Sorts::BitVec(i) => Ok(new_z3_sort(
                    self.context,
                    Z3_mk_bv_sort(self.context, i),
                    false,
                )),
            }
        }
    }
    fn apply_sort(&self, s: Sorts, s1: &Z3Sort, s2: &Z3Sort) -> SMTResult<Z3Sort> {
        unsafe {
            match s {
                Sorts::Array => {
                    let sort = {
                        mutex!();
                        Z3_mk_array_sort(self.context, s1.sort, s2.sort)
                    };
                    Ok(new_z3_sort(self.context, sort, true))
                }
                _ => Err(SMTError::new_api(
                    "apply_sort called with non-sort constructor",
                )),
            }
        }
    }
    fn declare_record_sort(
        &mut self,
        name: &str,
        fields: &[&str],
        sorts: &[&Z3Sort],
    ) -> SMTResult<Z3Sort> {
        let mut result = Ok(0 as Z3_sort);
        if fields.len() != sorts.len() {
            result = Err(SMTError::new_api(
                "declare_record_sort: fields and sorts must have same length",
            ));
        };
        unsafe {
            mutex!();
            let record_name = name.to_string();
            let cons_name = record_name.clone() + "_cons";
            let recognizer_name = record_name.clone() + "_is_cons";

            let record_name_sym = match CString::new(record_name.clone()) {
                Err(e) => {
                    if result.is_ok() {
                        result = Err(SMTError::new_internal(e.description()));
                    }
                    0 as Z3_symbol
                }
                Ok(str) => Z3_mk_string_symbol(self.context, str.as_ptr()),
            };
            let cons_name_sym = match CString::new(cons_name) {
                Err(e) => {
                    if result.is_ok() {
                        result = Err(SMTError::new_internal(e.description()));
                    };
                    0 as Z3_symbol
                }
                Ok(str) => Z3_mk_string_symbol(self.context, str.as_ptr()),
            };
            let recognizer_name_sym = match CString::new(recognizer_name) {
                Err(e) => {
                    if result.is_ok() {
                        result = Err(SMTError::new_internal(e.description()));
                    };
                    0 as Z3_symbol
                }
                Ok(str) => Z3_mk_string_symbol(self.context, str.as_ptr()),
            };
            let mut selector_names = Vec::new();
            let mut z3_sorts = Vec::new();
            let mut sort_refs = Vec::new();
            for (i, sort) in sorts.iter().enumerate() {
                let selector_name = fields[i].to_string();
                let selector_name_sym = match CString::new(selector_name) {
                    Err(e) => {
                        if result.is_ok() {
                            result = Err(SMTError::new_internal(e.description()));
                        };
                        0 as Z3_symbol
                    }
                    Ok(str) => Z3_mk_string_symbol(self.context, str.as_ptr()),
                };
                selector_names.push(selector_name_sym);
                z3_sorts.push(sort.sort);
                sort_refs.push(0);
            }
            if result.is_ok() {
                let constructor = Z3_mk_constructor(
                    self.context,
                    cons_name_sym,
                    recognizer_name_sym,
                    fields.len() as ::std::os::raw::c_uint,
                    selector_names.as_ptr(),
                    z3_sorts.as_ptr(),
                    sort_refs.as_mut_ptr(),
                );
                let mut tmp = Vec::new();
                tmp.push(constructor);
                let datatype = Z3_mk_datatype(self.context, record_name_sym, 1, tmp.as_mut_ptr());
                println!("Datatype: {:?}", datatype);
                let dummy = 0 as Z3_func_decl;
                let mut cons_decls = [dummy];
                let mut tester_decls = [dummy];
                let mut accessors = Vec::new();
                for _sort in sorts {
                    accessors.push(dummy);
                }
                Z3_query_constructor(
                    self.context,
                    constructor,
                    fields.len() as ::std::os::raw::c_uint,
                    cons_decls.as_mut_ptr(),
                    tester_decls.as_mut_ptr(),
                    accessors.as_mut_ptr(),
                );
                let mut field_map = HashMap::new();
                for (i, field) in fields.iter().enumerate() {
                    match field_map.entry(field.to_string()) {
                        Entry::Occupied(_) => {
                            if result.is_ok() {
                                result = Err(SMTError::new_api(
                                    "declare_record_sort: field names must be distinct",
                                ));
                            }
                        }
                        Entry::Vacant(v) => {
                            v.insert(i as u32);
                        }
                    }
                }
                match self.record_map.entry(datatype) {
                    Entry::Occupied(_) => {
                        if result.is_ok() {
                            result = Err(SMTError::new_api(
                                "declare_record_sort: record already exists",
                            ));
                        }
                    }
                    Entry::Vacant(v) => {
                        let record_info = RecordInfo {
                            field_map,
                            cons_decl: new_z3_uninterpreted_function(
                                self.context,
                                cons_decls[0],
                                false,
                            ),
                        };
                        v.insert(record_info);
                    }
                };
                Z3_del_constructor(self.context, constructor);
                if result.is_ok() {
                    result = Ok(datatype);
                }
            }
        };
        match result {
            Err(err) => Err(err),
            Ok(sort) => Ok(new_z3_sort(self.context, sort, true)),
        }
    }
    fn declare_fun(
        &self,
        name: &str,
        args: &[&Z3Sort],
        sort: &Z3Sort,
    ) -> SMTResult<Z3UninterpretedFunction> {
        unsafe {
            match CString::new(name) {
                Err(e) => Err(SMTError::new_internal(e.description())),
                Ok(str) => {
                    let decl = {
                        mutex!();
                        let sym = Z3_mk_string_symbol(self.context, str.as_ptr());
                        let mut tmp = Vec::new();
                        for arg in args {
                            tmp.push(arg.sort);
                        }
                        Z3_mk_func_decl(
                            self.context,
                            sym,
                            tmp.len() as ::std::os::raw::c_uint,
                            tmp.as_ptr(),
                            sort.sort,
                        )
                    };
                    Ok(new_z3_uninterpreted_function(self.context, decl, true))
                }
            }
        }
    }
    fn declare_const(&self, name: &str, sort: &Z3Sort) -> SMTResult<Z3Term> {
        unsafe {
            match CString::new(name) {
                Err(e) => Err(SMTError::new_internal(e.description())),
                Ok(str) => {
                    let sym = Z3_mk_string_symbol(self.context, str.as_ptr());
                    let term = {
                        mutex!();
                        Z3_mk_const(self.context, sym, sort.sort)
                    };
                    Ok(new_z3_term(self.context, term, true))
                }
            }
        }
    }
    fn lookup_const(&self, f: Fn) -> SMTResult<Z3Term> {
        unsafe {
            mutex!();
            match f {
                Fn::False => Ok(new_z3_term(self.context, Z3_mk_false(self.context), false)),
                Fn::True => Ok(new_z3_term(self.context, Z3_mk_true(self.context), false)),
                _ => Err(SMTError::new_api("lookup_const called with non-constant")),
            }
        }
    }
    fn const_from_int(&self, value: i64, sort: &Z3Sort) -> SMTResult<Z3Term> {
        unsafe {
            mutex!();
            let sortkind = Z3_get_sort_kind(self.context, sort.sort);
            let ok = match sortkind {
                SortKind::Int => true,
                SortKind::Real => true,
                SortKind::BV => {
                    if value < 0 {
                        false
                    } else {
                        let size = Z3_get_bv_sort_size(self.context, sort.sort);
                        if size >= 63 {
                            true
                        } else {
                            value < ((1 as i64) << size)
                        }
                    }
                }
                _ => false,
            };
            if !ok {
                if sortkind == SortKind::BV {
                    Err(SMTError::new_api("const_from_int: bitvector requires non-negative value representable in the bit-width"))
                } else {
                    Err(SMTError::new_api(
                        "const_from_int: sort of term is not int, real, or bitvector",
                    ))
                }
            } else {
                Ok(new_z3_term(
                    self.context,
                    Z3_mk_int64(self.context, value, sort.sort),
                    false,
                ))
            }
        }
    }
    fn const_from_string(&self, value: &str, sort: &Z3Sort) -> SMTResult<Z3Term> {
        unsafe {
            mutex!();
            let sortkind = Z3_get_sort_kind(self.context, sort.sort);
            let mut ok = match sortkind {
                SortKind::Int => true,
                SortKind::Real => true,
                SortKind::BV => true,
                _ => false,
            };
            if !ok {
                Err(SMTError::new_api(
                    "const_from_string: sort must be int, real or bitvector",
                ))
            } else {
                let mut dec = 0;
                ok = true;
                let mut neg = false;
                for (i, c) in value.chars().enumerate() {
                    if c == '.' {
                        dec += 1;
                    } else if c == '-' && i == 0 {
                        neg = true;
                    } else if !c.is_digit(10) {
                        ok = false;
                    }
                }
                if sortkind != SortKind::Real && dec > 0 {
                    Err(SMTError::new_api(
                        "const_from_string: decimal not allowed in non-real",
                    ))
                } else if dec > 1 {
                    Err(SMTError::new_api(
                        "const_from_string: no more than one decimal place allowed",
                    ))
                } else if neg && sortkind == SortKind::BV {
                    Err(SMTError::new_api(
                        "const_from_string: negative value not allowed for bitvectors",
                    ))
                } else if !ok {
                    Err(SMTError::new_api(
                        "const_from_string: string contains invalid character: digit expected",
                    ))
                } else {
                    match CString::new(value) {
                        Err(e) => Err(SMTError::new_internal(e.description())),
                        Ok(str) => Ok(new_z3_term(
                            self.context,
                            Z3_mk_numeral(self.context, str.as_ptr(), sort.sort),
                            false,
                        )),
                    }
                }
            }
        }
    }
    fn record_const(&self, record_sort: &Z3Sort, field_values: &[Z3Term]) -> SMTResult<Z3Term> {
        let mut tmp = Vec::new();
        for value in field_values {
            tmp.push(value);
        }
        self.record_const_refs(record_sort, &tmp)
    }
    fn record_const_refs(
        &self,
        record_sort: &Z3Sort,
        field_values: &[&Z3Term],
    ) -> SMTResult<Z3Term> {
        let mut tmp = Vec::new();
        for value in field_values {
            tmp.push(value.ast);
        }
        match self.record_map.get(&record_sort.sort) {
            None => Err(SMTError::new_api(
                "record_const_refs: Non-record or unknown sort",
            )),
            Some(record_info) => unsafe {
                mutex!();
                Ok(new_z3_term(
                    self.context,
                    Z3_mk_app(
                        self.context,
                        record_info.cons_decl.decl,
                        tmp.len() as ::std::os::raw::c_uint,
                        tmp.as_ptr(),
                    ),
                    false,
                ))
            },
        }
    }
    fn apply_fun(
        &self,
        f: &Function<Z3UninterpretedFunction>,
        args: &[Z3Term],
    ) -> SMTResult<Z3Term> {
        let mut tmp = Vec::new();
        for arg in args {
            tmp.push(arg);
        }
        self.apply_fun_refs(f, &tmp)
    }
    fn apply_fun_refs(
        &self,
        f: &Function<Z3UninterpretedFunction>,
        args: &[&Z3Term],
    ) -> SMTResult<Z3Term> {
        macro_rules! unary_fun {
            ( $z3fun:ident ) => {
                Ok($z3fun(self.context, args[0].ast))
            };
        }
        macro_rules! unary_int_fun {
            ( $z3fun:ident, $i:ident ) => {
                Ok($z3fun(
                    self.context,
                    *$i as ::std::os::raw::c_uint,
                    args[0].ast,
                ))
            };
        }
        macro_rules! binary_fun {
            ( $z3fun:ident ) => {
                Ok($z3fun(self.context, args[0].ast, args[1].ast))
            };
        }
        macro_rules! trinary_fun {
            ( $z3fun:ident ) => {
                Ok($z3fun(self.context, args[0].ast, args[1].ast, args[2].ast))
            };
        }
        macro_rules! nary_fun {
            ( $z3fun:ident ) => {{
                let mut tmp = Vec::new();
                for arg in args {
                    tmp.push(arg.ast);
                }
                Ok($z3fun(
                    self.context,
                    tmp.len() as ::std::os::raw::c_uint,
                    tmp.as_ptr(),
                ))
            }};
        }

        let term = unsafe {
            mutex!();
            match f {
                // Uninterpreted function
                UF(f) => {
                    let mut tmp = Vec::new();
                    for arg in args {
                        tmp.push(arg.ast);
                    }
                    Ok(Z3_mk_app(
                        self.context,
                        f.decl,
                        tmp.len() as ::std::os::raw::c_uint,
                        tmp.as_ptr(),
                    ))
                }

                // Core
                Op(Fn::Not) => unary_fun!(Z3_mk_not),
                Op(Fn::Implies) => binary_fun!(Z3_mk_implies),
                Op(Fn::And) => nary_fun!(Z3_mk_and),
                Op(Fn::Or) => nary_fun!(Z3_mk_or),
                Op(Fn::Xor) => binary_fun!(Z3_mk_xor),
                Op(Fn::Eq) => binary_fun!(Z3_mk_eq),
                Op(Fn::Ite) => trinary_fun!(Z3_mk_ite),
                Op(Fn::Distinct) => nary_fun!(Z3_mk_distinct),

                // Arithmetic
                Op(Fn::Uminus) => unary_fun!(Z3_mk_unary_minus),
                Op(Fn::Minus) => nary_fun!(Z3_mk_sub),
                Op(Fn::Plus) => nary_fun!(Z3_mk_add),
                Op(Fn::Times) => nary_fun!(Z3_mk_mul),
                Op(Fn::Divide) => binary_fun!(Z3_mk_div),
                Op(Fn::Div) => binary_fun!(Z3_mk_div),
                Op(Fn::Mod) => binary_fun!(Z3_mk_mod),
                Op(Fn::Abs) => Err(SMTError::new_unsupported("Z3 does not support abs")),
                Op(Fn::LE) => binary_fun!(Z3_mk_le),
                Op(Fn::LT) => binary_fun!(Z3_mk_lt),
                Op(Fn::GE) => binary_fun!(Z3_mk_ge),
                Op(Fn::GT) => binary_fun!(Z3_mk_gt),
                Op(Fn::ToReal) => unary_fun!(Z3_mk_int2real),
                Op(Fn::ToInt) => unary_fun!(Z3_mk_real2int),
                Op(Fn::IsInt) => unary_fun!(Z3_mk_is_int),

                // Arrays
                Op(Fn::Select) => binary_fun!(Z3_mk_select),
                Op(Fn::Store) => trinary_fun!(Z3_mk_store),

                // Bitvectors
                Op(Fn::Concat) => binary_fun!(Z3_mk_concat),
                Op(Fn::Bvnot) => unary_fun!(Z3_mk_bvnot),
                Op(Fn::Bvand) => binary_fun!(Z3_mk_bvand),
                Op(Fn::Bvor) => binary_fun!(Z3_mk_bvor),
                Op(Fn::Bvneg) => unary_fun!(Z3_mk_bvneg),
                Op(Fn::Bvadd) => binary_fun!(Z3_mk_bvadd),
                Op(Fn::Bvmul) => binary_fun!(Z3_mk_bvmul),
                Op(Fn::Bvudiv) => binary_fun!(Z3_mk_bvudiv),
                Op(Fn::Bvurem) => binary_fun!(Z3_mk_bvurem),
                Op(Fn::Bvshl) => binary_fun!(Z3_mk_bvshl),
                Op(Fn::Bvlshr) => binary_fun!(Z3_mk_bvlshr),
                Op(Fn::Bvult) => binary_fun!(Z3_mk_bvult),
                Op(Fn::Bvnand) => binary_fun!(Z3_mk_bvnand),
                Op(Fn::Bvnor) => binary_fun!(Z3_mk_bvnor),
                Op(Fn::Bvxor) => binary_fun!(Z3_mk_bvxor),
                Op(Fn::Bvxnor) => binary_fun!(Z3_mk_bvxnor),
                Op(Fn::Bvcomp) => Err(SMTError::new_unsupported("Z3 does not support bvcomp")),
                Op(Fn::Bvsub) => binary_fun!(Z3_mk_bvsub),
                Op(Fn::Bvsdiv) => binary_fun!(Z3_mk_bvsdiv),
                Op(Fn::Bvsrem) => binary_fun!(Z3_mk_bvsrem),
                Op(Fn::Bvsmod) => binary_fun!(Z3_mk_bvsmod),
                Op(Fn::Bvashr) => binary_fun!(Z3_mk_bvashr),
                Op(Fn::Bvule) => binary_fun!(Z3_mk_bvule),
                Op(Fn::Bvugt) => binary_fun!(Z3_mk_bvugt),
                Op(Fn::Bvuge) => binary_fun!(Z3_mk_bvuge),
                Op(Fn::Bvslt) => binary_fun!(Z3_mk_bvslt),
                Op(Fn::Bvsle) => binary_fun!(Z3_mk_bvsle),
                Op(Fn::Bvsgt) => binary_fun!(Z3_mk_bvsgt),
                Op(Fn::Bvsge) => binary_fun!(Z3_mk_bvsge),
                // Bitvector ops with one integer index
                Op(Fn::Repeat(i)) => unary_int_fun!(Z3_mk_repeat, i),
                Op(Fn::ZeroExtend(i)) => unary_int_fun!(Z3_mk_zero_ext, i),
                Op(Fn::SignExtend(i)) => unary_int_fun!(Z3_mk_sign_ext, i),
                Op(Fn::RotateLeft(i)) => unary_int_fun!(Z3_mk_rotate_left, i),
                Op(Fn::RotateRight(i)) => unary_int_fun!(Z3_mk_rotate_right, i),
                // Bitvector ops with two integer indices
                Op(Fn::Extract(i, j)) => Ok(Z3_mk_extract(
                    self.context,
                    *i as ::std::os::raw::c_uint,
                    *j as ::std::os::raw::c_uint,
                    args[0].ast,
                )),
                // Record operators
                Op(Fn::RecordSelect(field)) => {
                    let sort = Z3_get_sort(self.context, args[0].ast);
                    match self.record_map.get(&sort) {
                        None => Err(SMTError::new_api(
                            "RecordSelect applied to non-record or unknown sort",
                        )),
                        Some(record_info) => match record_info.field_map.get(&field.to_string()) {
                            None => {
                                Err(SMTError::new_api("RecordSelect applied with unknown field"))
                            }
                            Some(i) => {
                                let selector = Z3_get_datatype_sort_constructor_accessor(
                                    self.context,
                                    sort,
                                    0,
                                    *i,
                                );
                                let mut tmp = Vec::new();
                                tmp.push(args[0].ast);
                                Ok(Z3_mk_app(self.context, selector, 1, tmp.as_ptr()))
                            }
                        },
                    }
                }

                // Unknown operator
                _ => Err(SMTError::new_unsupported(
                    "apply_fun called with unknown operator",
                )),
            }
        };
        match term {
            Ok(t) => Ok(new_z3_term(self.context, t, true)),
            Err(err) => Err(err),
        }
    }
    fn level(&self) -> u32 {
        self.level
    }
    fn push(&mut self, n: u32) -> SMTResult<bool> {
        unsafe {
            mutex!();
            for _x in 0..n {
                Z3_solver_push(self.context, self.solver);
            }
        }
        self.level += n;
        Ok(true)
    }
    fn pop(&mut self, n: u32) -> SMTResult<bool> {
        if n > self.level {
            Err(SMTError::new_api("pop: called with n > level"))
        } else {
            unsafe {
                mutex!();
                if let Some(m) = self.model {
                    Z3_model_dec_ref(self.context, m);
                }
                self.model = None;
                Z3_solver_pop(self.context, self.solver, 1);
            }
            self.level -= n;
            Ok(true)
        }
    }
    fn assert(&mut self, t: &Z3Term) -> SMTResult<bool> {
        unsafe {
            mutex!();
            Z3_solver_assert(self.context, self.solver, t.ast);
            Ok(true)
        }
    }
    fn check_sat(&mut self) -> CheckSatResult {
        unsafe {
            mutex!();
            if let Some(m) = self.model {
                Z3_model_dec_ref(self.context, m);
            }
            self.model = None;
            self.last_result = match Z3_solver_check(self.context, self.solver) {
                Z3_L_TRUE => CheckSatResult::Sat,
                Z3_L_FALSE => CheckSatResult::Unsat,
                _ => CheckSatResult::Unknown,
            };
            self.last_result
        }
    }
    fn get_value(&mut self, t: &Z3Term) -> SMTResult<Z3Term> {
        if self.last_result != CheckSatResult::Sat {
            Err(SMTError::new_api(
                "get_value: can only be called after a call to check_sat that returns Sat",
            ))
        } else {
            unsafe {
                mutex!();
                if self.model == None {
                    let m = Z3_solver_get_model(self.context, self.solver);
                    if !m.is_null() {
                        Z3_model_inc_ref(self.context, m);
                        self.model = Some(m);
                    }
                }
                if let Some(m) = self.model {
                    let mut tmp: Z3_ast = t.ast;
                    let res = Z3_model_eval(self.context, m, t.ast, true, &mut tmp);
                    if !res {
                        Err(SMTError::new_internal("Unable to get value"))
                    } else {
                        Ok(new_z3_term(self.context, tmp, false))
                    }
                } else {
                    Err(SMTError::new_internal("Model not found"))
                }
            }
        }
    }
}
