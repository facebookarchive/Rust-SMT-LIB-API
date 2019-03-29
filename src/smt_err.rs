// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use std::error::Error;
use std::fmt;

#[derive(Debug, PartialEq)]
pub enum SMTError {
    APIError(String),
    UnsupportedError(String),
    InternalError(String),
}
use SMTError::*;

impl SMTError {
    // An error resulting from an illegal use of the API.
    pub fn new_api(msg: &str) -> SMTError {
        APIError(msg.to_string())
    }

    // An error resulting from an usupported feature.
    pub fn new_unsupported(msg: &str) -> SMTError {
        UnsupportedError(msg.to_string())
    }

    // An error propagated from the solver or from some library function.
    pub fn new_internal(msg: &str) -> SMTError {
        InternalError(msg.to_string())
    }
}

impl fmt::Display for SMTError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let message = match self {
            APIError(s) => s,
            UnsupportedError(s) => s,
            InternalError(s) => s,
        };
        write!(f, "{}", message)
    }
}

impl Error for SMTError {
    fn description(&self) -> &str {
        match self {
            APIError(s) => s,
            UnsupportedError(s) => s,
            InternalError(s) => s,
        }
    }
}
