#![allow(dead_code)]

use serde::{Serialize, Deserialize};

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub enum Label {
    Uid(u64),
    Allocate,
    AllocateAndMemset,
    PrintlnInt,
    PrintlnString,
    PrintInt,
    PrintString,
}

#[derive(Debug)]
pub struct LabelGenerator {
    next_uid: u64,
}

impl LabelGenerator {
    pub fn new() -> Self {
        LabelGenerator { next_uid: 0 }
    }
    pub fn new_label(&mut self) -> Label {
        let uid = self.next_uid;
        self.next_uid = self.next_uid + 1;
        Label::Uid(uid)
    }
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, Serialize, Deserialize)]
pub struct Comparison {
    pub c: ComparisonType,
    pub left: Symbol,
    pub right: Symbol,
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, Serialize, Deserialize)]
pub enum ComparisonType {
    Equal,
    NotEqual,
    GreaterThan,
    LessThan,
    GreaterThanEqual,
    LessThanEqual,
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, Serialize, Deserialize)]
pub enum InfixOp {
    Multiply,
    Divide,
    Add,
    Substract,
    And,
    Or,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Symbol {
    uid: u64,
}

#[derive(Debug)]
pub struct SymbolGenerator {
    next_uid: u64,
}

impl SymbolGenerator {
        pub fn new() -> Self {
        SymbolGenerator { next_uid: 0 }
    }
    pub fn new_symbol(&mut self) -> Symbol {
        let uid = self.next_uid;
        self.next_uid = self.next_uid + 1;
        Symbol { uid }
    }
}

use std::fmt;

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Label::Uid(u) => write!(f, "L{}", u),
            Label::Allocate => write!(f, "allocate"),
            Label::AllocateAndMemset => write!(f, "allocate_and_memset"),
            Label::PrintlnInt => write!(f, "print_line_int"),
            Label::PrintlnString => write!(f, "print_line_string"),
            Label::PrintInt => write!(f, "print_int"),
            Label::PrintString => write!(f, "print_string"),
        }
    }
}
