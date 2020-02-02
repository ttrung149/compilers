/*
 * This is the x64 grammar.
 */

#![allow(dead_code)]

use crate::common::Label;

use std::collections::HashMap;

use serde::{Serialize, Deserialize};

/*
 * Note that these registers are only those which are 64-bit
 * Cat only contains 64 bit numbers (and pointers)
 */
#[derive(Debug, Copy, Clone, Serialize, Deserialize)]
pub enum X64Register {
    Rax, // Not Saved - Return
    Rbx, // Saved
    Rcx, // Not Saved - 3rd argument
    Rdx, // Not Saved - 4th argument
    Rsp, // Saved - Stack Pointer
    Rbp, // Not Saved - Base Pointer
    Rsi, // Not Saved - 2nd argument
    Rdi, // Not Saved - 1st argument
    R8,  // Not Saved - 5th argument
    R9,  // Not Saved - 6th argument
    R10, // Not Saved
    R11, // Not Saved
    R12, // Saved Across Calls
    R13, // Saved Across Calls
    R14, // Saved Across Calls
    R15, // Saved Across Calls
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum X64opCode {
    Add,
    Sub,
    IMulq,
    IDivq,
    Or,
    And,
    Movq,
    Neg,
    Push,
    Pop,
    Call,
    Ret,
    Jmp,
    Je,
    Jne,
    Jg,
    Jge,
    Jl,
    Jle,
    Lea,
    Nop,
    Cmp,
    // Feel free to add opCodes
    // if you find them useful
}

/** Immediate value
 *  Used to represent integer constants, known addresses, and label
 *  addresses
 */
#[derive(Debug, Copy, Clone, Serialize, Deserialize)]
pub enum X64Value {
    LabelRef(Label),
    Absolute(i64),
}

#[derive(Debug, Copy, Clone, Serialize, Deserialize)]
pub enum Operand {
    Immediate(X64Value),
    Register(X64Register),
    MemoryImm(X64Value),
    MemoryReg(X64Register),
    MemoryOffset(X64Value, X64Register),
    MemoryScaledIndexed(X64Value, X64Register, u8, X64Register),
}

#[derive(Debug, Copy, Clone, Serialize, Deserialize)]
pub enum Operands {
    Zero,
    One(Operand),
    Two(Operand, Operand),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct X64Instruction {
    pub op_code: X64opCode,
    pub args: Operands,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum X64Assembly {
    Label(Label),
    Instruction(X64Instruction),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct X64Function {
    pub instruction_listing: Vec<X64Assembly>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct X64Program {
    pub main_function: X64Function,
    pub other_functions: HashMap<Label, X64Function>,
    pub string_literals: HashMap<Label, String>,
}

/* Helpful Macros */
macro_rules! nop {
    () => {
        X64Instruction { op_code: X64opCode::Nop, args: Operands::Zero }
    };
}

macro_rules! ret {
    () => {
        X64Instruction { op_code: X64opCode::Ret, args: Operands::Zero }
    };
}

/* Converting to assembly text file */
use std::fmt;

/*
 * Depending on the architecture you use you may have different assembly header
 * requirements. To get started implement the trait below.
 *
 * Note that string literals should be referred to by their location.
 * Use compiler directives to setup all the strings. e.g. L3 -> "Hello World"
 *
 * .LS3:
 *      .string "Hello World"
 * .L3:
 *      .quad .LNEW
 *
 * Note that labels get displayed as L#, so LS# will never conflict.
 *
 * Otherwise the translation should be straight forward.
 */
impl fmt::Display for X64Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Basic main only assembly generation:
        write!(f, ".globl main\nmain:\n{}", self.main_function)
        // TODO include strings and other_functions
    }
}

impl fmt::Display for X64Register {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            X64Register::Rax => "rax",
            X64Register::Rbx => "rbx",
            X64Register::Rcx => "rcx",
            X64Register::Rdx => "rdx",
            X64Register::Rsp => "rsp",
            X64Register::Rbp => "rbp",
            X64Register::Rsi => "rsi",
            X64Register::Rdi => "rdi",
            X64Register::R8  => "r8",
            X64Register::R9  => "r9",
            X64Register::R10 => "r10",
            X64Register::R11 => "r11",
            X64Register::R12 => "r12",
            X64Register::R13 => "r13",
            X64Register::R14 => "r14",
            X64Register::R15 => "r15",
        };
        write!(f, "%{}", name)
    }
}

impl fmt::Display for X64opCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            X64opCode::Add => "add",
            X64opCode::Sub => "sub",
            X64opCode::IMulq => "imulq",
            X64opCode::IDivq => "idivq",
            X64opCode::Or => "or",
            X64opCode::And => "and",
            X64opCode::Movq => "movq",
            X64opCode::Neg => "neg",
            X64opCode::Push => "pushq",
            X64opCode::Pop => "popq",
            X64opCode::Call => "call",
            X64opCode::Ret => "ret",
            X64opCode::Jmp => "jmp",
            X64opCode::Je => "je",
            X64opCode::Jne => "jne",
            X64opCode::Jg => "jg",
            X64opCode::Jge => "jge",
            X64opCode::Jl => "jl",
            X64opCode::Jle => "jle",
	    X64opCode::Lea => "lea",
            X64opCode::Nop => "nop",
            X64opCode::Cmp => "cmp",
        };
        write!(f, "{}", name)
    }
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
	// HOMEWORK 1: write display code for each kind of operand
    }
}

impl fmt::Display for X64Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
	// HOMEWORK 1: write display code for each kind of X64Value
    }
}

impl fmt::Display for Operands {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
	// HOMEWORK 1: write display code for zero, one, or two operands
    }
}

impl fmt::Display for X64Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
	// HOMEWORK 1: write display code for a full instruction
    }
}

impl fmt::Display for X64Assembly {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
	// HOMEWORK 1: write display code for either label or instruction
    }
}

impl fmt::Display for X64Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
	// HOMEWORK 1: Loop over the assembly in the function, write out
	// each entry
    }
}

