mod common;

#[macro_use]
mod x64;

use crate::common::{ComparisonType, InfixOp, Label, LabelGenerator, Symbol, SymbolGenerator, Comparison};

use crate::x64::{
    Operand, Operands, X64Assembly, X64Function, X64Instruction, X64Program, X64Register, X64Value,
    X64opCode,
};

use std::collections::HashMap;

fn example_1() -> X64Program {
    use X64Register::*;
    use X64opCode::*;
    use X64Value::*;
    use Operand::*;
    use Operands::*;
    use X64Assembly::*;
    use crate::common::Label::Uid;
    use crate::common::Label::PrintlnInt;
    
    let example = X64Program {
	main_function: X64Function {
	    instruction_listing: vec![
		Instruction(X64Instruction { op_code:
					     Push, args: One(Register(Rbp)) }),
		Instruction(X64Instruction { op_code:
					     Movq, args: Two(Register(Rsp), Register(Rbp)) }),
		Instruction(X64Instruction { op_code:
					     Sub, args:  Two(Immediate(Absolute(64)), Register(Rsp)) }),
		Instruction(X64Instruction { op_code:
					     Movq, args: Two(Immediate(Absolute(10)), MemoryOffset(Absolute(-56), Rbp)) }),
		Instruction(X64Instruction { op_code:
					     Movq, args: Two(Immediate(Absolute(2)), MemoryOffset(Absolute(-8), Rbp)) }),
		Instruction(X64Instruction { op_code:
					     Movq,args:  Two(MemoryOffset(Absolute(-8), Rbp), Register(R11)) }),
		Instruction(X64Instruction { op_code:
					     Movq, args: Two(MemoryOffset(Absolute(-56), Rbp), Register(R10)) }),
		Instruction(X64Instruction { op_code:
					     Cmp, args:  Two(Register(R10), Register(R11)) }),
		Instruction(X64Instruction { op_code:
					     Jg, args:   One(Immediate(LabelRef(Uid(0)))) }),
		Instruction(X64Instruction { op_code:
					     Movq, args: Two(MemoryOffset(Absolute(-56), Rbp), Register(Rdi)) }),
		Instruction(X64Instruction { op_code:
					     Call, args: One(Immediate(LabelRef(PrintlnInt))) }),
		Instruction(X64Instruction { op_code:
					     Movq, args: Two(Register(Rax), MemoryOffset(Absolute(-48), Rbp)) }),
		Label(Uid(0)),
		Instruction(X64Instruction { op_code:
					     Movq, args: Two(MemoryOffset(Absolute(-56), Rbp), Register(Rax)) }),
		Instruction(X64Instruction { op_code:
					     Add, args:  Two(Immediate(Absolute(64)), Register(Rsp)) }),
		Instruction(X64Instruction { op_code:
					     Pop, args:  One(Register(Rbp)) }),
		Instruction(X64Instruction { op_code: Ret, args: Zero })]
	},
	other_functions: HashMap::new(),
	string_literals: HashMap::new()
    };

    return example;
}

// Example 2: Print 1
fn example_2() -> X64Program {
    use X64Register::*;
    use X64opCode::*;
    use X64Value::*;
    use Operand::*;
    use Operands::*;
    use X64Assembly::*;
    use crate::common::Label::Uid;
    use crate::common::Label::PrintlnInt;
    
	let example = X64Program {
		main_function: X64Function {
			instruction_listing: vec![
			Instruction(X64Instruction { op_code:
							 Push, args: One(Register(Rbp)) }),
			Instruction(X64Instruction { op_code:
							 Movq, args: Two(Register(Rsp), Register(Rbp)) }),
			Instruction(X64Instruction { op_code:
							 Sub, args:  Two(Immediate(Absolute(64)), Register(Rsp)) }),
			
			Instruction(X64Instruction { op_code:
							 Call, args: One(Immediate(LabelRef(PrintlnInt))) }),
			Instruction(X64Instruction { op_code:
							 Movq, args: Two(Immediate(Absolute(1)), Register(Rax)) }),

			Label(Uid(0)),
			Instruction(X64Instruction { op_code:
							 Add, args:  Two(Immediate(Absolute(64)), Register(Rsp)) }),
			Instruction(X64Instruction { op_code:
							 Pop, args:  One(Register(Rbp)) }),
			Instruction(X64Instruction { op_code: Ret, args: Zero })]
		},
		other_functions: HashMap::new(),
		string_literals: HashMap::new()
		};
	
    return example;
}

fn main() {
    let example = example_2();
    print!("{}\n", example);
}
