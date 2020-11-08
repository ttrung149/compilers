(* ll ir compilation -------------------------------------------------------- *)

open Ll
open X86

(* Overview ----------------------------------------------------------------- *)

(* We suggest that you spend some time understanding this entire file and
   how it fits with the compiler pipeline before making changes.  The suggested
   plan for implementing the compiler is provided on the project web page.
*)


(* helpers ------------------------------------------------------------------ *)

(* Map LL comparison operations to X86 condition codes *)
let compile_cnd = function
  | Ll.Eq  -> X86.Eq
  | Ll.Ne  -> X86.Neq
  | Ll.Slt -> X86.Lt
  | Ll.Sle -> X86.Le
  | Ll.Sgt -> X86.Gt
  | Ll.Sge -> X86.Ge



(* locals and layout -------------------------------------------------------- *)

(* One key problem in compiling the LLVM IR is how to map its local
   identifiers to X86 abstractions.  For the best performance, one
   would want to use an X86 register for each LLVM %uid.  However,
   since there are an unlimited number of %uids and only 16 registers,
   doing so effectively is quite difficult.  We will see later in the
   course how _register allocation_ algorithms can do a good job at
   this.

   A simpler, but less performant, implementation is to map each %uid
   in the LLVM source to a _stack slot_ (i.e. a region of memory in
   the stack).  Since LLVMlite, unlike real LLVM, permits %uid locals
   to store only 64-bit data, each stack slot is an 8-byte value.

   [ NOTE: For compiling LLVMlite, even i1 data values should be
   represented as a 8-byte quad. This greatly simplifies code
   generation. ]

   We call the datastructure that maps each %uid to its stack slot a
   'stack layout'.  A stack layout maps a uid to an X86 operand for
   accessing its contents.  For this compilation strategy, the operand
   is always an offset from %rbp (in bytes) that represents a storage slot in
   the stack.
*)

type layout = (uid * X86.operand) list

(* A context contains the global type declarations (needed for getelementptr
   calculations) and a stack layout. *)
type ctxt = { tdecls : (tid * ty) list
            ; layout : layout
            }

(* useful for looking up items in tdecls or layouts *)
let lookup m x = List.assoc x m


(* compiling operands  ------------------------------------------------------ *)

(* LLVM IR instructions support several kinds of operands.

   LL local %uids live in stack slots, whereas global ids live at
   global addresses that must be computed from a label.  Constants are
   immediately available, and the operand Null is the 64-bit 0 value.

     NOTE: two important facts about global identifiers:

     (1) You should use (Platform.mangle gid) to obtain a string
     suitable for naming a global label on your platform (OS X expects
     "_main" while linux expects "main").

     (2) 64-bit assembly labels are not allowed as immediate operands.
     That is, the X86 code: movq _gid %rax which looks like it should
     put the address denoted by _gid into %rax is not allowed.
     Instead, you need to compute an %rip-relative address using the
     leaq instruction:   leaq _gid(%rip).

   One strategy for compiling instruction operands is to use a
   designated register (or registers) for holding the values being
   manipulated by the LLVM IR instruction. You might find it useful to
   implement the following helper function, whose job is to generate
   the X86 instruction that moves an LLVM operand into a designated
   destination (usually a register).
*)
let compile_operand (ctxt:ctxt) (dest:X86.operand) : Ll.operand -> ins list =
  function (ll_operand:Ll.operand) ->
    match ll_operand with
    | Null    -> [Movq, [Imm(Lit 0L); dest]]
    | Const x -> [Movq, [Imm(Lit x); dest]]
    | Gid id  -> [Leaq, [Ind3((Lbl(Platform.mangle id)), Rip); dest]]
    | Id id   -> [
        (Movq, [(lookup ctxt.layout id); Reg R11]);
        (Movq, [Reg R11; dest])
      ]

(* compiling call  ---------------------------------------------------------- *)

(* You will probably find it helpful to implement a helper function that
   generates code for the LLVM IR call instruction.

   The code you generate should follow the x64 System V AMD64 ABI
   calling conventions, which places the first six 64-bit (or smaller)
   values in registers and pushes the rest onto the stack.  Note that,
   since all LLVM IR operands are 64-bit values, the first six
   operands will always be placed in registers.  (See the notes about
   compiling fdecl below.)

   [ NOTE: It is the caller's responsibility to clean up arguments
   pushed onto the stack, so you must free the stack space after the
   call returns. ]

   [ NOTE: Don't forget to preserve caller-save registers (only if
   needed). ]
*)

(*let compile_call (ctxt:ctxt) (op:operand, args:(ty * operand) list) : ins =

  *)



(* compiling getelementptr (gep)  ------------------------------------------- *)

(* The getelementptr instruction computes an address by indexing into
   a datastructure, following a path of offsets.  It computes the
   address based on the size of the data, which is dictated by the
   data's type.

   To compile getelementptr, you must generate x86 code that performs
   the appropriate arithmetic calculations.
*)

(* [size_ty] maps an LLVMlite type to a size in bytes.
    (needed for getelementptr)

   - the size of a struct is the sum of the sizes of each component
   - the size of an array of t's with n elements is n * the size of t
   - all pointers, I1, and I64 are 8 bytes
   - the size of a named type is the size of its definition

   - Void, i8, and functions have undefined sizes according to LLVMlite.
     Your function should simply return 0 in those cases
*)
let rec size_ty (tdecls:(tid * ty) list) (t:Ll.ty) : int =
  let acc_size (size:int) (ll_type:Ll.ty) : int =
    size + (size_ty tdecls ll_type)
  in
  match t with
  | Void | I8  | Fun _ -> 0
  | I1   | I64 | Ptr _ -> 8
  | Struct elems -> List.fold_left acc_size 0 elems
  | Array (num, t) -> (size_ty tdecls t) * num
  | Namedt tid -> size_ty tdecls (lookup tdecls tid)


(* Generates code that computes a pointer value.

   1. op must be of pointer type: t*

   2. the value of op is the base address of the calculation

   3. the first index in the path is treated as the index into an array
     of elements of type t located at the base address

   4. subsequent indices are interpreted according to the type t:

     - if t is a struct, the index must be a constant n and it
       picks out the n'th element of the struct. [ NOTE: the offset
       within the struct of the n'th element is determined by the
       sizes of the types of the previous elements ]

     - if t is an array, the index can be any operand, and its
       value determines the offset within the array.

     - if t is any other type, the path is invalid

   5. if the index is valid, the remainder of the path is computed as
      in (4), but relative to the type f the sub-element picked out
      by the path so far
*)
let compile_gep (ctxt:ctxt) (op:Ll.ty * Ll.operand) (path:Ll.operand list) : ins list =
failwith "compile_gep not implemented"



(* compiling instructions  -------------------------------------------------- *)

(* The result of compiling a single LLVM instruction might be many x86
   instructions.  We have not determined the structure of this code
   for you. Some of the instructions require only a couple of assembly
   instructions, while others require more.  We have suggested that
   you need at least compile_operand, compile_call, and compile_gep
   helpers; you may introduce more as you see fit.

   Here are a few notes:

   - Icmp:  the Setb instruction may be of use.  Depending on how you
     compile Cbr, you may want to ensure that the value produced by
     Icmp is exactly 0 or 1.

   - Load & Store: these need to dereference the pointers. Const and
     Null operands aren't valid pointers.  Don't forget to
     Platform.mangle the global identifier.

   - Alloca: needs to return a pointer into the stack

   - Bitcast: does nothing interesting at the assembly level
*)
let compile_insn (ctxt:ctxt) ((uid:uid), (i:Ll.insn)) : X86.ins list =
  []

(*
  match i with
  | Binop (bop, ty, operand_1, operand_2) ->
    match bop with
    | Add ->
      (compile_operand ctxt (Reg R12) operand_1) @
      (compile_operand ctxt (Reg R13) operand_2) @
      [
        (Addq, [Reg R12; Reg R13]);
        (Movq, [Reg R13; (lookup ctxt.layout uid)])
      ]
    | Sub ->
      (compile_operand ctxt (Reg R12) operand_1) @
      (compile_operand ctxt (Reg R13) operand_2) @
      [
        (Subq, [Reg R13; Reg R12]);
        (Movq, [Reg R12; (lookup ctxt.layout uid)])
      ]
    | _ -> []

*)
(* compiling terminators  --------------------------------------------------- *)

(* prefix the function name [fn] to a label to ensure that the X86 labels are
   globally unique. *)
let mk_lbl (fn:string) (l:string) = fn ^ "." ^ l

(* Compile block terminators is not too difficult:

   - Ret should properly exit the function: freeing stack space,
     restoring the value of %rbp, and putting the return value (if
     any) in %rax.

   - Br should jump

   - Cbr branch should treat its operand as a boolean conditional

   [fn] - the name of the function containing this terminator
*)
let compile_terminator (fn:string) (ctxt:ctxt) (t:Ll.terminator) : ins list =
  match t with
  | Ret (ty, operand) ->
    (* Deallocate stack, restore callee save registers *)
    let exit_sequence = [
        (Movq, [(Ind3(Lit(Int64.neg 8L) , Rbp)); (Reg Rbx)]);
        (Movq, [(Ind3(Lit(Int64.neg 16L), Rbp)); (Reg R12)]);
        (Movq, [(Ind3(Lit(Int64.neg 24L), Rbp)); (Reg R13)]);
        (Movq, [(Ind3(Lit(Int64.neg 32L), Rbp)); (Reg R14)]);
        (Movq, [(Ind3(Lit(Int64.neg 40L), Rbp)); (Reg R15)]);
        (Movq, [Reg Rbp; Reg Rsp]);
        (Popq, [Reg Rbp]);
        (Retq, [])
    ]
    in
    begin match operand with
      | Some op ->
          begin match ty with
            | Void -> exit_sequence
            | _    -> (compile_operand ctxt (Reg Rax) op) @ exit_sequence
          end
      | None -> exit_sequence
    end

  | Br lbl -> [(Jmp, [Imm (Lbl (mk_lbl fn lbl))])]
  | Cbr (operand, lbl1, lbl2) ->
    begin match operand with
      | Const _ | Gid _ | Id _ ->
        (compile_operand ctxt (Reg R10) operand) @
        [
          (Cmpq, [Imm(Lit 1L); Reg R10]);
          (J Eq, [Imm(Lbl(mk_lbl fn lbl1))]);
          (Jmp,  [Imm(Lbl(mk_lbl fn lbl2))])
        ]
      | Null -> failwith "ERR: Fail to compile null operand as terminator"
    end


(* compiling blocks --------------------------------------------------------- *)

(* We have left this helper function here for you to complete.
   [fn] - the name of the function containing this block
   [ctxt] - the current context
   [blk]  - LLVM IR code for the block
*)
let compile_block (fn:string) (ctxt:ctxt) (blk:Ll.block) : ins list =
  let blk_term_id, blk_terminator = blk.term in
  let _compile_insn (insn) = compile_insn ctxt insn in

  let compiled_insns = List.flatten (List.map _compile_insn blk.insns) in
  let compiled_term  = compile_terminator fn ctxt blk_terminator in
  compiled_insns @ compiled_term


let compile_lbl_block fn lbl ctxt blk : elem =
  Asm.text (mk_lbl fn lbl) (compile_block fn ctxt blk)



(* compile_fdecl ------------------------------------------------------------ *)


(* This helper function computes the location of the nth incoming
   function argument: either in a register or relative to %rbp,
   according to the calling conventions.  You might find it useful for
   compile_fdecl.

   [ NOTE: the first six arguments are numbered 0 .. 5 ]
*)
let arg_loc (n : int) : operand =
  match n with
  | 0 -> Reg Rdi
  | 1 -> Reg Rsi
  | 2 -> Reg Rdx
  | 3 -> Reg Rcx
  | 4 -> Reg R08
  | 5 -> Reg R09
  | _ -> Ind3(Lit (Int64.of_int ((n - 4) * 8)), Rbp)

(* We suggest that you create a helper function that computes the
   stack layout for a given function declaration.

   - each function argument should be copied into a stack slot
   - in this (inefficient) compilation strategy, each local id
     is also stored as a stack slot.
   - see the discussion about locals

*)
let stack_layout (args : uid list) ((block, lbled_blocks):cfg) : layout =
  let stk_idx = ref 0 in
  let get_uid (insn:uid * insn) =
    match insn with
    | (uid, _) -> uid
  in
  let get_uids_from_blk (blk:block) = List.map get_uid blk.insns in
  let uids_entry_blk = get_uids_from_blk block in
  let uids_labled_blks = List.map (fun (_, blk) -> get_uids_from_blk blk) lbled_blocks in
  let blk_uids = List.flatten (uids_entry_blk :: uids_labled_blks) in
  let uids = args @ blk_uids in

  let acc_uid acc uid =
    let acc' = acc @ [(uid, Ind3(Lit(Int64.of_int (!stk_idx * 8)), Rsp))] in
    stk_idx := !stk_idx + 1;
    acc'
  in
  List.fold_left acc_uid [] uids

(* The code for the entry-point of a function must do several things:

   - since our simple compiler maps local %uids to stack slots,
     compiling the control-flow-graph body of an fdecl requires us to
     compute the layout (see the discussion of locals and layout)

   - the function code should also comply with the calling
     conventions, typically by moving arguments out of the parameter
     registers (or stack slots) into local storage space.  For our
     simple compilation strategy, that local storage space should be
     in the stack. (So the function parameters can also be accounted
     for in the layout.)

   - the function entry code should allocate the stack storage needed
     to hold all of the local stack slots.
*)
let compile_fdecl (tdecls:(tid * ty) list) (name:string)
                  ({ f_ty; f_param; f_cfg }:fdecl) : prog =

  let ctxt = { tdecls = tdecls; layout = (stack_layout f_param f_cfg) } in
  let entry_blk, lbl_blks =
    match f_cfg with
    | (blk, blks) -> blk, blks
  in

  (* Helper function: maps i-th arg to stack slot  *)
  let map_arg_to_stk (i:int) (uid:uid) : ins list =
     let op = arg_loc i in
     match op with
     | Reg Rdi | Reg Rsi | Reg Rdx
     | Reg Rcx | Reg R08 | Reg R09 -> [(Movq, [op; lookup ctxt.layout uid])]
     | _ -> [
         (Movq, [op; Reg R10]);
         (Movq, [Reg R10; lookup ctxt.layout uid])
       ]
  in
  let compiled_args = List.flatten (List.mapi map_arg_to_stk f_param) in

  (* Allocate new stack frame, push callee saved registers onto the stack *)
  let entry_sequence = [
    (Pushq, [Reg Rbp]);
    (Movq,  [Reg Rsp; Reg Rbp]);
    (Pushq, [Reg Rbx]);
    (Pushq, [Reg R12]);
    (Pushq, [Reg R13]);
    (Pushq, [Reg R14]);
    (Pushq, [Reg R15]);
    (Subq,  [Imm(Lit(Int64.of_int ((List.length ctxt.layout) * 8))); Reg Rsp])
  ]
  in

  (* Entry block compiled instructions *)
  let entry_compiled_insns = [
    Asm.gtext(Platform.mangle name)
    (
      entry_sequence
      @ compiled_args
      @ (compile_block name ctxt entry_blk)
    )
  ]
  in

  (* Labeled blocks compiled instructions *)
  let lbl_blks_compiled_insns =
    List.map (fun (lbl, blk) -> compile_lbl_block name lbl ctxt blk) lbl_blks
  in
  entry_compiled_insns @ lbl_blks_compiled_insns


(* compile_gdecl ------------------------------------------------------------ *)
(* Compile a global value into an X86 global data declaration and map
   a global uid to its associated X86 label.
*)
let rec compile_ginit : ginit -> X86.data list = function
  | GNull     -> [Quad (Lit 0L)]
  | GGid gid  -> [Quad (Lbl (Platform.mangle gid))]
  | GInt c    -> [Quad (Lit c)]
  | GString s -> [Asciz s]
  | GArray gs | GStruct gs -> List.map compile_gdecl gs |> List.flatten
  | GBitcast (t1,g,t2) -> compile_ginit g

and compile_gdecl (_, g) = compile_ginit g


(* compile_prog ------------------------------------------------------------- *)
let compile_prog {tdecls; gdecls; fdecls} : X86.prog =
  let g = fun (lbl, gdecl) -> Asm.data (Platform.mangle lbl) (compile_gdecl gdecl) in
  let f = fun (name, fdecl) -> compile_fdecl tdecls name fdecl in
  (List.map g gdecls) @ (List.map f fdecls |> List.flatten)
