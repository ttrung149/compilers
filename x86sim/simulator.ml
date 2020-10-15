(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the
   course web pages, for a detailed explanation of the instruction
   semantics.
*)

open X86

(* simulator machine state -------------------------------------------------- *)

let mem_bot = 0x400000L          (* lowest valid address *)
let mem_top = 0x410000L          (* one past the last byte in memory *)
let mem_size = Int64.to_int (Int64.sub mem_top mem_bot)
let nregs = 17                   (* including Rip *)
let ins_size = 8L                (* assume we have a 8-byte encoding *)
let exit_addr = 0xfdeadL         (* halt when m.regs(%rip) = exit_addr *)

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* The simulator memory maps addresses to symbolic bytes.  Symbolic
   bytes are either actual data indicated by the Byte constructor or
   'symbolic instructions' that take up eight bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next sevent bytes are InsFrag
   elements, which aren't valid data.

   For example, the two-instruction sequence:
        at&t syntax             ocaml syntax
      movq %rdi, (%rsp)       Movq,  [~%Rdi; Ind2 Rsp]
      decq %rdi               Decq,  [~%Rdi]

   is represented by the following elements of the mem array (starting
   at address 0x400000):

       0x400000 :  InsB0 (Movq,  [~%Rdi; Ind2 Rsp])
       0x400001 :  InsFrag
       0x400002 :  InsFrag
       0x400003 :  InsFrag
       0x400004 :  InsFrag
       0x400005 :  InsFrag
       0x400006 :  InsFrag
       0x400007 :  InsFrag
       0x400008 :  InsB0 (Decq,  [~%Rdi])
       0x40000A :  InsFrag
       0x40000B :  InsFrag
       0x40000C :  InsFrag
       0x40000D :  InsFrag
       0x40000E :  InsFrag
       0x40000F :  InsFrag
       0x400010 :  InsFrag
*)
type sbyte = InsB0 of ins       (* 1st byte of an instruction *)
           | InsFrag            (* 2nd - 8th bytes of an instruction *)
           | Byte of char       (* non-instruction byte *)

(* memory maps addresses to symbolic bytes *)
type mem = sbyte array

(* Flags for condition codes *)
type flags = { mutable fo : bool
             ; mutable fs : bool
             ; mutable fz : bool
             }

(* Register files *)
type regs = int64 array

(* Complete machine state *)
type mach = { flags : flags
            ; regs : regs
            ; mem : mem
            }

(* simulator helper functions ----------------------------------------------- *)

(* The index of a register in the regs array *)
let rind : reg -> int = function
  | Rip -> 16
  | Rax -> 0  | Rbx -> 1  | Rcx -> 2  | Rdx -> 3
  | Rsi -> 4  | Rdi -> 5  | Rbp -> 6  | Rsp -> 7
  | R08 -> 8  | R09 -> 9  | R10 -> 10 | R11 -> 11
  | R12 -> 12 | R13 -> 13 | R14 -> 14 | R15 -> 15

(* Helper functions for reading/writing sbytes *)

(* Convert an int64 to its sbyte representation *)
let sbytes_of_int64 (i:int64) : sbyte list =
  let open Char in
  let open Int64 in
  List.map (fun n -> Byte (shift_right i n |> logand 0xffL |> to_int |> chr))
           [0; 8; 16; 24; 32; 40; 48; 56]

(* Convert an sbyte representation to an int64 *)
let int64_of_sbytes (bs:sbyte list) : int64 =
  let open Char in
  let open Int64 in
  let f b i = match b with
    | Byte c -> logor (shift_left i 8) (c |> code |> of_int)
    | _ -> 0L
  in
  List.fold_right f bs 0L

(* Convert a string to its sbyte representation *)
let sbytes_of_string (s:string) : sbyte list =
  let rec loop acc = function
    | i when i < 0 -> acc
    | i -> loop (Byte s.[i]::acc) (pred i)
  in
  loop [Byte '\x00'] @@ String.length s - 1

(* Serialize an instruction to sbytes *)
let sbytes_of_ins (op, args:ins) : sbyte list =
  let check = function
    | Imm (Lbl _) | Ind1 (Lbl _) | Ind3 (Lbl _, _) ->
      invalid_arg "sbytes_of_ins: tried to serialize a label!"
    | o -> ()
  in
  List.iter check args;
  [InsB0 (op, args); InsFrag; InsFrag; InsFrag;
   InsFrag; InsFrag; InsFrag; InsFrag]

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"


(* It might be useful to toggle printing of intermediate states of your
   simulator. Our implementation uses this mutable flag to turn on/off
   printing.  For instance, you might write something like:

     [if !debug_simulator then print_endline @@ string_of_ins u; ...]

*)
let debug_simulator = ref false

(* Interpret a condition code with respect to the given flags. *)
let interp_cnd {fo; fs; fz} : cnd -> bool = fun x ->
  match x with
  | Eq -> fz
  | Neq -> not fz
  | Gt -> not (fz || (fo <> fs))
  | Ge -> not (fo <> fs)
  | Lt -> fo <> fs
  | Le -> fz || (fo <> fs)

(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option =
  let in_range_lo addr = Int64.compare addr mem_bot >= 0 in
  let in_range_hi addr = Int64.compare addr mem_top < 0 in
    if in_range_hi addr && in_range_lo addr
    then Some(Int64.to_int(Int64.sub addr mem_bot))
    else None

(* Step function helper function -------------------------------------------- *)

(* Increment program counter (%rip register) *)
let increment_rip_by (m:mach) (i:int64) : unit =
  let rip_idx = rind Rip in
    m.regs.(rip_idx) <- Int64.add m.regs.(rip_idx) i

let fetch_next_isn_rip (m:mach) : unit =
    increment_rip_by m 8L


(* Load and store ----------------------------------------------------------- *)
(* Fetch data from memory address (LOAD) *)
let load_mem (addr:quad) (m:mach) : int64 =
  let mapped_addr = match (map_addr addr) with
    | None      -> raise X86lite_segfault
    | Some addr -> addr
  in
  int64_of_sbytes [
    m.mem.(mapped_addr + 0);
    m.mem.(mapped_addr + 1);
    m.mem.(mapped_addr + 2);
    m.mem.(mapped_addr + 3);
    m.mem.(mapped_addr + 4);
    m.mem.(mapped_addr + 5);
    m.mem.(mapped_addr + 6);
    m.mem.(mapped_addr + 7)
  ]

(* Store data at memory address (STORE) *)
let store_mem (addr:quad) (data:quad) (m:mach) : unit =
  let mapped_addr = match (map_addr addr) with
    | None      -> raise X86lite_segfault
    | Some addr -> addr
  in
  let sbytes = sbytes_of_int64 data in
    m.mem.(mapped_addr + 0) <- List.nth sbytes 0;
    m.mem.(mapped_addr + 1) <- List.nth sbytes 1;
    m.mem.(mapped_addr + 2) <- List.nth sbytes 2;
    m.mem.(mapped_addr + 3) <- List.nth sbytes 3;
    m.mem.(mapped_addr + 4) <- List.nth sbytes 4;
    m.mem.(mapped_addr + 5) <- List.nth sbytes 5;
    m.mem.(mapped_addr + 6) <- List.nth sbytes 6;
    m.mem.(mapped_addr + 7) <- List.nth sbytes 7;
    ()

(* Store data in register *)
let store_reg (data:quad) (reg:reg) (m:mach) : unit =
  m.regs.(rind reg) <- data


(* Condition flags setter --------------------------------------------------- *)
let set_overflow_flag (result:Int64_overflow.t) (m:mach) : unit =
  m.flags.fo <- result.overflow

let set_zero_flag (result:int64) (m:mach) : unit =
  m.flags.fz <- result = 0L

let set_signed_flag (result:int64) (m:mach) : unit =
  m.flags.fs <- (Int64.shift_right_logical result 63) = 1L

let set_cond_flags (result:Int64_overflow.t) (m:mach) : unit =
  set_overflow_flag result m;
  set_zero_flag result.value m;
  set_signed_flag result.value m;
  ()


(* Operands eval helper ----------------------------------------------------- *)
(* Eval indirect address
 *   - Ind1: imm       : displacement by a literal or label imm value
 *   - Ind2: reg       : indirect reference to an address held in a register
 *   - Ind3L imm * reg : offset of an address held in a register
 *)
let eval_indirect_address (m:mach) (operand:operand) : int64 =
    match operand with
    | Ind1 (Lit x)      -> x
    | Ind1 (Lbl _)      -> failwith "TODO: Unable to eval label indirect"
    | Ind2 reg          -> m.regs.(rind reg)
    | Ind3 (Lit x, reg) -> Int64.add m.regs.(rind reg) x
    | Ind3 (Lbl _, _)   -> failwith "Fail to eval Ind3 for label immediate"
    | _                 -> failwith "Fail to eval non-indirect operand"

(* Eval operand value *)
let eval_operand_val (m:mach) (operand:operand) : int64 =
    match operand with
    | Imm (Lit x) -> x
    | Imm (Lbl _) -> failwith "Fail to eval value for label immediate"
    | Reg reg     -> m.regs.(rind reg)
    | Ind1 _ | Ind2 _ | Ind3 _ ->
      let addr = eval_indirect_address m operand in load_mem addr m

(* Generic store function *)
let store (operand:operand) (data:quad) (m:mach) : unit =
  match operand with
  | Imm _   -> failwith "Unable to store immediate value operand"
  | Reg reg -> store_reg data reg m
  | Ind1 _ | Ind2 _ | Ind3 _ ->
    let addr = eval_indirect_address m operand in
      store_mem addr data m

(* Eval arith instructions *)
let eval_arith (m:mach) (opcode:opcode) (operands:operand list) : unit =
  match opcode with
  | Negq ->
    let operand = List.nth operands 0 in
    let dest = eval_operand_val m operand in
    let res  = Int64_overflow.neg dest in
      store operand res.value m;
      set_cond_flags res m;
      (* OF is set to 1 if DEST is MIN_INT, and 0 otherwise *)
      m.flags.fo <- (dest = Int64.min_int)

  | Addq ->
    let operand_1 = List.nth operands 0 in
    let operand_2 = List.nth operands 1 in
    let src  = eval_operand_val m operand_1 in
    let dest = eval_operand_val m operand_2 in
    let res  = Int64_overflow.add dest src in
      store operand_2 res.value m;
      set_cond_flags res m

  | Subq ->
    let operand_1 = List.nth operands 0 in
    let operand_2 = List.nth operands 1 in
    let src  = eval_operand_val m operand_1 in
    let dest = eval_operand_val m operand_2 in
    let res  = Int64_overflow.sub dest src in
      store operand_2 res.value m;
      set_cond_flags res m

  | Imulq ->
    let operand_1 = List.nth operands 0 in
    let operand_2 = List.nth operands 1 in
    let src = eval_operand_val m operand_1 in
    let reg = eval_operand_val m operand_2 in
    let res = Int64_overflow.mul reg src in
      store operand_2 res.value m;
      set_cond_flags res m

  | Incq ->
    let operand_1 = List.nth operands 0 in
    let src = eval_operand_val m operand_1 in
    let res = Int64_overflow.succ src in
      store operand_1 res.value m;
      set_cond_flags res m

  | Decq ->
    let operand_1 = List.nth operands 0 in
    let src = eval_operand_val m operand_1 in
    let res = Int64_overflow.pred src in
      store operand_1 res.value m;
      set_cond_flags res m

  | _ -> ()

(* Eval logic instructions *)
let eval_logic (m:mach) (opcode:opcode) (operands:operand list) : unit =
  match opcode with
  | Notq ->
    let operand_1 = List.nth operands 0 in
    let dest = eval_operand_val m operand_1 in
      store operand_1 (Int64.lognot dest) m

  | Andq ->
    let operand_1 = List.nth operands 0 in
    let operand_2 = List.nth operands 1 in
    let src  = eval_operand_val m operand_1 in
    let dest = eval_operand_val m operand_2 in
    let res = Int64.logand dest src in
      store operand_2 res m;
      set_zero_flag res m;
      set_signed_flag res m;
      m.flags.fo <- false

  | Orq ->
    let operand_1 = List.nth operands 0 in
    let operand_2 = List.nth operands 1 in
    let src  = eval_operand_val m operand_1 in
    let dest = eval_operand_val m operand_2 in
    let res = Int64.logor dest src in
      store operand_2 res m;
      set_zero_flag res m;
      set_signed_flag res m;
      m.flags.fo <- false

  | Xorq ->
    let operand_1 = List.nth operands 0 in
    let operand_2 = List.nth operands 1 in
    let src  = eval_operand_val m operand_1 in
    let dest = eval_operand_val m operand_2 in
    let res = Int64.logxor dest src in
      store operand_2 res m;
      set_zero_flag res m;
      set_signed_flag res m;
      m.flags.fo <- false

  | _ -> ()

let eval_bit_m (m:mach) (opcode:opcode) (operands:operand list) : unit =
  let eval_amt (m:mach)(operand:operand) : int64 =
    match operand with
    | Imm Lit x -> x
    | Reg Rcx -> m.regs.(rind Rcx)
    | _ -> failwith "Invalid shift amount"
  in
  match opcode with
  | Sarq ->
    let operand_1 = List.nth operands 0 in
    let operand_2 = List.nth operands 1 in
    let amt  = Int64.to_int(eval_amt m operand_1) in
    let dest = eval_operand_val m operand_2 in
    let res = Int64.shift_right dest amt in
    let set_sarq_flags =
      match amt with
      | 0 -> ()
      | 1 -> m.flags.fo <- false
      | _ -> set_zero_flag res m; set_signed_flag res m
    in
    store operand_2 res m; set_sarq_flags

  | Shlq ->
    let operand_1 = List.nth operands 0 in
    let operand_2 = List.nth operands 1 in
    let amt  = Int64.to_int(eval_amt m operand_1) in
    let dest = eval_operand_val m operand_2 in
    let res = Int64.shift_left dest amt in
    let set_shlq_flags =
      match amt with
      | 0 -> ()
      | 1 ->
        if Int64.logand (Int64.shift_right dest 63) 1L <>
           Int64.logand (Int64.shift_right dest 64) 1L
        then m.flags.fo <- true
      | _ -> set_zero_flag res m; set_signed_flag res m
    in
    store operand_2 res m; set_shlq_flags

  | Shrq ->
    let operand_1 = List.nth operands 0 in
    let operand_2 = List.nth operands 1 in
    let amt  = Int64.to_int(eval_amt m operand_1) in
    let dest = eval_operand_val m operand_2 in
    let res = Int64.shift_right_logical dest amt in
    let set_shrq_flags =
      match amt with
      | 1 -> m.flags.fo <- (Int64.shift_right_logical dest 63) = 1L
      | _ -> set_zero_flag res m; set_signed_flag res m
    in
    store operand_2 res m; set_shrq_flags

(* TODO IMPLEMENT *)
  | Set cnd ->
    let curr_flags = { fo = m.flags.fo; fs = m.flags.fs; fz = m.flags.fz } in
    if interp_cnd curr_flags cnd
    then ()
    else ()

  | _ -> ()

(* Eval data movement instructions *)
let eval_data (m:mach) (opcode:opcode) (operands:operand list) : unit =
  match opcode with
  | Leaq ->
    let operand_1 = List.nth operands 0 in
    let operand_2 = List.nth operands 1 in
    let addr_of_ind = eval_indirect_address m operand_1 in
    store operand_2 addr_of_ind m

  | Movq ->
    let operand_1 = List.nth operands 0 in
    let operand_2 = List.nth operands 1 in
    let src_val = eval_operand_val m operand_1 in
    store operand_2 src_val m

  | Pushq ->
    let operand_1 = List.nth operands 0 in
    let src_val = eval_operand_val m operand_1 in
    m.regs.(rind Rsp) <- Int64.sub m.regs.(rind Rsp) 8L;
    store (Ind2 Rsp) src_val m

  | Popq ->
    let operand_1 = List.nth operands 0 in
    let src_val = eval_operand_val m (Ind2 Rsp) in
    store operand_1 src_val m;
    m.regs.(rind Rsp) <- Int64.add m.regs.(rind Rsp) 8L;

  | _ -> ()

(* Eval control flow instructions *)
let eval_flow (m:mach) (opcode:opcode) (operands:operand list) : unit =
  match opcode with
  | Cmpq ->
    let operand_1 = List.nth operands 0 in
    let operand_2 = List.nth operands 1 in
    let src  = eval_operand_val m operand_1 in
    let dest = eval_operand_val m operand_2 in
    let res  = Int64_overflow.sub dest src in
    set_cond_flags res m

  | Jmp ->
    let operand_1 = List.nth operands 0 in
    let src  = eval_operand_val m operand_1 in
    m.regs.(rind Rip) <- src

  | Callq -> ()
  | Retq -> ()
  | J _ -> ()
  | _ -> ()

(* Eval instruction dispatcher *)
let eval_instr (m:mach) (instruction:ins) : unit =
  match instruction with
  | (opcode, operands) ->
    match opcode with
    | Negq | Addq | Subq  | Imulq | Incq | Decq -> eval_arith m opcode operands;
                                                   fetch_next_isn_rip m
    | Notq | Andq | Orq   | Xorq                -> eval_logic m opcode operands;
                                                   fetch_next_isn_rip m
    | Sarq | Shlq | Shrq  | Set _               -> eval_bit_m m opcode operands;
                                                   fetch_next_isn_rip m
    | Leaq | Movq | Pushq | Popq                -> eval_data  m opcode operands;
                                                   fetch_next_isn_rip m
    | Cmpq | Jmp  | Callq | Retq | J _          -> eval_flow  m opcode operands

(* Dispatch eval function based on provided symbolic byte *)
let dispatch_eval_instr (m:mach) (instr:sbyte) : unit =
  match instr with
  | InsB0 ins -> eval_instr m ins
  | InsFrag | Byte _ -> increment_rip_by m 1L

(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)
let step (m:mach) : unit =
  let rip_idx = rind Rip in
  let fetched_instruction =
    match map_addr m.regs.(rip_idx) with
    | None -> raise X86lite_segfault
    | Some addr -> m.mem.(addr)
  in
    dispatch_eval_instr m fetched_instruction


(* Run program -------------------------------------------------------------- *)

(* Runs the machine until the rip register reaches a designated
   memory address. Returns the contents of %rax when the
   machine halts. *)
let run (m:mach) : int64 =
  while m.regs.(rind Rip) <> exit_addr do step m done;
  m.regs.(rind Rax)

(* assembling and linking --------------------------------------------------- *)

(* A representation of the executable *)
type exec = { entry    : quad              (* address of the entry point *)
            ; text_pos : quad              (* starting address of the code *)
            ; data_pos : quad              (* starting address of the data *)
            ; text_seg : sbyte list        (* contents of the text segment *)
            ; data_seg : sbyte list        (* contents of the data segment *)
            }

(* Assemble should raise this when a label is used but not defined *)
exception Undefined_sym of lbl

(* Assemble should raise this when a label is defined more than once *)
exception Redefined_sym of lbl

(* Convert an X86 program into an object file:
   - separate the text and data segments
   - compute the size of each segment
      Note: the size of an Asciz string section is (1 + the string length)
            due to the null terminator

   - resolve the labels to concrete addresses and 'patch' the instructions to
     replace Lbl values with the corresponding Imm values.

   - the text segment starts at the lowest address
   - the data segment starts after the text segment

  HINT: List.fold_left and List.fold_right are your friends.
 *)

type seg_type = Text | Data

let compute_seg_size (seg_type:seg_type) (e:elem) : int64 =
  match (seg_type, e.asm) with
  | (Text, Text t) -> Int64.of_int ((List.length t) * 8)
  | (Data, Data d) ->
    let get_data_size (acc:int64) (data:data) : int64 =
      match data with
      | Asciz str ->
        Int64.add (Int64.add acc 1L) (Int64.of_int (String.length str))
      | Quad imm -> Int64.add acc 8L
    in
    List.fold_left get_data_size 0L d
  | _ -> 0L

type lbl_tbl = (lbl, quad) Hashtbl.t
type lbl_addr_lookup = lbl_tbl * int64

let update_lbl_tbl (seg_type:seg_type) (lookup: lbl_addr_lookup) (e:elem)
  : lbl_addr_lookup =
  match seg_type with
  | Text ->
      let seg_sz =
        match e.asm with
        | Text _ -> compute_seg_size Text e
        | Data _ -> 0L
      in
      let (lbl_tbl, acc_sz) = lookup in
      let _ =
        match (Hashtbl.find_opt lbl_tbl e.lbl, e.asm) with
        | (None, Text _)   -> Hashtbl.add lbl_tbl e.lbl acc_sz
        | (Some _, Text _) -> raise (Redefined_sym e.lbl)
        | _                -> ()
      in
        (lbl_tbl, Int64.add seg_sz acc_sz)
  | Data ->
      let seg_sz =
        match e.asm with
        | Text _ -> 0L
        | Data _ -> compute_seg_size Data e
      in
      let (lbl_tbl, acc_sz) = lookup in
      let _ =
        match (Hashtbl.find_opt lbl_tbl e.lbl, e.asm) with
        | (None, Data _)   -> Hashtbl.add lbl_tbl e.lbl acc_sz
        | (Some _, Data _) -> raise (Redefined_sym e.lbl)
        | _                -> ()
      in
        (lbl_tbl, Int64.add seg_sz acc_sz)

(*
 * Resolve operands with label, given a label lookup table and original
 * list of operands.
 *)
let resolve_lbl_operand (operands:operand list) (lookup:lbl_tbl) : operand list =
  let find_lbl (lbl:lbl) : int64 =
    match (Hashtbl.find_opt lookup lbl) with
    | Some addr -> addr
    | None -> raise (Undefined_sym lbl)
  in
  let resolve_addr (operand:operand) : operand =
    match operand with
    | Imm (Lbl l) -> Imm (Lit (find_lbl l))
    | Ind1 (Lbl l) -> Ind1 (Lit (find_lbl l))
    | Ind3 ((Lbl l), r) -> Ind3 ((Lit (find_lbl l)), r)
    | op -> op
  in
  List.map resolve_addr operands

let resolve_lbl_text (lookup:lbl_tbl) (acc:sbyte list) (ins:ins) : sbyte list =
  let (opcode, operands) = ins in
  List.append acc (sbytes_of_ins (opcode, (resolve_lbl_operand operands lookup)))

let resolve_lbl_data (lookup:lbl_tbl) (acc:sbyte list) (data:data) : sbyte list =
  let find_lbl (lbl:lbl) : int64 =
    match (Hashtbl.find_opt lookup lbl) with
    | Some addr -> addr
    | None -> raise (Undefined_sym lbl)
  in
  match data with
  | Asciz str    -> List.append acc (sbytes_of_string str)
  | Quad (Lit x) -> List.append acc (sbytes_of_int64 x)
  | Quad (Lbl l) -> List.append acc (sbytes_of_data (Quad (Lit (find_lbl l))))

let serialize_seg (seg_type:seg_type) (lookup:lbl_tbl) (acc:sbyte list) (e:elem)
    : sbyte list =
  match (seg_type, e.asm) with
  | (Text, Text ins_list) ->
    List.append acc (List.fold_left (resolve_lbl_text lookup) [] ins_list)
  | (Data, Data data_list) ->
    List.append acc (List.fold_left (resolve_lbl_data lookup) [] data_list)
  | (_, _) -> acc

let assemble (p:prog) : exec =
  let init_lookup : lbl_tbl = Hashtbl.create 0xFFFF in
  let text_start : quad = 0x400000L in

  let (new_text_lookup, text_end)
    = List.fold_left (update_lbl_tbl Text) (init_lookup, text_start) p
  in
  let (new_lookup, text_sz)
    = List.fold_left (update_lbl_tbl Data) (new_text_lookup, text_end) p
  in

  let text_sbytes = List.fold_left (serialize_seg Text new_lookup) [] p in
  let data_sbytes = List.fold_left (serialize_seg Data new_lookup) [] p in

  let main =
    match (Hashtbl.find_opt new_text_lookup "main") with
    | Some addr -> addr
    | None -> raise (Undefined_sym "main")
  in
  {
    entry = main;
    text_pos = text_start;
    data_pos = text_end;
    text_seg = text_sbytes;
    data_seg = data_sbytes
  }


(* Convert an object file into an executable machine state.
    - allocate the mem array
    - set up the memory state by writing the symbolic bytes to the
      appropriate locations
    - create the inital register state
      - initialize rip to the entry point address
      - initializes rsp to the last word in memory
      - the other registers are initialized to 0
    - the condition code flags start as 'false'

  Hint: The Array.make, Array.blit, and Array.of_list library functions
  may be of use.
*)
let load {entry; text_pos; data_pos; text_seg; data_seg} : mach =
  let text_arr = Array.of_list text_seg in
  let data_arr = Array.of_list data_seg in
  let text_data_arr = Array.append text_arr data_arr in
  let mem_arr =
    Array.append (Array.make 0xFFF8 InsFrag)
                 (Array.of_list (sbytes_of_int64 exit_addr)) in

  let init_mem =
    Array.blit text_data_arr 0 mem_arr 0 (Array.length text_data_arr) in
  let flags = { fo = false; fz = false; fs = false } in
  let regs  = Array.make 17 0L in

  init_mem;
  Array.set regs (rind Rip) entry;
  Array.set regs (rind Rsp) 0x40FFF8L;
  { flags = flags; regs = regs; mem = mem_arr }

