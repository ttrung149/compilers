open Ll
open Llutil
open Ast

(* instruction streams ------------------------------------------------------ *)

(* As in the last project, we'll be working with a flattened representation
   of LLVMlite programs to make emitting code easier. This version
   additionally makes it possible to emit elements will be gathered up and
   "hoisted" to specific parts of the constructed CFG
   - G of gid * Ll.gdecl: allows you to output global definitions in the middle
     of the instruction stream. You will find this useful for compiling string
     literals
   - E of uid * insn: allows you to emit an instruction that will be moved up
     to the entry block of the current function. This will be useful for 
     compiling local variable declarations
*)

type elt = 
  | L of Ll.lbl             (* block labels *)
  | I of uid * Ll.insn      (* instruction *)
  | T of Ll.terminator      (* block terminators *)
  | G of gid * Ll.gdecl     (* hoisted globals (usually strings) *)
  | E of uid * Ll.insn      (* hoisted entry block instructions *)

type stream = elt list
let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x
let lift : (uid * insn) list -> stream = List.rev_map (fun (x,i) -> I (x,i))

(* Build a CFG and collection of global variable definitions from a stream *)
let cfg_of_stream (code:stream) : Ll.cfg * (Ll.gid * Ll.gdecl) list  =
    let gs, einsns, insns, term_opt, blks = List.fold_left
      (fun (gs, einsns, insns, term_opt, blks) e ->
        match e with
        | L l ->
           begin match term_opt with
           | None -> 
              if (List.length insns) = 0 then (gs, einsns, [], None, blks)
              else failwith @@ Printf.sprintf "build_cfg: block labeled %s has\
                                               no terminator" l
           | Some term ->
              (gs, einsns, [], None, (l, {insns; term})::blks)
           end
        | T t  -> (gs, einsns, [], Some (Llutil.Parsing.gensym "tmn", t), blks)
        | I (uid,insn)  -> (gs, einsns, (uid,insn)::insns, term_opt, blks)
        | G (gid,gdecl) ->  ((gid,gdecl)::gs, einsns, insns, term_opt, blks)
        | E (uid,i) -> (gs, (uid, i)::einsns, insns, term_opt, blks)
      ) ([], [], [], None, []) code
    in
    match term_opt with
    | None -> failwith "build_cfg: entry block has no terminator" 
    | Some term -> 
       let insns = einsns @ insns in
       ({insns; term}, blks), gs


(* compilation contexts ----------------------------------------------------- *)

(* To compile OAT variables, we maintain a mapping of source identifiers to the
   corresponding LLVMlite operands. Bindings are added for global OAT variables
   and local variables that are in scope. *)

module Ctxt = struct

  type t = (Ast.id * (Ll.ty * Ll.operand)) list
  let empty = []

  (* Add a binding to the context *)
  let add (c:t) (id:id) (bnd:Ll.ty * Ll.operand) : t = (id,bnd)::c

  (* Lookup a binding in the context *)
  let lookup (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    List.assoc id c

  (* Lookup a function, fail otherwise *)
  let lookup_function (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    match List.assoc id c with
    | Ptr (Fun (args, ret)), g -> Ptr (Fun (args, ret)), g
    | _ -> failwith @@ id ^ " not bound to a function"

  let lookup_function_option (id:Ast.id) (c:t) : (Ll.ty * Ll.operand) option =
    try Some (lookup_function id c) with _ -> None
  
end

(* compiling OAT types ------------------------------------------------------ *)

(* The mapping of source types onto LLVMlite is straightforward. Booleans and ints
   are represented as the corresponding integer types. OAT strings are
   pointers to bytes (I8). Arrays are the most interesting type: they are
   represented as pointers to structs where the first component is the number
   of elements in the following array.

   The trickiest part of this project will be satisfying LLVM's rudimentary type
   system. Recall that global arrays in LLVMlite need to be declared with their
   length in the type to statically allocate the right amount of memory. The 
   global strings and arrays you emit will therefore have a more specific type
   annotation than the output of cmp_rty. You will have to carefully bitcast
   gids to satisfy the LLVM type checker.
*)

let rec cmp_ty : Ast.ty -> Ll.ty = function
  | Ast.TBool  -> I1
  | Ast.TInt   -> I64
  | Ast.TRef r -> Ptr (cmp_rty r)

and cmp_rty : Ast.rty -> Ll.ty = function
  | Ast.RString  -> I8
  | Ast.RArray u -> Struct [I64; Array(0, cmp_ty u)]
  | Ast.RFun (ts, t) -> 
      let args, ret = cmp_fty (ts, t) in
      Fun (args, ret)

and cmp_ret_ty : Ast.ret_ty -> Ll.ty = function
  | Ast.RetVoid  -> Void
  | Ast.RetVal t -> cmp_ty t

and cmp_fty (ts, r) : Ll.fty =
  List.map cmp_ty ts, cmp_ret_ty r


let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Eq | Neq | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)

let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* Compiler Invariants

   The LLVM IR type of a variable (whether global or local) that stores an Oat
   array value (or any other reference type, like "string") will always be a
   double pointer.  In general, any Oat variable of Oat-type t will be
   represented by an LLVM IR value of type Ptr (cmp_ty t).  So the Oat variable
   x : int will be represented by an LLVM IR value of type i64*, y : string will
   be represented by a value of type i8**, and arr : int[] will be represented
   by a value of type {i64, [0 x i64]}**.  Whether the LLVM IR type is a
   "single" or "double" pointer depends on whether t is a reference type.

   We can think of the compiler as paying careful attention to whether a piece
   of Oat syntax denotes the "value" of an expression or a pointer to the
   "storage space associated with it".  This is the distinction between an
   "expression" and the "left-hand-side" of an assignment statement.  Compiling
   an Oat variable identifier as an expression ("value") does the load, so
   cmp_exp called on an Oat variable of type t returns (code that) generates a
   LLVM IR value of type cmp_ty t.  Compiling an identifier as a left-hand-side
   does not do the load, so cmp_lhs called on an Oat variable of type t returns
   and operand of type (cmp_ty t)*.  Extending these invariants to account for
   array accesses: the assignment e1[e2] = e3; treats e1[e2] as a
   left-hand-side, so we compile it as follows: compile e1 as an expression to
   obtain an array value (which is of pointer of type {i64, [0 x s]}* ).
   compile e2 as an expression to obtain an operand of type i64, generate code
   that uses getelementptr to compute the offset from the array value, which is
   a pointer to the "storage space associated with e1[e2]".

   On the other hand, compiling e1[e2] as an expression (to obtain the value of
   the array), we can simply compile e1[e2] as a left-hand-side and then do the
   load.  So cmp_exp and cmp_lhs are mutually recursive.  [[Actually, as I am
   writing this, I think it could make sense to factor the Oat grammar in this
   way, which would make things clearer, I may do that for next time around.]]

 
   Consider globals7.oat

   /--------------- globals7.oat ------------------ 
   global arr = int[] null;

   int foo() { 
     var x = new int[3]; 
     arr = x; 
     x[2] = 3; 
     return arr[2]; 
   }
   /------------------------------------------------

   The translation (given by cmp_ty) of the type int[] is {i64, [0 x i64}* so
   the corresponding LLVM IR declaration will look like:

   @arr = global { i64, [0 x i64] }* null

   This means that the type of the LLVM IR identifier @arr is {i64, [0 x i64]}**
   which is consistent with the type of a locally-declared array variable.

   The local variable x would be allocated and initialized by (something like)
   the following code snippet.  Here %_x7 is the LLVM IR uid containing the
   pointer to the "storage space" for the Oat variable x.

   %_x7 = alloca { i64, [0 x i64] }*                              ;; (1)
   %_raw_array5 = call i64*  @oat_alloc_array(i64 3)              ;; (2)
   %_array6 = bitcast i64* %_raw_array5 to { i64, [0 x i64] }*    ;; (3)
   store { i64, [0 x i64]}* %_array6, { i64, [0 x i64] }** %_x7   ;; (4)

   (1) note that alloca uses cmp_ty (int[]) to find the type, so %_x7 has 
       the same type as @arr 

   (2) @oat_alloc_array allocates len+1 i64's 

   (3) we have to bitcast the result of @oat_alloc_array so we can store it
        in %_x7 

   (4) stores the resulting array value (itself a pointer) into %_x7 

  The assignment arr = x; gets compiled to (something like):

  %_x8 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7     ;; (5)
  store {i64, [0 x i64] }* %_x8, { i64, [0 x i64] }** @arr       ;; (6)

  (5) load the array value (a pointer) that is stored in the address pointed 
      to by %_x7 

  (6) store the array value (a pointer) into @arr 

  The assignment x[2] = 3; gets compiled to (something like):

  %_x9 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7      ;; (7)
  %_index_ptr11 = getelementptr { i64, [0 x  i64] }, 
                  { i64, [0 x i64] }* %_x9, i32 0, i32 1, i32 2   ;; (8)
  store i64 3, i64* %_index_ptr11                                 ;; (9)

  (7) as above, load the array value that is stored %_x7 

  (8) calculate the offset from the array using GEP

  (9) store 3 into the array

  Finally, return arr[2]; gets compiled to (something like) the following.
  Note that the way arr is treated is identical to x.  (Once we set up the
  translation, there is no difference between Oat globals and locals, except
  how their storage space is initially allocated.)

  %_arr12 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** @arr    ;; (10)
  %_index_ptr14 = getelementptr { i64, [0 x i64] },
                 { i64, [0 x i64] }* %_arr12, i32 0, i32 1, i32 2  ;; (11)
  %_index15 = load i64, i64* %_index_ptr14                         ;; (12)
  ret i64 %_index15

  (10) just like for %_x9, load the array value that is stored in @arr 

  (11)  calculate the array index offset

  (12) load the array value at the index 

*)

(* Global initialized arrays:

  There is another wrinkle: To compile global initialized arrays like in the
  globals4.oat, it is helpful to do a bitcast once at the global scope to
  convert the "precise type" required by the LLVM initializer to the actual
  translation type (which sets the array length to 0).  So for globals4.oat,
  the arr global would compile to (something like):

  @arr = global { i64, [0 x i64] }* bitcast 
           ({ i64, [4 x i64] }* @_global_arr5 to { i64, [0 x i64] }* ) 
  @_global_arr5 = global { i64, [4 x i64] } 
                  { i64 4, [4 x i64] [ i64 1, i64 2, i64 3, i64 4 ] }

*) 



(* Some useful helper functions *)

(* Generate a fresh temporary identifier. Since OAT identifiers cannot begin
   with an underscore, these should not clash with any source variables *)
let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_%s%d" s (!c)

(* Amount of space an Oat type takes when stored in the satck, in bytes.  
   Note that since structured values are manipulated by reference, all
   Oat values take 8 bytes on the stack.
*)
let size_oat_ty (t : Ast.ty) = 8L

(* Generate code to allocate a zero-initialized array of source type TRef (RArray t) of the
   given size. Note "size" is an operand whose value can be computed at
   runtime *)
let oat_alloc_array (t:Ast.ty) (size:Ll.operand) : Ll.ty * operand * stream =
  let ans_id, arr_id = gensym "array", gensym "raw_array" in
  let ans_ty = cmp_ty @@ TRef (RArray t) in
  let arr_ty = Ptr I64 in
  ans_ty, Id ans_id, lift
    [ arr_id, Call(arr_ty, Gid "oat_alloc_array", [I64, size])
    ; ans_id, Bitcast(arr_ty, Id arr_id, ans_ty) ]




(* Compiles an expression exp in context c, outputting the Ll operand that will
   recieve the value of the expression, and the stream of instructions
   implementing the expression. 

   Tips:
   - use the provided cmp_ty function!

   - string literals (CStr s) should be hoisted. You'll need to make sure
     either that the resulting gid has type (Ptr I8), or, if the gid has type
     [n x i8] (where n is the length of the string), convert the gid to a 
     (Ptr I8), e.g., by using getelementptr.

   - use the provided "oat_alloc_array" function to implement literal arrays
     (CArr) and the (NewArr) expressions

*)
let rec cmp_exp (c:Ctxt.t) (exp:Ast.exp node) : Ll.ty * Ll.operand * stream =
  match exp.elt with
  | CNull rty -> Ptr(cmp_rty rty), Null, []
  | CBool b -> let i = if b then 1L else 0L in I1, Const(i), []
  | CInt i  -> I64, Const(i), []
  | CStr s ->
    let uid = gensym "str" in
    let gid = gensym "str_arr" in
    let str_typ = Array(String.length s + 1, I8) in
    Ptr I8, Id uid, [
      G(gid, (str_typ, GString s));
      I(uid, Gep(Ptr str_typ, Gid gid, [Const 0L; Const 0L]))
    ]

  | CArr (ty, es) ->
    let size_op = Const(Int64.of_int (List.length es)) in
    let arr_ty, arr_op, alloc_code = oat_alloc_array ty size_op in
    let ll_ty = cmp_ty ty in

    let indexed_es = List.mapi (fun i e -> (i, e)) es in
    let acc_add_elem_code s (i, elt) =
      let elt_op, cast_code = cmp_cast c elt ll_ty in
      let index = gensym "index" in 
      let store = gensym "store" in
      let i' = Int64.of_int i in
      s >@ cast_code
        >@ lift [
          index, Gep(arr_ty, arr_op, [Const 0L; Const 1L; Const i']);
          store, Store(ll_ty, elt_op, Id index)
        ] 
    in
    let add_elem_code = List.fold_left acc_add_elem_code [] indexed_es in
    arr_ty, arr_op, alloc_code >@ add_elem_code

  | NewArr(ty, exp) ->
    let _, len_op, len_code = cmp_exp c exp in
    let arr_ty, arr_op, alloc_code = oat_alloc_array ty len_op in
    arr_ty, arr_op, len_code >@ alloc_code

  | Id id ->
    let ty, op = Ctxt.lookup id c in
    let uid = gensym id in
    begin match ty with
      | Ptr (Fun _) -> ty, op, []
      | Ptr ty      -> ty, Id(uid), [I(uid, Load(Ptr ty, op))]
      | _           -> failwith "ERR: Id must be of Ptr type"
    end

  | Index(e, i) ->
    let ty, op, code = cmp_lhs c exp in
    let id = gensym "idx" in
    ty, Id id, code >:: I(id, Load(Ptr ty, op))

  | Call(f, es) -> cmp_call c f es 

  | Bop (binop, exp1, exp2) ->
    let (_, _, ret_ty) = typ_of_binop binop in
    let ret_ty = cmp_ty ret_ty in
    let uid = gensym "" in
    let (ty_exp1, op_exp1, stream_exp1) = cmp_exp c exp1 in
    let (ty_exp2, op_exp2, stream_exp2) = cmp_exp c exp2 in

    let ast_binop_to_ll_cnd binop =
      begin match binop with
        | Eq  -> Some(Ll.Eq)
        | Neq -> Some(Ll.Ne)
        | Gt  -> Some(Ll.Sgt)
        | Gte -> Some(Ll.Sge)
        | Lt  -> Some(Ll.Slt)
        | Lte -> Some(Ll.Sle)
        | _   -> None
      end
    in

    let ast_binop_to_ll_binop binop =
      begin match binop with
        | Add  -> Ll.Add
        | Sub  -> Ll.Sub
        | Mul  -> Ll.Mul
        | Shl  -> Ll.Shl
        | Shr  -> Ll.Lshr
        | Sar  -> Ll.Ashr
        | And | IAnd -> Ll.And
        | Or  | IOr  -> Ll.Or
        | _ -> failwith "ERR: Failed to convert AST binop to LLVMlite binop" 
      end
    in

    let ll_cnd = ast_binop_to_ll_cnd binop in
    begin match ll_cnd with
      | Some cnd ->
        let instruction = Icmp(cnd, ty_exp1, op_exp1, op_exp2) in
        let stream = stream_exp2 >@ stream_exp1 >:: I(uid, instruction) in
        (ret_ty, Id(uid), stream)
      | None ->
        let ll_binop = ast_binop_to_ll_binop binop in
        let instruction = Binop(ll_binop, ty_exp1, op_exp1, op_exp2) in
        let stream = stream_exp2 >@ stream_exp1 >:: I(uid, instruction) in
        (ret_ty, Id(uid), stream)
    end

  | Uop(op, exp) ->
    let res_node = begin match op with
      | Neg ->
        let minus_one_node = no_loc (CInt(Int64.of_int (-1))) in
        no_loc (Bop(Mul, exp, minus_one_node))
      | Lognot ->
        let false_node = no_loc (CBool(false)) in
        no_loc (Bop(And, exp, false_node))
      | Bitnot ->
        let minus_one_node = no_loc (CInt(Int64.of_int (-1))) in
        let get_twos_complement_node = no_loc (Bop(Mul, exp, minus_one_node)) in
        no_loc @@ Bop(Add, get_twos_complement_node, minus_one_node)
    end
    in cmp_exp c res_node


(* HELPER FUNCTION: compile some lhs expression *)
and cmp_lhs (c:Ctxt.t) (e:exp node) : Ll.ty * Ll.operand * stream =
  match e.elt with
  | Index (e, idx) ->
    let _, idx_op, idx_code = cmp_exp c idx in
    let arr_ty, arr_op, arr_code = cmp_exp c e in
    let ty = match arr_ty with
      | Ptr (Struct [_; Array (_,t)]) -> t
      | _ -> failwith "ERR: Can't index in non-array object" in

    let idx_ptr = gensym "idx_ptr" in
    let tmp_id = gensym "tmp" in
    ty, (Id idx_ptr),
    arr_code >@ idx_code >@ lift [
      tmp_id, Bitcast(arr_ty, arr_op, Ptr I64);
      idx_ptr, Gep(arr_ty, arr_op, [Const 0L; Const 1L; idx_op])
    ]

  | Id x ->
    let ty, op = Ctxt.lookup x c in
    let t = match ty with
      | Ptr ty -> ty
      | _     -> failwith "ERR: Expecting Ptr type" in
    t, op, []
  
  | _ -> failwith "ERR: cmp_lhs only supports Id and Index expression"

(* HELPER FUNCTION: compile function call expression *)
and cmp_call (c:Ctxt.t) (f:Ast.exp node) (args:Ast.exp node list)
                                           : Ll.ty * Ll.operand * stream =
  let t, op, code = cmp_exp c f in
  let tys, rt  = 
    match t with
    | Ptr (Fun (param_tys, ret_ty)) -> param_tys, ret_ty
    | _ -> failwith "ERR: cmp_call can't compile non-function expressions"
  in
  let acc e ty (args, code) =
    let arg_op, arg_code = cmp_cast c e ty in
    (ty, arg_op) :: args, arg_code @ code
  in
  let args, args_code = List.fold_right2 acc args tys ([],[]) in
  let result_id = gensym "call_result" in
  rt, Id result_id, code >@ args_code >:: I(result_id, Call(rt, op, args))

(* HELPER FUNCTION: compile cast expression *)
and cmp_cast (c:Ctxt.t) (e:Ast.exp node) (t:Ll.ty) : Ll.operand * stream =
  let from_ty, op, code = cmp_exp c e in
  if t = from_ty then
    op, code
  else
    let cast_id = gensym "cast" in
    let code' = code >:: I(cast_id, Bitcast(from_ty, op, t)) in
    Id cast_id, code' 


(* Compile a statement in context c with return typ rt. Return a new context, 
   possibly extended with new local bindings, and the instruction stream
   implementing the statement.

   Left-hand-sides of assignment statements must either be OAT identifiers,
   or an index into some arbitrary expression of array type. Otherwise, the
   program is not well-formed and your compiler may throw an error.

   Tips:
   - for local variable declarations, you will need to emit Allocas in the
     entry block of the current function using the E() constructor.

   - don't forget to add a bindings to the context for local variable 
     declarations
   
   - you can avoid some work by translating For loops to the corresponding
     While loop, building the AST and recursively calling cmp_stmt

   - you might find it helpful to reuse the code you wrote for the Call
     expression to implement the SCall statement

   - compiling the left-hand-side of an assignment is almost exactly like
     compiling the Id or Index expression. Instead of loading the resulting
     pointer, you just need to store to it!

 *)
let rec cmp_stmt (c:Ctxt.t) (rt:Ll.ty) (stmt:Ast.stmt node) : Ctxt.t * stream =
  match stmt.elt with 
  | Assn (p, e) ->
     let ty, pop, path_code = cmp_lhs c p in
     let eop, cast_code = cmp_cast c e ty in
     let store_lbl = gensym "store" in
     c, path_code >@ cast_code >:: I(store_lbl, (Store (ty, eop, pop)))

  | Decl (id, exp) ->
    let (ty, op, stream) = cmp_exp c exp in
    let uid = gensym id in
    let c' = Ctxt.add c id (Ptr ty, Id uid) in
    c', stream
        >:: E(uid, Alloca ty)
        >:: I("store", Store(ty, op, Id uid)) 

  | Ret e ->
    begin match e with
      | None -> c, [ T(Ret(Void, None)) ]
      | Some exp ->
        let (ty, op, stream) = cmp_exp c exp in
        c, stream >:: T(Ret(ty, Some op)) 
    end

  | SCall(fn, args) ->
    let _, _, stream = cmp_call c fn args in
    c, stream

  | If(cond, stmt_1, stmt_2) -> 
     let cond_ty, cond_op, cond_code = cmp_exp c cond in
     let _, then_code = cmp_block c rt stmt_1 in
     let _, else_code = cmp_block c rt stmt_2 in
     let then_lbl  = gensym "then" in
     let else_lbl  = gensym "else" in
     let after_lbl = gensym "after" in
     c, cond_code 
        >:: T(Cbr (cond_op, then_lbl, else_lbl))
        >:: L(then_lbl) >@ then_code
        >:: T(Br after_lbl) 
        >:: L(else_lbl) >@ else_code
        >:: T(Br after_lbl) 
        >:: L(after_lbl)

  | For(inits, cond, after, body) ->
     let decls = List.map (fun d -> no_loc (Decl d)) inits in
     let init_cond, init_code = cmp_block c rt decls in
     let guard =
       match cond with 
       | Some e -> e
       | None -> no_loc(CBool true)
     in
     let guard_ty, guard_op, guard_code = cmp_exp init_cond guard in
     let after =
       match after with
       | None -> []
       | Some s -> [s]
     in
     let cond_lbl  = gensym "cond" in
     let body_lbl  = gensym "body" in
     let after_lbl = gensym "after" in
     let _, body_code = cmp_block init_cond rt body  in
     let _, after_code = cmp_block init_cond rt after  in
     c, init_code 
        >:: T (Br cond_lbl)
        >:: L cond_lbl >@ guard_code
        >:: T (Cbr (guard_op, body_lbl, after_lbl))
        >:: L body_lbl >@ body_code >@ after_code
        >:: T (Br cond_lbl)
        >:: L after_lbl

  | While(cond, body) ->
     let cond_ty, cond_op, cond_code = cmp_exp c cond in
     let cond_lbl  = gensym "cond" in
     let body_lbl  = gensym "body" in
     let after_lbl = gensym "after" in
     let _, body_code = cmp_block c rt body in
     c, [] 
        >:: T(Br cond_lbl)
        >:: L(cond_lbl) >@ cond_code
        >:: T(Cbr (cond_op, body_lbl, after_lbl))
        >:: L(body_lbl) >@ body_code
        >:: T(Br cond_lbl)
        >:: L(after_lbl)


(* Compile a series of statements *)
and cmp_block (c:Ctxt.t) (rt:Ll.ty) (stmts:Ast.block) : Ctxt.t * stream =
  List.fold_left (fun (c, code) s -> 
      let c, stmt_code = cmp_stmt c rt s in
      c, code >@ stmt_code
    ) (c,[]) stmts



(* Adds each function identifer to the context at an
   appropriately translated type.  

   NOTE: The Gid of a function is just its source name
*)
let cmp_function_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
    List.fold_left (fun c -> function
      | Ast.Gfdecl { elt={ frtyp; fname; args } } ->
         let ft = TRef (RFun (List.map fst args, frtyp)) in
         Ctxt.add c fname (cmp_ty ft, Gid fname)
      | _ -> c
    ) c p 

(* Populate a context with bindings for global variables 
   mapping OAT identifiers to LLVMlite gids and their types.

   Only a small subset of OAT expressions can be used as global initializers
   in well-formed programs. (The constructors starting with C). 
*)
let cmp_global_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
  let acc_ctxt ctxt prog =
    begin match prog with
    | Ast.Gvdecl { elt = { name; init } } ->
      let ty = begin match init.elt with
        | CBool _         -> Ptr I1
        | CInt _          -> Ptr I64
        | CStr _          -> Ptr(Ptr I8)
        | CArr (ty, exps) -> Ptr(Ptr (Struct [I64; Array(0, cmp_ty ty)]))
        | CNull ty        -> Ptr(Ptr (cmp_rty ty))
        | _               -> failwith "ERR: Fail to compile global context for types."
      end
      in
      Ctxt.add ctxt name (ty, Gid name)
    | _ -> ctxt
    end
  in
  List.fold_left acc_ctxt c p

(* Compile a function declaration in global context c. Return the LLVMlite cfg
   and a list of global declarations containing the string literals appearing
   in the function.

   You will need to
   1. Allocate stack space for the function parameters using Alloca
   2. Store the function arguments in their corresponding alloca'd stack slot
   3. Extend the context with bindings for function variables
   4. Compile the body of the function using cmp_block
   5. Use cfg_of_stream to produce a LLVMlite cfg from 
 *)
let cmp_fdecl (c:Ctxt.t) (f:Ast.fdecl node) : Ll.fdecl * (Ll.gid * Ll.gdecl) list =
  let f_elt = f.elt in
  let args_ty = List.map (fun (ty, _) -> cmp_ty ty) f_elt.args in
  let return_ty  = cmp_ret_ty f_elt.frtyp in

  (* Accumlate args stream *)
  let acc_args_stream (ctxt, stream) (ty, id) =
    let compiled_uid = gensym id in
    let compiled_type = cmp_ty ty in
    let c' = Ctxt.add ctxt id (Ptr compiled_type, Id compiled_uid) in
    let stream' =
      stream >:: E(compiled_uid, Alloca compiled_type)
             >:: I("", Store(compiled_type, Id id, Id compiled_uid))
    in
    (c', stream')
  in
  let c', fargs_stream = List.fold_left acc_args_stream (c, Ctxt.empty) f_elt.args in

  (* Generate function body stream *)
  let _, fbody_stream = cmp_block c' return_ty f_elt.body in

  (* Compiled function declaration *)
  let (fcfg, gdecls) = cfg_of_stream (fargs_stream >@ fbody_stream) in
  let fargs_id = List.map (fun (_, id) -> id) f_elt.args in
  let fty = (args_ty, return_ty) in

  ({f_ty = fty; f_param = fargs_id; f_cfg = fcfg}, gdecls)


(* Compile a global initializer, returning the resulting LLVMlite global
   declaration, and a list of additional global declarations.

   Tips:
   - Only CNull, CBool, CInt, CStr, and CArr can appear as global initializers
     in well-formed OAT programs. Your compiler may throw an error for the other
     cases

   - OAT arrays are always handled via pointers. A global array of arrays will
     be an array of pointers to arrays emitted as additional global declarations.
*)

let rec cmp_gexp c (e:Ast.exp node) : Ll.gdecl * (Ll.gid * Ll.gdecl) list =
  match e.elt with
  | CNull rty -> (Ptr(cmp_rty rty), GNull), []
  | CBool b ->
      let i = if b then 1L else 0L in
      (I1, GInt(i)), []
  | CInt i -> (I64, GInt i), []
  | CStr s ->
    let gid = gensym "global_str" in
    let ty = Array(String.length s + 1, I8) in
    let str_cast = GBitcast(Ptr ty, GGid gid, Ptr I8) in
    (Ptr I8, str_cast), [gid, (ty, GString s)]

  | CArr (ty, es) ->
    let len = List.length es in
    let ll_ty = cmp_ty ty in
    let gid = gensym "global_arr" in
    let arr_ty    = Struct [I64; Array(len, ll_ty)] in
    let casted_ty = Struct [I64; Array(0, ll_ty)] in

    let acc cs (elts, gs) =
      let elem, gs' = cmp_gexp c cs in
      elem :: elts, gs' @ gs
    in
    let elems, gs = List.fold_right acc es ([], []) in
    let arr_str   = GStruct[I64, GInt(Int64.of_int len); Array(len, ll_ty), GArray elems] in
    let cast      = GBitcast(Ptr arr_ty, GGid gid, Ptr casted_ty) in
    let gs'       = (gid, (arr_ty, arr_str)) :: gs in
    (Ptr casted_ty, cast), gs' 

  | _ -> failwith "ERR: Invalid type for compiling global initializer."


(* Oat internals function context ------------------------------------------- *)
let internals = [
    "oat_alloc_array",         Ll.Fun ([I64], Ptr I64)
  ]

(* Oat builtin function context --------------------------------------------- *)
let builtins =
  [ "array_of_string",  cmp_rty @@ RFun ([TRef RString], RetVal (TRef(RArray TInt)))
  ; "string_of_array",  cmp_rty @@ RFun ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", cmp_rty @@ RFun ([TRef RString],  RetVal TInt)
  ; "string_of_int",    cmp_rty @@ RFun ([TInt],  RetVal (TRef RString))
  ; "string_cat",       cmp_rty @@ RFun ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     cmp_rty @@ RFun ([TRef RString],  RetVoid)
  ; "print_int",        cmp_rty @@ RFun ([TInt],  RetVoid)
  ; "print_bool",       cmp_rty @@ RFun ([TBool], RetVoid)
  ]

(* Compile a OAT program to LLVMlite *)
let cmp_prog (p:Ast.prog) : Ll.prog =
  (* add built-in functions to context *)
  let init_ctxt =
    List.fold_left (fun c (i, t) -> Ctxt.add c i (Ll.Ptr t, Gid i))
      Ctxt.empty builtins
  in
  let fc = cmp_function_ctxt init_ctxt p in

  (* build global variable context *)
  let c = cmp_global_ctxt fc p in

  (* compile functions and global variables *)
  let fdecls, gdecls =
    List.fold_right (fun d (fs, gs) ->
        match d with
        | Ast.Gvdecl { elt=gd } ->
           let ll_gd, gs' = cmp_gexp c gd.init in
           (fs, (gd.name, ll_gd)::gs' @ gs)
        | Ast.Gfdecl fd ->
           let fdecl, gs' = cmp_fdecl c fd in
           (fd.elt.fname,fdecl)::fs, gs' @ gs
      ) p ([], [])
  in

  (* gather external declarations *)
  let edecls = internals @ builtins in
  { tdecls = []; gdecls; fdecls; edecls }
