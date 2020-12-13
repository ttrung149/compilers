open Ast
open Astlib
open Tctxt

(* Error Reporting ---------------------------------------------------------- *)
(* NOTE: Use type_error to report error messages for ill-typed programs. *)

exception TypeError of string

let type_error (l : 'a node) err = 
  let (_, (s, e), _) = l.loc in
  raise (TypeError (Printf.sprintf "[%d, %d] %s" s e err))


(* initial context: G0 ------------------------------------------------------ *)
(* The Oat types of the Oat built-in functions *)
let builtins =
  [ "array_of_string",  ([TRef RString],  RetVal (TRef(RArray TInt)))
  ; "string_of_array",  ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", ([TRef RString],  RetVal TInt)
  ; "string_of_int",    ([TInt], RetVal (TRef RString))
  ; "string_cat",       ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     ([TRef RString],  RetVoid)
  ; "print_int",        ([TInt], RetVoid)
  ; "print_bool",       ([TBool], RetVoid)
  ]

(* binary operation types --------------------------------------------------- *)
let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)
  | Eq | Neq -> failwith "typ_of_binop called on polymorphic == or !="

(* unary operation types ---------------------------------------------------- *)
let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* subtyping ---------------------------------------------------------------- *)
(* Decides whether H |- t1 <: t2 
    - assumes that H contains the declarations of all the possible struct types

    - you will want to introduce addition (possibly mutually recursive) 
      helper functions to implement the different judgments of the subtyping
      relation. We have included a template for subtype_ref to get you started.
      (Don't forget about OCaml's 'and' keyword.)
*)
let rec subtype (c : Tctxt.t) (t1 : Ast.ty) (t2 : Ast.ty) : bool =
  match t1, t2 with
  | TInt, TInt -> true
  | TBool, TBool -> true
  | TRef(rty_1), TRef(rty_2)
  | TNullRef(rty_1), TNullRef(rty_2)
  | TRef(rty_1), TNullRef(rty_2) -> subtype_ref c rty_1 rty_2
  | _ -> false

(* Decides whether H |-r ref1 <: ref2 *)
and subtype_ref (c : Tctxt.t) (t1 : Ast.rty) (t2 : Ast.rty) : bool =
  match t1, t2 with
  | RString, RString -> true
  | RFun(args, ret_ty), RFun(args', ret_ty') -> subtype_func c args ret_ty args' ret_ty'
  | RArray t1, RArray t2 -> t1 = t2
  | RStruct id1, RStruct id2 -> subtype_struct c id1 id2
  | _ -> false

and subtype_struct (c : Tctxt.t) (s1 : Ast.id) (s2 : Ast.id) : bool =
  (s1 = s2) ||
  match Tctxt.lookup_struct_option s2 c with
  | None -> false
  | Some fields ->
    List.fold_left (fun acc field -> acc && (
      let field_s1 = Tctxt.lookup_field_option s1 field.fieldName c in
      match field_s1 with
      | Some t -> t = field.ftyp
      | None -> false
    )) true fields

and subtype_return_ty (c : Tctxt.t) (t1 : Ast.ret_ty) (t2 : Ast.ret_ty) : bool =
  match t1, t2 with
  | RetVoid, RetVoid -> true
  | RetVal t1 , RetVal t2 -> subtype c t1 t2
  | _ -> false

and subtype_func (c : Tctxt.t) (args : Ast.ty list) (ret_ty : Ast.ret_ty)
                               (args': Ast.ty list) (ret_ty': Ast.ret_ty) : bool = 
  let same_args_len = (List.length args = List.length args') in
  let args_subtype_acc acc arg arg' = acc && subtype c arg' arg in
  let is_args_subtype =
    same_args_len && (List.fold_left2 args_subtype_acc true args args') in
  let is_ret_subtype = subtype_return_ty c ret_ty ret_ty' in
  is_args_subtype && is_ret_subtype 


(* well-formed types -------------------------------------------------------- *)
(* Implement a (set of) functions that check that types are well formed according
   to the H |- t and related inference rules

    - the function should succeed by returning () if the type is well-formed
      according to the rules

    - the function should fail using the "type_error" helper function if the 
      type is not well formed

    - l is just an ast node that provides source location information for
      generating error messages (it's only needed for the type_error generation)

    - tc contains the structure definition context
 *)
let rec typecheck_ty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ty) : unit =
  match t with
  | TInt | TBool -> ()
  | TNullRef rty | TRef rty -> typecheck_rty l tc rty

and typecheck_ret_ty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ret_ty) : unit =
  match t with
  | RetVoid -> ()
  | RetVal ty -> typecheck_ty l tc ty

and typecheck_rty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.rty) : unit =
  begin match t with
  | RString -> ()
  | RStruct id ->
    begin match Tctxt.lookup_struct_option id tc with
      | Some _ -> ()
      | None -> type_error l (Printf.sprintf "ERR: Undefined struct '%s'" id)
    end
  | RArray ty -> typecheck_ty l tc ty
  | RFun (args, ret_ty) ->
    let typecheck_arg ty = typecheck_ty l tc ty in
    List.iter typecheck_arg args;
    typecheck_ret_ty l tc ret_ty
  end

(* A helper function to determine whether a type allows the null value *)
let is_nullable_ty (t : Ast.ty) : bool =
  match t with
  | TNullRef _ -> true
  | _ -> false

(* typechecking expressions ------------------------------------------------- *)
(* Typechecks an expression in the typing context c, returns the type of the
   expression.  This function should implement the inference rules given in the
   oat.pdf specification.  There, they are written:

       H; G; L |- exp : t

   See tctxt.ml for the implementation of the context c, which represents the
   four typing contexts: H - for structure definitions G - for global
   identifiers L - for local identifiers

   Returns the (most precise) type for the expression, if it is type correct
   according to the inference rules.

   Uses the type_error function to indicate a (useful!) error message if the
   expression is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   Notes: - Structure values permit the programmer to write the fields in any
   order (compared with the structure definition).  This means that, given the
   declaration struct T { a:int; b:int; c:int } The expression new T {b=3; c=4;
   a=1} is well typed.  (You should sort the fields to compare them.)

*)
let rec typecheck_exp (c : Tctxt.t) (e : Ast.exp node) : Ast.ty =
  begin match e.elt with
    | CNull rty -> typecheck_rty e c rty; TNullRef(rty)
    | CBool _ -> TBool 
    | CInt _  -> TInt
    | CStr _  -> TRef(RString) 

    | Id id ->
      begin match (Tctxt.lookup_option id c) with
        | None -> type_error e (Printf.sprintf "ERR: Undefined id '%s'" id)
        | Some ty -> ty
      end

    | CArr(ty, exps) ->
      typecheck_ty e c ty;
      let exp_types = List.map (fun e -> typecheck_exp c e) exps in
      let acc_ty acc t = acc && subtype c t ty in
      let sound_ty = List.fold_left acc_ty true exp_types in
      if sound_ty then TRef(RArray(ty))
      else type_error e "ERR: Invalid type for array element"

    | NewArr(ty, exp) ->
      let exp_type = typecheck_exp c exp in
      begin match ty, exp_type with
        | TBool, TInt -> TRef(RArray(TBool))
        | TInt,  TInt -> TRef(RArray(TInt))
        | TNullRef rty, TInt -> TRef(RArray(TNullRef rty))
        | _    -> type_error e "ERR: Invalid type for array element"
      end

    | NewArrInit(ty, len, id, init) ->
      typecheck_ty e c ty;
      let sound_len_ty = (typecheck_exp c len = TInt) in
      let valid_id = begin match Tctxt.lookup_local_option id c with
        | None -> true
        | Some _ -> false 
      end in
      let valid_init = subtype c (typecheck_exp (Tctxt.add_local c id TInt) init) ty in
      begin match sound_len_ty, valid_id, valid_init with
        | true, true, true -> TRef(RArray(ty))
        | false, _, _ -> type_error e "ERR: Expect type int for array length"
        | _, false, _ -> type_error e (Printf.sprintf "ERR: Undefined id '%s'" id)
        | _, _, false -> type_error e "ERR: Invalid type for initializers"
      end

    | Index(arr, ind) ->
      let ind_ty = typecheck_exp c ind in
      let arr_ty = typecheck_exp c arr in
      begin match arr_ty, ind_ty with
        | TRef(RArray(ty)), TInt -> ty
        | TRef(RArray(_)), ty -> type_error e
            (Printf.sprintf "ERR: Expect Int type index, got '%s'" (string_of_ty ty))
        | ty, TInt -> type_error e 
            (Printf.sprintf "ERR: Expect an expression of type TRef(TArray(t)), got '%s'"
              (string_of_ty ty))
        | _, _ -> type_error e "ERR: Invalid type for array indexing"
      end

    | Length arr ->
      let arr_ty = typecheck_exp c arr in
      begin match arr_ty with
        | TRef(RArray(_)) -> TInt
        | ty -> type_error e "ERR: Invalid type for 'Length'"
      end

    | CStruct(id, fs) ->
      let found_struct_fs = Tctxt.lookup_struct id c in
      let same_len = (List.length found_struct_fs = List.length fs) in
      let has_all_fields = List.fold_left (
        fun acc f -> acc && (List.exists (fun (id, _) -> id = f.fieldName) fs)
      ) true found_struct_fs in

      let acc_field_subtype acc (fid, init_exp) = acc &&
        let init_ty = typecheck_exp c init_exp in
        let lookup = Tctxt.lookup_field_option id fid c in 
        begin match lookup with
          | None -> false 
          | Some field_ty -> subtype c init_ty field_ty
        end
      in
      let sound_fields_ty = List.fold_left acc_field_subtype true fs in

      if same_len && has_all_fields && sound_fields_ty then TRef(RStruct id)
      else type_error e "ERR: Invalid struct fields"

    | Proj(s, id) ->
      let s_ty = typecheck_exp c s in
      begin match s_ty with
        | TRef(RStruct s_id) ->
          let f_ty = Tctxt.lookup_field_option s_id id c in
          begin match f_ty with
            | None -> type_error e
               (Printf.sprintf  "ERR: Undefined field '%s'" id)
            | Some ty -> ty
          end
        | ty -> type_error e
            (Printf.sprintf "ERR: Proj expects 'struct' type, got '%s'" (string_of_ty ty))
      end

    | Call(fun_id, args) ->
      let params, ret_ty =
        begin match typecheck_exp c fun_id with
          | TRef(RFun(params, ret_ty)) -> params, ret_ty
          | ty -> type_error e
            (Printf.sprintf "ERR: Can't call non-function '%s'" (string_of_ty ty))
        end
      in

      let args_ty = List.map (fun arg -> typecheck_exp c arg) args in
      let same_len = (List.length params = List.length args) in

      let acc_subtype acc param arg = acc && subtype c arg param in
      if same_len then
        let sound_args_ty = List.fold_left2 acc_subtype true params args_ty in
        begin match ret_ty, sound_args_ty with
          | RetVal r, true -> r
          | _, _ -> type_error e "ERR: Invalid args type in function call"
        end
      else
        type_error e
          (Printf.sprintf "ERR: Expected %d args, got %d"(List.length args) (List.length params))

    | Bop (op, e1, e2) ->
      begin match op with
        | Eq | Neq ->
          let ty_1 = typecheck_exp c e1 in
          let ty_2 = typecheck_exp c e2 in
          if (subtype c ty_1 ty_2) && (subtype c ty_2 ty_1) then TBool
          else type_error e "ERR: Mismatching types for binop comparator"

        | _ ->
          let ty_1, ty_2, ret_ty = typ_of_binop op in
          if (typecheck_exp c e1 = ty_1) && (typecheck_exp c e2 = ty_2) then ret_ty
          else type_error e "ERR: Mismatching operands type for binop"
      end

    | Uop (op, e) ->
      let exp_ty, ret_ty = typ_of_unop op in
      if (typecheck_exp c e = exp_ty) then ret_ty
      else type_error e "ERR: Mismatching types for unary operation"

  end

(* Typecheck global expressions *)
let rec typecheck_gexp (tc : Tctxt.t) (e : Ast.exp node) : Ast.ty =
  match e.elt with
  | CNull _
  | CBool _
  | CInt _
  | CStr _
  | CArr _
  | Id _ -> typecheck_exp tc e
  | CStruct (id, fs) -> (
    let f_tys = List.map (fun (f_id, _) -> Tctxt.lookup_field id f_id tc) fs in
    let e_tys = List.map (fun (_, elem    ) -> typecheck_gexp tc elem) fs in
    let acc_ty acc exp_ty ty = acc && subtype tc ty exp_ty in
    let sound_ty = List.fold_left2 acc_ty true f_tys e_tys in
    if sound_ty then TRef(RStruct id)
    else type_error e "ERR: Invalid global struct type"
  )
  | _ -> type_error e "ERR: Invalid global types"


(* statements --------------------------------------------------------------- *)

(* Typecheck a statement
   This function should implement the statment typechecking rules from oat.pdf.

   Inputs:
    - tc: the type context
    - s: the statement node
    - to_ret: the desired return type (from the function declaration)

   Returns:
     - the new type context (which includes newly declared variables in scope
       after this statement)

     - A boolean indicating the return behavior of a statement:
        false:  might not return
        true: definitely returns 

        in the branching statements, the return behavior of the branching 
        statement is the conjunction of the return behavior of the two 
        branches: both both branches must definitely return in order for 
        the whole statement to definitely return.

        Intuitively: if one of the two branches of a conditional does not 
        contain a return statement, then the entire conditional statement might 
        not return.
  
        looping constructs never definitely return 

   Uses the type_error function to indicate a (useful!) error message if the
   statement is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   - You will probably find it convenient to add a helper function that implements the 
     block typecheck rules.
*)
let rec typecheck_stmt (tc : Tctxt.t) (s:Ast.stmt node) (to_ret:ret_ty) : Tctxt.t * bool =
  begin match s.elt with
    | Assn (lhs, rhs) ->
      let lhs_ty = begin match lhs.elt with
        | Id id ->
          let ty = typecheck_exp tc lhs in
          begin match Tctxt.lookup_global_option id tc, ty with
            | Some _, TRef(RFun _) -> type_error lhs (
                Printf.sprintf "ERR: Function '%s' cannot be assigned" id
              )
            | _ -> ty
          end

        | _ -> typecheck_exp tc lhs
      end
      in
      let rhs_ty = typecheck_exp tc rhs in
      if (subtype tc rhs_ty lhs_ty) then (tc, false)
      else type_error s "ERR: Fail to assign left exp to right exp"

    | Decl vdecl -> (typecheck_decl tc s vdecl, false)

    | Ret opt ->
      begin match (opt, to_ret) with
        | None, RetVoid -> tc, true
        | None, RetVal ret_ty -> type_error s
            (Printf.sprintf "ERR: Expected return type '%s'" (string_of_ty ret_ty))
        | Some exp, RetVoid ->
          let exp_ty = typecheck_exp tc exp in
          type_error s (Printf.sprintf "ERR: Expected void return type, got '%s'"
                       (string_of_ty exp_ty))
        | Some exp, RetVal ret_ty ->
          let exp_ty = typecheck_exp tc exp in
          if subtype tc exp_ty ret_ty then (tc, true)
          else type_error exp (Printf.sprintf "ERR: Expected type '%s', got '%s'"
                       (string_of_ty ret_ty) (string_of_ty exp_ty))
      end

    | SCall(fun_id, args) ->
      let params =
        begin match typecheck_exp tc fun_id with
          | TRef(RFun(params, RetVoid)) -> params
          | _ -> type_error fun_id "ERR: Unexpected types for SCall"
        end
      in
      let args_ty = List.map (fun arg -> typecheck_exp tc arg) args in
      let same_len = (List.length params = List.length args) in
      let acc_subtype acc param arg = acc && subtype tc arg param in
      let sound_args_ty = List.fold_left2 acc_subtype true params args_ty in

      begin match sound_args_ty, same_len with
        | true, true -> tc, false
        | false, true -> type_error fun_id "ERR: Invalid args type in function call"
        | _, false -> type_error fun_id
          (Printf.sprintf "ERR: Expected %d args, got %d"(List.length args) (List.length params))
      end

    | If(cond, if_blk, else_blk) ->
      let cond_ty    = typecheck_exp tc cond in
      let _, if_ty   = typecheck_blk tc if_blk to_ret in
      let _, else_ty = typecheck_blk tc else_blk to_ret in
      begin match cond_ty with
        | TBool -> tc, if_ty && else_ty
        | _ -> type_error cond "ERR: Condition is not of boolean type"
      end

    | Cast(rty, id, exp, b1, b2) ->
      let exp_type = typecheck_exp tc exp in
      begin match exp_type with
        | TNullRef r' ->
          if subtype_ref tc r' rty then
          let _, l_ret = typecheck_blk (Tctxt.add_local tc id (TRef rty)) b1 to_ret in
          let _, r_ret = typecheck_blk tc b2 to_ret in
          tc, l_ret && r_ret
          else type_error exp "ERR: Invalid cast"
        | _ -> type_error exp "ERR: Invalid cast"
      end

    | For (decls, guard, stmts, blk) ->
      let acc_tc c (id, e) =
        let ty = typecheck_exp tc e in
        Tctxt.add_local c id ty
      in
      let tc' = List.fold_left acc_tc tc decls in
      let _ = typecheck_blk tc' blk to_ret in
      let _ = begin match guard, stmts with
        | None, _  |  _ , None  -> ()
        | Some b, _ ->
          if (typecheck_exp tc' b) <> TBool then type_error b "ERR: Expect bool type for cond"
          else ()
      end
      in tc, false

    | While (cond, while_blk) ->
      let _ = typecheck_blk tc while_blk to_ret in
      let cond_ty = typecheck_exp tc cond in
      begin match cond_ty with
        | TBool -> tc, false
        | _ -> type_error cond "ERR: Expected type bool for cond"
      end
  end

and typecheck_decl (tc : Tctxt.t) (s : Ast.stmt node) (vdecl : Ast.vdecl) : Tctxt.t =  
  let id, e = vdecl in
  let ty = typecheck_exp tc e in
  let lookup = Tctxt.lookup_local_option id tc in
  match lookup with
  | None -> Tctxt.add_local tc id ty
  | Some _ -> type_error s 
    (Printf.sprintf "ERR: Redefinition of identifier '%s'" id)

and typecheck_blk (tc : Tctxt.t) (blk : Ast.block) (to_ret:ret_ty) : Tctxt.t * bool =
  match blk with
  | [] -> tc, false
  | [stmt] -> typecheck_stmt tc stmt to_ret
  | stmt :: stmts -> (
    let tc', returns = typecheck_stmt tc stmt to_ret in
    if returns then type_error stmt "ERR: Stmt is not expected to return"
    else typecheck_blk tc' stmts to_ret
  )


(* struct type declarations ------------------------------------------------- *)
(* Here is an example of how to implement the TYP_TDECLOK rule, which is 
   is needed elswhere in the type system.
 *)

(* Helper function to look for duplicate field names *)
let rec check_dups fs =
  match fs with
  | [] -> false
  | h :: t -> (List.exists (fun x -> x.fieldName = h.fieldName) t) || check_dups t

let typecheck_tdecl (tc : Tctxt.t) id fs  (l : 'a Ast.node) : unit =
  if check_dups fs
  then type_error l ("Repeated fields in " ^ id) 
  else List.iter (fun f -> typecheck_ty l tc f.ftyp) fs

(* function declarations ---------------------------------------------------- *)
(* typecheck a function declaration 
    - extends the local context with the types of the formal parameters to the 
      function
    - typechecks the body of the function (passing in the expected return type
    - checks that the function actually returns
*)
let typecheck_fdecl (tc : Tctxt.t) (f : Ast.fdecl) (l : 'a Ast.node) : unit =
  let { frtyp; fname; args; body } = f in

  let acc_tctxt acc (ty, id) = Tctxt.add_local acc id ty in 
  let extended_tc = List.fold_left acc_tctxt tc args in
  let _, returns = typecheck_blk extended_tc body frtyp in
  if returns then ()
  else type_error l (Printf.sprintf "ERR: Function '%s' does not return" fname) 

(* creating the typchecking context ----------------------------------------- *)

(* The following functions correspond to the
   judgments that create the global typechecking context.

   create_struct_ctxt: - adds all the struct types to the struct 'S'
   context (checking to see that there are no duplicate fields

     H |-s prog ==> H'


   create_function_ctxt: - adds the the function identifiers and their
   types to the 'G' context (ensuring that there are no redeclared
   function identifiers)

     H ; G1 |-f prog ==> G2


   create_global_ctxt: - typechecks the global initializers and adds
   their identifiers to the 'G' global context

     H ; G1 |-g prog ==> G2    


   NOTE: global initializers may mention function identifiers as
   constants, but can mention only other global values that were declared earlier
*)

let create_struct_ctxt (p:Ast.prog) : Tctxt.t =
   let acc_tctxt c decl =
     match decl with
     | Gtdecl(tdecl) -> (
       let id, fields = tdecl.elt in
       let has_duplicate = check_dups fields in
       if has_duplicate then
         type_error tdecl "ERR: struct definition has duplicated fields"
       else
         match Tctxt.lookup_struct_option id c with
         | None -> Tctxt.add_struct c id fields
         | Some _ -> type_error tdecl (
             Printf.sprintf "ERR: struct '%s' has previously been defined" id
           )
     )
     | _ -> c
   in
   List.fold_left acc_tctxt Tctxt.empty p


let create_function_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  (* Add builtin functions to tcontext *)
  let builtins_tctxt = List.fold_left (
    fun acc_tc (id, (param_ty, ret_ty))
      -> Tctxt.add_global acc_tc id (TRef(RFun(param_ty, ret_ty)))
  ) tc builtins
  in

  let acc_tctxt c decl =
    match decl with
    | Gfdecl(fdecl) -> (
      let { frtyp; fname; args } = fdecl.elt in
      match Tctxt.lookup_global_option fname c with
      | None -> 
        let arg_types = List.map (fun (ty, _) -> ty) args in
        Tctxt.add_global c fname (TRef(RFun(arg_types, frtyp)))
      | Some ty -> type_error fdecl (
         Printf.sprintf "ERR: Function '%s' was previously defined as type '%s'"
                        fname (string_of_ty ty)
        )
    ) 
    | _ -> c
  in
  List.fold_left acc_tctxt builtins_tctxt p

let create_global_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  let acc_tctxt c decl =
    begin match decl with
      | Gvdecl(gdecl) ->
        let { name; init } = gdecl.elt in
        begin match Tctxt.lookup_global_option name c with
          | None -> Tctxt.add_global c name (typecheck_gexp tc init)
          | Some ty -> type_error gdecl (
            Printf.sprintf "ERR: Global id '%s' was previously defined as type '%s'"
                          name (string_of_ty ty))
        end
      | _ -> c
    end
  in
  List.fold_left acc_tctxt tc p


(* This function implements the |- prog and the H ; G |- prog 
   rules of the oat.pdf specification.   
*)
let typecheck_program (p:Ast.prog) : unit =
  let sc = create_struct_ctxt p in
  let fc = create_function_ctxt sc p in
  let tc = create_global_ctxt fc p in
  List.iter (fun p ->
    match p with
    | Gfdecl ({elt=f} as l) -> typecheck_fdecl tc f l
    | Gtdecl ({elt=(id, fs)} as l) -> typecheck_tdecl tc id fs l 
    | _ -> ()) p
