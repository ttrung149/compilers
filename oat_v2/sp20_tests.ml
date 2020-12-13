open Assert
open Ast
open X86
open Driver
open Ll
open Backend

(* from gradedtests *)

let typecheck_error (a : assertion) () =
  try a (); failwith "Should have a type error" with Typechecker.TypeError s -> ()
let typecheck_correct (a : assertion) () =
  try a () with Typechecker.TypeError s -> failwith "Should not have had a type error"

(* Student tests *)

let aleena_tests = [
    "subtype_subarray_subarray",
    (fun () ->
      if Typechecker.subtype Tctxt.empty (TRef (RArray TInt)) (TRef (RArray TInt)) then ()
      else failwith "should not fail")
  ; ("no_subtype_subarray_subarray",
     (fun () ->
       if Typechecker.subtype Tctxt.empty (TNullRef (RArray TInt)) (TRef (RArray TInt)) then
         failwith "should not succeed" else ())
    )
  ]

let andrewme_tests = [
    ("UopSucceeds", typecheck_correct ( fun () -> ignore(Typechecker.typecheck_exp Tctxt.empty (Ast.no_loc (Ast.Uop (Ast.Bitnot, (Ast.no_loc (Ast.CInt 8L)))))) ) ) ;
    ("UopFails", typecheck_error ( fun () -> ignore(Typechecker.typecheck_exp Tctxt.empty (Ast.no_loc (Ast.Uop (Ast.Bitnot, (Ast.no_loc (Ast.CBool true)))))) ) )
  ]

let tc = Tctxt.add_struct (
             Tctxt.add_struct Tctxt.empty "sub"
               [{fieldName="a"; ftyp=TBool}; {fieldName="b"; ftyp=TInt}]
           ) "super" [{fieldName="a"; ftyp=TBool}]

let armaant_tests = [
  ("subtype_refs",
     (fun () ->
       if Typechecker.subtype tc (TRef (RStruct "sub")) (TRef (RStruct "super")) then ()
       else failwith "should not fail")
    )
  ; ("subtype_refs",
     (fun () ->
       if not (Typechecker.subtype tc (TRef (RStruct "super")) (TRef (RStruct "sub"))) then ()
       else failwith "should not fail")
    )
  ]

(* syntax error *)
(* let dhaupt_tests = [
 *     ("typ_length pass", (fun () ->
 *        if Typechecker.typecheck_exp Tctxt.empty @@ Ast.no_loc (Ast.Length (Ast.no_loc (Ast.NewArr (Ast.TInt, Ast.no_loc (Ast.CInt 7L))))) = Ast.TInt then () else failwith "expected TInt";
 *     ));
 *     ("typ_length fail", (fun () ->
 *        try if Typechecker.typecheck_exp Tctxt.empty @@ Ast.no_loc (Ast.Length (Ast.no_loc (Ast.CStr "potato"))) = Ast.TInt then failwith "expected type error"; else failwith "expected type error"; with _ -> ()
 *     ))
 *   ] *)

let dlike_tests = [
    ("valid array subtyping",
     fun () -> if Typechecker.subtype Tctxt.empty (TRef (RArray TInt))
                    (TRef (RArray TInt))
               then ()
               else failwith "should be subtype"
    )
  ;
    ("invalid array subtyping",
     fun () -> if Typechecker.subtype Tctxt.empty (TRef (RArray (TRef RString)))
                    (TRef (RArray (TNullRef RString)))
               then failwith "not a valid subtype"
               else ()
    )
  ]

let ehilman_tests = [
    ("struct_subtype_success", fun () ->
    let struct_ctxt = Tctxt.empty in
    let struct_ctxt1 = Tctxt.add_struct struct_ctxt "empty" [] in
    let struct_ctxt2 = Tctxt.add_struct struct_ctxt1 "singleton" [{fieldName="hi"; ftyp=TInt}] in
    let type1 = Ast.TRef (RFun ([TRef (RStruct "empty")], RetVal(TRef (RStruct "singleton")) )) in
    let type2 = Ast.TRef (RFun ([TRef (RStruct "singleton")], RetVal(TRef (RStruct "empty")) )) in
  if Typechecker.subtype struct_ctxt2 type1 type2 then () else
    failwith "contravariant in input, covariant in output should succeed" )
; ("struct_subtype_failure", fun () ->
    let struct_ctxt = Tctxt.empty in
    let struct_ctxt1 = Tctxt.add_struct struct_ctxt "empty" [] in
    let struct_ctxt2 = Tctxt.add_struct struct_ctxt1 "singleton" [{fieldName="hi"; ftyp=TInt}] in
    let type1 = Ast.TRef (RFun ([TRef (RStruct "empty")], RetVal(TRef (RStruct "singleton")) )) in
    let type2 = Ast.TRef (RFun ([TRef (RStruct "singleton")], RetVal(TRef (RStruct "empty")) )) in
    if Typechecker.subtype struct_ctxt2 type2 type1 then
      failwith "covariant in input, contravariant in output should fail"  else () )
  ]

let ghemlick_tests = [
    ("typecheck_exp_id",
     (fun () ->
       let id : Ast.id = "variable" in
       let c : Tctxt.t = { locals = [(id, TInt)]; globals = [(id, TBool)]; structs = [] } in
       let e : Ast.exp Ast.node = Ast.Id "variable" |> Ast.no_loc in
       if Typechecker.typecheck_exp c e = TInt then ()
       else failwith "should return local type before global type"
     )
    )
  ; ("typecheck_exp_id_illtyped",
     (fun () ->
       let id : Ast.id = "variable" in
       let c : Tctxt.t = { locals = [(id, TInt)]; globals = [(id, TBool)]; structs = [] } in
       let e : Ast.exp Ast.node = Ast.Id "variable" |> Ast.no_loc in
       if Typechecker.typecheck_exp c e = TBool
       then failwith "should return local type before global type" else ()
     )
    )
  ]

(* compile warning *)
(* let hyan99_tests = [
 *     ("subtype_func_struct",
 *      (fun () ->
 *        let c = Tctxt.add_struct Tctxt.empty "id1" [{fieldName="1"; ftyp=TBool}] in
 *        let c' = Tctxt.add_struct c "id2" [{fieldName="1"; ftyp=TBool}; {fieldName="2"; ftyp=TInt}] in
 *        let f1_ty = Ast.TRef (RFun ([TRef(RStruct "id1"); TInt], RetVal (TRef RString))) in
 *        let f2_ty = Ast.TRef (RFun ([TRef(RStruct "id2"); TInt], RetVal (TNullRef RString))) in
 *        if Typechecker.subtype c' f1_ty f2_ty then ()
 *        else failwith "function with struct argument")
 *     )
 *   ; ("typecheck_stmt_decl_error",
 *      (fun () ->
 *        let c = Tctxt.add_struct Tctxt.empty "id1" [{fieldName="1"; ftyp=TNullRef RString}] in
 *        let c' = Tctxt.add_local c "x" (TRef (RStruct "id1")) in
 *        try
 *          Typechecker.typecheck_stmt c' (Ast.no_loc (Ast.Decl ("x", Ast.no_loc (Ast.CStruct ("id1", [])))));
 *          failwith "should not typecheck"
 *        with _ -> ())
 *     )
 *   ] *)

(* gives wrong answer *)
(* let inadas_tests = [
 *     "yes_subtype",
 *     (fun () ->
 *       let x1 = Ast.TRef (RArray (TRef RString)) in
 *       let x2 = Ast.TRef (RArray (TNullRef RString)) in
 *       if Typechecker.subtype Tctxt.empty x1 x2 then ()
 *       else failwith "should not succeed")
 *   ; ("no_subtype",
 *      (fun () ->
 *        let x1 = Ast.TRef (RArray (TRef RString)) in
 *        let x2 = Ast.TRef (RArray (TNullRef RString)) in
 *        if Typechecker.subtype Tctxt.empty x2 x1 then
 *          failwith "should not succeed" else ())
 *     )
 *   ] *)

let jediahk_tests = [
    ("declaration_int",
     (fun () ->
       let _ = (Typechecker.typecheck_stmt Tctxt.empty (Ast.no_loc (Ast.Decl ("x", Ast.no_loc (Ast.CInt 0L)))) RetVoid)
       in ()
     )
    )
  ; ("no_redeclaration_int",
     (fun () -> try
         let _ = (Typechecker.typecheck_stmt (Tctxt.add_local Tctxt.empty "x" Ast.TInt)
                    (Ast.no_loc (Ast.Decl ("x", Ast.no_loc (Ast.CInt 0L)))) RetVoid) in
         failwith "should not succeed"
       with _ -> ()
     )
    )
  ]

let jpowe_tests = [
    "New array with appropriate array type",
    (fun () ->
      let res = begin
          try Typechecker.typecheck_exp Tctxt.empty
                (Ast.no_loc @@ Ast.NewArr (TBool, Ast.no_loc @@ CInt 3L))
          with _ -> failwith "should not throw type error"
        end in
      assert_eq res (TRef (RArray TBool)) ()
    )
  ; "New array with inappropriate array type",
    (fun () ->
      try begin
          ignore @@ Typechecker.typecheck_exp Tctxt.empty
                      (no_loc @@ Ast.NewArr (TRef RString, no_loc @@ CInt 3L));
          failwith "typecheck should not success"
        end with _ -> ()
    )
  ]

let jupierce_tests = [
    ("sub_sub_nref",
	 (fun () ->
	   if Typechecker.subtype Tctxt.empty (TRef RString) (TNullRef RString) then ()
	   else failwith "should not fail"))
  ; ("no_sub_sub_nref",
	 (fun () ->
	   if Typechecker.subtype Tctxt.empty TInt (TNullRef RString) then
		 failwith "should not succeed" else ()))
  ]

let kocc_tests = [
    ( "tc correct array subtype",
	  fun () ->
	  if Typechecker.subtype Tctxt.empty (TRef (RArray (TRef RString))) (TRef (RArray (TRef RString)))
	  then ()
	  else failwith "Type 2 not recognized as subtype." )
  ; ( "tc error array subtype",
	  fun () -> if Typechecker.subtype Tctxt.empty (TRef (RArray TBool)) (TRef (RArray TInt))
	            then failwith "Type 2 incorrectly recognized as subtype."
	            else () )
  ]

let ksugama_tests = [
    ("Equality operator match", fun () ->
                                let res : Ast.ty = (try Typechecker.typecheck_exp Tctxt.empty
                                                          (no_loc (Bop (Eq, no_loc (CInt 5L), no_loc (CInt 3L))))
                                                    with Typechecker.TypeError _ -> failwith "should not fail") in
                                match res with | TBool -> () | _ -> failwith "expected TInt");
    ("Equality operator mismatch", fun () ->
                                   let res = ref 0 in
                                   let _ = (try Typechecker.typecheck_exp Tctxt.empty
                                                  (no_loc (Bop (Eq, no_loc (CInt 5L), no_loc (CBool true))))
                                            with Typechecker.TypeError _ -> res := 1 ; TInt ) in
                                   if !res = 1 then () else failwith "shoud not succeed")
  ]

(* compile error *)
(* let lukasks_tests = [
 *   (\* test TYP_WHILE *\)
 *     "while loop with bool exp", (typecheck_correct
 *                                    (fun () -> Typechecker.typecheck_program
 *                                       [ Gfdecl (no_loc {frtyp=RetVoid; fname="f"; args=[]
 *                                       ; body=[ no_loc @@ While (no_loc @@ CBool false, [])
 *                                       ; no_loc @@ Ret None ]});]));
 *     "while loop with non-bool exp", (typecheck_error
 *                                    (fun () -> Typechecker.typecheck_program
 *                                       [ Gfdecl (no_loc {frtyp=RetVoid; fname="f"; args=[]
 *                                       ; body=[ no_loc @@ While (no_loc @@ CInt 12L, [])
 *                                       ; no_loc @@ Ret None ]});]));
 * ] *)

let mksaga_tests = [
    ("struct_subtype", (fun () ->
       let field_list_a = [ {fieldName = "int_field"; ftyp = TInt}; {fieldName = "bool_field"; ftyp = TBool} ] in
       let field_list_b = [ {fieldName = "int_field"; ftyp = TInt} ] in
       let (c1:Tctxt.t) = Tctxt.add_struct Tctxt.empty "struct_a" field_list_a in
       let (c2:Tctxt.t) = Tctxt.add_struct c1 "struct_b" field_list_b in
       if Typechecker.subtype c2 (TRef (RStruct "struct_a")) (TRef (RStruct "struct_b")) then ()
       else failwith "shouldn't fail"))
  ; ("struct_not_subtype", (fun () ->
       let field_list_a = [ {fieldName = "int_field"; ftyp = TInt}; {fieldName = "bool_field"; ftyp = TBool} ] in
       let field_list_b = [ {fieldName = "int_field"; ftyp = TInt} ] in
       let (c1:Tctxt.t) = Tctxt.add_struct Tctxt.empty "struct_a" field_list_a in
       let (c2:Tctxt.t) = Tctxt.add_struct c1 "struct_b" field_list_b in
       if Typechecker.subtype c2 (TRef (RStruct "struct_b")) (TRef (RStruct "struct_a")) then failwith "shouldn't succeed"
       else ()))
  ]

let nshweky_tests = [
    "subtype_func_inside_func_valid", (fun () ->
      let f1_ty = TRef (RFun (
                            [TNullRef (RFun (
                                           [TRef RString],
                                           RetVal (TNullRef RString)))],
                            RetVal (TRef RString)
                    ))
      in
      let f2_ty = TNullRef (RFun (
                                [TRef (RFun (
                                           [TNullRef RString],
                                           RetVal (TRef RString)))],
                                RetVal (TNullRef RString)
                    ))
      in
      if Typechecker.subtype Tctxt.empty f1_ty f2_ty
      then ()
      else failwith "should be a valid subtype."
    )
  ; "subtype_func_inside_func_invalid",
    (fun () ->
      let f1_ty = TRef (RFun (
                            [TNullRef (RFun (
                                           [TNullRef RString],
                                           RetVal (TNullRef RString)))],
                            RetVal (TRef RString)
                    ))
      in
      let f2_ty = TNullRef (RFun (
                                [TRef (RFun (
                                           [TRef RString],
                                           RetVal (TRef RString)))],
                                RetVal (TNullRef RString)
                    ))
      in
      if Typechecker.subtype Tctxt.empty f1_ty f2_ty
      then failwith "This is not a valid subtype."
      else ()
    )
  ]

let xuyuan_tests = [
    "subtype_func_func",
    (fun () ->
      let f1_ty = Ast.TNullRef (RFun ([TNullRef RString; TBool], RetVal (TRef (RArray TBool)))) in
      let f2_ty = Ast.TNullRef (RFun ([TRef RString; TBool], RetVal (TNullRef (RArray TBool)))) in
      if Typechecker.subtype Tctxt.empty f1_ty f2_ty then ()
      else failwith "functions contravariant in first argument")
  ; ("no_subtype_func_func",
     (fun () ->
       let f1_ty = Ast.TNullRef (RFun ([TRef RString; TBool], RetVal (TRef (RArray TBool)))) in
       let f2_ty = Ast.TNullRef (RFun ([TNullRef RString; TBool], RetVal (TNullRef (RArray TBool)))) in
       if Typechecker.subtype Tctxt.empty f1_ty f2_ty then
         failwith "functions contravariant in first argument" else ())
    )
  ]

let zchuning_tests = [
    "equality_structs_diff_id", (fun () -> let ctxt = Tctxt.add_struct Tctxt.empty "S1" [{fieldName="field1"; ftyp=Ast.TNullRef(RString)};
                                                                                         {fieldName="field2"; ftyp=Ast.TInt}] in
                                           let ctxt2 = Tctxt.add_struct ctxt "S2" [{fieldName="field1"; ftyp=Ast.TNullRef(RString)};
                                                                                   {fieldName="field2"; ftyp=Ast.TInt}] in
                                           let struct_exp = fun id -> CStruct(id, ["field1",no_loc (CNull RString); "field2", no_loc (CInt 0L)]) in
                                           if Typechecker.typecheck_exp ctxt2 (no_loc (Bop(Eq, no_loc (struct_exp "S1"), no_loc (struct_exp "S2")))) = TBool
                                           then ()
                                           else failwith ("equality_structs_diff_id should not fail")
                                );
    "function_not_a_subtype", (fun () -> let ctxt = Tctxt.add_struct Tctxt.empty "S1" [{fieldName="field1"; ftyp=Ast.TNullRef(RString)};
                                                                                       {fieldName="field2"; ftyp=Ast.TBool}] in
                                         let ctxt2 = Tctxt.add_struct ctxt "S2" [{fieldName="field1"; ftyp=Ast.TNullRef(RString)}] in
                                         if Typechecker.subtype ctxt2 (TRef (RFun ([TRef(RStruct "S1")], (RetVal TInt)))) (TRef (RFun ([TRef(RStruct "S2")], (RetVal TInt)))) then
                                           failwith "should not succeed" else ()
                              )
]

let tests = aleena_tests
            @ andrewme_tests
            @ armaant_tests
            @ dlike_tests
            @ ehilman_tests
            @ ghemlick_tests
            @ jediahk_tests
            @ jpowe_tests
            @ jupierce_tests
            @ kocc_tests
            @ ksugama_tests
            @ mksaga_tests
            @ nshweky_tests
            @ xuyuan_tests
            @ zchuning_tests
