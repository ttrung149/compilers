open Assert
open X86
open Simulator
open Asm

(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let student_program_test (p:prog) (ans:int64) () =
  let res = assemble p |> load |> run in
  if res <> ans
  then failwith (Printf.sprintf("Expected %Ld but got %Ld") ans res)
  else ()

let acc n =  [ text "main"
                      [ Movq,  [~$1; ~%Rax]
                      ; Movq,  [~$n; ~%Rdi]
                      ]
               ; text "loop"
                      [ Cmpq,  [~$1; ~%Rdi]
                      ; J Eq,  [~$$"exit"]
                      ; Addq, [~%Rdi; ~%Rax]
                      ; Decq,  [~%Rdi]
                      ; Jmp,   [~$$"loop"]
                      ]
               ; text "exit"
                      [ Retq,  [] 
                      ]
               ]

let sqrt n =  [ text "main"
                      [ Movq,  [~$0; ~%Rax]
                      ; Movq,  [~$n; ~%Rdi]
                      ]
               ; text "loop"
                      [ Movq,  [~%Rax; ~%Rbx]
                      ; Imulq, [~%Rbx; ~%Rbx]
                      ; Cmpq,  [~%Rdi; ~%Rbx]
                      ; J Gt,  [~$$"exit"]
                      ; Addq,  [~$1; ~%Rax]
                      ; Jmp,   [~$$"loop"]
                      ]
               ; text "exit"
                      [ Subq,  [~$1; ~%Rax]
                      ; Retq,  [] 
                      ]
               ]
let provided_tests : suite = [
  Test ("Student-Provided Big Test for Part III: Score recorded as PartIIITestCase", [
    ("acc 10", student_program_test (acc 10) 55L);
    ("sqrt 16", student_program_test (sqrt 16) 4L);
    ("sqrt 18", student_program_test (sqrt 18) 4L);
    ("sqrt 226", student_program_test (sqrt 225) 15L);
  ]);

] 
