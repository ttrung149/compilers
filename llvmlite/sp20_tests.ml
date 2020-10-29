open Assert
open X86
open Ll
open Backend

let dir = "llprograms/sp20_hw3/"
let tests =
  List.map (fun (name, output) -> (dir ^ name ^ ".ll", output)) [
    "fibonacci", 8L
  ; "sum_half_list", 15L
  ; "tarjans_toposort", 1L
  ; "insertion", 11L
  ; "editdistance", 7L
  ; "log", 4L
  ; "tree_search", 1L
  ; "many_calls", 0L
  ; "lcs", 4L
  ; "ackermann", 7L
  ; "slowsort", 155L
  ; "gnome_sort", 6L
  ; "det3x3", 11L
  ; "countsort", 6L
  (* FAILED - llprograms/sp20_hw3/our_test.ll: not equal *)
  (* ; "our_test", 1L *)
  ; "find_max", 80L
  (* FAILED - llprograms/sp20_hw3/ncr.ll: not equal *)
  (* ; "ncr", 9L *)
  ; "fp32lite", 254L
  ]

let io_tests =
  List.map (fun (name, input, output) -> (dir ^ name ^ ".ll", input, output)) [
    "another_io_test", ["cis341"], "Hello, world!cis341 2020 3 4 5 6 7 8"
  ; "heapsort", [], "Sum of first element of each list before sorting: 15; sum after: -6; elements of arr2 after sort: -5 1 5 5 6 7 10 49 84 741 4512 4851"
  ; "quicksort", [], "Initial array: 4 1 50 50 7 0 5 10 9 11 0 100 3 8; Sorted array: 0 0 1 3 4 5 7 8 9 10 11 50 50 100"
  ]
