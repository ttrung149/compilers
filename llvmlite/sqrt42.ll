;; Silly square root of 42 program :/

define i64 @sqrt(i64 %x) {
  %res = mul i64 0, 0
  br label %loop
 
loop:
  %res = add i64 %res, 1
  %2 = add i64 %res, 1
  %3 = mul i64 %2, %2
  
  %lt = icmp sle i64 %3, %x
  br i1 %lt, label %loop, label %else

else:
  ret i64 %res
}

define i64 @main(i64 %argc, i8** %arcv) {
  
  ; Expecting sqrt(42) == 6 
  %1 = call i64 @sqrt(i64 42)

  ret i64 %1
}

