.globl main
main:
	pushq 	 %rbp
	movq 	 %rsp, %rbp
	sub 	 $64, %rsp
	call 	 print_line_int
	movq 	 $10, %rax
L0:
	add 	 $64, %rsp
	popq 	 %rbp
	ret 	 
