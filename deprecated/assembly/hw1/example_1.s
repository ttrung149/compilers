.globl _main
_main:
	pushq 	 %rbp
	movq 	 %rsp, %rbp
	sub 	 $64, %rsp
	movq 	 $10, -56(%rbp)
	movq 	 $2, -8(%rbp)
	movq 	 -8(%rbp), %r11
	movq 	 -56(%rbp), %r10
	cmp 	 %r10, %r11
	jg 	 L0
	movq 	 -56(%rbp), %rdi
	call 	 _print_line_int
	movq 	 %rax, -48(%rbp)
L0:
	movq 	 -56(%rbp), %rax
	add 	 $64, %rsp
	popq 	 %rbp
	ret 	 
