	.text
	.globl	main
	.type	main, @function
main:
    pushq   %rbp
    movq    %rsp, %rbp
    subq    $16, %rsp
    
    movq    8(%rsi), %rdi
    call    atoi
    cmp     $100, %rax
    jl      lessthan
    jg      greaterthan

lessthan:
    movq    %rax, %rsi
    movabsq $str2, %rdi
    jmp     print

greaterthan:
    movq    %rax, %rsi
    movabsq $str1, %rdi

print:
    callq   printf
    
    movl    $0, %eax
    addq    $16, %rsp
    popq    %rbp
    retq

str1:
    .asciz  "%d is greater than 100\n"
str2:
    .asciz  "%d is less or equal to 100\n"
