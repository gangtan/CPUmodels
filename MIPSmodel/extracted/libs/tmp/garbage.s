	.section	__TEXT,__text,regular,pure_instructions
	.globl	_main
	.align	4, 0x90
_main:                                  ## @main
	.cfi_startproc
## BB#0:
	pushq	%rbp
Ltmp2:
	.cfi_def_cfa_offset 16
Ltmp3:
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
Ltmp4:
	.cfi_def_cfa_register %rbp
	subq	$64, %rsp
	leaq	L_.str(%rip), %rax
	movl	$0, -4(%rbp)
	movl	%edi, -8(%rbp)
	movq	%rsi, -16(%rbp)
	movq	8(%rsi), %rdi
	movq	%rax, -40(%rbp)         ## 8-byte Spill
	callq	_atoi
	movl	%eax, -20(%rbp)
	movq	-16(%rbp), %rsi
	movq	16(%rsi), %rdi
	callq	_atoi
	movl	%eax, -24(%rbp)
	movl	-20(%rbp), %ecx
	movl	%eax, -44(%rbp)         ## 4-byte Spill
	movl	%ecx, %eax
	cltd
	movl	-44(%rbp), %ecx         ## 4-byte Reload
	idivl	%ecx
	cvtsi2ssl	%eax, %xmm0
	movss	%xmm0, -32(%rbp)
	movl	-20(%rbp), %esi
	movl	-24(%rbp), %edx
	cvtss2sd	-32(%rbp), %xmm0
	movq	-40(%rbp), %rdi         ## 8-byte Reload
	movb	$1, %al
	movl	%ecx, -48(%rbp)         ## 4-byte Spill
	callq	_printf
	movl	$0, %ecx
	movl	%eax, -52(%rbp)         ## 4-byte Spill
	movl	%ecx, %eax
	addq	$64, %rsp
	popq	%rbp
	ret
	.cfi_endproc

	.section	__TEXT,__cstring,cstring_literals
L_.str:                                 ## @.str
	.asciz	 "%d/%d = %f \n"


.subsections_via_symbols
