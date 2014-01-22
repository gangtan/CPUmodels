	.section	__TEXT,__text,regular,pure_instructions
	.globl	_main
	.align	4, 0x90
_main:                                  ## @main
	.cfi_startproc
## BB#0:
	pushq	%rbp
Ltmp3:
	.cfi_def_cfa_offset 16
Ltmp4:
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
Ltmp5:
	.cfi_def_cfa_register %rbp
	pushq	%r15
	pushq	%r14
	pushq	%rbx
	pushq	%rax
Ltmp6:
	.cfi_offset %rbx, -40
Ltmp7:
	.cfi_offset %r14, -32
Ltmp8:
	.cfi_offset %r15, -24
	movl	$-2147483648, %r15d     ## imm = 0xFFFFFFFF80000000
	movl	$1, %ebx
	leaq	L_.str(%rip), %r14
	.align	4, 0x90
LBB0_1:                                 ## =>This Inner Loop Header: Depth=1
	testb	$5, %r15b
	setne	%al
	movzbl	%al, %esi
	movq	%r14, %rdi
	xorb	%al, %al
	callq	_printf
	testb	$3, %bl
	jne	LBB0_3
## BB#2:                                ##   in Loop: Header=BB0_1 Depth=1
	movl	$32, %edi
	callq	_putchar
LBB0_3:                                 ##   in Loop: Header=BB0_1 Depth=1
	shrl	%r15d
	incl	%ebx
	cmpl	$33, %ebx
	jne	LBB0_1
## BB#4:
	movl	$10, %edi
	callq	_putchar
	xorl	%eax, %eax
	addq	$8, %rsp
	popq	%rbx
	popq	%r14
	popq	%r15
	popq	%rbp
	ret
	.cfi_endproc

	.section	__TEXT,__cstring,cstring_literals
L_.str:                                 ## @.str
	.asciz	 "%x"


.subsections_via_symbols
