	.file	"main.c"
	.text
	.globl	test
	.type	test, @function
test:
.LFB0:
	.cfi_startproc
	pushl	%ebp
	.cfi_def_cfa_offset 8
	.cfi_offset 5, -8
	movl	%esp, %ebp
	.cfi_def_cfa_register 5
	subl	$40, %esp
	flds	8(%ebp)
	fdivs	12(%ebp)
	fstps	-20(%ebp)
	flds	-20(%ebp)
	flds	-20(%ebp)
	fldl	.LC0
	fmulp	%st, %st(1)
	faddp	%st, %st(1)
	flds	8(%ebp)
	fmuls	12(%ebp)
	fsubrp	%st, %st(1)
	fstps	-16(%ebp)
	flds	-20(%ebp)
	fmuls	-16(%ebp)
	fmuls	-16(%ebp)
	fstps	-12(%ebp)
	flds	-16(%ebp)
	fsubs	-20(%ebp)
	flds	-16(%ebp)
	fldl	.LC1
	fmulp	%st, %st(1)
	flds	-16(%ebp)
	fmulp	%st, %st(1)
	flds	-16(%ebp)
	fmulp	%st, %st(1)
	flds	-16(%ebp)
	fmulp	%st, %st(1)
	flds	-16(%ebp)
	fmulp	%st, %st(1)
	faddp	%st, %st(1)
	flds	-20(%ebp)
	fmuls	-12(%ebp)
	faddp	%st, %st(1)
	flds	-16(%ebp)
	fadds	-12(%ebp)
	flds	-20(%ebp)
	fmuls	8(%ebp)
	fdivs	12(%ebp)
	fmuls	12(%ebp)
	fsubrp	%st, %st(1)
	fsubrp	%st, %st(1)
	fstps	-8(%ebp)
	flds	-8(%ebp)
	fnstcw	-38(%ebp)
	movzwl	-38(%ebp), %eax
	movb	$12, %ah
	movw	%ax, -40(%ebp)
	fldcw	-40(%ebp)
	fistpl	-4(%ebp)
	fldcw	-38(%ebp)
	flds	-20(%ebp)
	fmuls	-16(%ebp)
	fmuls	-12(%ebp)
	leave
	.cfi_restore 5
	.cfi_def_cfa 4, 4
	ret
	.cfi_endproc
.LFE0:
	.size	test, .-test
	.section	.rodata
.LC5:
	.string	"product: %f"
.LC6:
	.string	"test: %f"
	.text
	.globl	main
	.type	main, @function
main:
.LFB1:
	.cfi_startproc
	pushl	%ebp
	.cfi_def_cfa_offset 8
	.cfi_offset 5, -8
	movl	%esp, %ebp
	.cfi_def_cfa_register 5
	andl	$-16, %esp
	subl	$32, %esp
	movl	$0, 20(%esp)
	movl	$0x3f99999a, %eax
	movl	%eax, 24(%esp)
	movl	$0x4059999a, %eax
	movl	%eax, 28(%esp)
	flds	24(%esp)
	fmuls	28(%esp)
	fstpl	4(%esp)
	movl	$.LC5, (%esp)
	call	printf
	movl	28(%esp), %eax
	movl	%eax, 4(%esp)
	movl	24(%esp), %eax
	movl	%eax, (%esp)
	call	test
	fstpl	4(%esp)
	movl	$.LC6, (%esp)
	call	printf
	leave
	.cfi_restore 5
	.cfi_def_cfa 4, 4
	ret
	.cfi_endproc
.LFE1:
	.size	main, .-main
	.section	.rodata
	.align 8
.LC0:
	.long	1685001570
	.long	1073969438
	.align 8
.LC1:
	.long	-46273606
	.long	1088335633
	.ident	"GCC: (Ubuntu/Linaro 4.6.3-1ubuntu5) 4.6.3"
	.section	.note.GNU-stack,"",@progbits
