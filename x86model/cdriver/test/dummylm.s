	.file	"dummylm.c"
	.text
	.align 32
.globl acos
	.type	acos, @function
acos:
	pushl	%ebp
	movl	%esp, %ebp
	subl	$8, %esp
	movl	8(%ebp), %eax
	movl	%eax, -8(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -4(%ebp)
	movl	%ebp, %esp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	acos, .-acos
	.align 32
.globl asin
	.type	asin, @function
asin:
	pushl	%ebp
	movl	%esp, %ebp
	subl	$8, %esp
	movl	8(%ebp), %eax
	movl	%eax, -8(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -4(%ebp)
	movl	%ebp, %esp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	asin, .-asin
	.align 32
.globl atan
	.type	atan, @function
atan:
	pushl	%ebp
	movl	%esp, %ebp
	subl	$8, %esp
	movl	8(%ebp), %eax
	movl	%eax, -8(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -4(%ebp)
	movl	%ebp, %esp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	atan, .-atan
	.align 32
.globl atan2
	.type	atan2, @function
atan2:
	pushl	%ebp
	movl	%esp, %ebp
	subl	$16, %esp
	movl	8(%ebp), %eax
	movl	%eax, -8(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -4(%ebp)
	movl	16(%ebp), %eax
	movl	%eax, -16(%ebp)
	movl	20(%ebp), %eax
	movl	%eax, -12(%ebp)
	movl	%ebp, %esp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	atan2, .-atan2
	.align 32
.globl ceil
	.type	ceil, @function
ceil:
	pushl	%ebp
	movl	%esp, %ebp
	subl	$8, %esp
	movl	8(%ebp), %eax
	movl	%eax, -8(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -4(%ebp)
	movl	%ebp, %esp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	ceil, .-ceil
	.align 32
.globl cos
	.type	cos, @function
cos:
	pushl	%ebp
	movl	%esp, %ebp
	subl	$8, %esp
	movl	8(%ebp), %eax
	movl	%eax, -8(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -4(%ebp)
	movl	%ebp, %esp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	cos, .-cos
	.align 32
.globl cosh
	.type	cosh, @function
cosh:
	pushl	%ebp
	movl	%esp, %ebp
	subl	$8, %esp
	movl	8(%ebp), %eax
	movl	%eax, -8(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -4(%ebp)
	movl	%ebp, %esp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	cosh, .-cosh
	.align 32
.globl exp
	.type	exp, @function
exp:
	pushl	%ebp
	movl	%esp, %ebp
	subl	$8, %esp
	movl	8(%ebp), %eax
	movl	%eax, -8(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -4(%ebp)
	movl	%ebp, %esp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	exp, .-exp
	.align 32
.globl fabs
	.type	fabs, @function
fabs:
	pushl	%ebp
	movl	%esp, %ebp
	subl	$8, %esp
	movl	8(%ebp), %eax
	movl	%eax, -8(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -4(%ebp)
	movl	%ebp, %esp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	fabs, .-fabs
	.align 32
.globl floor
	.type	floor, @function
floor:
	pushl	%ebp
	movl	%esp, %ebp
	subl	$8, %esp
	movl	8(%ebp), %eax
	movl	%eax, -8(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -4(%ebp)
	movl	%ebp, %esp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	floor, .-floor
	.align 32
.globl fmod
	.type	fmod, @function
fmod:
	pushl	%ebp
	movl	%esp, %ebp
	subl	$16, %esp
	movl	8(%ebp), %eax
	movl	%eax, -8(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -4(%ebp)
	movl	16(%ebp), %eax
	movl	%eax, -16(%ebp)
	movl	20(%ebp), %eax
	movl	%eax, -12(%ebp)
	movl	%ebp, %esp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	fmod, .-fmod
	.align 32
.globl frexp
	.type	frexp, @function
frexp:
	pushl	%ebp
	movl	%esp, %ebp
	subl	$8, %esp
	movl	8(%ebp), %eax
	movl	%eax, -8(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -4(%ebp)
	movl	%ebp, %esp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	frexp, .-frexp
	.align 32
.globl ldexp
	.type	ldexp, @function
ldexp:
	pushl	%ebp
	movl	%esp, %ebp
	subl	$8, %esp
	movl	8(%ebp), %eax
	movl	%eax, -8(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -4(%ebp)
	movl	%ebp, %esp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	ldexp, .-ldexp
	.align 32
.globl log
	.type	log, @function
log:
	pushl	%ebp
	movl	%esp, %ebp
	subl	$8, %esp
	movl	8(%ebp), %eax
	movl	%eax, -8(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -4(%ebp)
	movl	%ebp, %esp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	log, .-log
	.align 32
.globl log10
	.type	log10, @function
log10:
	pushl	%ebp
	movl	%esp, %ebp
	subl	$8, %esp
	movl	8(%ebp), %eax
	movl	%eax, -8(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -4(%ebp)
	movl	%ebp, %esp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	log10, .-log10
	.align 32
.globl modf
	.type	modf, @function
modf:
	pushl	%ebp
	movl	%esp, %ebp
	subl	$8, %esp
	movl	8(%ebp), %eax
	movl	%eax, -8(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -4(%ebp)
	movl	%ebp, %esp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	modf, .-modf
	.align 32
.globl pow
	.type	pow, @function
pow:
	pushl	%ebp
	movl	%esp, %ebp
	subl	$16, %esp
	movl	8(%ebp), %eax
	movl	%eax, -8(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -4(%ebp)
	movl	16(%ebp), %eax
	movl	%eax, -16(%ebp)
	movl	20(%ebp), %eax
	movl	%eax, -12(%ebp)
	movl	%ebp, %esp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	pow, .-pow
	.align 32
.globl sin
	.type	sin, @function
sin:
	pushl	%ebp
	movl	%esp, %ebp
	subl	$8, %esp
	movl	8(%ebp), %eax
	movl	%eax, -8(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -4(%ebp)
	movl	%ebp, %esp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	sin, .-sin
	.align 32
.globl sinh
	.type	sinh, @function
sinh:
	pushl	%ebp
	movl	%esp, %ebp
	subl	$8, %esp
	movl	8(%ebp), %eax
	movl	%eax, -8(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -4(%ebp)
	movl	%ebp, %esp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	sinh, .-sinh
	.align 32
.globl sqrt
	.type	sqrt, @function
sqrt:
	pushl	%ebp
	movl	%esp, %ebp
	subl	$8, %esp
	movl	8(%ebp), %eax
	movl	%eax, -8(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -4(%ebp)
	movl	%ebp, %esp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	sqrt, .-sqrt
	.align 32
.globl tan
	.type	tan, @function
tan:
	pushl	%ebp
	movl	%esp, %ebp
	subl	$8, %esp
	movl	8(%ebp), %eax
	movl	%eax, -8(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -4(%ebp)
	movl	%ebp, %esp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	tan, .-tan
	.align 32
.globl tanh
	.type	tanh, @function
tanh:
	pushl	%ebp
	movl	%esp, %ebp
	subl	$8, %esp
	movl	8(%ebp), %eax
	movl	%eax, -8(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -4(%ebp)
	movl	%ebp, %esp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	tanh, .-tanh
	.section	.rodata
	.align 4
.LC0:
	.long	2143289344
	.ident	"GCC: (GNU) 4.4.3 2011-05-27 (Native Client r5492, Git Commit 2ad889d442a4c40d2682f32738dca56a5a087605)"
	.section	.note.GNU-stack,"",@progbits
