	.file	"dummy.c"
	.text
	.align 32
.globl __addsf3
	.type	__addsf3, @function
__addsf3:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__addsf3, .-__addsf3
	.align 32
.globl __adddf3
	.type	__adddf3, @function
__adddf3:
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
	.size	__adddf3, .-__adddf3
	.align 32
.globl __addtf3
	.type	__addtf3, @function
__addtf3:
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
	.size	__addtf3, .-__addtf3
	.align 32
.globl __addxf3
	.type	__addxf3, @function
__addxf3:
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
	.size	__addxf3, .-__addxf3
	.align 32
.globl __subsf3
	.type	__subsf3, @function
__subsf3:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__subsf3, .-__subsf3
	.align 32
.globl __subdf3
	.type	__subdf3, @function
__subdf3:
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
	.size	__subdf3, .-__subdf3
	.align 32
.globl __subtf3
	.type	__subtf3, @function
__subtf3:
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
	.size	__subtf3, .-__subtf3
	.align 32
.globl __subxf3
	.type	__subxf3, @function
__subxf3:
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
	.size	__subxf3, .-__subxf3
	.align 32
.globl __mulsf3
	.type	__mulsf3, @function
__mulsf3:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__mulsf3, .-__mulsf3
	.align 32
.globl __muldf3
	.type	__muldf3, @function
__muldf3:
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
	.size	__muldf3, .-__muldf3
	.align 32
.globl __multf3
	.type	__multf3, @function
__multf3:
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
	.size	__multf3, .-__multf3
	.align 32
.globl __mulxf3
	.type	__mulxf3, @function
__mulxf3:
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
	.size	__mulxf3, .-__mulxf3
	.align 32
.globl __divsf3
	.type	__divsf3, @function
__divsf3:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__divsf3, .-__divsf3
	.align 32
.globl __divdf3
	.type	__divdf3, @function
__divdf3:
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
	.size	__divdf3, .-__divdf3
	.align 32
.globl __divtf3
	.type	__divtf3, @function
__divtf3:
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
	.size	__divtf3, .-__divtf3
	.align 32
.globl __divxf3
	.type	__divxf3, @function
__divxf3:
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
	.size	__divxf3, .-__divxf3
	.align 32
.globl __negsf2
	.type	__negsf2, @function
__negsf2:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__negsf2, .-__negsf2
	.align 32
.globl __negdf2
	.type	__negdf2, @function
__negdf2:
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
	.size	__negdf2, .-__negdf2
	.align 32
.globl __negtf2
	.type	__negtf2, @function
__negtf2:
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
	.size	__negtf2, .-__negtf2
	.align 32
.globl __negxf2
	.type	__negxf2, @function
__negxf2:
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
	.size	__negxf2, .-__negxf2
	.align 32
.globl __extendsfdf2
	.type	__extendsfdf2, @function
__extendsfdf2:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__extendsfdf2, .-__extendsfdf2
	.align 32
.globl __extendsftf2
	.type	__extendsftf2, @function
__extendsftf2:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__extendsftf2, .-__extendsftf2
	.align 32
.globl __extendsfxf2
	.type	__extendsfxf2, @function
__extendsfxf2:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__extendsfxf2, .-__extendsfxf2
	.align 32
.globl __extenddftf2
	.type	__extenddftf2, @function
__extenddftf2:
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
	.size	__extenddftf2, .-__extenddftf2
	.align 32
.globl __extenddfxf2
	.type	__extenddfxf2, @function
__extenddfxf2:
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
	.size	__extenddfxf2, .-__extenddfxf2
	.align 32
.globl __truncxfdf2
	.type	__truncxfdf2, @function
__truncxfdf2:
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
	.size	__truncxfdf2, .-__truncxfdf2
	.align 32
.globl __trunctfdf2
	.type	__trunctfdf2, @function
__trunctfdf2:
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
	.size	__trunctfdf2, .-__trunctfdf2
	.align 32
.globl __truncxfsf2
	.type	__truncxfsf2, @function
__truncxfsf2:
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
	.size	__truncxfsf2, .-__truncxfsf2
	.align 32
.globl __trunctfsf2
	.type	__trunctfsf2, @function
__trunctfsf2:
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
	.size	__trunctfsf2, .-__trunctfsf2
	.align 32
.globl __truncdfsf2
	.type	__truncdfsf2, @function
__truncdfsf2:
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
	.size	__truncdfsf2, .-__truncdfsf2
	.align 32
.globl __fixsfsi
	.type	__fixsfsi, @function
__fixsfsi:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__fixsfsi, .-__fixsfsi
	.align 32
.globl __fixdfsi
	.type	__fixdfsi, @function
__fixdfsi:
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
	.size	__fixdfsi, .-__fixdfsi
	.align 32
.globl __fixtfsi
	.type	__fixtfsi, @function
__fixtfsi:
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
	.size	__fixtfsi, .-__fixtfsi
	.align 32
.globl __fixxfsi
	.type	__fixxfsi, @function
__fixxfsi:
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
	.size	__fixxfsi, .-__fixxfsi
	.align 32
.globl __fixsfdi
	.type	__fixsfdi, @function
__fixsfdi:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__fixsfdi, .-__fixsfdi
	.align 32
.globl __fixdfdi
	.type	__fixdfdi, @function
__fixdfdi:
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
	.size	__fixdfdi, .-__fixdfdi
	.align 32
.globl __fixtfdi
	.type	__fixtfdi, @function
__fixtfdi:
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
	.size	__fixtfdi, .-__fixtfdi
	.align 32
.globl __fixxfdi
	.type	__fixxfdi, @function
__fixxfdi:
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
	.size	__fixxfdi, .-__fixxfdi
	.align 32
.globl __fixsfti
	.type	__fixsfti, @function
__fixsfti:
	pushl	%ebp
	movl	%esp, %ebp
	pushl	%ebx
	popl	%ebx
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__fixsfti, .-__fixsfti
	.align 32
.globl __fixdfti
	.type	__fixdfti, @function
__fixdfti:
	pushl	%ebp
	movl	%esp, %ebp
	pushl	%ebx
	subl	$12, %esp
	movl	8(%ebp), %eax
	movl	%eax, -16(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -12(%ebp)
	addl	$12, %esp
	popl	%ebx
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__fixdfti, .-__fixdfti
	.align 32
.globl __fixtfti
	.type	__fixtfti, @function
__fixtfti:
	pushl	%ebp
	movl	%esp, %ebp
	pushl	%ebx
	subl	$12, %esp
	movl	8(%ebp), %eax
	movl	%eax, -16(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -12(%ebp)
	addl	$12, %esp
	popl	%ebx
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__fixtfti, .-__fixtfti
	.align 32
.globl __fixxfti
	.type	__fixxfti, @function
__fixxfti:
	pushl	%ebp
	movl	%esp, %ebp
	pushl	%ebx
	subl	$12, %esp
	movl	8(%ebp), %eax
	movl	%eax, -16(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -12(%ebp)
	addl	$12, %esp
	popl	%ebx
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__fixxfti, .-__fixxfti
	.align 32
.globl __fixunssfsi
	.type	__fixunssfsi, @function
__fixunssfsi:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__fixunssfsi, .-__fixunssfsi
	.align 32
.globl __fixunsdfsi
	.type	__fixunsdfsi, @function
__fixunsdfsi:
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
	.size	__fixunsdfsi, .-__fixunsdfsi
	.align 32
.globl __fixunstfsi
	.type	__fixunstfsi, @function
__fixunstfsi:
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
	.size	__fixunstfsi, .-__fixunstfsi
	.align 32
.globl __fixunsxfsi
	.type	__fixunsxfsi, @function
__fixunsxfsi:
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
	.size	__fixunsxfsi, .-__fixunsxfsi
	.align 32
.globl __fixunssfdi
	.type	__fixunssfdi, @function
__fixunssfdi:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__fixunssfdi, .-__fixunssfdi
	.align 32
.globl __fixunsdfdi
	.type	__fixunsdfdi, @function
__fixunsdfdi:
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
	.size	__fixunsdfdi, .-__fixunsdfdi
	.align 32
.globl __fixunstfdi
	.type	__fixunstfdi, @function
__fixunstfdi:
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
	.size	__fixunstfdi, .-__fixunstfdi
	.align 32
.globl __fixunsxfdi
	.type	__fixunsxfdi, @function
__fixunsxfdi:
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
	.size	__fixunsxfdi, .-__fixunsxfdi
	.align 32
.globl __fixunssfti
	.type	__fixunssfti, @function
__fixunssfti:
	pushl	%ebp
	movl	%esp, %ebp
	pushl	%ebx
	popl	%ebx
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__fixunssfti, .-__fixunssfti
	.align 32
.globl __fixunsdfti
	.type	__fixunsdfti, @function
__fixunsdfti:
	pushl	%ebp
	movl	%esp, %ebp
	pushl	%ebx
	subl	$12, %esp
	movl	8(%ebp), %eax
	movl	%eax, -16(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -12(%ebp)
	addl	$12, %esp
	popl	%ebx
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__fixunsdfti, .-__fixunsdfti
	.align 32
.globl __fixunstfti
	.type	__fixunstfti, @function
__fixunstfti:
	pushl	%ebp
	movl	%esp, %ebp
	pushl	%ebx
	subl	$12, %esp
	movl	8(%ebp), %eax
	movl	%eax, -16(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -12(%ebp)
	addl	$12, %esp
	popl	%ebx
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__fixunstfti, .-__fixunstfti
	.align 32
.globl __fixunsxfti
	.type	__fixunsxfti, @function
__fixunsxfti:
	pushl	%ebp
	movl	%esp, %ebp
	pushl	%ebx
	subl	$12, %esp
	movl	8(%ebp), %eax
	movl	%eax, -16(%ebp)
	movl	12(%ebp), %eax
	movl	%eax, -12(%ebp)
	addl	$12, %esp
	popl	%ebx
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__fixunsxfti, .-__fixunsxfti
	.align 32
.globl __floatsisf
	.type	__floatsisf, @function
__floatsisf:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__floatsisf, .-__floatsisf
	.align 32
.globl __floatsidf
	.type	__floatsidf, @function
__floatsidf:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__floatsidf, .-__floatsidf
	.align 32
.globl __floatsitf
	.type	__floatsitf, @function
__floatsitf:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__floatsitf, .-__floatsitf
	.align 32
.globl __floatsixf
	.type	__floatsixf, @function
__floatsixf:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__floatsixf, .-__floatsixf
	.align 32
.globl __floatdisf
	.type	__floatdisf, @function
__floatdisf:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__floatdisf, .-__floatdisf
	.align 32
.globl __floatdidf
	.type	__floatdidf, @function
__floatdidf:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__floatdidf, .-__floatdidf
	.align 32
.globl __floatditf
	.type	__floatditf, @function
__floatditf:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__floatditf, .-__floatditf
	.align 32
.globl __floatdixf
	.type	__floatdixf, @function
__floatdixf:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__floatdixf, .-__floatdixf
	.align 32
.globl __floattisf
	.type	__floattisf, @function
__floattisf:
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
	.size	__floattisf, .-__floattisf
	.align 32
.globl __floattidf
	.type	__floattidf, @function
__floattidf:
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
	.size	__floattidf, .-__floattidf
	.align 32
.globl __floattitf
	.type	__floattitf, @function
__floattitf:
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
	.size	__floattitf, .-__floattitf
	.align 32
.globl __floattixf
	.type	__floattixf, @function
__floattixf:
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
	.size	__floattixf, .-__floattixf
	.align 32
.globl __floatunsisf
	.type	__floatunsisf, @function
__floatunsisf:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__floatunsisf, .-__floatunsisf
	.align 32
.globl __floatunsidf
	.type	__floatunsidf, @function
__floatunsidf:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__floatunsidf, .-__floatunsidf
	.align 32
.globl __floatunsitf
	.type	__floatunsitf, @function
__floatunsitf:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__floatunsitf, .-__floatunsitf
	.align 32
.globl __floatunsixf
	.type	__floatunsixf, @function
__floatunsixf:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__floatunsixf, .-__floatunsixf
	.align 32
.globl __floatundisf
	.type	__floatundisf, @function
__floatundisf:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__floatundisf, .-__floatundisf
	.align 32
.globl __floatundidf
	.type	__floatundidf, @function
__floatundidf:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__floatundidf, .-__floatundidf
	.align 32
.globl __floatunditf
	.type	__floatunditf, @function
__floatunditf:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__floatunditf, .-__floatunditf
	.align 32
.globl __floatundixf
	.type	__floatundixf, @function
__floatundixf:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__floatundixf, .-__floatundixf
	.align 32
.globl __floatuntisf
	.type	__floatuntisf, @function
__floatuntisf:
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
	.size	__floatuntisf, .-__floatuntisf
	.align 32
.globl __floatuntidf
	.type	__floatuntidf, @function
__floatuntidf:
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
	.size	__floatuntidf, .-__floatuntidf
	.align 32
.globl __floatuntitf
	.type	__floatuntitf, @function
__floatuntitf:
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
	.size	__floatuntitf, .-__floatuntitf
	.align 32
.globl __floatuntixf
	.type	__floatuntixf, @function
__floatuntixf:
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
	.size	__floatuntixf, .-__floatuntixf
	.align 32
.globl __cmpsf2
	.type	__cmpsf2, @function
__cmpsf2:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__cmpsf2, .-__cmpsf2
	.align 32
.globl __cmpdf2
	.type	__cmpdf2, @function
__cmpdf2:
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
	.size	__cmpdf2, .-__cmpdf2
	.align 32
.globl __cmptf2
	.type	__cmptf2, @function
__cmptf2:
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
	.size	__cmptf2, .-__cmptf2
	.align 32
.globl __unordsf2
	.type	__unordsf2, @function
__unordsf2:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__unordsf2, .-__unordsf2
	.align 32
.globl __unorddf2
	.type	__unorddf2, @function
__unorddf2:
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
	.size	__unorddf2, .-__unorddf2
	.align 32
.globl __unordtf2
	.type	__unordtf2, @function
__unordtf2:
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
	.size	__unordtf2, .-__unordtf2
	.align 32
.globl __eqsf2
	.type	__eqsf2, @function
__eqsf2:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__eqsf2, .-__eqsf2
	.align 32
.globl __eqdf2
	.type	__eqdf2, @function
__eqdf2:
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
	.size	__eqdf2, .-__eqdf2
	.align 32
.globl __eqtf2
	.type	__eqtf2, @function
__eqtf2:
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
	.size	__eqtf2, .-__eqtf2
	.align 32
.globl __nesf2
	.type	__nesf2, @function
__nesf2:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__nesf2, .-__nesf2
	.align 32
.globl __nedf2
	.type	__nedf2, @function
__nedf2:
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
	.size	__nedf2, .-__nedf2
	.align 32
.globl __netf2
	.type	__netf2, @function
__netf2:
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
	.size	__netf2, .-__netf2
	.align 32
.globl __gesf2
	.type	__gesf2, @function
__gesf2:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__gesf2, .-__gesf2
	.align 32
.globl __gedf2
	.type	__gedf2, @function
__gedf2:
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
	.size	__gedf2, .-__gedf2
	.align 32
.globl __getf2
	.type	__getf2, @function
__getf2:
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
	.size	__getf2, .-__getf2
	.align 32
.globl __ltsf2
	.type	__ltsf2, @function
__ltsf2:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__ltsf2, .-__ltsf2
	.align 32
.globl __ltdf2
	.type	__ltdf2, @function
__ltdf2:
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
	.size	__ltdf2, .-__ltdf2
	.align 32
.globl __lttf2
	.type	__lttf2, @function
__lttf2:
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
	.size	__lttf2, .-__lttf2
	.align 32
.globl __lesf2
	.type	__lesf2, @function
__lesf2:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__lesf2, .-__lesf2
	.align 32
.globl __ledf2
	.type	__ledf2, @function
__ledf2:
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
	.size	__ledf2, .-__ledf2
	.align 32
.globl __letf2
	.type	__letf2, @function
__letf2:
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
	.size	__letf2, .-__letf2
	.align 32
.globl __gtsf2
	.type	__gtsf2, @function
__gtsf2:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__gtsf2, .-__gtsf2
	.align 32
.globl __gtdf2
	.type	__gtdf2, @function
__gtdf2:
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
	.size	__gtdf2, .-__gtdf2
	.align 32
.globl __gttf2
	.type	__gttf2, @function
__gttf2:
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
	.size	__gttf2, .-__gttf2
	.align 32
.globl __powisf2
	.type	__powisf2, @function
__powisf2:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	popl	%ecx
	nacljmp	%ecx
	.size	__powisf2, .-__powisf2
	.align 32
.globl __powidf2
	.type	__powidf2, @function
__powidf2:
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
	.size	__powidf2, .-__powidf2
	.align 32
.globl __powitf2
	.type	__powitf2, @function
__powitf2:
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
	.size	__powitf2, .-__powitf2
	.align 32
.globl __powixf2
	.type	__powixf2, @function
__powixf2:
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
	.size	__powixf2, .-__powixf2
	.section	.rodata
	.align 4
.LC0:
	.long	2143289344
	.ident	"GCC: (GNU) 4.4.3 2011-05-27 (Native Client r5492, Git Commit 2ad889d442a4c40d2682f32738dca56a5a087605)"
	.section	.note.GNU-stack,"",@progbits
