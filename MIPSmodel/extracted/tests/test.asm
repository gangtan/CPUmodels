ori $s1,$0,999
lui $s1,999
add $s2,$s1,$s1
subu $s3,$s2,$s1
bgezal $s1, start
start:
nop
bltz $s3, start
and $t4,$s3,$s2
addi $t4,$t4,1777
andi $t4,$t4,0xFFFF
mult $t4,$s3
mflo $t1
addi $t2,$t1,-100
mfhi $t2
li $t1,1774
ori $t6,$t5,0xF0F0
sllv $t1,$t6,$t2
xor $t1,$t1,$s2
test:
j test
nop
