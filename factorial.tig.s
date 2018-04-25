L0:
addi $sp, $sp, 4
L16:
move $a3, $fp 
move $a2, $ra 
la $ra, L11
addi $sp, $sp, ~8
move $a0, $fp 
li $a1, 4
move $fp, $sp 
jal  $ra 
move $fp, $a3 
move $ra, $a2 
j L15
L15:
addi $sp, $sp, ~4
jr $ra
L11:
addi $sp, $sp, 0
L18:
sw $a0 , 0($fp) 
move $a3, $fp 
move $a2, $ra 
beqz $a1, L12
b L13 
L13:
la $ra, L11
addi $sp, $sp, ~8
lw $a0, 0($fp) 
addi $a1, $a1, ~1
move $fp, $sp 
jal  $ra 
L14:
move $fp, $a3 
move $ra, $a2 
j L17
L12:
li $v1, 1
j L14
L17:
addi $sp, $sp, 0
jr $ra
