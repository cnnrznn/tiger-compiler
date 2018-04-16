L16:
move a0, FP 
li a1, 10
move FP, SP 
addi SP, SP,L11_fs 
jal L11
move RV, RV 
j L15
L15:
L18:
beqz t137, L12
b L13L13:
move t140, t137 
lw t141, 0(FP)move a0, t141 
addi t142, t137, ~1
move a1, t142 
move FP, SP 
addi SP, SP,L11_fs 
jal L11
move t139, RV 
mulo t143, t140, t139
move t138, t143 
L14:
move RV, t138 
j L17
L12:
li t138, 1
j L14
L17:
