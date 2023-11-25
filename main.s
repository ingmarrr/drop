.text
.global _main
.align 2
_main:
    add X0, X1, #3
    mov X0, #69
    mov X16, #1
    svc #0
