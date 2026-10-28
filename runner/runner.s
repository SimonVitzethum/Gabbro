; the S0IR runner, x86-64, Intel syntax; written by `lake exe runner` from Runner/Prog/Code.lean
; while the IR runs: r12 = IR pc, r13 = IR fp (frame), r14 = dispatch table; slot i = [r13 + 8*i]
; an IR instruction is 16 bytes: opcode byte, then three 32-bit fields at pc+4, pc+8, pc+12
; ELF loaded at 0x400000, code from 0x400100, dispatch table at 0x4008c0


loader:
  0x400100:  mov rdi, qword ptr [rsp+0x10]
  0x400108:  mov rax, 0x2
  0x40010f:  mov rsi, 0x0
  0x400116:  mov rdx, 0x0
  0x40011d:  syscall
  0x40011f:  test rax, rax
  0x400122:  js 0x4001b7
  0x400128:  mov rbx, rax
  0x40012b:  mov rdi, rbx
  0x40012e:  mov rsi, 0x0
  0x400135:  mov rdx, 0x2
  0x40013c:  mov rax, 0x8
  0x400143:  syscall
  0x400145:  test rax, rax
  0x400148:  js 0x4001b7
  0x40014e:  je 0x4001b7
  0x400154:  mov rsi, rax
  0x400157:  mov rdi, 0x10000000
  0x40015e:  mov rdx, 0x3
  0x400165:  mov r10, 0x100002
  0x40016c:  mov r8, rbx
  0x40016f:  mov r9, 0x0
  0x400176:  mov rax, 0x9
  0x40017d:  syscall
  0x40017f:  mov rcx, 0x10000000
  0x400186:  cmp rax, rcx
  0x400189:  jne 0x4001b7
  0x40018f:  mov r14, 0x4008c0
  0x400196:  mov r13, qword ptr [rcx]
  0x40019e:  lea r12, [rcx+0x10]
  0x4001a6:  movzx rax, byte ptr [r12]
  0x4001af:  jmp qword ptr [r14+rax*8]
  0x4001b7:  ud2

op1:  ; const d k
  0x4001b9:  movsxd rax, dword ptr [r12+0x8]
  0x4001c1:  movsxd rcx, dword ptr [r12+0x4]
  0x4001c9:  mov qword ptr [r13+rcx*8], rax
  0x4001d1:  add r12, 0x10
  0x4001d8:  movzx rax, byte ptr [r12]
  0x4001e1:  jmp qword ptr [r14+rax*8]

op2:  ; mov d a
  0x4001e9:  movsxd rax, dword ptr [r12+0x8]
  0x4001f1:  mov rax, qword ptr [r13+rax*8]
  0x4001f9:  movsxd rcx, dword ptr [r12+0x4]
  0x400201:  mov qword ptr [r13+rcx*8], rax
  0x400209:  add r12, 0x10
  0x400210:  movzx rax, byte ptr [r12]
  0x400219:  jmp qword ptr [r14+rax*8]

op3:  ; add d a b
  0x400221:  movsxd rax, dword ptr [r12+0x8]
  0x400229:  mov rax, qword ptr [r13+rax*8]
  0x400231:  movsxd rdx, dword ptr [r12+0xc]
  0x400239:  mov rdx, qword ptr [r13+rdx*8]
  0x400241:  add rax, rdx
  0x400244:  movsxd rcx, dword ptr [r12+0x4]
  0x40024c:  mov qword ptr [r13+rcx*8], rax
  0x400254:  add r12, 0x10
  0x40025b:  movzx rax, byte ptr [r12]
  0x400264:  jmp qword ptr [r14+rax*8]

op4:  ; sub d a b
  0x40026c:  movsxd rax, dword ptr [r12+0x8]
  0x400274:  mov rax, qword ptr [r13+rax*8]
  0x40027c:  movsxd rdx, dword ptr [r12+0xc]
  0x400284:  mov rdx, qword ptr [r13+rdx*8]
  0x40028c:  sub rax, rdx
  0x40028f:  movsxd rcx, dword ptr [r12+0x4]
  0x400297:  mov qword ptr [r13+rcx*8], rax
  0x40029f:  add r12, 0x10
  0x4002a6:  movzx rax, byte ptr [r12]
  0x4002af:  jmp qword ptr [r14+rax*8]

op5:  ; mul d a b
  0x4002b7:  movsxd rax, dword ptr [r12+0x8]
  0x4002bf:  mov rax, qword ptr [r13+rax*8]
  0x4002c7:  movsxd rdx, dword ptr [r12+0xc]
  0x4002cf:  mov rdx, qword ptr [r13+rdx*8]
  0x4002d7:  imul rax, rdx
  0x4002db:  movsxd rcx, dword ptr [r12+0x4]
  0x4002e3:  mov qword ptr [r13+rcx*8], rax
  0x4002eb:  add r12, 0x10
  0x4002f2:  movzx rax, byte ptr [r12]
  0x4002fb:  jmp qword ptr [r14+rax*8]

op6:  ; div d a b
  0x400303:  movsxd rax, dword ptr [r12+0x8]
  0x40030b:  mov rax, qword ptr [r13+rax*8]
  0x400313:  movsxd rsi, dword ptr [r12+0xc]
  0x40031b:  mov rsi, qword ptr [r13+rsi*8]
  0x400323:  cqo
  0x400325:  idiv rsi
  0x400328:  movsxd rcx, dword ptr [r12+0x4]
  0x400330:  mov qword ptr [r13+rcx*8], rax
  0x400338:  add r12, 0x10
  0x40033f:  movzx rax, byte ptr [r12]
  0x400348:  jmp qword ptr [r14+rax*8]

op7:  ; rem d a b
  0x400350:  movsxd rax, dword ptr [r12+0x8]
  0x400358:  mov rax, qword ptr [r13+rax*8]
  0x400360:  movsxd rsi, dword ptr [r12+0xc]
  0x400368:  mov rsi, qword ptr [r13+rsi*8]
  0x400370:  cqo
  0x400372:  idiv rsi
  0x400375:  movsxd rcx, dword ptr [r12+0x4]
  0x40037d:  mov qword ptr [r13+rcx*8], rdx
  0x400385:  add r12, 0x10
  0x40038c:  movzx rax, byte ptr [r12]
  0x400395:  jmp qword ptr [r14+rax*8]

op8:  ; and d a b
  0x40039d:  movsxd rax, dword ptr [r12+0x8]
  0x4003a5:  mov rax, qword ptr [r13+rax*8]
  0x4003ad:  movsxd rdx, dword ptr [r12+0xc]
  0x4003b5:  mov rdx, qword ptr [r13+rdx*8]
  0x4003bd:  and rax, rdx
  0x4003c0:  movsxd rcx, dword ptr [r12+0x4]
  0x4003c8:  mov qword ptr [r13+rcx*8], rax
  0x4003d0:  add r12, 0x10
  0x4003d7:  movzx rax, byte ptr [r12]
  0x4003e0:  jmp qword ptr [r14+rax*8]

op9:  ; or d a b
  0x4003e8:  movsxd rax, dword ptr [r12+0x8]
  0x4003f0:  mov rax, qword ptr [r13+rax*8]
  0x4003f8:  movsxd rdx, dword ptr [r12+0xc]
  0x400400:  mov rdx, qword ptr [r13+rdx*8]
  0x400408:  or rax, rdx
  0x40040b:  movsxd rcx, dword ptr [r12+0x4]
  0x400413:  mov qword ptr [r13+rcx*8], rax
  0x40041b:  add r12, 0x10
  0x400422:  movzx rax, byte ptr [r12]
  0x40042b:  jmp qword ptr [r14+rax*8]

op10:  ; xor d a b
  0x400433:  movsxd rax, dword ptr [r12+0x8]
  0x40043b:  mov rax, qword ptr [r13+rax*8]
  0x400443:  movsxd rdx, dword ptr [r12+0xc]
  0x40044b:  mov rdx, qword ptr [r13+rdx*8]
  0x400453:  xor rax, rdx
  0x400456:  movsxd rcx, dword ptr [r12+0x4]
  0x40045e:  mov qword ptr [r13+rcx*8], rax
  0x400466:  add r12, 0x10
  0x40046d:  movzx rax, byte ptr [r12]
  0x400476:  jmp qword ptr [r14+rax*8]

op11:  ; shl d a b
  0x40047e:  movsxd rax, dword ptr [r12+0x8]
  0x400486:  mov rax, qword ptr [r13+rax*8]
  0x40048e:  movsxd rcx, dword ptr [r12+0xc]
  0x400496:  mov rcx, qword ptr [r13+rcx*8]
  0x40049e:  shl rax, cl
  0x4004a1:  movsxd rdx, dword ptr [r12+0x4]
  0x4004a9:  mov qword ptr [r13+rdx*8], rax
  0x4004b1:  add r12, 0x10
  0x4004b8:  movzx rax, byte ptr [r12]
  0x4004c1:  jmp qword ptr [r14+rax*8]

op12:  ; shr d a b
  0x4004c9:  movsxd rax, dword ptr [r12+0x8]
  0x4004d1:  mov rax, qword ptr [r13+rax*8]
  0x4004d9:  movsxd rcx, dword ptr [r12+0xc]
  0x4004e1:  mov rcx, qword ptr [r13+rcx*8]
  0x4004e9:  shr rax, cl
  0x4004ec:  movsxd rdx, dword ptr [r12+0x4]
  0x4004f4:  mov qword ptr [r13+rdx*8], rax
  0x4004fc:  add r12, 0x10
  0x400503:  movzx rax, byte ptr [r12]
  0x40050c:  jmp qword ptr [r14+rax*8]

op13:  ; lt d a b
  0x400514:  movsxd rax, dword ptr [r12+0x8]
  0x40051c:  mov rax, qword ptr [r13+rax*8]
  0x400524:  movsxd rdx, dword ptr [r12+0xc]
  0x40052c:  mov rdx, qword ptr [r13+rdx*8]
  0x400534:  cmp rax, rdx
  0x400537:  setl al
  0x40053b:  movzx rax, al
  0x40053f:  movsxd rcx, dword ptr [r12+0x4]
  0x400547:  mov qword ptr [r13+rcx*8], rax
  0x40054f:  add r12, 0x10
  0x400556:  movzx rax, byte ptr [r12]
  0x40055f:  jmp qword ptr [r14+rax*8]

op14:  ; eq d a b
  0x400567:  movsxd rax, dword ptr [r12+0x8]
  0x40056f:  mov rax, qword ptr [r13+rax*8]
  0x400577:  movsxd rdx, dword ptr [r12+0xc]
  0x40057f:  mov rdx, qword ptr [r13+rdx*8]
  0x400587:  cmp rax, rdx
  0x40058a:  sete al
  0x40058e:  movzx rax, al
  0x400592:  movsxd rcx, dword ptr [r12+0x4]
  0x40059a:  mov qword ptr [r13+rcx*8], rax
  0x4005a2:  add r12, 0x10
  0x4005a9:  movzx rax, byte ptr [r12]
  0x4005b2:  jmp qword ptr [r14+rax*8]

op15:  ; ld d a (d := M[a])
  0x4005ba:  movsxd rax, dword ptr [r12+0x8]
  0x4005c2:  mov rax, qword ptr [r13+rax*8]
  0x4005ca:  mov rax, qword ptr [rax]
  0x4005d2:  movsxd rcx, dword ptr [r12+0x4]
  0x4005da:  mov qword ptr [r13+rcx*8], rax
  0x4005e2:  add r12, 0x10
  0x4005e9:  movzx rax, byte ptr [r12]
  0x4005f2:  jmp qword ptr [r14+rax*8]

op16:  ; st a b (M[a] := b)
  0x4005fa:  movsxd rax, dword ptr [r12+0x4]
  0x400602:  mov rax, qword ptr [r13+rax*8]
  0x40060a:  movsxd rdx, dword ptr [r12+0x8]
  0x400612:  mov rdx, qword ptr [r13+rdx*8]
  0x40061a:  mov qword ptr [rax], rdx
  0x400622:  add r12, 0x10
  0x400629:  movzx rax, byte ptr [r12]
  0x400632:  jmp qword ptr [r14+rax*8]

op17:  ; lea d a
  0x40063a:  movsxd rax, dword ptr [r12+0x8]
  0x400642:  lea rax, [r13+rax*8]
  0x40064a:  movsxd rcx, dword ptr [r12+0x4]
  0x400652:  mov qword ptr [r13+rcx*8], rax
  0x40065a:  add r12, 0x10
  0x400661:  movzx rax, byte ptr [r12]
  0x40066a:  jmp qword ptr [r14+rax*8]

op18:  ; jmp L
  0x400672:  movsxd rax, dword ptr [r12+0x4]
  0x40067a:  add r12, rax
  0x40067d:  movzx rax, byte ptr [r12]
  0x400686:  jmp qword ptr [r14+rax*8]

op19:  ; brz a L
  0x40068e:  movsxd rax, dword ptr [r12+0x4]
  0x400696:  mov rax, qword ptr [r13+rax*8]
  0x40069e:  test rax, rax
  0x4006a1:  jne 0x4006c3
  0x4006a7:  movsxd rax, dword ptr [r12+0x8]
  0x4006af:  add r12, rax
  0x4006b2:  movzx rax, byte ptr [r12]
  0x4006bb:  jmp qword ptr [r14+rax*8]
  0x4006c3:  add r12, 0x10
  0x4006ca:  movzx rax, byte ptr [r12]
  0x4006d3:  jmp qword ptr [r14+rax*8]

op20:  ; call a k
  0x4006db:  movsxd rax, dword ptr [r12+0x4]
  0x4006e3:  mov rax, qword ptr [r13+rax*8]
  0x4006eb:  movsxd rdx, dword ptr [r12+0x8]
  0x4006f3:  lea rdx, [r13+rdx*8]
  0x4006fb:  lea rcx, [r12+0x10]
  0x400703:  mov qword ptr [rdx], rcx
  0x40070b:  mov qword ptr [rdx+0x8], r13
  0x400713:  mov r13, rdx
  0x400716:  mov r12, rax
  0x400719:  movzx rax, byte ptr [r12]
  0x400722:  jmp qword ptr [r14+rax*8]

op21:  ; ret
  0x40072a:  mov rax, qword ptr [r13]
  0x400732:  mov r13, qword ptr [r13+0x8]
  0x40073a:  mov r12, rax
  0x40073d:  movzx rax, byte ptr [r12]
  0x400746:  jmp qword ptr [r14+rax*8]

op22:  ; cas d a e
  0x40074e:  movsxd rax, dword ptr [r12+0x8]
  0x400756:  mov rdx, qword ptr [r13+rax*8]
  0x40075e:  movsxd rcx, dword ptr [r12+0xc]
  0x400766:  mov rax, qword ptr [r13+rcx*8]
  0x40076e:  mov rsi, qword ptr [r13+rcx*8+0x8]
  0x400776:  lock cmpxchg qword ptr [rdx], rsi
  0x400780:  movsxd rcx, dword ptr [r12+0x4]
  0x400788:  mov qword ptr [r13+rcx*8], rax
  0x400790:  add r12, 0x10
  0x400797:  movzx rax, byte ptr [r12]
  0x4007a0:  jmp qword ptr [r14+rax*8]

op23:  ; sys d a
  0x4007a8:  movsxd rbx, dword ptr [r12+0x4]
  0x4007b0:  lea rbx, [r13+rbx*8]
  0x4007b8:  movsxd rcx, dword ptr [r12+0x8]
  0x4007c0:  lea rcx, [r13+rcx*8]
  0x4007c8:  mov rax, qword ptr [rcx]
  0x4007d0:  mov rdi, qword ptr [rcx+0x8]
  0x4007d8:  mov rsi, qword ptr [rcx+0x10]
  0x4007e0:  mov rdx, qword ptr [rcx+0x18]
  0x4007e8:  mov r10, qword ptr [rcx+0x20]
  0x4007f0:  mov r8, qword ptr [rcx+0x28]
  0x4007f8:  mov r9, qword ptr [rcx+0x30]
  0x400800:  syscall
  0x400802:  mov qword ptr [rbx], rax
  0x40080a:  add r12, 0x10
  0x400811:  movzx rax, byte ptr [r12]
  0x40081a:  jmp qword ptr [r14+rax*8]

op24:  ; spawn d a (clone, a new OS thread)
  0x400822:  movsxd rcx, dword ptr [r12+0x8]
  0x40082a:  lea rcx, [r13+rcx*8]
  0x400832:  mov rbx, qword ptr [rcx]
  0x40083a:  mov rbp, qword ptr [rcx+0x8]
  0x400842:  mov rax, 0x38
  0x400849:  mov rdi, 0x50f00
  0x400850:  mov rsi, 0x0
  0x400857:  mov rdx, 0x0
  0x40085e:  mov r10, 0x0
  0x400865:  mov r8, 0x0
  0x40086c:  mov r9, 0x0
  0x400873:  syscall
  0x400875:  test rax, rax
  0x400878:  je 0x4008a6
  0x40087e:  movsxd rcx, dword ptr [r12+0x4]
  0x400886:  mov qword ptr [r13+rcx*8], rax
  0x40088e:  add r12, 0x10
  0x400895:  movzx rax, byte ptr [r12]
  0x40089e:  jmp qword ptr [r14+rax*8]
  0x4008a6:  mov r12, rbx
  0x4008a9:  mov r13, rbp
  0x4008ac:  movzx rax, byte ptr [r12]
  0x4008b5:  jmp qword ptr [r14+rax*8]

bad:
  0x4008bd:  ud2

table:  ; 256 handler addresses at 0x4008c0
  dq 0x4008bd  ; opcode 0
  dq 0x4001b9  ; opcode 1
  dq 0x4001e9  ; opcode 2
  dq 0x400221  ; opcode 3
  dq 0x40026c  ; opcode 4
  dq 0x4002b7  ; opcode 5
  dq 0x400303  ; opcode 6
  dq 0x400350  ; opcode 7
  dq 0x40039d  ; opcode 8
  dq 0x4003e8  ; opcode 9
  dq 0x400433  ; opcode 10
  dq 0x40047e  ; opcode 11
  dq 0x4004c9  ; opcode 12
  dq 0x400514  ; opcode 13
  dq 0x400567  ; opcode 14
  dq 0x4005ba  ; opcode 15
  dq 0x4005fa  ; opcode 16
  dq 0x40063a  ; opcode 17
  dq 0x400672  ; opcode 18
  dq 0x40068e  ; opcode 19
  dq 0x4006db  ; opcode 20
  dq 0x40072a  ; opcode 21
  dq 0x40074e  ; opcode 22
  dq 0x4007a8  ; opcode 23
  dq 0x400822  ; opcode 24
  dq 0x4008bd  ; opcode 25
  dq 0x4008bd  ; opcode 26
  dq 0x4008bd  ; opcode 27
  dq 0x4008bd  ; opcode 28
  dq 0x4008bd  ; opcode 29
  dq 0x4008bd  ; opcode 30
  dq 0x4008bd  ; opcode 31
  dq 0x4008bd  ; opcode 32
  dq 0x4008bd  ; opcode 33
  dq 0x4008bd  ; opcode 34
  dq 0x4008bd  ; opcode 35
  dq 0x4008bd  ; opcode 36
  dq 0x4008bd  ; opcode 37
  dq 0x4008bd  ; opcode 38
  dq 0x4008bd  ; opcode 39
  dq 0x4008bd  ; opcode 40
  dq 0x4008bd  ; opcode 41
  dq 0x4008bd  ; opcode 42
  dq 0x4008bd  ; opcode 43
  dq 0x4008bd  ; opcode 44
  dq 0x4008bd  ; opcode 45
  dq 0x4008bd  ; opcode 46
  dq 0x4008bd  ; opcode 47
  dq 0x4008bd  ; opcode 48
  dq 0x4008bd  ; opcode 49
  dq 0x4008bd  ; opcode 50
  dq 0x4008bd  ; opcode 51
  dq 0x4008bd  ; opcode 52
  dq 0x4008bd  ; opcode 53
  dq 0x4008bd  ; opcode 54
  dq 0x4008bd  ; opcode 55
  dq 0x4008bd  ; opcode 56
  dq 0x4008bd  ; opcode 57
  dq 0x4008bd  ; opcode 58
  dq 0x4008bd  ; opcode 59
  dq 0x4008bd  ; opcode 60
  dq 0x4008bd  ; opcode 61
  dq 0x4008bd  ; opcode 62
  dq 0x4008bd  ; opcode 63
  dq 0x4008bd  ; opcode 64
  dq 0x4008bd  ; opcode 65
  dq 0x4008bd  ; opcode 66
  dq 0x4008bd  ; opcode 67
  dq 0x4008bd  ; opcode 68
  dq 0x4008bd  ; opcode 69
  dq 0x4008bd  ; opcode 70
  dq 0x4008bd  ; opcode 71
  dq 0x4008bd  ; opcode 72
  dq 0x4008bd  ; opcode 73
  dq 0x4008bd  ; opcode 74
  dq 0x4008bd  ; opcode 75
  dq 0x4008bd  ; opcode 76
  dq 0x4008bd  ; opcode 77
  dq 0x4008bd  ; opcode 78
  dq 0x4008bd  ; opcode 79
  dq 0x4008bd  ; opcode 80
  dq 0x4008bd  ; opcode 81
  dq 0x4008bd  ; opcode 82
  dq 0x4008bd  ; opcode 83
  dq 0x4008bd  ; opcode 84
  dq 0x4008bd  ; opcode 85
  dq 0x4008bd  ; opcode 86
  dq 0x4008bd  ; opcode 87
  dq 0x4008bd  ; opcode 88
  dq 0x4008bd  ; opcode 89
  dq 0x4008bd  ; opcode 90
  dq 0x4008bd  ; opcode 91
  dq 0x4008bd  ; opcode 92
  dq 0x4008bd  ; opcode 93
  dq 0x4008bd  ; opcode 94
  dq 0x4008bd  ; opcode 95
  dq 0x4008bd  ; opcode 96
  dq 0x4008bd  ; opcode 97
  dq 0x4008bd  ; opcode 98
  dq 0x4008bd  ; opcode 99
  dq 0x4008bd  ; opcode 100
  dq 0x4008bd  ; opcode 101
  dq 0x4008bd  ; opcode 102
  dq 0x4008bd  ; opcode 103
  dq 0x4008bd  ; opcode 104
  dq 0x4008bd  ; opcode 105
  dq 0x4008bd  ; opcode 106
  dq 0x4008bd  ; opcode 107
  dq 0x4008bd  ; opcode 108
  dq 0x4008bd  ; opcode 109
  dq 0x4008bd  ; opcode 110
  dq 0x4008bd  ; opcode 111
  dq 0x4008bd  ; opcode 112
  dq 0x4008bd  ; opcode 113
  dq 0x4008bd  ; opcode 114
  dq 0x4008bd  ; opcode 115
  dq 0x4008bd  ; opcode 116
  dq 0x4008bd  ; opcode 117
  dq 0x4008bd  ; opcode 118
  dq 0x4008bd  ; opcode 119
  dq 0x4008bd  ; opcode 120
  dq 0x4008bd  ; opcode 121
  dq 0x4008bd  ; opcode 122
  dq 0x4008bd  ; opcode 123
  dq 0x4008bd  ; opcode 124
  dq 0x4008bd  ; opcode 125
  dq 0x4008bd  ; opcode 126
  dq 0x4008bd  ; opcode 127
  dq 0x4008bd  ; opcode 128
  dq 0x4008bd  ; opcode 129
  dq 0x4008bd  ; opcode 130
  dq 0x4008bd  ; opcode 131
  dq 0x4008bd  ; opcode 132
  dq 0x4008bd  ; opcode 133
  dq 0x4008bd  ; opcode 134
  dq 0x4008bd  ; opcode 135
  dq 0x4008bd  ; opcode 136
  dq 0x4008bd  ; opcode 137
  dq 0x4008bd  ; opcode 138
  dq 0x4008bd  ; opcode 139
  dq 0x4008bd  ; opcode 140
  dq 0x4008bd  ; opcode 141
  dq 0x4008bd  ; opcode 142
  dq 0x4008bd  ; opcode 143
  dq 0x4008bd  ; opcode 144
  dq 0x4008bd  ; opcode 145
  dq 0x4008bd  ; opcode 146
  dq 0x4008bd  ; opcode 147
  dq 0x4008bd  ; opcode 148
  dq 0x4008bd  ; opcode 149
  dq 0x4008bd  ; opcode 150
  dq 0x4008bd  ; opcode 151
  dq 0x4008bd  ; opcode 152
  dq 0x4008bd  ; opcode 153
  dq 0x4008bd  ; opcode 154
  dq 0x4008bd  ; opcode 155
  dq 0x4008bd  ; opcode 156
  dq 0x4008bd  ; opcode 157
  dq 0x4008bd  ; opcode 158
  dq 0x4008bd  ; opcode 159
  dq 0x4008bd  ; opcode 160
  dq 0x4008bd  ; opcode 161
  dq 0x4008bd  ; opcode 162
  dq 0x4008bd  ; opcode 163
  dq 0x4008bd  ; opcode 164
  dq 0x4008bd  ; opcode 165
  dq 0x4008bd  ; opcode 166
  dq 0x4008bd  ; opcode 167
  dq 0x4008bd  ; opcode 168
  dq 0x4008bd  ; opcode 169
  dq 0x4008bd  ; opcode 170
  dq 0x4008bd  ; opcode 171
  dq 0x4008bd  ; opcode 172
  dq 0x4008bd  ; opcode 173
  dq 0x4008bd  ; opcode 174
  dq 0x4008bd  ; opcode 175
  dq 0x4008bd  ; opcode 176
  dq 0x4008bd  ; opcode 177
  dq 0x4008bd  ; opcode 178
  dq 0x4008bd  ; opcode 179
  dq 0x4008bd  ; opcode 180
  dq 0x4008bd  ; opcode 181
  dq 0x4008bd  ; opcode 182
  dq 0x4008bd  ; opcode 183
  dq 0x4008bd  ; opcode 184
  dq 0x4008bd  ; opcode 185
  dq 0x4008bd  ; opcode 186
  dq 0x4008bd  ; opcode 187
  dq 0x4008bd  ; opcode 188
  dq 0x4008bd  ; opcode 189
  dq 0x4008bd  ; opcode 190
  dq 0x4008bd  ; opcode 191
  dq 0x4008bd  ; opcode 192
  dq 0x4008bd  ; opcode 193
  dq 0x4008bd  ; opcode 194
  dq 0x4008bd  ; opcode 195
  dq 0x4008bd  ; opcode 196
  dq 0x4008bd  ; opcode 197
  dq 0x4008bd  ; opcode 198
  dq 0x4008bd  ; opcode 199
  dq 0x4008bd  ; opcode 200
  dq 0x4008bd  ; opcode 201
  dq 0x4008bd  ; opcode 202
  dq 0x4008bd  ; opcode 203
  dq 0x4008bd  ; opcode 204
  dq 0x4008bd  ; opcode 205
  dq 0x4008bd  ; opcode 206
  dq 0x4008bd  ; opcode 207
  dq 0x4008bd  ; opcode 208
  dq 0x4008bd  ; opcode 209
  dq 0x4008bd  ; opcode 210
  dq 0x4008bd  ; opcode 211
  dq 0x4008bd  ; opcode 212
  dq 0x4008bd  ; opcode 213
  dq 0x4008bd  ; opcode 214
  dq 0x4008bd  ; opcode 215
  dq 0x4008bd  ; opcode 216
  dq 0x4008bd  ; opcode 217
  dq 0x4008bd  ; opcode 218
  dq 0x4008bd  ; opcode 219
  dq 0x4008bd  ; opcode 220
  dq 0x4008bd  ; opcode 221
  dq 0x4008bd  ; opcode 222
  dq 0x4008bd  ; opcode 223
  dq 0x4008bd  ; opcode 224
  dq 0x4008bd  ; opcode 225
  dq 0x4008bd  ; opcode 226
  dq 0x4008bd  ; opcode 227
  dq 0x4008bd  ; opcode 228
  dq 0x4008bd  ; opcode 229
  dq 0x4008bd  ; opcode 230
  dq 0x4008bd  ; opcode 231
  dq 0x4008bd  ; opcode 232
  dq 0x4008bd  ; opcode 233
  dq 0x4008bd  ; opcode 234
  dq 0x4008bd  ; opcode 235
  dq 0x4008bd  ; opcode 236
  dq 0x4008bd  ; opcode 237
  dq 0x4008bd  ; opcode 238
  dq 0x4008bd  ; opcode 239
  dq 0x4008bd  ; opcode 240
  dq 0x4008bd  ; opcode 241
  dq 0x4008bd  ; opcode 242
  dq 0x4008bd  ; opcode 243
  dq 0x4008bd  ; opcode 244
  dq 0x4008bd  ; opcode 245
  dq 0x4008bd  ; opcode 246
  dq 0x4008bd  ; opcode 247
  dq 0x4008bd  ; opcode 248
  dq 0x4008bd  ; opcode 249
  dq 0x4008bd  ; opcode 250
  dq 0x4008bd  ; opcode 251
  dq 0x4008bd  ; opcode 252
  dq 0x4008bd  ; opcode 253
  dq 0x4008bd  ; opcode 254
  dq 0x4008bd  ; opcode 255
