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
  0x400122:  js 0x4008bb
  0x400128:  mov rbx, rax
  0x40012b:  mov rdi, rbx
  0x40012e:  mov rsi, 0x0
  0x400135:  mov rdx, 0x2
  0x40013c:  mov rax, 0x8
  0x400143:  syscall
  0x400145:  test rax, rax
  0x400148:  js 0x4008bb
  0x40014e:  je 0x4008bb
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
  0x400189:  jne 0x4008bb
  0x40018f:  mov r14, 0x4008c0
  0x400196:  mov r13, qword ptr [rcx]
  0x40019e:  lea r12, [rcx+0x10]
  0x4001a6:  movzx rax, byte ptr [r12]
  0x4001af:  jmp qword ptr [r14+rax*8]

op1:  ; const d k
  0x4001b7:  movsxd rax, dword ptr [r12+0x8]
  0x4001bf:  movsxd rcx, dword ptr [r12+0x4]
  0x4001c7:  mov qword ptr [r13+rcx*8], rax
  0x4001cf:  add r12, 0x10
  0x4001d6:  movzx rax, byte ptr [r12]
  0x4001df:  jmp qword ptr [r14+rax*8]

op2:  ; mov d a
  0x4001e7:  movsxd rax, dword ptr [r12+0x8]
  0x4001ef:  mov rax, qword ptr [r13+rax*8]
  0x4001f7:  movsxd rcx, dword ptr [r12+0x4]
  0x4001ff:  mov qword ptr [r13+rcx*8], rax
  0x400207:  add r12, 0x10
  0x40020e:  movzx rax, byte ptr [r12]
  0x400217:  jmp qword ptr [r14+rax*8]

op3:  ; add d a b
  0x40021f:  movsxd rax, dword ptr [r12+0x8]
  0x400227:  mov rax, qword ptr [r13+rax*8]
  0x40022f:  movsxd rdx, dword ptr [r12+0xc]
  0x400237:  mov rdx, qword ptr [r13+rdx*8]
  0x40023f:  add rax, rdx
  0x400242:  movsxd rcx, dword ptr [r12+0x4]
  0x40024a:  mov qword ptr [r13+rcx*8], rax
  0x400252:  add r12, 0x10
  0x400259:  movzx rax, byte ptr [r12]
  0x400262:  jmp qword ptr [r14+rax*8]

op4:  ; sub d a b
  0x40026a:  movsxd rax, dword ptr [r12+0x8]
  0x400272:  mov rax, qword ptr [r13+rax*8]
  0x40027a:  movsxd rdx, dword ptr [r12+0xc]
  0x400282:  mov rdx, qword ptr [r13+rdx*8]
  0x40028a:  sub rax, rdx
  0x40028d:  movsxd rcx, dword ptr [r12+0x4]
  0x400295:  mov qword ptr [r13+rcx*8], rax
  0x40029d:  add r12, 0x10
  0x4002a4:  movzx rax, byte ptr [r12]
  0x4002ad:  jmp qword ptr [r14+rax*8]

op5:  ; mul d a b
  0x4002b5:  movsxd rax, dword ptr [r12+0x8]
  0x4002bd:  mov rax, qword ptr [r13+rax*8]
  0x4002c5:  movsxd rdx, dword ptr [r12+0xc]
  0x4002cd:  mov rdx, qword ptr [r13+rdx*8]
  0x4002d5:  imul rax, rdx
  0x4002d9:  movsxd rcx, dword ptr [r12+0x4]
  0x4002e1:  mov qword ptr [r13+rcx*8], rax
  0x4002e9:  add r12, 0x10
  0x4002f0:  movzx rax, byte ptr [r12]
  0x4002f9:  jmp qword ptr [r14+rax*8]

op6:  ; div d a b
  0x400301:  movsxd rax, dword ptr [r12+0x8]
  0x400309:  mov rax, qword ptr [r13+rax*8]
  0x400311:  movsxd rsi, dword ptr [r12+0xc]
  0x400319:  mov rsi, qword ptr [r13+rsi*8]
  0x400321:  cqo
  0x400323:  idiv rsi
  0x400326:  movsxd rcx, dword ptr [r12+0x4]
  0x40032e:  mov qword ptr [r13+rcx*8], rax
  0x400336:  add r12, 0x10
  0x40033d:  movzx rax, byte ptr [r12]
  0x400346:  jmp qword ptr [r14+rax*8]

op7:  ; rem d a b
  0x40034e:  movsxd rax, dword ptr [r12+0x8]
  0x400356:  mov rax, qword ptr [r13+rax*8]
  0x40035e:  movsxd rsi, dword ptr [r12+0xc]
  0x400366:  mov rsi, qword ptr [r13+rsi*8]
  0x40036e:  cqo
  0x400370:  idiv rsi
  0x400373:  movsxd rcx, dword ptr [r12+0x4]
  0x40037b:  mov qword ptr [r13+rcx*8], rdx
  0x400383:  add r12, 0x10
  0x40038a:  movzx rax, byte ptr [r12]
  0x400393:  jmp qword ptr [r14+rax*8]

op8:  ; and d a b
  0x40039b:  movsxd rax, dword ptr [r12+0x8]
  0x4003a3:  mov rax, qword ptr [r13+rax*8]
  0x4003ab:  movsxd rdx, dword ptr [r12+0xc]
  0x4003b3:  mov rdx, qword ptr [r13+rdx*8]
  0x4003bb:  and rax, rdx
  0x4003be:  movsxd rcx, dword ptr [r12+0x4]
  0x4003c6:  mov qword ptr [r13+rcx*8], rax
  0x4003ce:  add r12, 0x10
  0x4003d5:  movzx rax, byte ptr [r12]
  0x4003de:  jmp qword ptr [r14+rax*8]

op9:  ; or d a b
  0x4003e6:  movsxd rax, dword ptr [r12+0x8]
  0x4003ee:  mov rax, qword ptr [r13+rax*8]
  0x4003f6:  movsxd rdx, dword ptr [r12+0xc]
  0x4003fe:  mov rdx, qword ptr [r13+rdx*8]
  0x400406:  or rax, rdx
  0x400409:  movsxd rcx, dword ptr [r12+0x4]
  0x400411:  mov qword ptr [r13+rcx*8], rax
  0x400419:  add r12, 0x10
  0x400420:  movzx rax, byte ptr [r12]
  0x400429:  jmp qword ptr [r14+rax*8]

op10:  ; xor d a b
  0x400431:  movsxd rax, dword ptr [r12+0x8]
  0x400439:  mov rax, qword ptr [r13+rax*8]
  0x400441:  movsxd rdx, dword ptr [r12+0xc]
  0x400449:  mov rdx, qword ptr [r13+rdx*8]
  0x400451:  xor rax, rdx
  0x400454:  movsxd rcx, dword ptr [r12+0x4]
  0x40045c:  mov qword ptr [r13+rcx*8], rax
  0x400464:  add r12, 0x10
  0x40046b:  movzx rax, byte ptr [r12]
  0x400474:  jmp qword ptr [r14+rax*8]

op11:  ; shl d a b
  0x40047c:  movsxd rax, dword ptr [r12+0x8]
  0x400484:  mov rax, qword ptr [r13+rax*8]
  0x40048c:  movsxd rcx, dword ptr [r12+0xc]
  0x400494:  mov rcx, qword ptr [r13+rcx*8]
  0x40049c:  shl rax, cl
  0x40049f:  movsxd rdx, dword ptr [r12+0x4]
  0x4004a7:  mov qword ptr [r13+rdx*8], rax
  0x4004af:  add r12, 0x10
  0x4004b6:  movzx rax, byte ptr [r12]
  0x4004bf:  jmp qword ptr [r14+rax*8]

op12:  ; shr d a b
  0x4004c7:  movsxd rax, dword ptr [r12+0x8]
  0x4004cf:  mov rax, qword ptr [r13+rax*8]
  0x4004d7:  movsxd rcx, dword ptr [r12+0xc]
  0x4004df:  mov rcx, qword ptr [r13+rcx*8]
  0x4004e7:  shr rax, cl
  0x4004ea:  movsxd rdx, dword ptr [r12+0x4]
  0x4004f2:  mov qword ptr [r13+rdx*8], rax
  0x4004fa:  add r12, 0x10
  0x400501:  movzx rax, byte ptr [r12]
  0x40050a:  jmp qword ptr [r14+rax*8]

op13:  ; lt d a b
  0x400512:  movsxd rax, dword ptr [r12+0x8]
  0x40051a:  mov rax, qword ptr [r13+rax*8]
  0x400522:  movsxd rdx, dword ptr [r12+0xc]
  0x40052a:  mov rdx, qword ptr [r13+rdx*8]
  0x400532:  cmp rax, rdx
  0x400535:  setl al
  0x400539:  movzx rax, al
  0x40053d:  movsxd rcx, dword ptr [r12+0x4]
  0x400545:  mov qword ptr [r13+rcx*8], rax
  0x40054d:  add r12, 0x10
  0x400554:  movzx rax, byte ptr [r12]
  0x40055d:  jmp qword ptr [r14+rax*8]

op14:  ; eq d a b
  0x400565:  movsxd rax, dword ptr [r12+0x8]
  0x40056d:  mov rax, qword ptr [r13+rax*8]
  0x400575:  movsxd rdx, dword ptr [r12+0xc]
  0x40057d:  mov rdx, qword ptr [r13+rdx*8]
  0x400585:  cmp rax, rdx
  0x400588:  sete al
  0x40058c:  movzx rax, al
  0x400590:  movsxd rcx, dword ptr [r12+0x4]
  0x400598:  mov qword ptr [r13+rcx*8], rax
  0x4005a0:  add r12, 0x10
  0x4005a7:  movzx rax, byte ptr [r12]
  0x4005b0:  jmp qword ptr [r14+rax*8]

op15:  ; ld d a (d := M[a])
  0x4005b8:  movsxd rax, dword ptr [r12+0x8]
  0x4005c0:  mov rax, qword ptr [r13+rax*8]
  0x4005c8:  mov rax, qword ptr [rax]
  0x4005d0:  movsxd rcx, dword ptr [r12+0x4]
  0x4005d8:  mov qword ptr [r13+rcx*8], rax
  0x4005e0:  add r12, 0x10
  0x4005e7:  movzx rax, byte ptr [r12]
  0x4005f0:  jmp qword ptr [r14+rax*8]

op16:  ; st a b (M[a] := b)
  0x4005f8:  movsxd rax, dword ptr [r12+0x4]
  0x400600:  mov rax, qword ptr [r13+rax*8]
  0x400608:  movsxd rdx, dword ptr [r12+0x8]
  0x400610:  mov rdx, qword ptr [r13+rdx*8]
  0x400618:  mov qword ptr [rax], rdx
  0x400620:  add r12, 0x10
  0x400627:  movzx rax, byte ptr [r12]
  0x400630:  jmp qword ptr [r14+rax*8]

op17:  ; lea d a
  0x400638:  movsxd rax, dword ptr [r12+0x8]
  0x400640:  lea rax, [r13+rax*8]
  0x400648:  movsxd rcx, dword ptr [r12+0x4]
  0x400650:  mov qword ptr [r13+rcx*8], rax
  0x400658:  add r12, 0x10
  0x40065f:  movzx rax, byte ptr [r12]
  0x400668:  jmp qword ptr [r14+rax*8]

op18:  ; jmp L
  0x400670:  movsxd rax, dword ptr [r12+0x4]
  0x400678:  add r12, rax
  0x40067b:  movzx rax, byte ptr [r12]
  0x400684:  jmp qword ptr [r14+rax*8]

op19:  ; brz a L
  0x40068c:  movsxd rax, dword ptr [r12+0x4]
  0x400694:  mov rax, qword ptr [r13+rax*8]
  0x40069c:  test rax, rax
  0x40069f:  jne 0x4006c1
  0x4006a5:  movsxd rax, dword ptr [r12+0x8]
  0x4006ad:  add r12, rax
  0x4006b0:  movzx rax, byte ptr [r12]
  0x4006b9:  jmp qword ptr [r14+rax*8]
  0x4006c1:  add r12, 0x10
  0x4006c8:  movzx rax, byte ptr [r12]
  0x4006d1:  jmp qword ptr [r14+rax*8]

op20:  ; call a k
  0x4006d9:  movsxd rax, dword ptr [r12+0x4]
  0x4006e1:  mov rax, qword ptr [r13+rax*8]
  0x4006e9:  movsxd rdx, dword ptr [r12+0x8]
  0x4006f1:  lea rdx, [r13+rdx*8]
  0x4006f9:  lea rcx, [r12+0x10]
  0x400701:  mov qword ptr [rdx], rcx
  0x400709:  mov qword ptr [rdx+0x8], r13
  0x400711:  mov r13, rdx
  0x400714:  mov r12, rax
  0x400717:  movzx rax, byte ptr [r12]
  0x400720:  jmp qword ptr [r14+rax*8]

op21:  ; ret
  0x400728:  mov rax, qword ptr [r13]
  0x400730:  mov r13, qword ptr [r13+0x8]
  0x400738:  mov r12, rax
  0x40073b:  movzx rax, byte ptr [r12]
  0x400744:  jmp qword ptr [r14+rax*8]

op22:  ; cas d a e
  0x40074c:  movsxd rax, dword ptr [r12+0x8]
  0x400754:  mov rdx, qword ptr [r13+rax*8]
  0x40075c:  movsxd rcx, dword ptr [r12+0xc]
  0x400764:  mov rax, qword ptr [r13+rcx*8]
  0x40076c:  mov rsi, qword ptr [r13+rcx*8+0x8]
  0x400774:  lock cmpxchg qword ptr [rdx], rsi
  0x40077e:  movsxd rcx, dword ptr [r12+0x4]
  0x400786:  mov qword ptr [r13+rcx*8], rax
  0x40078e:  add r12, 0x10
  0x400795:  movzx rax, byte ptr [r12]
  0x40079e:  jmp qword ptr [r14+rax*8]

op23:  ; sys d a
  0x4007a6:  movsxd rbx, dword ptr [r12+0x4]
  0x4007ae:  lea rbx, [r13+rbx*8]
  0x4007b6:  movsxd rcx, dword ptr [r12+0x8]
  0x4007be:  lea rcx, [r13+rcx*8]
  0x4007c6:  mov rax, qword ptr [rcx]
  0x4007ce:  mov rdi, qword ptr [rcx+0x8]
  0x4007d6:  mov rsi, qword ptr [rcx+0x10]
  0x4007de:  mov rdx, qword ptr [rcx+0x18]
  0x4007e6:  mov r10, qword ptr [rcx+0x20]
  0x4007ee:  mov r8, qword ptr [rcx+0x28]
  0x4007f6:  mov r9, qword ptr [rcx+0x30]
  0x4007fe:  syscall
  0x400800:  mov qword ptr [rbx], rax
  0x400808:  add r12, 0x10
  0x40080f:  movzx rax, byte ptr [r12]
  0x400818:  jmp qword ptr [r14+rax*8]

op24:  ; spawn d a (clone, a new OS thread)
  0x400820:  movsxd rcx, dword ptr [r12+0x8]
  0x400828:  lea rcx, [r13+rcx*8]
  0x400830:  mov rbx, qword ptr [rcx]
  0x400838:  mov rbp, qword ptr [rcx+0x8]
  0x400840:  mov rax, 0x38
  0x400847:  mov rdi, 0x50f00
  0x40084e:  mov rsi, 0x0
  0x400855:  mov rdx, 0x0
  0x40085c:  mov r10, 0x0
  0x400863:  mov r8, 0x0
  0x40086a:  mov r9, 0x0
  0x400871:  syscall
  0x400873:  test rax, rax
  0x400876:  je 0x4008a4
  0x40087c:  movsxd rcx, dword ptr [r12+0x4]
  0x400884:  mov qword ptr [r13+rcx*8], rax
  0x40088c:  add r12, 0x10
  0x400893:  movzx rax, byte ptr [r12]
  0x40089c:  jmp qword ptr [r14+rax*8]
  0x4008a4:  mov r12, rbx
  0x4008a7:  mov r13, rbp
  0x4008aa:  movzx rax, byte ptr [r12]
  0x4008b3:  jmp qword ptr [r14+rax*8]

bad:
  0x4008bb:  ud2

table:  ; 256 handler addresses at 0x4008c0
  dq 0x4008bb  ; opcode 0
  dq 0x4001b7  ; opcode 1
  dq 0x4001e7  ; opcode 2
  dq 0x40021f  ; opcode 3
  dq 0x40026a  ; opcode 4
  dq 0x4002b5  ; opcode 5
  dq 0x400301  ; opcode 6
  dq 0x40034e  ; opcode 7
  dq 0x40039b  ; opcode 8
  dq 0x4003e6  ; opcode 9
  dq 0x400431  ; opcode 10
  dq 0x40047c  ; opcode 11
  dq 0x4004c7  ; opcode 12
  dq 0x400512  ; opcode 13
  dq 0x400565  ; opcode 14
  dq 0x4005b8  ; opcode 15
  dq 0x4005f8  ; opcode 16
  dq 0x400638  ; opcode 17
  dq 0x400670  ; opcode 18
  dq 0x40068c  ; opcode 19
  dq 0x4006d9  ; opcode 20
  dq 0x400728  ; opcode 21
  dq 0x40074c  ; opcode 22
  dq 0x4007a6  ; opcode 23
  dq 0x400820  ; opcode 24
  dq 0x4008bb  ; opcode 25
  dq 0x4008bb  ; opcode 26
  dq 0x4008bb  ; opcode 27
  dq 0x4008bb  ; opcode 28
  dq 0x4008bb  ; opcode 29
  dq 0x4008bb  ; opcode 30
  dq 0x4008bb  ; opcode 31
  dq 0x4008bb  ; opcode 32
  dq 0x4008bb  ; opcode 33
  dq 0x4008bb  ; opcode 34
  dq 0x4008bb  ; opcode 35
  dq 0x4008bb  ; opcode 36
  dq 0x4008bb  ; opcode 37
  dq 0x4008bb  ; opcode 38
  dq 0x4008bb  ; opcode 39
  dq 0x4008bb  ; opcode 40
  dq 0x4008bb  ; opcode 41
  dq 0x4008bb  ; opcode 42
  dq 0x4008bb  ; opcode 43
  dq 0x4008bb  ; opcode 44
  dq 0x4008bb  ; opcode 45
  dq 0x4008bb  ; opcode 46
  dq 0x4008bb  ; opcode 47
  dq 0x4008bb  ; opcode 48
  dq 0x4008bb  ; opcode 49
  dq 0x4008bb  ; opcode 50
  dq 0x4008bb  ; opcode 51
  dq 0x4008bb  ; opcode 52
  dq 0x4008bb  ; opcode 53
  dq 0x4008bb  ; opcode 54
  dq 0x4008bb  ; opcode 55
  dq 0x4008bb  ; opcode 56
  dq 0x4008bb  ; opcode 57
  dq 0x4008bb  ; opcode 58
  dq 0x4008bb  ; opcode 59
  dq 0x4008bb  ; opcode 60
  dq 0x4008bb  ; opcode 61
  dq 0x4008bb  ; opcode 62
  dq 0x4008bb  ; opcode 63
  dq 0x4008bb  ; opcode 64
  dq 0x4008bb  ; opcode 65
  dq 0x4008bb  ; opcode 66
  dq 0x4008bb  ; opcode 67
  dq 0x4008bb  ; opcode 68
  dq 0x4008bb  ; opcode 69
  dq 0x4008bb  ; opcode 70
  dq 0x4008bb  ; opcode 71
  dq 0x4008bb  ; opcode 72
  dq 0x4008bb  ; opcode 73
  dq 0x4008bb  ; opcode 74
  dq 0x4008bb  ; opcode 75
  dq 0x4008bb  ; opcode 76
  dq 0x4008bb  ; opcode 77
  dq 0x4008bb  ; opcode 78
  dq 0x4008bb  ; opcode 79
  dq 0x4008bb  ; opcode 80
  dq 0x4008bb  ; opcode 81
  dq 0x4008bb  ; opcode 82
  dq 0x4008bb  ; opcode 83
  dq 0x4008bb  ; opcode 84
  dq 0x4008bb  ; opcode 85
  dq 0x4008bb  ; opcode 86
  dq 0x4008bb  ; opcode 87
  dq 0x4008bb  ; opcode 88
  dq 0x4008bb  ; opcode 89
  dq 0x4008bb  ; opcode 90
  dq 0x4008bb  ; opcode 91
  dq 0x4008bb  ; opcode 92
  dq 0x4008bb  ; opcode 93
  dq 0x4008bb  ; opcode 94
  dq 0x4008bb  ; opcode 95
  dq 0x4008bb  ; opcode 96
  dq 0x4008bb  ; opcode 97
  dq 0x4008bb  ; opcode 98
  dq 0x4008bb  ; opcode 99
  dq 0x4008bb  ; opcode 100
  dq 0x4008bb  ; opcode 101
  dq 0x4008bb  ; opcode 102
  dq 0x4008bb  ; opcode 103
  dq 0x4008bb  ; opcode 104
  dq 0x4008bb  ; opcode 105
  dq 0x4008bb  ; opcode 106
  dq 0x4008bb  ; opcode 107
  dq 0x4008bb  ; opcode 108
  dq 0x4008bb  ; opcode 109
  dq 0x4008bb  ; opcode 110
  dq 0x4008bb  ; opcode 111
  dq 0x4008bb  ; opcode 112
  dq 0x4008bb  ; opcode 113
  dq 0x4008bb  ; opcode 114
  dq 0x4008bb  ; opcode 115
  dq 0x4008bb  ; opcode 116
  dq 0x4008bb  ; opcode 117
  dq 0x4008bb  ; opcode 118
  dq 0x4008bb  ; opcode 119
  dq 0x4008bb  ; opcode 120
  dq 0x4008bb  ; opcode 121
  dq 0x4008bb  ; opcode 122
  dq 0x4008bb  ; opcode 123
  dq 0x4008bb  ; opcode 124
  dq 0x4008bb  ; opcode 125
  dq 0x4008bb  ; opcode 126
  dq 0x4008bb  ; opcode 127
  dq 0x4008bb  ; opcode 128
  dq 0x4008bb  ; opcode 129
  dq 0x4008bb  ; opcode 130
  dq 0x4008bb  ; opcode 131
  dq 0x4008bb  ; opcode 132
  dq 0x4008bb  ; opcode 133
  dq 0x4008bb  ; opcode 134
  dq 0x4008bb  ; opcode 135
  dq 0x4008bb  ; opcode 136
  dq 0x4008bb  ; opcode 137
  dq 0x4008bb  ; opcode 138
  dq 0x4008bb  ; opcode 139
  dq 0x4008bb  ; opcode 140
  dq 0x4008bb  ; opcode 141
  dq 0x4008bb  ; opcode 142
  dq 0x4008bb  ; opcode 143
  dq 0x4008bb  ; opcode 144
  dq 0x4008bb  ; opcode 145
  dq 0x4008bb  ; opcode 146
  dq 0x4008bb  ; opcode 147
  dq 0x4008bb  ; opcode 148
  dq 0x4008bb  ; opcode 149
  dq 0x4008bb  ; opcode 150
  dq 0x4008bb  ; opcode 151
  dq 0x4008bb  ; opcode 152
  dq 0x4008bb  ; opcode 153
  dq 0x4008bb  ; opcode 154
  dq 0x4008bb  ; opcode 155
  dq 0x4008bb  ; opcode 156
  dq 0x4008bb  ; opcode 157
  dq 0x4008bb  ; opcode 158
  dq 0x4008bb  ; opcode 159
  dq 0x4008bb  ; opcode 160
  dq 0x4008bb  ; opcode 161
  dq 0x4008bb  ; opcode 162
  dq 0x4008bb  ; opcode 163
  dq 0x4008bb  ; opcode 164
  dq 0x4008bb  ; opcode 165
  dq 0x4008bb  ; opcode 166
  dq 0x4008bb  ; opcode 167
  dq 0x4008bb  ; opcode 168
  dq 0x4008bb  ; opcode 169
  dq 0x4008bb  ; opcode 170
  dq 0x4008bb  ; opcode 171
  dq 0x4008bb  ; opcode 172
  dq 0x4008bb  ; opcode 173
  dq 0x4008bb  ; opcode 174
  dq 0x4008bb  ; opcode 175
  dq 0x4008bb  ; opcode 176
  dq 0x4008bb  ; opcode 177
  dq 0x4008bb  ; opcode 178
  dq 0x4008bb  ; opcode 179
  dq 0x4008bb  ; opcode 180
  dq 0x4008bb  ; opcode 181
  dq 0x4008bb  ; opcode 182
  dq 0x4008bb  ; opcode 183
  dq 0x4008bb  ; opcode 184
  dq 0x4008bb  ; opcode 185
  dq 0x4008bb  ; opcode 186
  dq 0x4008bb  ; opcode 187
  dq 0x4008bb  ; opcode 188
  dq 0x4008bb  ; opcode 189
  dq 0x4008bb  ; opcode 190
  dq 0x4008bb  ; opcode 191
  dq 0x4008bb  ; opcode 192
  dq 0x4008bb  ; opcode 193
  dq 0x4008bb  ; opcode 194
  dq 0x4008bb  ; opcode 195
  dq 0x4008bb  ; opcode 196
  dq 0x4008bb  ; opcode 197
  dq 0x4008bb  ; opcode 198
  dq 0x4008bb  ; opcode 199
  dq 0x4008bb  ; opcode 200
  dq 0x4008bb  ; opcode 201
  dq 0x4008bb  ; opcode 202
  dq 0x4008bb  ; opcode 203
  dq 0x4008bb  ; opcode 204
  dq 0x4008bb  ; opcode 205
  dq 0x4008bb  ; opcode 206
  dq 0x4008bb  ; opcode 207
  dq 0x4008bb  ; opcode 208
  dq 0x4008bb  ; opcode 209
  dq 0x4008bb  ; opcode 210
  dq 0x4008bb  ; opcode 211
  dq 0x4008bb  ; opcode 212
  dq 0x4008bb  ; opcode 213
  dq 0x4008bb  ; opcode 214
  dq 0x4008bb  ; opcode 215
  dq 0x4008bb  ; opcode 216
  dq 0x4008bb  ; opcode 217
  dq 0x4008bb  ; opcode 218
  dq 0x4008bb  ; opcode 219
  dq 0x4008bb  ; opcode 220
  dq 0x4008bb  ; opcode 221
  dq 0x4008bb  ; opcode 222
  dq 0x4008bb  ; opcode 223
  dq 0x4008bb  ; opcode 224
  dq 0x4008bb  ; opcode 225
  dq 0x4008bb  ; opcode 226
  dq 0x4008bb  ; opcode 227
  dq 0x4008bb  ; opcode 228
  dq 0x4008bb  ; opcode 229
  dq 0x4008bb  ; opcode 230
  dq 0x4008bb  ; opcode 231
  dq 0x4008bb  ; opcode 232
  dq 0x4008bb  ; opcode 233
  dq 0x4008bb  ; opcode 234
  dq 0x4008bb  ; opcode 235
  dq 0x4008bb  ; opcode 236
  dq 0x4008bb  ; opcode 237
  dq 0x4008bb  ; opcode 238
  dq 0x4008bb  ; opcode 239
  dq 0x4008bb  ; opcode 240
  dq 0x4008bb  ; opcode 241
  dq 0x4008bb  ; opcode 242
  dq 0x4008bb  ; opcode 243
  dq 0x4008bb  ; opcode 244
  dq 0x4008bb  ; opcode 245
  dq 0x4008bb  ; opcode 246
  dq 0x4008bb  ; opcode 247
  dq 0x4008bb  ; opcode 248
  dq 0x4008bb  ; opcode 249
  dq 0x4008bb  ; opcode 250
  dq 0x4008bb  ; opcode 251
  dq 0x4008bb  ; opcode 252
  dq 0x4008bb  ; opcode 253
  dq 0x4008bb  ; opcode 254
  dq 0x4008bb  ; opcode 255
