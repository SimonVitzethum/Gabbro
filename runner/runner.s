; the S0IR runner, x86-64, Intel syntax; written by `lake exe runner` from Runner/Prog/Code.lean
; while the IR runs: r12 = IR pc, r13 = IR fp (frame), r14 = dispatch table; slot i = [r13 + 8*i]
; an IR instruction is 16 bytes: opcode byte, then three 32-bit fields at pc+4, pc+8, pc+12
; ELF loaded at 0x400000, code from 0x400100, dispatch table at 0x4018d0


loader:
  0x400100:  mov rdi, qword ptr [rsp+0x10]
  0x400108:  mov rax, 0x2
  0x40010f:  mov rsi, 0x0
  0x400116:  mov rdx, 0x0
  0x40011d:  syscall
  0x40011f:  test rax, rax
  0x400122:  js 0x4001c0
  0x400128:  mov rbx, rax
  0x40012b:  mov rdi, rbx
  0x40012e:  mov rsi, 0x0
  0x400135:  mov rdx, 0x2
  0x40013c:  mov rax, 0x8
  0x400143:  syscall
  0x400145:  test rax, rax
  0x400148:  js 0x4001c0
  0x40014e:  je 0x4001c0
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
  0x400189:  jne 0x4001c0
  0x40018f:  mov r14, 0x4018d0
  0x400196:  ldmxcsr dword ptr [r14+0x800]
  0x40019f:  mov r13, qword ptr [rcx]
  0x4001a7:  lea r12, [rcx+0x10]
  0x4001af:  movzx rax, byte ptr [r12]
  0x4001b8:  jmp qword ptr [r14+rax*8]
  0x4001c0:  ud2

op1:  ; const d k
  0x4001c2:  movsxd rax, dword ptr [r12+0x8]
  0x4001ca:  movsxd rcx, dword ptr [r12+0x4]
  0x4001d2:  mov qword ptr [r13+rcx*8], rax
  0x4001da:  add r12, 0x10
  0x4001e1:  movzx rax, byte ptr [r12]
  0x4001ea:  jmp qword ptr [r14+rax*8]

op2:  ; mov d a
  0x4001f2:  movsxd rax, dword ptr [r12+0x8]
  0x4001fa:  mov rax, qword ptr [r13+rax*8]
  0x400202:  movsxd rcx, dword ptr [r12+0x4]
  0x40020a:  mov qword ptr [r13+rcx*8], rax
  0x400212:  add r12, 0x10
  0x400219:  movzx rax, byte ptr [r12]
  0x400222:  jmp qword ptr [r14+rax*8]

op3:  ; add d a b
  0x40022a:  movsxd rax, dword ptr [r12+0x8]
  0x400232:  mov rax, qword ptr [r13+rax*8]
  0x40023a:  movsxd rdx, dword ptr [r12+0xc]
  0x400242:  mov rdx, qword ptr [r13+rdx*8]
  0x40024a:  add rax, rdx
  0x40024d:  movsxd rcx, dword ptr [r12+0x4]
  0x400255:  mov qword ptr [r13+rcx*8], rax
  0x40025d:  add r12, 0x10
  0x400264:  movzx rax, byte ptr [r12]
  0x40026d:  jmp qword ptr [r14+rax*8]

op4:  ; sub d a b
  0x400275:  movsxd rax, dword ptr [r12+0x8]
  0x40027d:  mov rax, qword ptr [r13+rax*8]
  0x400285:  movsxd rdx, dword ptr [r12+0xc]
  0x40028d:  mov rdx, qword ptr [r13+rdx*8]
  0x400295:  sub rax, rdx
  0x400298:  movsxd rcx, dword ptr [r12+0x4]
  0x4002a0:  mov qword ptr [r13+rcx*8], rax
  0x4002a8:  add r12, 0x10
  0x4002af:  movzx rax, byte ptr [r12]
  0x4002b8:  jmp qword ptr [r14+rax*8]

op5:  ; mul d a b
  0x4002c0:  movsxd rax, dword ptr [r12+0x8]
  0x4002c8:  mov rax, qword ptr [r13+rax*8]
  0x4002d0:  movsxd rdx, dword ptr [r12+0xc]
  0x4002d8:  mov rdx, qword ptr [r13+rdx*8]
  0x4002e0:  imul rax, rdx
  0x4002e4:  movsxd rcx, dword ptr [r12+0x4]
  0x4002ec:  mov qword ptr [r13+rcx*8], rax
  0x4002f4:  add r12, 0x10
  0x4002fb:  movzx rax, byte ptr [r12]
  0x400304:  jmp qword ptr [r14+rax*8]

op6:  ; sdiv d a b
  0x40030c:  movsxd rax, dword ptr [r12+0x8]
  0x400314:  mov rax, qword ptr [r13+rax*8]
  0x40031c:  movsxd rsi, dword ptr [r12+0xc]
  0x400324:  mov rsi, qword ptr [r13+rsi*8]
  0x40032c:  cqo
  0x40032e:  idiv rsi
  0x400331:  movsxd rcx, dword ptr [r12+0x4]
  0x400339:  mov qword ptr [r13+rcx*8], rax
  0x400341:  add r12, 0x10
  0x400348:  movzx rax, byte ptr [r12]
  0x400351:  jmp qword ptr [r14+rax*8]

op7:  ; srem d a b
  0x400359:  movsxd rax, dword ptr [r12+0x8]
  0x400361:  mov rax, qword ptr [r13+rax*8]
  0x400369:  movsxd rsi, dword ptr [r12+0xc]
  0x400371:  mov rsi, qword ptr [r13+rsi*8]
  0x400379:  cqo
  0x40037b:  idiv rsi
  0x40037e:  movsxd rcx, dword ptr [r12+0x4]
  0x400386:  mov qword ptr [r13+rcx*8], rdx
  0x40038e:  add r12, 0x10
  0x400395:  movzx rax, byte ptr [r12]
  0x40039e:  jmp qword ptr [r14+rax*8]

op8:  ; and d a b
  0x4003a6:  movsxd rax, dword ptr [r12+0x8]
  0x4003ae:  mov rax, qword ptr [r13+rax*8]
  0x4003b6:  movsxd rdx, dword ptr [r12+0xc]
  0x4003be:  mov rdx, qword ptr [r13+rdx*8]
  0x4003c6:  and rax, rdx
  0x4003c9:  movsxd rcx, dword ptr [r12+0x4]
  0x4003d1:  mov qword ptr [r13+rcx*8], rax
  0x4003d9:  add r12, 0x10
  0x4003e0:  movzx rax, byte ptr [r12]
  0x4003e9:  jmp qword ptr [r14+rax*8]

op9:  ; or d a b
  0x4003f1:  movsxd rax, dword ptr [r12+0x8]
  0x4003f9:  mov rax, qword ptr [r13+rax*8]
  0x400401:  movsxd rdx, dword ptr [r12+0xc]
  0x400409:  mov rdx, qword ptr [r13+rdx*8]
  0x400411:  or rax, rdx
  0x400414:  movsxd rcx, dword ptr [r12+0x4]
  0x40041c:  mov qword ptr [r13+rcx*8], rax
  0x400424:  add r12, 0x10
  0x40042b:  movzx rax, byte ptr [r12]
  0x400434:  jmp qword ptr [r14+rax*8]

op10:  ; xor d a b
  0x40043c:  movsxd rax, dword ptr [r12+0x8]
  0x400444:  mov rax, qword ptr [r13+rax*8]
  0x40044c:  movsxd rdx, dword ptr [r12+0xc]
  0x400454:  mov rdx, qword ptr [r13+rdx*8]
  0x40045c:  xor rax, rdx
  0x40045f:  movsxd rcx, dword ptr [r12+0x4]
  0x400467:  mov qword ptr [r13+rcx*8], rax
  0x40046f:  add r12, 0x10
  0x400476:  movzx rax, byte ptr [r12]
  0x40047f:  jmp qword ptr [r14+rax*8]

op11:  ; shl d a b
  0x400487:  movsxd rax, dword ptr [r12+0x8]
  0x40048f:  mov rax, qword ptr [r13+rax*8]
  0x400497:  movsxd rcx, dword ptr [r12+0xc]
  0x40049f:  mov rcx, qword ptr [r13+rcx*8]
  0x4004a7:  shl rax, cl
  0x4004aa:  movsxd rdx, dword ptr [r12+0x4]
  0x4004b2:  mov qword ptr [r13+rdx*8], rax
  0x4004ba:  add r12, 0x10
  0x4004c1:  movzx rax, byte ptr [r12]
  0x4004ca:  jmp qword ptr [r14+rax*8]

op12:  ; shr d a b
  0x4004d2:  movsxd rax, dword ptr [r12+0x8]
  0x4004da:  mov rax, qword ptr [r13+rax*8]
  0x4004e2:  movsxd rcx, dword ptr [r12+0xc]
  0x4004ea:  mov rcx, qword ptr [r13+rcx*8]
  0x4004f2:  shr rax, cl
  0x4004f5:  movsxd rdx, dword ptr [r12+0x4]
  0x4004fd:  mov qword ptr [r13+rdx*8], rax
  0x400505:  add r12, 0x10
  0x40050c:  movzx rax, byte ptr [r12]
  0x400515:  jmp qword ptr [r14+rax*8]

op13:  ; lt d a b
  0x40051d:  movsxd rax, dword ptr [r12+0x8]
  0x400525:  mov rax, qword ptr [r13+rax*8]
  0x40052d:  movsxd rdx, dword ptr [r12+0xc]
  0x400535:  mov rdx, qword ptr [r13+rdx*8]
  0x40053d:  cmp rax, rdx
  0x400540:  setl al
  0x400544:  movzx rax, al
  0x400548:  movsxd rcx, dword ptr [r12+0x4]
  0x400550:  mov qword ptr [r13+rcx*8], rax
  0x400558:  add r12, 0x10
  0x40055f:  movzx rax, byte ptr [r12]
  0x400568:  jmp qword ptr [r14+rax*8]

op14:  ; eq d a b
  0x400570:  movsxd rax, dword ptr [r12+0x8]
  0x400578:  mov rax, qword ptr [r13+rax*8]
  0x400580:  movsxd rdx, dword ptr [r12+0xc]
  0x400588:  mov rdx, qword ptr [r13+rdx*8]
  0x400590:  cmp rax, rdx
  0x400593:  sete al
  0x400597:  movzx rax, al
  0x40059b:  movsxd rcx, dword ptr [r12+0x4]
  0x4005a3:  mov qword ptr [r13+rcx*8], rax
  0x4005ab:  add r12, 0x10
  0x4005b2:  movzx rax, byte ptr [r12]
  0x4005bb:  jmp qword ptr [r14+rax*8]

op15:  ; ld d a (d := M[a])
  0x4005c3:  movsxd rax, dword ptr [r12+0x8]
  0x4005cb:  mov rax, qword ptr [r13+rax*8]
  0x4005d3:  mov rax, qword ptr [rax]
  0x4005db:  movsxd rcx, dword ptr [r12+0x4]
  0x4005e3:  mov qword ptr [r13+rcx*8], rax
  0x4005eb:  add r12, 0x10
  0x4005f2:  movzx rax, byte ptr [r12]
  0x4005fb:  jmp qword ptr [r14+rax*8]

op16:  ; st a b (M[a] := b)
  0x400603:  movsxd rax, dword ptr [r12+0x4]
  0x40060b:  mov rax, qword ptr [r13+rax*8]
  0x400613:  movsxd rdx, dword ptr [r12+0x8]
  0x40061b:  mov rdx, qword ptr [r13+rdx*8]
  0x400623:  mov qword ptr [rax], rdx
  0x40062b:  add r12, 0x10
  0x400632:  movzx rax, byte ptr [r12]
  0x40063b:  jmp qword ptr [r14+rax*8]

op17:  ; lea d a
  0x400643:  movsxd rax, dword ptr [r12+0x8]
  0x40064b:  lea rax, [r13+rax*8]
  0x400653:  movsxd rcx, dword ptr [r12+0x4]
  0x40065b:  mov qword ptr [r13+rcx*8], rax
  0x400663:  add r12, 0x10
  0x40066a:  movzx rax, byte ptr [r12]
  0x400673:  jmp qword ptr [r14+rax*8]

op18:  ; jmp L
  0x40067b:  movsxd rax, dword ptr [r12+0x4]
  0x400683:  add r12, rax
  0x400686:  movzx rax, byte ptr [r12]
  0x40068f:  jmp qword ptr [r14+rax*8]

op19:  ; brz a L
  0x400697:  movsxd rax, dword ptr [r12+0x4]
  0x40069f:  mov rax, qword ptr [r13+rax*8]
  0x4006a7:  test rax, rax
  0x4006aa:  jne 0x4006cc
  0x4006b0:  movsxd rax, dword ptr [r12+0x8]
  0x4006b8:  add r12, rax
  0x4006bb:  movzx rax, byte ptr [r12]
  0x4006c4:  jmp qword ptr [r14+rax*8]
  0x4006cc:  add r12, 0x10
  0x4006d3:  movzx rax, byte ptr [r12]
  0x4006dc:  jmp qword ptr [r14+rax*8]

op20:  ; call a k
  0x4006e4:  movsxd rax, dword ptr [r12+0x4]
  0x4006ec:  mov rax, qword ptr [r13+rax*8]
  0x4006f4:  movsxd rdx, dword ptr [r12+0x8]
  0x4006fc:  lea rdx, [r13+rdx*8]
  0x400704:  lea rcx, [r12+0x10]
  0x40070c:  mov qword ptr [rdx], rcx
  0x400714:  mov qword ptr [rdx+0x8], r13
  0x40071c:  mov r13, rdx
  0x40071f:  mov r12, rax
  0x400722:  movzx rax, byte ptr [r12]
  0x40072b:  jmp qword ptr [r14+rax*8]

op21:  ; ret
  0x400733:  mov rax, qword ptr [r13]
  0x40073b:  mov r13, qword ptr [r13+0x8]
  0x400743:  mov r12, rax
  0x400746:  movzx rax, byte ptr [r12]
  0x40074f:  jmp qword ptr [r14+rax*8]

op22:  ; cas d a e
  0x400757:  movsxd rax, dword ptr [r12+0x8]
  0x40075f:  mov rdx, qword ptr [r13+rax*8]
  0x400767:  movsxd rcx, dword ptr [r12+0xc]
  0x40076f:  mov rax, qword ptr [r13+rcx*8]
  0x400777:  mov rsi, qword ptr [r13+rcx*8+0x8]
  0x40077f:  lock cmpxchg qword ptr [rdx], rsi
  0x400789:  movsxd rcx, dword ptr [r12+0x4]
  0x400791:  mov qword ptr [r13+rcx*8], rax
  0x400799:  add r12, 0x10
  0x4007a0:  movzx rax, byte ptr [r12]
  0x4007a9:  jmp qword ptr [r14+rax*8]

op23:  ; sys d a
  0x4007b1:  movsxd rbx, dword ptr [r12+0x4]
  0x4007b9:  lea rbx, [r13+rbx*8]
  0x4007c1:  movsxd rcx, dword ptr [r12+0x8]
  0x4007c9:  lea rcx, [r13+rcx*8]
  0x4007d1:  mov rax, qword ptr [rcx]
  0x4007d9:  mov rdi, qword ptr [rcx+0x8]
  0x4007e1:  mov rsi, qword ptr [rcx+0x10]
  0x4007e9:  mov rdx, qword ptr [rcx+0x18]
  0x4007f1:  mov r10, qword ptr [rcx+0x20]
  0x4007f9:  mov r8, qword ptr [rcx+0x28]
  0x400801:  mov r9, qword ptr [rcx+0x30]
  0x400809:  syscall
  0x40080b:  mov qword ptr [rbx], rax
  0x400813:  add r12, 0x10
  0x40081a:  movzx rax, byte ptr [r12]
  0x400823:  jmp qword ptr [r14+rax*8]

op24:  ; spawn d a (clone, a new OS thread)
  0x40082b:  movsxd rcx, dword ptr [r12+0x8]
  0x400833:  lea rcx, [r13+rcx*8]
  0x40083b:  mov rbx, qword ptr [rcx]
  0x400843:  mov rbp, qword ptr [rcx+0x8]
  0x40084b:  mov rax, 0x38
  0x400852:  mov rdi, 0x50f00
  0x400859:  mov rsi, 0x0
  0x400860:  mov rdx, 0x0
  0x400867:  mov r10, 0x0
  0x40086e:  mov r8, 0x0
  0x400875:  mov r9, 0x0
  0x40087c:  syscall
  0x40087e:  test rax, rax
  0x400881:  je 0x4008af
  0x400887:  movsxd rcx, dword ptr [r12+0x4]
  0x40088f:  mov qword ptr [r13+rcx*8], rax
  0x400897:  add r12, 0x10
  0x40089e:  movzx rax, byte ptr [r12]
  0x4008a7:  jmp qword ptr [r14+rax*8]
  0x4008af:  mov r12, rbx
  0x4008b2:  mov r13, rbp
  0x4008b5:  movzx rax, byte ptr [r12]
  0x4008be:  jmp qword ptr [r14+rax*8]

op25:  ; udiv d a b
  0x4008c6:  movsxd rax, dword ptr [r12+0x8]
  0x4008ce:  mov rax, qword ptr [r13+rax*8]
  0x4008d6:  movsxd rsi, dword ptr [r12+0xc]
  0x4008de:  mov rsi, qword ptr [r13+rsi*8]
  0x4008e6:  mov rdx, 0x0
  0x4008ed:  div rsi
  0x4008f0:  movsxd rcx, dword ptr [r12+0x4]
  0x4008f8:  mov qword ptr [r13+rcx*8], rax
  0x400900:  add r12, 0x10
  0x400907:  movzx rax, byte ptr [r12]
  0x400910:  jmp qword ptr [r14+rax*8]

op26:  ; urem d a b
  0x400918:  movsxd rax, dword ptr [r12+0x8]
  0x400920:  mov rax, qword ptr [r13+rax*8]
  0x400928:  movsxd rsi, dword ptr [r12+0xc]
  0x400930:  mov rsi, qword ptr [r13+rsi*8]
  0x400938:  mov rdx, 0x0
  0x40093f:  div rsi
  0x400942:  movsxd rcx, dword ptr [r12+0x4]
  0x40094a:  mov qword ptr [r13+rcx*8], rdx
  0x400952:  add r12, 0x10
  0x400959:  movzx rax, byte ptr [r12]
  0x400962:  jmp qword ptr [r14+rax*8]

op27:  ; ult d a b
  0x40096a:  movsxd rax, dword ptr [r12+0x8]
  0x400972:  mov rax, qword ptr [r13+rax*8]
  0x40097a:  movsxd rdx, dword ptr [r12+0xc]
  0x400982:  mov rdx, qword ptr [r13+rdx*8]
  0x40098a:  cmp rax, rdx
  0x40098d:  setb al
  0x400991:  movzx rax, al
  0x400995:  movsxd rcx, dword ptr [r12+0x4]
  0x40099d:  mov qword ptr [r13+rcx*8], rax
  0x4009a5:  add r12, 0x10
  0x4009ac:  movzx rax, byte ptr [r12]
  0x4009b5:  jmp qword ptr [r14+rax*8]

op28:  ; Runner.NativeFPOp.add (Runner.FPFormat.f32) d a b
  0x4009bd:  movsxd rax, dword ptr [r12+0x8]
  0x4009c5:  mov rax, qword ptr [r13+rax*8]
  0x4009cd:  movsxd rdx, dword ptr [r12+0xc]
  0x4009d5:  mov rdx, qword ptr [r13+rdx*8]
  0x4009dd:  movd xmm0, eax
  0x4009e2:  movd xmm1, edx
  0x4009e7:  addss xmm0, xmm1
  0x4009ec:  movd eax, xmm0
  0x4009f1:  movsxd rcx, dword ptr [r12+0x4]
  0x4009f9:  mov qword ptr [r13+rcx*8], rax
  0x400a01:  add r12, 0x10
  0x400a08:  movzx rax, byte ptr [r12]
  0x400a11:  jmp qword ptr [r14+rax*8]

op29:  ; Runner.NativeFPOp.add (Runner.FPFormat.f64) d a b
  0x400a19:  movsxd rax, dword ptr [r12+0x8]
  0x400a21:  mov rax, qword ptr [r13+rax*8]
  0x400a29:  movsxd rdx, dword ptr [r12+0xc]
  0x400a31:  mov rdx, qword ptr [r13+rdx*8]
  0x400a39:  movq xmm0, rax
  0x400a3e:  movq xmm1, rdx
  0x400a43:  addsd xmm0, xmm1
  0x400a48:  movq rax, xmm0
  0x400a4d:  movsxd rcx, dword ptr [r12+0x4]
  0x400a55:  mov qword ptr [r13+rcx*8], rax
  0x400a5d:  add r12, 0x10
  0x400a64:  movzx rax, byte ptr [r12]
  0x400a6d:  jmp qword ptr [r14+rax*8]

op30:  ; Runner.NativeFPOp.sub (Runner.FPFormat.f32) d a b
  0x400a75:  movsxd rax, dword ptr [r12+0x8]
  0x400a7d:  mov rax, qword ptr [r13+rax*8]
  0x400a85:  movsxd rdx, dword ptr [r12+0xc]
  0x400a8d:  mov rdx, qword ptr [r13+rdx*8]
  0x400a95:  movd xmm0, eax
  0x400a9a:  movd xmm1, edx
  0x400a9f:  subss xmm0, xmm1
  0x400aa4:  movd eax, xmm0
  0x400aa9:  movsxd rcx, dword ptr [r12+0x4]
  0x400ab1:  mov qword ptr [r13+rcx*8], rax
  0x400ab9:  add r12, 0x10
  0x400ac0:  movzx rax, byte ptr [r12]
  0x400ac9:  jmp qword ptr [r14+rax*8]

op31:  ; Runner.NativeFPOp.sub (Runner.FPFormat.f64) d a b
  0x400ad1:  movsxd rax, dword ptr [r12+0x8]
  0x400ad9:  mov rax, qword ptr [r13+rax*8]
  0x400ae1:  movsxd rdx, dword ptr [r12+0xc]
  0x400ae9:  mov rdx, qword ptr [r13+rdx*8]
  0x400af1:  movq xmm0, rax
  0x400af6:  movq xmm1, rdx
  0x400afb:  subsd xmm0, xmm1
  0x400b00:  movq rax, xmm0
  0x400b05:  movsxd rcx, dword ptr [r12+0x4]
  0x400b0d:  mov qword ptr [r13+rcx*8], rax
  0x400b15:  add r12, 0x10
  0x400b1c:  movzx rax, byte ptr [r12]
  0x400b25:  jmp qword ptr [r14+rax*8]

op32:  ; Runner.NativeFPOp.mul (Runner.FPFormat.f32) d a b
  0x400b2d:  movsxd rax, dword ptr [r12+0x8]
  0x400b35:  mov rax, qword ptr [r13+rax*8]
  0x400b3d:  movsxd rdx, dword ptr [r12+0xc]
  0x400b45:  mov rdx, qword ptr [r13+rdx*8]
  0x400b4d:  movd xmm0, eax
  0x400b52:  movd xmm1, edx
  0x400b57:  mulss xmm0, xmm1
  0x400b5c:  movd eax, xmm0
  0x400b61:  movsxd rcx, dword ptr [r12+0x4]
  0x400b69:  mov qword ptr [r13+rcx*8], rax
  0x400b71:  add r12, 0x10
  0x400b78:  movzx rax, byte ptr [r12]
  0x400b81:  jmp qword ptr [r14+rax*8]

op33:  ; Runner.NativeFPOp.mul (Runner.FPFormat.f64) d a b
  0x400b89:  movsxd rax, dword ptr [r12+0x8]
  0x400b91:  mov rax, qword ptr [r13+rax*8]
  0x400b99:  movsxd rdx, dword ptr [r12+0xc]
  0x400ba1:  mov rdx, qword ptr [r13+rdx*8]
  0x400ba9:  movq xmm0, rax
  0x400bae:  movq xmm1, rdx
  0x400bb3:  mulsd xmm0, xmm1
  0x400bb8:  movq rax, xmm0
  0x400bbd:  movsxd rcx, dword ptr [r12+0x4]
  0x400bc5:  mov qword ptr [r13+rcx*8], rax
  0x400bcd:  add r12, 0x10
  0x400bd4:  movzx rax, byte ptr [r12]
  0x400bdd:  jmp qword ptr [r14+rax*8]

op34:  ; Runner.NativeFPOp.div (Runner.FPFormat.f32) d a b
  0x400be5:  movsxd rax, dword ptr [r12+0x8]
  0x400bed:  mov rax, qword ptr [r13+rax*8]
  0x400bf5:  movsxd rdx, dword ptr [r12+0xc]
  0x400bfd:  mov rdx, qword ptr [r13+rdx*8]
  0x400c05:  movd xmm0, eax
  0x400c0a:  movd xmm1, edx
  0x400c0f:  divss xmm0, xmm1
  0x400c14:  movd eax, xmm0
  0x400c19:  movsxd rcx, dword ptr [r12+0x4]
  0x400c21:  mov qword ptr [r13+rcx*8], rax
  0x400c29:  add r12, 0x10
  0x400c30:  movzx rax, byte ptr [r12]
  0x400c39:  jmp qword ptr [r14+rax*8]

op35:  ; Runner.NativeFPOp.div (Runner.FPFormat.f64) d a b
  0x400c41:  movsxd rax, dword ptr [r12+0x8]
  0x400c49:  mov rax, qword ptr [r13+rax*8]
  0x400c51:  movsxd rdx, dword ptr [r12+0xc]
  0x400c59:  mov rdx, qword ptr [r13+rdx*8]
  0x400c61:  movq xmm0, rax
  0x400c66:  movq xmm1, rdx
  0x400c6b:  divsd xmm0, xmm1
  0x400c70:  movq rax, xmm0
  0x400c75:  movsxd rcx, dword ptr [r12+0x4]
  0x400c7d:  mov qword ptr [r13+rcx*8], rax
  0x400c85:  add r12, 0x10
  0x400c8c:  movzx rax, byte ptr [r12]
  0x400c95:  jmp qword ptr [r14+rax*8]

op36:  ; Runner.NativeFPOp.neg (Runner.FPFormat.f32) d a b
  0x400c9d:  movsxd rax, dword ptr [r12+0x8]
  0x400ca5:  mov rax, qword ptr [r13+rax*8]
  0x400cad:  movsxd rdx, dword ptr [r12+0xc]
  0x400cb5:  mov rdx, qword ptr [r13+rdx*8]
  0x400cbd:  movd xmm0, eax
  0x400cc2:  movd eax, xmm0
  0x400cc7:  mov rdx, 0x1
  0x400cce:  mov rcx, 0x1f
  0x400cd5:  shl rdx, cl
  0x400cd8:  xor rax, rdx
  0x400cdb:  movsxd rcx, dword ptr [r12+0x4]
  0x400ce3:  mov qword ptr [r13+rcx*8], rax
  0x400ceb:  add r12, 0x10
  0x400cf2:  movzx rax, byte ptr [r12]
  0x400cfb:  jmp qword ptr [r14+rax*8]

op37:  ; Runner.NativeFPOp.neg (Runner.FPFormat.f64) d a b
  0x400d03:  movsxd rax, dword ptr [r12+0x8]
  0x400d0b:  mov rax, qword ptr [r13+rax*8]
  0x400d13:  movsxd rdx, dword ptr [r12+0xc]
  0x400d1b:  mov rdx, qword ptr [r13+rdx*8]
  0x400d23:  mov rdx, 0x1
  0x400d2a:  mov rcx, 0x3f
  0x400d31:  shl rdx, cl
  0x400d34:  xor rax, rdx
  0x400d37:  movsxd rcx, dword ptr [r12+0x4]
  0x400d3f:  mov qword ptr [r13+rcx*8], rax
  0x400d47:  add r12, 0x10
  0x400d4e:  movzx rax, byte ptr [r12]
  0x400d57:  jmp qword ptr [r14+rax*8]

op38:  ; Runner.NativeFPOp.eq (Runner.FPFormat.f32) d a b
  0x400d5f:  movsxd rax, dword ptr [r12+0x8]
  0x400d67:  mov rax, qword ptr [r13+rax*8]
  0x400d6f:  movsxd rdx, dword ptr [r12+0xc]
  0x400d77:  mov rdx, qword ptr [r13+rdx*8]
  0x400d7f:  movd xmm0, eax
  0x400d84:  movd xmm1, edx
  0x400d89:  cmpeqss xmm0, xmm1
  0x400d8f:  movd eax, xmm0
  0x400d94:  and rax, 0x1
  0x400d9b:  movsxd rcx, dword ptr [r12+0x4]
  0x400da3:  mov qword ptr [r13+rcx*8], rax
  0x400dab:  add r12, 0x10
  0x400db2:  movzx rax, byte ptr [r12]
  0x400dbb:  jmp qword ptr [r14+rax*8]

op39:  ; Runner.NativeFPOp.eq (Runner.FPFormat.f64) d a b
  0x400dc3:  movsxd rax, dword ptr [r12+0x8]
  0x400dcb:  mov rax, qword ptr [r13+rax*8]
  0x400dd3:  movsxd rdx, dword ptr [r12+0xc]
  0x400ddb:  mov rdx, qword ptr [r13+rdx*8]
  0x400de3:  movq xmm0, rax
  0x400de8:  movq xmm1, rdx
  0x400ded:  cmpeqsd xmm0, xmm1
  0x400df3:  movq rax, xmm0
  0x400df8:  and rax, 0x1
  0x400dff:  movsxd rcx, dword ptr [r12+0x4]
  0x400e07:  mov qword ptr [r13+rcx*8], rax
  0x400e0f:  add r12, 0x10
  0x400e16:  movzx rax, byte ptr [r12]
  0x400e1f:  jmp qword ptr [r14+rax*8]

op40:  ; Runner.NativeFPOp.lt (Runner.FPFormat.f32) d a b
  0x400e27:  movsxd rax, dword ptr [r12+0x8]
  0x400e2f:  mov rax, qword ptr [r13+rax*8]
  0x400e37:  movsxd rdx, dword ptr [r12+0xc]
  0x400e3f:  mov rdx, qword ptr [r13+rdx*8]
  0x400e47:  movd xmm0, eax
  0x400e4c:  movd xmm1, edx
  0x400e51:  cmpltss xmm0, xmm1
  0x400e57:  movd eax, xmm0
  0x400e5c:  and rax, 0x1
  0x400e63:  movsxd rcx, dword ptr [r12+0x4]
  0x400e6b:  mov qword ptr [r13+rcx*8], rax
  0x400e73:  add r12, 0x10
  0x400e7a:  movzx rax, byte ptr [r12]
  0x400e83:  jmp qword ptr [r14+rax*8]

op41:  ; Runner.NativeFPOp.lt (Runner.FPFormat.f64) d a b
  0x400e8b:  movsxd rax, dword ptr [r12+0x8]
  0x400e93:  mov rax, qword ptr [r13+rax*8]
  0x400e9b:  movsxd rdx, dword ptr [r12+0xc]
  0x400ea3:  mov rdx, qword ptr [r13+rdx*8]
  0x400eab:  movq xmm0, rax
  0x400eb0:  movq xmm1, rdx
  0x400eb5:  cmpltsd xmm0, xmm1
  0x400ebb:  movq rax, xmm0
  0x400ec0:  and rax, 0x1
  0x400ec7:  movsxd rcx, dword ptr [r12+0x4]
  0x400ecf:  mov qword ptr [r13+rcx*8], rax
  0x400ed7:  add r12, 0x10
  0x400ede:  movzx rax, byte ptr [r12]
  0x400ee7:  jmp qword ptr [r14+rax*8]

op42:  ; Runner.NativeFPOp.le (Runner.FPFormat.f32) d a b
  0x400eef:  movsxd rax, dword ptr [r12+0x8]
  0x400ef7:  mov rax, qword ptr [r13+rax*8]
  0x400eff:  movsxd rdx, dword ptr [r12+0xc]
  0x400f07:  mov rdx, qword ptr [r13+rdx*8]
  0x400f0f:  movd xmm0, eax
  0x400f14:  movd xmm1, edx
  0x400f19:  cmpless xmm0, xmm1
  0x400f1f:  movd eax, xmm0
  0x400f24:  and rax, 0x1
  0x400f2b:  movsxd rcx, dword ptr [r12+0x4]
  0x400f33:  mov qword ptr [r13+rcx*8], rax
  0x400f3b:  add r12, 0x10
  0x400f42:  movzx rax, byte ptr [r12]
  0x400f4b:  jmp qword ptr [r14+rax*8]

op43:  ; Runner.NativeFPOp.le (Runner.FPFormat.f64) d a b
  0x400f53:  movsxd rax, dword ptr [r12+0x8]
  0x400f5b:  mov rax, qword ptr [r13+rax*8]
  0x400f63:  movsxd rdx, dword ptr [r12+0xc]
  0x400f6b:  mov rdx, qword ptr [r13+rdx*8]
  0x400f73:  movq xmm0, rax
  0x400f78:  movq xmm1, rdx
  0x400f7d:  cmplesd xmm0, xmm1
  0x400f83:  movq rax, xmm0
  0x400f88:  and rax, 0x1
  0x400f8f:  movsxd rcx, dword ptr [r12+0x4]
  0x400f97:  mov qword ptr [r13+rcx*8], rax
  0x400f9f:  add r12, 0x10
  0x400fa6:  movzx rax, byte ptr [r12]
  0x400faf:  jmp qword ptr [r14+rax*8]

op44:  ; Runner.NativeFPOp.isFinite (Runner.FPFormat.f32) d a b
  0x400fb7:  movsxd rax, dword ptr [r12+0x8]
  0x400fbf:  mov rax, qword ptr [r13+rax*8]
  0x400fc7:  movsxd rdx, dword ptr [r12+0xc]
  0x400fcf:  mov rdx, qword ptr [r13+rdx*8]
  0x400fd7:  movd xmm0, eax
  0x400fdc:  movd eax, xmm0
  0x400fe1:  mov rdx, 0x7f800000
  0x400fe8:  and rax, rdx
  0x400feb:  cmp rax, rdx
  0x400fee:  setne al
  0x400ff2:  movzx rax, al
  0x400ff6:  movsxd rcx, dword ptr [r12+0x4]
  0x400ffe:  mov qword ptr [r13+rcx*8], rax
  0x401006:  add r12, 0x10
  0x40100d:  movzx rax, byte ptr [r12]
  0x401016:  jmp qword ptr [r14+rax*8]

op45:  ; Runner.NativeFPOp.isFinite (Runner.FPFormat.f64) d a b
  0x40101e:  movsxd rax, dword ptr [r12+0x8]
  0x401026:  mov rax, qword ptr [r13+rax*8]
  0x40102e:  movsxd rdx, dword ptr [r12+0xc]
  0x401036:  mov rdx, qword ptr [r13+rdx*8]
  0x40103e:  mov rdx, 0x7ff0
  0x401045:  mov rcx, 0x30
  0x40104c:  shl rdx, cl
  0x40104f:  and rax, rdx
  0x401052:  cmp rax, rdx
  0x401055:  setne al
  0x401059:  movzx rax, al
  0x40105d:  movsxd rcx, dword ptr [r12+0x4]
  0x401065:  mov qword ptr [r13+rcx*8], rax
  0x40106d:  add r12, 0x10
  0x401074:  movzx rax, byte ptr [r12]
  0x40107d:  jmp qword ptr [r14+rax*8]

op46:  ; Runner.NativeFPOp.fromInt64 (Runner.FPFormat.f32) d a b
  0x401085:  movsxd rax, dword ptr [r12+0x8]
  0x40108d:  mov rax, qword ptr [r13+rax*8]
  0x401095:  movsxd rdx, dword ptr [r12+0xc]
  0x40109d:  mov rdx, qword ptr [r13+rdx*8]
  0x4010a5:  cvtsi2ss xmm0, rax
  0x4010aa:  movd eax, xmm0
  0x4010af:  movsxd rcx, dword ptr [r12+0x4]
  0x4010b7:  mov qword ptr [r13+rcx*8], rax
  0x4010bf:  add r12, 0x10
  0x4010c6:  movzx rax, byte ptr [r12]
  0x4010cf:  jmp qword ptr [r14+rax*8]

op47:  ; Runner.NativeFPOp.fromInt64 (Runner.FPFormat.f64) d a b
  0x4010d7:  movsxd rax, dword ptr [r12+0x8]
  0x4010df:  mov rax, qword ptr [r13+rax*8]
  0x4010e7:  movsxd rdx, dword ptr [r12+0xc]
  0x4010ef:  mov rdx, qword ptr [r13+rdx*8]
  0x4010f7:  cvtsi2sd xmm0, rax
  0x4010fc:  movq rax, xmm0
  0x401101:  movsxd rcx, dword ptr [r12+0x4]
  0x401109:  mov qword ptr [r13+rcx*8], rax
  0x401111:  add r12, 0x10
  0x401118:  movzx rax, byte ptr [r12]
  0x401121:  jmp qword ptr [r14+rax*8]

op48:  ; Runner.NativeFPOp.fromUInt64 (Runner.FPFormat.f32) d a b
  0x401129:  movsxd rax, dword ptr [r12+0x8]
  0x401131:  mov rax, qword ptr [r13+rax*8]
  0x401139:  movsxd rdx, dword ptr [r12+0xc]
  0x401141:  mov rdx, qword ptr [r13+rdx*8]
  0x401149:  test rax, rax
  0x40114c:  js 0x401161
  0x401152:  cvtsi2ss xmm0, rax
  0x401157:  movd eax, xmm0
  0x40115c:  jmp 0x401187
  0x401161:  mov rsi, rax
  0x401164:  and rsi, 0x1
  0x40116b:  mov rcx, 0x1
  0x401172:  shr rax, cl
  0x401175:  or rax, rsi
  0x401178:  cvtsi2ss xmm0, rax
  0x40117d:  addss xmm0, xmm0
  0x401182:  movd eax, xmm0
  0x401187:  movsxd rcx, dword ptr [r12+0x4]
  0x40118f:  mov qword ptr [r13+rcx*8], rax
  0x401197:  add r12, 0x10
  0x40119e:  movzx rax, byte ptr [r12]
  0x4011a7:  jmp qword ptr [r14+rax*8]

op49:  ; Runner.NativeFPOp.fromUInt64 (Runner.FPFormat.f64) d a b
  0x4011af:  movsxd rax, dword ptr [r12+0x8]
  0x4011b7:  mov rax, qword ptr [r13+rax*8]
  0x4011bf:  movsxd rdx, dword ptr [r12+0xc]
  0x4011c7:  mov rdx, qword ptr [r13+rdx*8]
  0x4011cf:  test rax, rax
  0x4011d2:  js 0x4011e7
  0x4011d8:  cvtsi2sd xmm0, rax
  0x4011dd:  movq rax, xmm0
  0x4011e2:  jmp 0x40120d
  0x4011e7:  mov rsi, rax
  0x4011ea:  and rsi, 0x1
  0x4011f1:  mov rcx, 0x1
  0x4011f8:  shr rax, cl
  0x4011fb:  or rax, rsi
  0x4011fe:  cvtsi2sd xmm0, rax
  0x401203:  addsd xmm0, xmm0
  0x401208:  movq rax, xmm0
  0x40120d:  movsxd rcx, dword ptr [r12+0x4]
  0x401215:  mov qword ptr [r13+rcx*8], rax
  0x40121d:  add r12, 0x10
  0x401224:  movzx rax, byte ptr [r12]
  0x40122d:  jmp qword ptr [r14+rax*8]

op50:  ; Runner.NativeFPOp.toInt64 (Runner.FPFormat.f32) d a b
  0x401235:  movsxd rax, dword ptr [r12+0x8]
  0x40123d:  mov rax, qword ptr [r13+rax*8]
  0x401245:  movsxd rdx, dword ptr [r12+0xc]
  0x40124d:  mov rdx, qword ptr [r13+rdx*8]
  0x401255:  movd xmm0, eax
  0x40125a:  movd eax, xmm0
  0x40125f:  mov rsi, rax
  0x401262:  mov rdx, 0x1
  0x401269:  mov rcx, 0x1f
  0x401270:  shl rdx, cl
  0x401273:  xor rdx, -0x1
  0x40127a:  and rsi, rdx
  0x40127d:  mov rdx, 0x7f800000
  0x401284:  cmp rdx, rsi
  0x401287:  jb 0x4012ee
  0x40128d:  mov rdx, 0x5f000000
  0x401294:  cmp rsi, rdx
  0x401297:  jb 0x4012df
  0x40129d:  mov rdi, rax
  0x4012a0:  mov rcx, 0x1f
  0x4012a7:  shr rdi, cl
  0x4012aa:  and rdi, 0x1
  0x4012b1:  test rdi, rdi
  0x4012b4:  mov rax, 0x1
  0x4012bb:  mov rcx, 0x3f
  0x4012c2:  shl rax, cl
  0x4012c5:  test rdi, rdi
  0x4012c8:  jne 0x4012da
  0x4012ce:  sub rax, 0x1
  0x4012d5:  jmp 0x4012da
  0x4012da:  jmp 0x4012e9
  0x4012df:  movd xmm0, eax
  0x4012e4:  cvttss2si rax, xmm0
  0x4012e9:  jmp 0x4012f5
  0x4012ee:  mov rax, 0x0
  0x4012f5:  movsxd rcx, dword ptr [r12+0x4]
  0x4012fd:  mov qword ptr [r13+rcx*8], rax
  0x401305:  add r12, 0x10
  0x40130c:  movzx rax, byte ptr [r12]
  0x401315:  jmp qword ptr [r14+rax*8]

op51:  ; Runner.NativeFPOp.toInt64 (Runner.FPFormat.f64) d a b
  0x40131d:  movsxd rax, dword ptr [r12+0x8]
  0x401325:  mov rax, qword ptr [r13+rax*8]
  0x40132d:  movsxd rdx, dword ptr [r12+0xc]
  0x401335:  mov rdx, qword ptr [r13+rdx*8]
  0x40133d:  mov rsi, rax
  0x401340:  mov rdx, 0x1
  0x401347:  mov rcx, 0x3f
  0x40134e:  shl rdx, cl
  0x401351:  xor rdx, -0x1
  0x401358:  and rsi, rdx
  0x40135b:  mov rdx, 0x7ff0
  0x401362:  mov rcx, 0x30
  0x401369:  shl rdx, cl
  0x40136c:  cmp rdx, rsi
  0x40136f:  jb 0x4013e0
  0x401375:  mov rdx, 0x43e0
  0x40137c:  mov rcx, 0x30
  0x401383:  shl rdx, cl
  0x401386:  cmp rsi, rdx
  0x401389:  jb 0x4013d1
  0x40138f:  mov rdi, rax
  0x401392:  mov rcx, 0x3f
  0x401399:  shr rdi, cl
  0x40139c:  and rdi, 0x1
  0x4013a3:  test rdi, rdi
  0x4013a6:  mov rax, 0x1
  0x4013ad:  mov rcx, 0x3f
  0x4013b4:  shl rax, cl
  0x4013b7:  test rdi, rdi
  0x4013ba:  jne 0x4013cc
  0x4013c0:  sub rax, 0x1
  0x4013c7:  jmp 0x4013cc
  0x4013cc:  jmp 0x4013db
  0x4013d1:  movq xmm0, rax
  0x4013d6:  cvttsd2si rax, xmm0
  0x4013db:  jmp 0x4013e7
  0x4013e0:  mov rax, 0x0
  0x4013e7:  movsxd rcx, dword ptr [r12+0x4]
  0x4013ef:  mov qword ptr [r13+rcx*8], rax
  0x4013f7:  add r12, 0x10
  0x4013fe:  movzx rax, byte ptr [r12]
  0x401407:  jmp qword ptr [r14+rax*8]

op52:  ; Runner.NativeFPOp.toUInt64 (Runner.FPFormat.f32) d a b
  0x40140f:  movsxd rax, dword ptr [r12+0x8]
  0x401417:  mov rax, qword ptr [r13+rax*8]
  0x40141f:  movsxd rdx, dword ptr [r12+0xc]
  0x401427:  mov rdx, qword ptr [r13+rdx*8]
  0x40142f:  movd xmm0, eax
  0x401434:  movd eax, xmm0
  0x401439:  mov rsi, rax
  0x40143c:  mov rdx, 0x1
  0x401443:  mov rcx, 0x1f
  0x40144a:  shl rdx, cl
  0x40144d:  xor rdx, -0x1
  0x401454:  and rsi, rdx
  0x401457:  mov rdx, 0x7f800000
  0x40145e:  cmp rdx, rsi
  0x401461:  jb 0x4014ff
  0x401467:  mov rdi, rax
  0x40146a:  mov rcx, 0x1f
  0x401471:  shr rdi, cl
  0x401474:  and rdi, 0x1
  0x40147b:  test rdi, rdi
  0x40147e:  jne 0x4014f3
  0x401484:  mov rdx, 0x5f800000
  0x40148b:  cmp rsi, rdx
  0x40148e:  jb 0x4014a0
  0x401494:  mov rax, -0x1
  0x40149b:  jmp 0x4014ee
  0x4014a0:  mov rdx, 0x5f000000
  0x4014a7:  cmp rsi, rdx
  0x4014aa:  jb 0x4014e4
  0x4014b0:  movd xmm0, eax
  0x4014b5:  mov rdx, 0x5f000000
  0x4014bc:  movd xmm1, edx
  0x4014c1:  subss xmm0, xmm1
  0x4014c6:  cvttss2si rax, xmm0
  0x4014cb:  mov rdx, 0x1
  0x4014d2:  mov rcx, 0x3f
  0x4014d9:  shl rdx, cl
  0x4014dc:  or rax, rdx
  0x4014df:  jmp 0x4014ee
  0x4014e4:  movd xmm0, eax
  0x4014e9:  cvttss2si rax, xmm0
  0x4014ee:  jmp 0x4014fa
  0x4014f3:  mov rax, 0x0
  0x4014fa:  jmp 0x401506
  0x4014ff:  mov rax, 0x0
  0x401506:  movsxd rcx, dword ptr [r12+0x4]
  0x40150e:  mov qword ptr [r13+rcx*8], rax
  0x401516:  add r12, 0x10
  0x40151d:  movzx rax, byte ptr [r12]
  0x401526:  jmp qword ptr [r14+rax*8]

op53:  ; Runner.NativeFPOp.toUInt64 (Runner.FPFormat.f64) d a b
  0x40152e:  movsxd rax, dword ptr [r12+0x8]
  0x401536:  mov rax, qword ptr [r13+rax*8]
  0x40153e:  movsxd rdx, dword ptr [r12+0xc]
  0x401546:  mov rdx, qword ptr [r13+rdx*8]
  0x40154e:  mov rsi, rax
  0x401551:  mov rdx, 0x1
  0x401558:  mov rcx, 0x3f
  0x40155f:  shl rdx, cl
  0x401562:  xor rdx, -0x1
  0x401569:  and rsi, rdx
  0x40156c:  mov rdx, 0x7ff0
  0x401573:  mov rcx, 0x30
  0x40157a:  shl rdx, cl
  0x40157d:  cmp rdx, rsi
  0x401580:  jb 0x40163c
  0x401586:  mov rdi, rax
  0x401589:  mov rcx, 0x3f
  0x401590:  shr rdi, cl
  0x401593:  and rdi, 0x1
  0x40159a:  test rdi, rdi
  0x40159d:  jne 0x401630
  0x4015a3:  mov rdx, 0x43f0
  0x4015aa:  mov rcx, 0x30
  0x4015b1:  shl rdx, cl
  0x4015b4:  cmp rsi, rdx
  0x4015b7:  jb 0x4015c9
  0x4015bd:  mov rax, -0x1
  0x4015c4:  jmp 0x40162b
  0x4015c9:  mov rdx, 0x43e0
  0x4015d0:  mov rcx, 0x30
  0x4015d7:  shl rdx, cl
  0x4015da:  cmp rsi, rdx
  0x4015dd:  jb 0x401621
  0x4015e3:  movq xmm0, rax
  0x4015e8:  mov rdx, 0x43e0
  0x4015ef:  mov rcx, 0x30
  0x4015f6:  shl rdx, cl
  0x4015f9:  movq xmm1, rdx
  0x4015fe:  subsd xmm0, xmm1
  0x401603:  cvttsd2si rax, xmm0
  0x401608:  mov rdx, 0x1
  0x40160f:  mov rcx, 0x3f
  0x401616:  shl rdx, cl
  0x401619:  or rax, rdx
  0x40161c:  jmp 0x40162b
  0x401621:  movq xmm0, rax
  0x401626:  cvttsd2si rax, xmm0
  0x40162b:  jmp 0x401637
  0x401630:  mov rax, 0x0
  0x401637:  jmp 0x401643
  0x40163c:  mov rax, 0x0
  0x401643:  movsxd rcx, dword ptr [r12+0x4]
  0x40164b:  mov qword ptr [r13+rcx*8], rax
  0x401653:  add r12, 0x10
  0x40165a:  movzx rax, byte ptr [r12]
  0x401663:  jmp qword ptr [r14+rax*8]

op54:  ; Runner.NativeFPOp.widen32 d a b
  0x40166b:  movsxd rax, dword ptr [r12+0x8]
  0x401673:  mov rax, qword ptr [r13+rax*8]
  0x40167b:  movsxd rdx, dword ptr [r12+0xc]
  0x401683:  mov rdx, qword ptr [r13+rdx*8]
  0x40168b:  movd xmm1, eax
  0x401690:  cvtss2sd xmm0, xmm1
  0x401695:  movq rax, xmm0
  0x40169a:  movsxd rcx, dword ptr [r12+0x4]
  0x4016a2:  mov qword ptr [r13+rcx*8], rax
  0x4016aa:  add r12, 0x10
  0x4016b1:  movzx rax, byte ptr [r12]
  0x4016ba:  jmp qword ptr [r14+rax*8]

op55:  ; Runner.NativeFPOp.narrow32 d a b
  0x4016c2:  movsxd rax, dword ptr [r12+0x8]
  0x4016ca:  mov rax, qword ptr [r13+rax*8]
  0x4016d2:  movsxd rdx, dword ptr [r12+0xc]
  0x4016da:  mov rdx, qword ptr [r13+rdx*8]
  0x4016e2:  movq xmm1, rax
  0x4016e7:  cvtsd2ss xmm0, xmm1
  0x4016ec:  movd eax, xmm0
  0x4016f1:  movsxd rcx, dword ptr [r12+0x4]
  0x4016f9:  mov qword ptr [r13+rcx*8], rax
  0x401701:  add r12, 0x10
  0x401708:  movzx rax, byte ptr [r12]
  0x401711:  jmp qword ptr [r14+rax*8]

op56:  ; Runner.NativeFPOp.compare (Runner.FPFormat.f32) d a b
  0x401719:  movsxd rax, dword ptr [r12+0x8]
  0x401721:  mov rax, qword ptr [r13+rax*8]
  0x401729:  movsxd rdx, dword ptr [r12+0xc]
  0x401731:  mov rdx, qword ptr [r13+rdx*8]
  0x401739:  movd xmm0, eax
  0x40173e:  movd xmm1, edx
  0x401743:  ucomiss xmm0, xmm1
  0x401747:  setb al
  0x40174b:  setp dl
  0x40174f:  sete sil
  0x401753:  movzx rax, al
  0x401757:  movzx rdx, dl
  0x40175b:  movzx rsi, sil
  0x40175f:  mov rcx, 0x2
  0x401766:  shl rdx, cl
  0x401769:  mov rcx, 0x6
  0x401770:  shl rsi, cl
  0x401773:  or rax, rdx
  0x401776:  or rax, rsi
  0x401779:  movsxd rcx, dword ptr [r12+0x4]
  0x401781:  mov qword ptr [r13+rcx*8], rax
  0x401789:  add r12, 0x10
  0x401790:  movzx rax, byte ptr [r12]
  0x401799:  jmp qword ptr [r14+rax*8]

op57:  ; Runner.NativeFPOp.compare (Runner.FPFormat.f64) d a b
  0x4017a1:  movsxd rax, dword ptr [r12+0x8]
  0x4017a9:  mov rax, qword ptr [r13+rax*8]
  0x4017b1:  movsxd rdx, dword ptr [r12+0xc]
  0x4017b9:  mov rdx, qword ptr [r13+rdx*8]
  0x4017c1:  movq xmm0, rax
  0x4017c6:  movq xmm1, rdx
  0x4017cb:  ucomisd xmm0, xmm1
  0x4017d0:  setb al
  0x4017d4:  setp dl
  0x4017d8:  sete sil
  0x4017dc:  movzx rax, al
  0x4017e0:  movzx rdx, dl
  0x4017e4:  movzx rsi, sil
  0x4017e8:  mov rcx, 0x2
  0x4017ef:  shl rdx, cl
  0x4017f2:  mov rcx, 0x6
  0x4017f9:  shl rsi, cl
  0x4017fc:  or rax, rdx
  0x4017ff:  or rax, rsi
  0x401802:  movsxd rcx, dword ptr [r12+0x4]
  0x40180a:  mov qword ptr [r13+rcx*8], rax
  0x401812:  add r12, 0x10
  0x401819:  movzx rax, byte ptr [r12]
  0x401822:  jmp qword ptr [r14+rax*8]

op58:  ; Runner.NativeFPOp.truncateInt64 (Runner.FPFormat.f32) d a b
  0x40182a:  movsxd rax, dword ptr [r12+0x8]
  0x401832:  mov rax, qword ptr [r13+rax*8]
  0x40183a:  movsxd rdx, dword ptr [r12+0xc]
  0x401842:  mov rdx, qword ptr [r13+rdx*8]
  0x40184a:  movd xmm0, eax
  0x40184f:  cvttss2si rax, xmm0
  0x401854:  movsxd rcx, dword ptr [r12+0x4]
  0x40185c:  mov qword ptr [r13+rcx*8], rax
  0x401864:  add r12, 0x10
  0x40186b:  movzx rax, byte ptr [r12]
  0x401874:  jmp qword ptr [r14+rax*8]

op59:  ; Runner.NativeFPOp.truncateInt64 (Runner.FPFormat.f64) d a b
  0x40187c:  movsxd rax, dword ptr [r12+0x8]
  0x401884:  mov rax, qword ptr [r13+rax*8]
  0x40188c:  movsxd rdx, dword ptr [r12+0xc]
  0x401894:  mov rdx, qword ptr [r13+rdx*8]
  0x40189c:  movq xmm0, rax
  0x4018a1:  cvttsd2si rax, xmm0
  0x4018a6:  movsxd rcx, dword ptr [r12+0x4]
  0x4018ae:  mov qword ptr [r13+rcx*8], rax
  0x4018b6:  add r12, 0x10
  0x4018bd:  movzx rax, byte ptr [r12]
  0x4018c6:  jmp qword ptr [r14+rax*8]

bad:
  0x4018ce:  ud2

table:  ; 256 handler addresses at 0x4018d0
  dq 0x4018ce  ; opcode 0
  dq 0x4001c2  ; opcode 1
  dq 0x4001f2  ; opcode 2
  dq 0x40022a  ; opcode 3
  dq 0x400275  ; opcode 4
  dq 0x4002c0  ; opcode 5
  dq 0x40030c  ; opcode 6
  dq 0x400359  ; opcode 7
  dq 0x4003a6  ; opcode 8
  dq 0x4003f1  ; opcode 9
  dq 0x40043c  ; opcode 10
  dq 0x400487  ; opcode 11
  dq 0x4004d2  ; opcode 12
  dq 0x40051d  ; opcode 13
  dq 0x400570  ; opcode 14
  dq 0x4005c3  ; opcode 15
  dq 0x400603  ; opcode 16
  dq 0x400643  ; opcode 17
  dq 0x40067b  ; opcode 18
  dq 0x400697  ; opcode 19
  dq 0x4006e4  ; opcode 20
  dq 0x400733  ; opcode 21
  dq 0x400757  ; opcode 22
  dq 0x4007b1  ; opcode 23
  dq 0x40082b  ; opcode 24
  dq 0x4008c6  ; opcode 25
  dq 0x400918  ; opcode 26
  dq 0x40096a  ; opcode 27
  dq 0x4009bd  ; opcode 28
  dq 0x400a19  ; opcode 29
  dq 0x400a75  ; opcode 30
  dq 0x400ad1  ; opcode 31
  dq 0x400b2d  ; opcode 32
  dq 0x400b89  ; opcode 33
  dq 0x400be5  ; opcode 34
  dq 0x400c41  ; opcode 35
  dq 0x400c9d  ; opcode 36
  dq 0x400d03  ; opcode 37
  dq 0x400d5f  ; opcode 38
  dq 0x400dc3  ; opcode 39
  dq 0x400e27  ; opcode 40
  dq 0x400e8b  ; opcode 41
  dq 0x400eef  ; opcode 42
  dq 0x400f53  ; opcode 43
  dq 0x400fb7  ; opcode 44
  dq 0x40101e  ; opcode 45
  dq 0x401085  ; opcode 46
  dq 0x4010d7  ; opcode 47
  dq 0x401129  ; opcode 48
  dq 0x4011af  ; opcode 49
  dq 0x401235  ; opcode 50
  dq 0x40131d  ; opcode 51
  dq 0x40140f  ; opcode 52
  dq 0x40152e  ; opcode 53
  dq 0x40166b  ; opcode 54
  dq 0x4016c2  ; opcode 55
  dq 0x401719  ; opcode 56
  dq 0x4017a1  ; opcode 57
  dq 0x40182a  ; opcode 58
  dq 0x40187c  ; opcode 59
  dq 0x4018ce  ; opcode 60
  dq 0x4018ce  ; opcode 61
  dq 0x4018ce  ; opcode 62
  dq 0x4018ce  ; opcode 63
  dq 0x4018ce  ; opcode 64
  dq 0x4018ce  ; opcode 65
  dq 0x4018ce  ; opcode 66
  dq 0x4018ce  ; opcode 67
  dq 0x4018ce  ; opcode 68
  dq 0x4018ce  ; opcode 69
  dq 0x4018ce  ; opcode 70
  dq 0x4018ce  ; opcode 71
  dq 0x4018ce  ; opcode 72
  dq 0x4018ce  ; opcode 73
  dq 0x4018ce  ; opcode 74
  dq 0x4018ce  ; opcode 75
  dq 0x4018ce  ; opcode 76
  dq 0x4018ce  ; opcode 77
  dq 0x4018ce  ; opcode 78
  dq 0x4018ce  ; opcode 79
  dq 0x4018ce  ; opcode 80
  dq 0x4018ce  ; opcode 81
  dq 0x4018ce  ; opcode 82
  dq 0x4018ce  ; opcode 83
  dq 0x4018ce  ; opcode 84
  dq 0x4018ce  ; opcode 85
  dq 0x4018ce  ; opcode 86
  dq 0x4018ce  ; opcode 87
  dq 0x4018ce  ; opcode 88
  dq 0x4018ce  ; opcode 89
  dq 0x4018ce  ; opcode 90
  dq 0x4018ce  ; opcode 91
  dq 0x4018ce  ; opcode 92
  dq 0x4018ce  ; opcode 93
  dq 0x4018ce  ; opcode 94
  dq 0x4018ce  ; opcode 95
  dq 0x4018ce  ; opcode 96
  dq 0x4018ce  ; opcode 97
  dq 0x4018ce  ; opcode 98
  dq 0x4018ce  ; opcode 99
  dq 0x4018ce  ; opcode 100
  dq 0x4018ce  ; opcode 101
  dq 0x4018ce  ; opcode 102
  dq 0x4018ce  ; opcode 103
  dq 0x4018ce  ; opcode 104
  dq 0x4018ce  ; opcode 105
  dq 0x4018ce  ; opcode 106
  dq 0x4018ce  ; opcode 107
  dq 0x4018ce  ; opcode 108
  dq 0x4018ce  ; opcode 109
  dq 0x4018ce  ; opcode 110
  dq 0x4018ce  ; opcode 111
  dq 0x4018ce  ; opcode 112
  dq 0x4018ce  ; opcode 113
  dq 0x4018ce  ; opcode 114
  dq 0x4018ce  ; opcode 115
  dq 0x4018ce  ; opcode 116
  dq 0x4018ce  ; opcode 117
  dq 0x4018ce  ; opcode 118
  dq 0x4018ce  ; opcode 119
  dq 0x4018ce  ; opcode 120
  dq 0x4018ce  ; opcode 121
  dq 0x4018ce  ; opcode 122
  dq 0x4018ce  ; opcode 123
  dq 0x4018ce  ; opcode 124
  dq 0x4018ce  ; opcode 125
  dq 0x4018ce  ; opcode 126
  dq 0x4018ce  ; opcode 127
  dq 0x4018ce  ; opcode 128
  dq 0x4018ce  ; opcode 129
  dq 0x4018ce  ; opcode 130
  dq 0x4018ce  ; opcode 131
  dq 0x4018ce  ; opcode 132
  dq 0x4018ce  ; opcode 133
  dq 0x4018ce  ; opcode 134
  dq 0x4018ce  ; opcode 135
  dq 0x4018ce  ; opcode 136
  dq 0x4018ce  ; opcode 137
  dq 0x4018ce  ; opcode 138
  dq 0x4018ce  ; opcode 139
  dq 0x4018ce  ; opcode 140
  dq 0x4018ce  ; opcode 141
  dq 0x4018ce  ; opcode 142
  dq 0x4018ce  ; opcode 143
  dq 0x4018ce  ; opcode 144
  dq 0x4018ce  ; opcode 145
  dq 0x4018ce  ; opcode 146
  dq 0x4018ce  ; opcode 147
  dq 0x4018ce  ; opcode 148
  dq 0x4018ce  ; opcode 149
  dq 0x4018ce  ; opcode 150
  dq 0x4018ce  ; opcode 151
  dq 0x4018ce  ; opcode 152
  dq 0x4018ce  ; opcode 153
  dq 0x4018ce  ; opcode 154
  dq 0x4018ce  ; opcode 155
  dq 0x4018ce  ; opcode 156
  dq 0x4018ce  ; opcode 157
  dq 0x4018ce  ; opcode 158
  dq 0x4018ce  ; opcode 159
  dq 0x4018ce  ; opcode 160
  dq 0x4018ce  ; opcode 161
  dq 0x4018ce  ; opcode 162
  dq 0x4018ce  ; opcode 163
  dq 0x4018ce  ; opcode 164
  dq 0x4018ce  ; opcode 165
  dq 0x4018ce  ; opcode 166
  dq 0x4018ce  ; opcode 167
  dq 0x4018ce  ; opcode 168
  dq 0x4018ce  ; opcode 169
  dq 0x4018ce  ; opcode 170
  dq 0x4018ce  ; opcode 171
  dq 0x4018ce  ; opcode 172
  dq 0x4018ce  ; opcode 173
  dq 0x4018ce  ; opcode 174
  dq 0x4018ce  ; opcode 175
  dq 0x4018ce  ; opcode 176
  dq 0x4018ce  ; opcode 177
  dq 0x4018ce  ; opcode 178
  dq 0x4018ce  ; opcode 179
  dq 0x4018ce  ; opcode 180
  dq 0x4018ce  ; opcode 181
  dq 0x4018ce  ; opcode 182
  dq 0x4018ce  ; opcode 183
  dq 0x4018ce  ; opcode 184
  dq 0x4018ce  ; opcode 185
  dq 0x4018ce  ; opcode 186
  dq 0x4018ce  ; opcode 187
  dq 0x4018ce  ; opcode 188
  dq 0x4018ce  ; opcode 189
  dq 0x4018ce  ; opcode 190
  dq 0x4018ce  ; opcode 191
  dq 0x4018ce  ; opcode 192
  dq 0x4018ce  ; opcode 193
  dq 0x4018ce  ; opcode 194
  dq 0x4018ce  ; opcode 195
  dq 0x4018ce  ; opcode 196
  dq 0x4018ce  ; opcode 197
  dq 0x4018ce  ; opcode 198
  dq 0x4018ce  ; opcode 199
  dq 0x4018ce  ; opcode 200
  dq 0x4018ce  ; opcode 201
  dq 0x4018ce  ; opcode 202
  dq 0x4018ce  ; opcode 203
  dq 0x4018ce  ; opcode 204
  dq 0x4018ce  ; opcode 205
  dq 0x4018ce  ; opcode 206
  dq 0x4018ce  ; opcode 207
  dq 0x4018ce  ; opcode 208
  dq 0x4018ce  ; opcode 209
  dq 0x4018ce  ; opcode 210
  dq 0x4018ce  ; opcode 211
  dq 0x4018ce  ; opcode 212
  dq 0x4018ce  ; opcode 213
  dq 0x4018ce  ; opcode 214
  dq 0x4018ce  ; opcode 215
  dq 0x4018ce  ; opcode 216
  dq 0x4018ce  ; opcode 217
  dq 0x4018ce  ; opcode 218
  dq 0x4018ce  ; opcode 219
  dq 0x4018ce  ; opcode 220
  dq 0x4018ce  ; opcode 221
  dq 0x4018ce  ; opcode 222
  dq 0x4018ce  ; opcode 223
  dq 0x4018ce  ; opcode 224
  dq 0x4018ce  ; opcode 225
  dq 0x4018ce  ; opcode 226
  dq 0x4018ce  ; opcode 227
  dq 0x4018ce  ; opcode 228
  dq 0x4018ce  ; opcode 229
  dq 0x4018ce  ; opcode 230
  dq 0x4018ce  ; opcode 231
  dq 0x4018ce  ; opcode 232
  dq 0x4018ce  ; opcode 233
  dq 0x4018ce  ; opcode 234
  dq 0x4018ce  ; opcode 235
  dq 0x4018ce  ; opcode 236
  dq 0x4018ce  ; opcode 237
  dq 0x4018ce  ; opcode 238
  dq 0x4018ce  ; opcode 239
  dq 0x4018ce  ; opcode 240
  dq 0x4018ce  ; opcode 241
  dq 0x4018ce  ; opcode 242
  dq 0x4018ce  ; opcode 243
  dq 0x4018ce  ; opcode 244
  dq 0x4018ce  ; opcode 245
  dq 0x4018ce  ; opcode 246
  dq 0x4018ce  ; opcode 247
  dq 0x4018ce  ; opcode 248
  dq 0x4018ce  ; opcode 249
  dq 0x4018ce  ; opcode 250
  dq 0x4018ce  ; opcode 251
  dq 0x4018ce  ; opcode 252
  dq 0x4018ce  ; opcode 253
  dq 0x4018ce  ; opcode 254
  dq 0x4018ce  ; opcode 255

mxcsr:  ; readonly control at 0x4020d0
  dd 0x1f80
