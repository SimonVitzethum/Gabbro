# Canonical pilot byte encoding (wave B)

This contract fixes one ordinary x86-64 encoding for each existing `Befehl`.
It is an implementation contract, not hardware correspondence or full source
validation. The decoder accepts only this canonical subset. All multi-byte
immediates/displacements are little endian; displacement bits are raw int32.
Register codes are rax=0, rcx=1, rdx=2, rbx=3, rsp=4, rbp=5, rsi=6, rdi=7,
r8=8 through r15=15; condition codes follow `Bedingung` order 0 through 15.

- `movImm64 dst v`: REX.W with B=dst/8, opcode B8+dst%8, imm64 (10 bytes).
- Register moves/arithmetic: REX.W with R=src/8, B=dst/8, X=0;
  opcode 89/01/29/31 for mov/add/sub/xor; ModRM C0+8*(src%8)+dst%8.
  `cmpReg64 lhs rhs` uses 39 with rhs in reg and lhs in r/m.
- `load64 dst base d`: REX.W R=dst/8 B=base/8 X=0, opcode 8B,
  ModRM 80+8*(dst%8)+base%8, optional SIB 24 iff base%8=4, disp32.
- `store64 base src d`: same addressing with opcode 89, src in reg.
  mod=10 ALWAYS; rbp/r13 are real bases and never RIP-relative.
  SIB 24 denotes scale=1, no index, rsp/r12 base (REX.X=0).
- `jump32 d`: E9 disp32 (5 bytes).
- `jumpIf32 c d`: 0F (80+code(c)) disp32 (6 bytes).
- `call32 d`: E8 disp32 (5 bytes).
- `push64 src` / `pop64 dst`: 50+r / 58+r for low registers;
  prefix 41 followed by 50+r / 58+r for high registers (1 or 2 bytes).
- `ret`: C3 (1 byte).

No other prefixes, ModRM/SIB modes, address-size overrides, LOCK, REX.X,
legacy high-byte registers, 32-bit operands or short branch forms are admitted.
Decoding returns the first instruction and consumed length plus remaining bytes;
whole-image coverage/control-flow/source/TSO validation are separate obligations.
All lengths are between 1 and 15. A non-canonical but architecturally valid
alternative is outside this pilot and must be refused explicitly.
