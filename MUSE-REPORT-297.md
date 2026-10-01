# Muse Report 297: Independent review of candidate 279 (X86/Codec.lean)

Lane 297, independent candidate review. Reviewed ONLY the pinned snapshot
`.tmp/review/author-279/` (SNAPSHOT.json: author 279, HEAD
`73e0563f5dbb431b3579ca856a9e6d0d2096846e`, base `9147c7a7…`, clean true)
against OWNER-TASK.md, `dokumente/x86/BYTE-PILOT.md`, and the existing
`grammatik/Grammatik/X86/Typen.lean` in this clone. No other clone read,
no source edits. Method: full read of the 806-line snapshot Codec.lean,
independent `./lean-probe` of the snapshot file (0 errors, axioms match),
and GNU objdump disassembly of all 10 pinned byte strings.

## Findings

1. TARGET statement exact: `roundtrip (b : Befehl) (suffix : List Byte) :
   decode (encode b ++ suffix) = some (⟨b, (encode b).length⟩, suffix)`
   (snapshot lines 561-563). All 14 `Befehl` constructors have encode arms,
   per-constructor round-trip lemmas, and cases in `roundtrip`. No added
   premise, no weakened conclusion.
2. Decoder parses bytes (first-byte dispatch, REX/opcode/ModRM/SIB matching,
   LE reassembly via `parseLe32`/`parseLe64`); the decode region (lines
   313-453) contains no reference to `encode` and no instruction enumeration.
   Register/condition recovery goes through `codeReg`/`codeCond` with generic
   inverses `codeReg_regCode`/`codeCond_condCode` (both axiom-free, `cases+rfl`).
3. Contract match verified arm by arm against BYTE-PILOT.md: REX.W+R/B layout
   (`72+4*rh+bh`), opcodes B8+/89/01/29/31/39/8B/E9/0F80+E8/50+/58+/C3,
   ModRM mod=3 (`192+…`) / mod=2 (`128+…`), SIB 36 iff base%8=4, mod=2 always
   (rbp/r13 real bases, never RIP-relative), LE immediates/displacements.
   Decode lengths (10/3/8/7/5/6/2/1) equal the encode lengths; length values
   rechecked on both sides, not just round-tripped.
4. Pins independently confirmed with local GNU objdump 2.47 (binary decode,
   no assembly involved): `49 B8 …` = movabs r8; `4D 01 F9` = add r9,r15
   (direction r/m+=reg correct for opcode 01 with reg=r15, rm=r9);
   `48 8B 84 24 10…` = mov [rsp+16],rax; `49 89 94 24 …` = mov [r12],rdx;
   `48 8B 8D …` = mov [rbp],rcx; `4D 89 85 01…` = mov [r13+1],r8;
   `E9 FB FF FF FF` = jmp -5 (lands on 0); `41 50`/`41 5F`/`C3` =
   push r8/pop r15/ret. All required shapes present (r8 imm, extended-reg
   arith, rsp+r12 SIB, rbp+r13 disp32, negative disp, high push+pop, RET).
5. Refusals: 15 `decode_nichts_*` theorems (empty, lone REX/0F/41 prefixes,
   truncated disp/SIB, unknown opcode 255, REX.X, missing REX.W, mod=0,
   reg-direct load, wrong SIB, short branch, 66 prefix, non-branch 0F
   second byte), each `rfl` (kernel-computed). Corrupted-opcode and
   truncated-prefix classes both covered.
6. Axioms (own probe): inverses + `encode_len` axiom-free; LE round trips
   `[propext, Quot.sound]`; `roundtrip`/`roundtrip_len_ok` exactly the
   standard trio; pins/refusals `[propext]`. No `sorry`/`admit`/`axiom`/
   `native_decide`/`unsafe` (grep clean). CUTS block + `#print axioms`
   present. `encode_len` proves 1..15 for every constructor.
7. File set: new `Codec.lean` + exactly one additive umbrella import line in
   `Grammatik.lean` + report. No new `Befehl`/state (only `def`/`theorem`),
   no Typen/goal/checker/emit/number changes. No hardware, source, TSO, cost,
   or ABI claim made; report disclaims them explicitly.
8. Honestly labelled OPEN (not defects): arbitrary-input length soundness
   (proved only for round-trip instances via `roundtrip_len_ok`), refusal-set
   vs hardware correspondence, whole-image coverage. No `_zeuge` needed:
   no premise quantifies over source syntax (`Vertrag`/`Stmt`/…), no ZEUGE
   line in the owner task, no source-syntax theorem.
9. Minor report inaccuracy (not in the proofs): MUSE-REPORT-279.md claims
   "Pins (22 …)" but the module contains 20 `pin_*` theorems (9 pairs + ret
   pair); all task-required shapes are present, so nothing is missing.
   Suggest fixing the count at merge; no re-proof needed.

No counterexample found; every report claim I could check against code,
probe output, or objdump held (up to the pin-count typo in item 9).

CANDIDATE: 279 73e0563f5dbb431b3579ca856a9e6d0d2096846e
VERDICT: ACCEPT
