# MUSE-REPORT-908: Exact review of author 758 (disp0 memory form)

CANDIDATE: 758 2b91001c617932fb0e372d37a0dd7214986f6e8d
VERDICT: ACCEPT

## Scope and method

- Verified clone `/home/simon/Dokumente/gabbro-muse/a908`, branch `muse/908`, clean (`git status --short` empty). Owned only this file; no source or live controls touched.
- Reviewed exact pinned snapshot from `.tmp/review/SNAPSHOT.json` (author 758, head `2b91001c...`, base `23b9a42f...`, files `MUSE-REPORT-758.md`, `grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/Disp0Frame.lean`, clean true) against `.tmp/review/author-758/OWNER-TASK.md`, `PATCH.diff`, `MUSE-REPORT-758.md`, `BUILD-EVIDENCE.json`, and the snapshot `Disp0Frame.lean` (316 lines).
- Independently inspected accepted base interfaces (`AddressEncoding.lean` §§1-15, `Codec.lean` regCode/regLow/rexByte, `Byteschritt.lean` geholt, `Speicher.lean` schreibbar8/write64/read64, `Ausfuehrung.lean` laengeOk/ripNach/zeugeFlags) and official local manuals (`.tmp/HARDWARE-REFERENCES/REFERENCES.json`: Intel SDM combined Vols. 1-4, edition 325462-093US Sep 2026; `intel-instruction-reference.txt`: Sec. 3.3.7.1 Canonical Addressing at line 4220, Table 2-2 32-Bit Addressing Forms with ModR/M at lines 32890/33532).
- Reproduced with queued wrapper: `./lean-probe .tmp/review/author-758/grammatik/Grammatik/X86/Disp0Frame.lean` => `== 0 error(s) in the COMPLETE output; exit 0`, axiom dump `[propext]` or `[propext, Quot.sound]` per theorem, matching BUILD-EVIDENCE final entry. Full `./lean-bau` was not re-run in this clone (integrating the candidate would violate report-only ownership); BUILD-EVIDENCE records `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`, `Build completed successfully (483 jobs)`.

## Architecture verification (not just Lean green)

- Byte forms: witness `mov [rbx], rax` = `[72, 137, 3]` is correct: REX.W 72 (rv=0, no extensions needed), opcode 0x89 store, ModRM 3 = mod00 reg000(r/m src rax) r/m011(base rbx). Decodes via accepted `decodeStoreIdx`/`parseAdrTail 0 0 0 [3]` to `(.rax, basisKeinForm .rbx, [])`, consistent with accepted pin `rundweg_basisKein`.
- SIB rule: `encodeAdr` (AddressEncoding lines 440-449) emits SIB iff `regLow b == 4`. regCode gives rsp=4, r12=12 (low 4), rbx=3. Candidate pins `disp0_sib_rsp` exact bytes `[rexByte 0 0, modrmByte 0 0 4, sibByte 0 4 4]` (ModRM mod00/reg000/rm100 SIB-follows; SIB scale00/index100-absent/base100-rsp) and `disp0_sib_r12` length 3 (honestly length-only since REX.B=1), plus `disp0_ohne_sib_rbx` SIB-free 2-byte form. Correct per Intel ModRM/SIB framing.
- rbp/r13 corner: accepted `adrOk` refuses `art=.kein` for `.rbp`/`.r13` (mod=00 r/m=101 is disp32/RIP-relative, never `[rbp]`/`[r13]`); candidate's `disp0_rbp_verweigert`/`disp0_r13_verweigert` (`decide`) and the mod=01 disp8=0 escapes (`disp0_rbp_entkommt`/`disp0_r13_entkommt` via accepted `dispWortArt_d8` + `disp8Wort_null`, computing the bare base) are correct. Intermediate BUILD-EVIDENCE failures on the escape lemmas were repaired before the final green; final proofs use only accepted lemmas.
- Width/REX: REX.W 64-bit store, low registers, no invented extensions. Flags: `mov` store claims no flag effect and none is claimed (witness carries `zeugeFlags` without a preservation claim). Operands: source rax, destination `[rbx]`, no implicit operands; RIP 4096 -> 4099 past the 3 actual bytes (`disp0Wit_rip`).
- Pre-fault effects: `adrStoreSchritt` = decode fetched window -> `laengeOk` -> `write64` permission check -> `none` on failure; dark-memory refusal (`disp0Wit_dunkel_verweigert`) proves no partial state on refusal. No invented pre-fault store.
- Permissions/order: 8-byte footprint via accepted `schreibbar8` + `fussZugelassen` (canonical + no-wrap + per-byte rights); connection theorem additionally pins `fussZugelassen ... = true` via `kanonisch48_8192`. Sequential per-byte only; CUTS explicitly leaves tearing/visibility open. No TSO/atomicity claim (no LOCK form), no feature/MXCSR/interrupt gate needed for an integer store and none claimed. Canonical execution via accepted fetched steps over actual executable memory with execute-only code / read-write-only data separation.
- No invented determinism: undefined hardware state is not zeroed/ignored; all computation is `decide`/`simp` over accepted definitions. No new register/memory/decoder/arithmetic/source model; `parseAdrTail` is reused indirectly through `decodeStoreIdx`/`adrStoreSchritt`.

## Premises, witnesses, negatives, weakening

- `Disp0Frame_verbindung` (f, s, n; hf: f = basisKeinForm .rbx; hbase: rbx=8192; hwr: schreibbar8 ... = true) concludes bare-base address, 2-byte tail length (`encodeAdr_laenge_basisKein`), footprint admission, admitted write. All three premises are used (haddr from `disp0_adr_base`+hbase; hwr' from haddr+hwr; hf rewrites each goal). The hardcoded `s.register .rax` write value faithfully mirrors accepted `adrSchreiben_erlaubt` (also rax-specific), not a weakening.
- Joint witness `Disp0Frame_verbindung_zeuge` instantiates all premises on `(basisKeinForm .rbx, disp0WitZustand, 0)` beside the fetched memory-changing run: 42 lands at 8192 from zero (`disp0Wit_speichert` vs `disp0Wit_vorher_null`), whole-word readback (`disp0Wit_liest`), RIP past 3 actual bytes. Non-degenerate reached run through actual bytes. Negative mutations: mod=00 rbp refusal, mod=00 r13 refusal, dark-memory store refusal. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the file (grep hits are only English "admitted/admits"); no `Prop`-typed premise; CUTS lists exactly what is/is not proved (disp0 frame + connection + witness proved; silicon correspondence, disp8/disp32, TSO/GX, source/ABI/loader/entry/budget open).
- Scope clean: PATCH touches only the new module + one `Grammatik.lean` import line + report. No diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no source/checker/Spec/goal/emitter edits, no friend-reserved optimiser files.

## Bounded acceptance

ACCEPT is bounded to: the mod=00 disp0 frame over accepted `AdrForm`/`adrEff`/`encodeAdr`/`adrStoreSchritt`/`fussZugelassen` vocabulary, sequential footprints only. Not accepted as (and not claimed as): silicon correspondence, disp8/disp32 frames, TSO/GX bridge, source correspondence.

## Observations (non-blocking, no repair demanded)

- File header prose names `leaGeholtSchritt` among reused fetched steps but no theorem uses it; comment-only overstatement, proofs do not depend on it.
- Provenance cites "Vol. 2 Table 2-2"; the local text titles it "32-Bit Addressing Forms with the ModR/M Byte" (same ModRM/SIB framing reused in 64-bit mode with REX/RIP extension). Citation precision only; the encoded rows match the accepted parser/encoder pins.

## Open / not claimed

Per file CUTS and report: silicon correspondence; disp8/disp32 frames (accepted API + own lanes); TSO/GX bridge; source/ABI/loader/entry/budget claims. Nothing else open for this lane's task.

## Task correctness note

Nothing in the lane task is believed wrong. The ZEUGE requirement (joint, non-degenerate, memory-changing reached run) is met.
