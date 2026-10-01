# MUSE-REPORT-313: Independent review of candidate 309 (stack frames / ABI memory obligations)

Lane 313, branch `muse/313`, model `opencode-go/muse-spark-1.3-contributor`.
Reviewed ONLY the pinned snapshot in `.tmp/review/author-309/` per `SNAPSHOT.json`
(author 309, HEAD `926f3f773861e3b329d18872fe966e597ad15153`, base
`345627a46732923a03a5f792ff4050b7e3b7c837`, clean): `MUSE-REPORT-309.md`,
`OWNER-TASK.md`, `BUILD-EVIDENCE.json`, `PATCH.diff`, and
`grammatik/Grammatik/X86/Stapel.lean` (673 lines). Canonical `Typen.lean` /
`Speicher.lean` in this clone served as read-only context (the candidate does
not modify them; its snapshot file list contains only the report, the new
module and one umbrella import line). The pinned commit itself is not present
in this clone and was not fetched (no network); file identity was verified
instead: the `PATCH.diff` Stapel body (673 `+` lines) is byte-identical to the
snapshot file (compared programmatically: 673 vs 673, IDENTICAL).

## What was checked

- Ran `./lean-probe` on the exact snapshot file (imports resolve through the
  `grammatik/` lake project): `0 error(s) in the COMPLETE output`. All 34
  `#print axioms` lines confirmed: every theorem depends on at most
  `[propext, Quot.sound]`, several on none — exactly as the author's report
  claims. No `sorry`, `admit`, `axiom` command, `native_decide` or `unsafe`
  (the only `axiom` substring hits are `#print axioms` lines); no `Prop`-typed
  premise; no `intro _` / `have _ :=`; no `Vertrag`/`Stmt`/`Endblock`/`ErgExpr`
  quantification anywhere, so HARD RULE 13's joint source/table-witness gate
  does not trigger (and the owner task names no `ZEUGE:` target).
- Audited premise use of all 34 theorems: every bound, permission, disjointness
  and write hypothesis is consumed (bounds feed `if_pos`/interval lemmas,
  permissions feed the shared `read64_nach_write64`/`write64_*` lemmas,
  `hsep`/`hne` feed the `omega` inequality steps, `hle` feeds every
  `schlitz_toNat`/`OhneUmbruch` step). No conclusion restates a premise; no
  contract parameter is quantified away (there are no contracts here); nothing
  is called a semantics.
- Grounded every shared-lemma call against canonical signatures in this tree:
  `read64_nach_write64 (m m' a v hwr hrd)`, `write64_rahmen`,
  `read64_rahmen`, `disjunkt_von_intervallen`, `lesbar8_nach_schreiben`,
  `writeBytesN_hit`, `addrOff_null`, `OhneUmbruch`, `Disjunkt` — all exist
  with matching shapes. No second register, instruction, state or memory model:
  `Register` is reused from `Typen.lean` and `argReg` follows true System V
  order `rdi rsi rdx rcx r8 r9` with `none` beyond (checked against the
  inductive); `schritt` is never duplicated.
- Witness quality: `rahmen_schreibLese_zeuge` is closed and non-degenerate —
  4-slot frame (`schlitzZahl = 4`), value `42 ≠ 0`, save succeeds, load reads
  back, and the byte observably changes (`ofNat 8 0` vs `wortByte 42 0`).
  Refusal probes are closed `decide` facts (slot 4 of 4 refuses; base `0x2001`
  fails `rahmenOk`). For the conditional `zeuge_liste_probe` I reproduced
  satisfiability in scratch (appended `#eval (...)isSome`, no central edits):
  `sichereListe speicherZeuge rahmenZeuge 0 [11, 22]` evaluates to `some`
  (`true`), so together with the generic `sichereListe_ladeListe_rundreise`
  the list round-trip genuinely fires — not vacuous. Scratch file removed;
  working tree otherwise untouched.
- Report-vs-evidence cross-check: every `MUSE-REPORT-309.md` §1–§7 claim names
  definitions/theorems present in the file with the stated roles (including the
  `Fin 6 -> Register` → if-chain redesign, which matches the `Decidable
  Function.Injective` failure visible in `BUILD-EVIDENCE.json`). Final build
  claims (`lean-bau` exit 0 / 372 jobs, probe 0 errors) match the evidence
  log's last entries; the intermediate red probes in the log are honest
  fixed iterations, not hidden breakage. Umbrella change is exactly one
  `import Grammatik.X86.Stapel` line (current master's tail has since moved on;
  merge-time union, not a candidate defect).
- Boundaries: CUTS in the file matches the report — no decoder/`schritt`/TSO
  bridge, no source correspondence, no assumed-correct caller (every op refuses
  with `none`), callee-save/entry contracts and external byte correspondence
  explicitly OPEN, no image/loader/cost/Linux content. Verified: no stack
  sizes, guard pages, clone flags or syscall numbers appear; addresses come
  from `BitVec.ofNat` of checked Nats, never from source ints. All rules are
  generic over `Rahmen`/`Belegung`/`Speicher`; no name- or example-specific
  case. Two wording nits, not defects: "top inside 64 bits" means
  `spitzeNat ≤ 2^64` (the correct one-past-end bound), and "fresh" slots are
  proved as disjointness (no allocator freshness — correctly out of scope for
  helper obligations per task and CUTS).

## Finding

No material defect. The bounded delivered claim — checked frame extents with
16-byte call-boundary alignment, single-slot and whole-region save/load
round-trips, slot/frame/layout disjointness and register/stack argument/result
carriage over the canonical `Speicher`, with a real memory-changing witness
and refusal probes — is true as stated, the needed checks are green, and the
proof/witness gates hold. CUTS honestly labels what stays OPEN, and the one
mandatory deliverable set (module + import + report + green build) is complete.

CANDIDATE: 309 926f3f773861e3b329d18872fe966e597ad15153
VERDICT: ACCEPT
