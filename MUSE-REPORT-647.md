# Muse Report 647: review of author 646 (two-assignment Block to fetched execution)

## Scope inspected

- Pinned snapshot `.tmp/review/SNAPSHOT.json`: author 646, head d54f3b12f0172badfed6584b6b228f901a4857f8, base 24e625c0, files MUSE-REPORT-646.md, grammatik/Grammatik.lean, grammatik/Grammatik/X86/BlockSequence646.lean.
- Owner task `.tmp/review/author-646/OWNER-TASK.md`, author report, PATCH diff header, BUILD-EVIDENCE.json, and the full 1384-line pinned module bytes (SHA tree via git show, diffed against the review copy: identical).
- Clone/branch verified: /home/simon/Dokumente/gabbro-muse/a647 on muse/647. No source edits made; this report is the only owned file.

## What the author claims

New file BlockSequence646.lean extends accepted senkFrag/senkAssign to a real typed two-assignSlot Block.cons term: senkSeq2 concatenation, senkSeq2_ok plus either-leg refusals, seq2_execBlock ok-chain, main seq2_korrekt deriving the finite lauf run, both RepSlot facts with read-back and the source ok block equation, seq2_fetch fetch-stability composition API from the checked Bild mapping, and a joint non-degenerate witness (12->42, 13->43, 8 fetched byte steps, planted alias/overlap/code-write/range/stopped/bad-byte refusals). CUTS keep the generic laufBytes induction, wider fragments, concurrency, valX86_sound and whole-binary closure OPEN.

## Independent checks

- Vocabulary is real: actual Syntax.Block.cons, Stmt.assignSlot, execStmt/execBlock, senkFrag/senkAssign, repOk/RepSlot/rep_schritt_bleibt, lauf/schritt, geholt/fetchDekodiert/byteschritt/laufBytes, codeFremd_von_abbildung, geladen/wohlgeformt. Imports are the accepted producer modules only; no new IR, no new interpreter, no alternative executor, no edits to accepted producers (Grammatik.lean diff is one import line).
- No forbidden tactics: no sorry/admit/axiom/native_decide/unsafe (the only "admit" substrings are the English word "admitted" in comments). No Prop-typed premise, no intro _ / have _ : discards found.
- Correspondence is derived, not premised: seq2_korrekt takes only single-step checked facts (write64 successes, lesbar8, Disjunkt, register/memory equalities, repOk, evaluated index/value equations, source steps, lowering equations, EnvRepr/Frisch/rsp/base conditions) and derives the lauf run, both RepSlot facts, both read-backs and the execBlock equation via senkung_korrekt, schritt_store64_erfolg, lauf_anhang/lauf_einzeln_gleich, rep_schritt_bleibt, rep_fremd_feld and read64_rahmen. Foreignness in seq2_fetch is derived via codeFremd_von_abbildung from mapping/section/no-wrap premises, with unchanged bytes from the actual store frames. No proof-valued certificate field, no assumed whole run or final equality.
- All premises used: traced each seq2_korrekt premise (hT1/hT2, hOk, hw/hL, hLese/hk/heval, hExec, hsenk/hrenv/hFr/hrsp, hBasis, hsMem/hBaseR/ha, hTgt/hRd, hDis with hk12/hf12, prog/hsenk) into the proof body or the rep_schritt_bleibt calls; seq2_fetch premises each feed the two foreignness derivations, W^X facts, or the chained geholt/fetchDekodiert/code-bytes conclusions.
- Witness is joint and non-degenerate: seq2_korrekt_zeuge invokes seq2_korrekt on the witness declaration and additionally proves slot changes 12->42 and 13->43, changed target bytes on both slots, the fetched 8-step value/memory observations (rax=43, cells 42/43 from zero), and the writer. senkSeq2_ok_zeuge and seq2_execBlock_zeuge likewise carry writer plus memory-changing run. Fetched execution is genuine byteschritt/laufBytes closed by decide over the loaded image, with forged-opcode fetch/decode refusals governing the run. Disjointness is proved arithmetically, not assumed.
- Bounded claim, no inflated closure: the main run is finite lauf over mapped Decodiert; the generic laufBytes lift is explicitly left OPEN in CUTS and the report, with witness bytes by decide and single steps by kanonisch_schritt_ueberein. No TSO/concurrency, hardware, OS/loader, or int->ptr claims. The two-registers-at-zero-displacement shape is an explicit documented fragment restriction.
- Build evidence is credible: BUILD-EVIDENCE.json ends with lean-probe 0 errors and lean-bau 458 jobs green on the pinned tree; axioms printed there are within propext/Classical.choice/Quot.sound (several fewer). Intermediate red probes in the log are development history, not the final state. Per review rules I made no source edits and ran no competing build over the review copy; verification is by pinned-byte inspection plus this evidence.
- One noted non-blocker: the closed = none refusal lemmas carry a free expression variable but no dedicated joint witness, as the author discloses with 599/628 precedent. The task-required refused variants are instead covered by planted decided refusals (alias, overlap, code write, range, leave, forged fetch/decode). Every main generic claim does have its joint witness, so this does not meet the bar for a minimal repair.

## Accepted bounded claim

Two admitted assignSlot statements as one actual Block.cons term lower to the concatenated pilot sequence; the finite lauf run, both RepSlot facts with read-back, and the source ok equation are derived; both data stores preserve fetch/decode/fetched code bytes under the checked mapping; joint witness with two memory-changing stores and fetched observations holds; generic laufBytes induction and anything beyond the stated fragment remain open.

CANDIDATE: 646 d54f3b12f0172badfed6584b6b228f901a4857f8
VERDICT: ACCEPT
