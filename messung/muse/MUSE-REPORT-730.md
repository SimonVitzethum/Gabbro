# MUSE-REPORT-730: Full selected SIB/RIP-relative addresses to actual effects

## Task
Close selected full base+index*scale+disp and RIP-relative byte addressing gaps
with a generic checked effective-address adapter binding actual instruction
length/next RIP and canonical register values to real producer access effects.
File: `grammatik/Grammatik/X86/AddressedHardwareExecution.lean` (new, owned),
plus additive `grammatik/Grammatik.lean` import. Nothing else touched.

## What was done
New module `Gabbro.Grammatik.X86.AddressedHardwareExecution` (~710 lines),
reusing accepted producers only (`AddressEncoding` forms/address/decode,
`EffectiveAddress` pilot address, `Speicher` checked access, `LockedOps`
event vocabulary, `LockedInstructionExecution` machine/outcome):

1. **Ordered admission adapter** — `AdrFehler` (unkanonisch/umbruch/
   keinLesen/keinSchreiben), `adrPruefe` (canonical, then no-wrap, then
   per-direction permission). `adrPruefe_gleich_fuss`: success coincides
   exactly with accepted `fussZugelassen` (no second admission model).
   Order lemmas: canonical and wrap refuse before permissions.
2. **Generic addressed access** — `adrLade`/`adrSpeichere` compute `adrEff`
   from canonical registers, admit through `adrPruefe`, perform the REAL
   `read64`/`write64`. Success/refusal equations; `adrLade_basisForm_pilot`
   ties adapter success to the pilot `effAddr` read.
3. **LOCK XADD through full forms** — `decodeLockAdr` matches LOCK +
   canonical REX.W (`rexLockBits`, hence X = 0 as the producer) + 0F + XADD
   and parses the tail with accepted `parseAdrTail`. `lockXaddAdr` mirrors
   the accepted `lockSchrittVoll` XADD arm with `adrEff` target plus
   canonical/no-wrap pre-checks (memory failures stay `speicherFehler`).
   `lockXaddAdr_basisForm`: on canonical/aligned base+disp the adapter
   reaches EXACTLY the producer outcome for every HwProfil/BereitProfil.
   Disjointness both ways on closed bytes (pilot tails refused here,
   scaled/RIP tails refused by `decodeLock`).
4. **Fetched witnesses** — `lockXaddGeholt` decodes the actual fetched
   window with measured length and post-decode RIP. Joint witnesses:
   scaled SIB XADD (`r8+rcx*8=8200`) and RIP-relative XADD
   (`ripNext+4095=8200`), each changing byte 8201 0 -> 32, exchanging
   `r8 := 0`, advancing RIP; plus pure `ripForm_beobachtung`.
5. **Negatives** — mod=3, truncated SIB/disp8, missing LOCK, legacy
   prefix, pilot tails both directions, zero length (all machines),
   buffer-before-address, noncanonical-before-permission (general +
   closed hole-under-full-rights pin), read fault. **Alias pins** —
   zero-index scaled = base form; both witness spellings name 8200.

## Checks
- `./lean-probe` on the file: `== 0 error(s)` (only unused-simp-arg
  linter warnings in §1, harmless).
- `./lean-bau`: `Build completed successfully (482 jobs)` — whole project
  green, no existing theorem weakened.
- `#print axioms` for all 31 main theorems: subsets of
  `[propext, Classical.choice, Quot.sound]` (most `[propext]` or
  `[propext, Quot.sound]`); no `sorry/admit/axiom/native_decide/unsafe`.
- Manual provenance: clone-local Intel SDM 325462-093US (Vol. 1
  §§3.7.5/3.7.5.1, LOCK, XADD) — architecture as stated model, no
  silicon claim.

## Remaining open (see CUTS in file)
REX.X=1 high-index scaled LOCK tails (refused by reused canonical REX
subset); LOCK CMPXCHG through full forms; generic all-pairs round trip
(closed pins per shape class, per producer convention); TSO/GX bridge
(events carry sequential `Fuss` hooks only); no source/ABI/budget claim.

## Possible task issue
None — the task's "lawful adapter or precise obstruction" is met by proof
(`lockXaddAdr_basisForm` + both-direction disjointness pins).
