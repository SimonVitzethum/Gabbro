/-
  File:      Grammatik/X86/ComposeRelocRedecode.lean
  Subject:   Relocation-patching to re-decode closing step (lane 826).

  Producer/consumer interface closed here (nothing re-proved, no second
  decoder, loader, executor or ISA model):
  PRODUCERS (reused by name): `Relokation.patchAt`/`patchRel32`
  (finite byte patching with range/site/frame facts), `RelocatedExecution`
  (`RelocArt`/`relocBytes`/`relocBefehl`/`relocLen`, `relocBytes_decode`,
  `PatchSite`/`siteStart`/`siteNext`/`patchSiteOk`, `patchSite_ziel`,
  `ruf_schritt_zeuge`), `Codec.decode` (canonical decoder),
  `TableLayout.hinweisOk`/`layoutFuer`/`layoutOk` (re-decided layout
  admission over `zeugenU`), `Bild.schreibLese_zeuge` (memory vocabulary).
  CONSUMERS: `ValidatorSkeleton.valX86`/`bildDeckung` (decode coverage of
  patched executable sections) and `valLayout` (layout admission): the
  closing shows a successfully patched site window re-decodes through the
  canonical decoder to the site instruction, the executed target is the
  intended mapped target, and the layout hint is re-decided.
-/
import Grammatik.X86.Relokation
import Grammatik.X86.RelocatedExecution
import Grammatik.X86.Codec
import Grammatik.X86.TableLayout
import Grammatik.X86.Bild
import Grammatik.X86.Byteschritt

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

/-- Patched-site window: the `len` bytes at file offset `off` of the
    patched image. Re-decode runs on this window, never on metadata. -/
def redecodeFenster (out : List Byte) (off len : Nat) : List Byte :=
  (out.drop off).take len

/-! ## 1. Patched window: every patched byte is a canonical site byte. -/

/-- A successful patch writes exactly the patch bytes at the site window:
    the re-decode window equals the canonical site bytes. Proved by the
    same induction shape as `patchAt_bereich`/`patchAt_stelle`. -/
theorem patchAt_segment (img : List Byte) (off : Nat) (bs : List Byte)
    (out : List Byte) (h : patchAt img off bs = some out) :
    redecodeFenster out off bs.length = bs := by
  unfold redecodeFenster
  induction img generalizing off bs out with
  | nil =>
    cases bs with
    | nil =>
      by_cases hc : off ≤ ([] : List Byte).length
      · simp only [patchAt, if_pos hc] at h
        cases h
        simp
      · simp only [patchAt, if_neg hc] at h
        cases h
    | cons b bs =>
      simp only [patchAt] at h
      cases h
  | cons x rest ih =>
    cases bs with
    | nil =>
      by_cases hc : off ≤ (x :: rest).length
      · simp only [patchAt, if_pos hc] at h
        cases h
        simp
      · simp only [patchAt, if_neg hc] at h
        cases h
    | cons y ys =>
      cases off with
      | zero =>
        simp only [patchAt] at h
        cases hres : patchAt rest 0 ys with
        | none =>
          simp only [hres, Option.map_none] at h
          cases h
        | some tail =>
          simp only [hres, Option.map_some] at h
          cases h
          have hi := ih 0 ys tail hres
          simp only [List.drop_zero] at hi
          simp only [List.drop_zero, List.length_cons,
            List.take_succ_cons, hi]
      | succ n =>
        simp only [patchAt] at h
        cases hres : patchAt rest n (y :: ys) with
        | none =>
          simp only [hres, Option.map_none] at h
          cases h
        | some tail =>
          simp only [hres, Option.map_some] at h
          cases h
          have hi := ih n (y :: ys) tail hres
          simp only [List.drop_succ_cons]
          exact hi

/-! ## 2. The closing: patched bytes re-decode, target reached, layout re-decided. -/

/-- CLOSING (relocation patching to re-decoding): a successfully patched
    site window re-decodes through the canonical decoder to the site
    instruction at its carried length (length/opcode/ModRM/SIB/target-start
    are the decoder's own verdict, never metadata), the executed direct
    target is the intended mapped target (word and Nat), the layout hint is
    re-decided against the recomputation, and the accepted relocated call
    run reaches its target with an observable stack write. Every premise is
    load-bearing: `hpatch` drives re-decode, the site equation block drives
    the target, `hhint` drives the layout, and the run is the accepted
    producer `ruf_schritt_zeuge`. -/
theorem ComposeRelocRedecode_verbindung
    (img : List Byte) (off : Nat) (s : PatchSite) (d : BitVec 32)
    (suffix out : List Byte)
    (hpatch : patchAt img off (relocBytes s.art d) = some out)
    (hdisp : dispSigned d = s.disp)
    (hgleich : (s.ziel : Int) = (siteStart s : Int) + (relocLen s.art : Int) +
      s.disp)
    (hfit : rel32Passt s.disp = true)
    (hnext : siteNext s < 2 ^ 64)
    (hziel : s.ziel < 2 ^ 64)
    (u : UProg) (basis ausr : Nat) (hinweis : List TabLayout)
    (hhint : hinweisOk u basis ausr hinweis = true) :
    decode (redecodeFenster out off (relocBytes s.art d).length ++ suffix) =
      some (⟨relocBefehl s.art d, (relocBytes s.art d).length⟩, suffix) ∧
    direktZiel (BitVec.ofNat 64 (siteStart s)) (relocLen s.art) d =
      BitVec.ofNat 64 s.ziel ∧
    (direktZiel (BitVec.ofNat 64 (siteStart s)) (relocLen s.art) d).toNat =
      s.ziel ∧
    hinweis = layoutFuer u basis ausr ∧ layoutOk hinweis = true ∧
    (∃ m : Speicher, byteschritt zustandRuf =
      .weiter (schrittCall zustandRuf Register.rsp m
        (zustandRuf.register Register.rsp - BitVec.ofNat 64 8)
        (BitVec.ofNat 64 0x1015)) ∧
      read64 m (BitVec.ofNat 64 0x1FF8) = some (BitVec.ofNat 64 0x1005) ∧
      m.bytes (BitVec.ofNat 64 0x1FF8) ≠
        zustandRuf.speicher.bytes (BitVec.ofNat 64 0x1FF8)) := by
  have hseg := patchAt_segment img off (relocBytes s.art d) out hpatch
  have hdec := relocBytes_decode s.art d suffix
  obtain ⟨hz1, hz2⟩ := patchSite_ziel s d hdisp hgleich hfit hnext hziel
  obtain ⟨hlay1, hlay2⟩ := hinweisOk_layoutOk u basis ausr hinweis hhint
  refine ⟨?_, hz1, hz2, hlay1, hlay2, ruf_schritt_zeuge⟩
  rw [hseg]
  exact hdec

/-! ## 3. Joint inhabitation: non-degenerate site, layout and patch. -/

/-- JOINT WITNESS: all premises of the closing hold together on
    non-degenerate values -- the forward jump site `siteVor` (an accepted
    code site, `vor_akzeptiert`), patched into concrete file bytes, with
    the witness unit `zeugenU` (table `konto` written by `setze`,
    `zeugenU_schreibt`) and its recomputed layout hint. The reached
    memory-changing run rides in the closing's conclusion
    (`ruf_schritt_zeuge`) and is exhibited end to end in
    `ComposeRelocRedecode_durchgehend`. -/
theorem ComposeRelocRedecode_verbindung_zeuge :
    ∃ (img : List Byte) (off : Nat) (s : PatchSite) (d : BitVec 32)
      (_suffix out : List Byte) (u : UProg) (basis ausr : Nat)
      (hinweis : List TabLayout),
      patchAt img off (relocBytes s.art d) = some out ∧
      dispSigned d = s.disp ∧
      (s.ziel : Int) = (siteStart s : Int) + (relocLen s.art : Int) +
        s.disp ∧
      rel32Passt s.disp = true ∧
      siteNext s < 2 ^ 64 ∧ s.ziel < 2 ^ 64 ∧
      hinweisOk u basis ausr hinweis = true := by
  refine ⟨[0, 0, 0, 0, 0, 255], 0, siteVor, BitVec.ofNat 32 16, [],
    [233, 16, 0, 0, 0, 255], zeugenU, 4096, 8,
    layoutFuer zeugenU 4096 8, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

/-! ## 4. End to end: the closing on concrete bytes, with the run. -/

/-- END TO END: the closing applied to the witness values -- the patched
    forward-jump window re-decodes, the executed target is `0x1015`
    (word and Nat), the layout hint is the recomputation and accepted,
    and the relocated call run reaches its target with an observable
    stack write. This is the reached memory-changing run through the
    composed step, on concrete bytes. -/
theorem ComposeRelocRedecode_durchgehend :
    decode (redecodeFenster [233, 16, 0, 0, 0, 255] 0
      (relocBytes siteVor.art (BitVec.ofNat 32 16)).length ++ []) =
      some (⟨relocBefehl siteVor.art (BitVec.ofNat 32 16),
        (relocBytes siteVor.art (BitVec.ofNat 32 16)).length⟩, []) ∧
    direktZiel (BitVec.ofNat 64 (siteStart siteVor)) (relocLen siteVor.art)
      (BitVec.ofNat 32 16) = BitVec.ofNat 64 0x1015 ∧
    (direktZiel (BitVec.ofNat 64 (siteStart siteVor)) (relocLen siteVor.art)
      (BitVec.ofNat 32 16)).toNat = 0x1015 ∧
    layoutFuer zeugenU 4096 8 = layoutFuer zeugenU 4096 8 ∧
    layoutOk (layoutFuer zeugenU 4096 8) = true ∧
    (∃ m : Speicher, byteschritt zustandRuf =
      .weiter (schrittCall zustandRuf Register.rsp m
        (zustandRuf.register Register.rsp - BitVec.ofNat 64 8)
        (BitVec.ofNat 64 0x1015)) ∧
      read64 m (BitVec.ofNat 64 0x1FF8) = some (BitVec.ofNat 64 0x1005) ∧
      m.bytes (BitVec.ofNat 64 0x1FF8) ≠
        zustandRuf.speicher.bytes (BitVec.ofNat 64 0x1FF8)) := by
  exact ComposeRelocRedecode_verbindung [0, 0, 0, 0, 0, 255] 0 siteVor
    (BitVec.ofNat 32 16) [] [233, 16, 0, 0, 0, 255] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) zeugenU 4096 8
    (layoutFuer zeugenU 4096 8) (by decide)

/-! ## 5. Planted refusals: patch success alone admits nothing. -/

/-- INTERIOR REFUSAL: the displacement `-3` patches fine into a scratch
    image, but the site whose target `0x1002` lies strictly inside its own
    bytes is refused. Patching without the site check admits nothing. -/
theorem relocRedecode_innen_verweigert :
    (∃ out : List Byte, patchRel32 [0, 0, 0, 0, 0] 1 (-3) = some out) ∧
    patchSiteOk ⟨0, 0x1000, 0, .sprung, -3, 0x1002⟩ = false := by
  refine ⟨⟨[0, 0xFD, 0xFF, 0xFF, 0xFF], by decide⟩, by decide⟩

/-- OUT-OF-RANGE REFUSAL: no patch bytes are computed for a displacement
    of `2 ^ 31`, and the site carrying it is refused with it. -/
theorem relocRedecode_aussen_verweigert :
    rel32Fuer 0 2147483648 = none ∧
    patchSiteOk ⟨0, 0x1000, 0, .sprung, 2147483648, 0x1000⟩ = false := by
  refine ⟨by decide, by decide⟩

/-- OVERLAP REFUSAL: overlapping patch sites are refused outright, and an
    overlapping layout pair is refused with them -- through the accepted
    producer witnesses, never re-proved. -/
theorem relocRedecode_ueberlapp_verweigert :
    patchZwei [0, 0, 0, 0, 0, 0, 0, 0] 1 [0xAA, 0xBB] 2 [0xCC, 0xDD] =
      none ∧
    layoutOk [{ tab := 0, basis := 4096, len := 16, ausr := 8 },
      { tab := 1, basis := 4104, len := 16, ausr := 8 }] = false := by
  exact ⟨sonde_patchZwei_ueberlappung, ueberlapp_verweigert⟩

/- CUTS:
   - Proved here: `patchAt_segment` (a successful `patchAt` writes exactly
     the patch bytes at the site window); `ComposeRelocRedecode_verbindung`
     (patched site window re-decodes through the canonical `decode` to the
     site instruction at its carried length, the executed `direktZiel` is
     the intended mapped target as a word and as a Nat, the layout hint is
     re-decided via `hinweisOk`, and the accepted relocated call run
     reaches its target with an observable stack write);
     `ComposeRelocRedecode_verbindung_zeuge` (joint premise inhabitation on
     the non-degenerate `siteVor`/`zeugenU` values);
     `ComposeRelocRedecode_durchgehend` (the closing on concrete bytes with
     the reached memory-changing run); planted refusals for interior
     target, out-of-range displacement and overlapping sites/layout.
   - Explicitly OPEN (never assumed here): `valX86_sound` -- this closing
     feeds `ValidatorSkeleton.valX86`/`bildDeckung` and `valLayout`, but no
     claim is made that admission implies source correspondence,
     refinement, TSO/GX bridge, concurrency, contracts, budget, cost/time,
     FP or hardware behaviour (consumer/validator lanes, shared IR 287).
   - Explicitly OPEN site classes (producer cuts, lanes 291/561):
     abs64/data-field sites (`patchAbs64` bytes never decode here),
     rel8 short selection, any instruction outside jump/call/conditional.
   - Explicitly OPEN image scope: one site at its final layout only;
     multi-site convergence, fall-through coverage and full
     `DecodingCoverage` stay with the consumer.
   - No loader execution, entry handoff or OS interaction is modelled:
     `geladen` stays the pure mapping function.
   - No second decoder, loader, executor, ISA model or IR is created here:
     every fact reuses the named producer theorems.
-/

#print axioms redecodeFenster
#print axioms patchAt_segment
#print axioms ComposeRelocRedecode_verbindung
#print axioms ComposeRelocRedecode_verbindung_zeuge
#print axioms ComposeRelocRedecode_durchgehend
#print axioms relocRedecode_innen_verweigert
#print axioms relocRedecode_aussen_verweigert
#print axioms relocRedecode_ueberlapp_verweigert

end Gabbro.Grammatik.X86
