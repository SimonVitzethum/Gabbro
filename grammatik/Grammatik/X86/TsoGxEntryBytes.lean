/-
  File:      Grammatik/X86/TsoGxEntryBytes.lean
  Subject:   Byte-level entry/call linkage for the start-anchored bridged run.

  Follow-up of lane 1253 (`TsoGxStart.lean`): the prefix there is
  source-level (`RufSchrittG` from `RufStartG`), while
  `PipelineEntry.prolog_lauf` and
  `StackExecution.geholt_verschachtelt_wiederhergestellt` live on the byte
  machine (`Zustand`, `laufBytes`). This module proves the linkage on the
  byte side and names the admission it stands on: the entry sequence
  (`prolog_lauf`: `AbiArgs` to `EnvRepr`) followed by one fetched
  call/push/pop/ret nest (return word below the old top, inner value
  delivered, stack pointer restored) reaches the fragment-head byte state
  with the entry `WorldRep`/`EnvRepr` transported across the two stack
  writes (both slots foreign to every placed slot). The source-level
  prefix (`fragmentKopf_erreichbar`, `startFragment_zeuge`) is reused by
  reference; the joint witness shows both sides reach their head, with the
  call frame written and restored through memory. What is NOT covered is
  refused (guard slot, non-executable return, clobbering prolog) or listed
  in CUTS. No new machine, no new decoder, no silicon claim.
-/
import Grammatik.X86.PipelineEntry
import Grammatik.X86.StackExecution
import Grammatik.X86.TsoGxStart

namespace Gabbro.Grammatik.X86.TsoGxEntryBytes

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineEntry

/-- Both stack slots are foreign to every placed slot: the admission that
    lets the entry representation survive the call frame writes. -/
def StapelLayoutFremd {D : Deklaration} (L : Layout D) (aussen innen : Adresse) : Prop :=
  ∀ (t : D.Tab) (k : Int) (f : D.Feld t) (a0 : Nat),
    L.loc t k f = some a0 → Disjunkt aussen (natAdresse a0) ∧ Disjunkt innen (natAdresse a0)

/-- WORLD SURVIVAL OF ONE FOREIGN WORD STORE: a successful `write64`
    at an address foreign to every placed slot keeps the representation of
    the same world: permissions are unchanged, and every placed slot reads
    through the frame (`read64_rahmen`). -/
theorem worldRep_schreiben_fremd {D : Deklaration} (L : Layout D) (m m' : Speicher)
    (σ : World D) (a : Adresse) (v : Wort)
    (hW : WorldRep L m σ) (hwr : write64 m a v = some m')
    (hf : ∀ (t : D.Tab) (k : Int) (f : D.Feld t) (a0 : Nat),
      L.loc t k f = some a0 → Disjunkt a (natAdresse a0)) :
    WorldRep L m' σ := by
  intro t2 k2 f2 a2 hloc2
  obtain ⟨hok2, hrd2, hwr2, hrep2⟩ := hW t2 k2 f2 a2 hloc2
  refine ⟨hok2, by rw [lesbar8_nach_schreiben m m' _ _ _ hwr]; exact hrd2,
    by rw [schreibbar8_nach_schreiben m m' _ _ _ hwr]; exact hwr2, ?_⟩
  intro lo2 hi2 hT2
  have hrep := hrep2 lo2 hi2 hT2
  unfold RepSlot at hrep ⊢
  rw [read64_rahmen m m' _ _ _ hwr (hf t2 k2 f2 a2 hloc2)]
  exact hrep

/-- THE BYTE ENTRY/CALL PREFIX RUNS: an entry run of `proLen` fetched
    steps (the `prolog_lauf` outcome: memory and stack top kept) followed
    by one fetched call/push/pop/ret nest reaches the fragment-head byte
    state: the stack pointer is restored to the entry top, control is on
    the next-`rip` return word, the inner value is delivered, and every
    permission map is preserved. Every premise is consumed by the accepted
    nested-restoration theorem. -/
theorem eintrittCallPrefix_lauf
    (s0 s1 b1 b2 b3 b4 : Zustand)
    (proLen : Nat) (disp : BitVec 32) (src dst : Register)
    (sc sp sq sr : List Byte)
    (mc mp : Speicher) (vp vr : Wort)
    (hpro : laufBytes proLen s0 = .weiter s1)
    (hrsp0 : s1.register Register.rsp = s0.register Register.rsp)
    (hwinc : StapelGeholt s1 (.call32 disp) sc)
    (hexec : ausfuehrbarN s1.speicher s1.rip
      (encode (.call32 disp)).length = true)
    (hwrc : write64 s1.speicher (s1.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s1.rip (encode (.call32 disp)).length) = some mc)
    (hlesc : lesbar8 s1.speicher
      (s1.register Register.rsp - BitVec.ofNat 64 8) = true)
    (hstepc : schritt ⟨.call32 disp, (encode (.call32 disp)).length⟩ s1 =
      some b1)
    (hwinp : StapelGeholt b1 (.push64 src) sp)
    (hexep : ausfuehrbarN b1.speicher b1.rip
      (encode (.push64 src)).length = true)
    (hwrp : write64 b1.speicher (b1.register Register.rsp - BitVec.ofNat 64 8)
      (b1.register src) = some mp)
    (hlesp : lesbar8 b1.speicher
      (b1.register Register.rsp - BitVec.ofNat 64 8) = true)
    (hstepp : schritt ⟨.push64 src, (encode (.push64 src)).length⟩ b1 =
      some b2)
    (hrdp : read64 b2.speicher (b2.register Register.rsp) = some vp)
    (hstepq : schritt ⟨.pop64 dst, (encode (.pop64 dst)).length⟩ b2 =
      some b3)
    (hdst : dst ≠ Register.rsp)
    (hsrc : src ≠ Register.rsp)
    (hwinq : StapelGeholt b2 (.pop64 dst) sq)
    (hexeq : ausfuehrbarN b2.speicher b2.rip
      (encode (.pop64 dst)).length = true)
    (hrdr : read64 b3.speicher (b3.register Register.rsp) = some vr)
    (hstepr : schritt ⟨.ret, (encode .ret).length⟩ b3 = some b4)
    (hwinr : StapelGeholt b3 .ret sr)
    (hexer : ausfuehrbarN b3.speicher b3.rip
      (encode .ret).length = true)
    (hdis : Disjunkt (s1.register Register.rsp - BitVec.ofNat 64 8)
      (b1.register Register.rsp - BitVec.ofNat 64 8)) :
    laufBytes (proLen + 4) s0 = .weiter b4 ∧
      b4.register Register.rsp = s0.register Register.rsp ∧
      b4.rip = ripNach s1.rip (encode (.call32 disp)).length ∧
      b4.register dst = s1.register src ∧
      b4.speicher.ausfuehrbar = s1.speicher.ausfuehrbar ∧
      b4.speicher.lesbar = s1.speicher.lesbar ∧
      b4.speicher.schreibbar = s1.speicher.schreibbar := by
  obtain ⟨hb1, hb2, hb3, hb4, hrsp, hrip, hval, hexeP, hlesP, hschrP⟩ :=
    geholt_verschachtelt_wiederhergestellt s1 b1 b2 b3 b4 disp src dst sc sp sq sr
      mc mp vp vr hwinc hexec hwrc hlesc hstepc hwinp hexep hwrp hlesp hstepp
      hrdp hstepq hdst hwinq hexeq hrdr hstepr hwinr hexer hdis
  have hrun : laufBytes (proLen + 4) s0 = .weiter b4 := by
    rw [laufBytes_add proLen 4 s0 s1 hpro]
    simp only [laufBytes, hb1, hb2, hb3, hb4]
  have hlenC : laengeOk (encode (.call32 disp)).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have eC := schritt_call32_erfolg ⟨.call32 disp, (encode (.call32 disp)).length⟩
    s1 disp mc hlenC rfl hwrc
  rw [hstepc] at eC
  have hsrc1 : b1.register src = s1.register src := by
    cases eC
    simp [schrittCall, regSet, hsrc]
  exact ⟨hrun, by rw [hrsp, hrsp0], hrip, by rw [hval, hsrc1], hexeP, hlesP, hschrP⟩

/- CUTS (exactly what is NOT proved here):
   - No lowering certificate from the source program `eP` to bytes: the
     identity of the source fragment head with the byte head is OPEN with
     the pipeline owners. Proved here is co-reachability plus transport.
   - No TSO/GX bridge: every fact is sequential over one canonical
     `Speicher`; store buffers and refinement stay with the TSO work.
   - Pilot ISA, one core, model memory, no time (cuts of the reused modules).
-/

#print axioms StapelLayoutFremd

end Gabbro.Grammatik.X86.TsoGxEntryBytes
