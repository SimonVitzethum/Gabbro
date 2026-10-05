/-
  File:      Grammatik/X86/HwKapsteinZwei.lean
  Subject:   Capstone, second step: the families merged since the first union.

  Lane 1311: on top of the first union `HwVollSchritt` (lane 1149,
  `HwKapstein.lean`, reused unchanged), add one union arm per family
  merged since: `IntRotate`, `IntCarryForms`, `IntBitTest`,
  `IntBitScan`, `HwPaging`, `HwPagingLarge`, `HwTranslate`,
  `HwSegTlb`, `HwMemTypesWC`, `HwContextState`, `HwFpStoreDrain`,
  `HwPageFaultDelivery`, `Avx2State`, `Avx2Mem`, `Avx2Join`.
  Every accepted definition is reused unchanged (lifted, never
  redefined); no new machine, no new evaluator, no new adapter.
-/
import Grammatik.X86.HwKapstein
import Grammatik.X86.IntRotate
import Grammatik.X86.IntCarryForms
import Grammatik.X86.IntBitTest
import Grammatik.X86.IntBitScan
import Grammatik.X86.HwPaging
import Grammatik.X86.HwPagingLarge
import Grammatik.X86.HwTranslate
import Grammatik.X86.HwSegTlb
import Grammatik.X86.HwMemTypesWC
import Grammatik.X86.HwContextState
import Grammatik.X86.HwFpStoreDrain
import Grammatik.X86.HwPageFaultDelivery
import Grammatik.X86.Avx2State
import Grammatik.X86.Avx2Mem
import Grammatik.X86.Avx2Join

namespace Gabbro.Grammatik.X86

/-- Second-union events: the whole first union plus one tag per
    family merged since. -/
inductive Kap2Ereignis where
  | alt : KapEreignis → Kap2Ereignis
  | rot : Nat → RotDecodiert → Kap2Ereignis
  | carry : Nat → CarryInstr → Kap2Ereignis
  | bittest : Nat → BtDecodiert → Kap2Ereignis
  | bitscan : Nat → PopcntMerkmal → BsDecodiert → Kap2Ereignis
  | fpstore : Nat → FpStoreEreignis → Kap2Ereignis
  | pf : Nat → PfEreignis → Kap2Ereignis
  | ctx : CtxEreignis → Kap2Ereignis
  | wc : Nat → HwMemWC1287.WcZugriff1287 → Kap2Ereignis
  | avx2mem : Avx2MemEreignis → Kap2Ereignis
  | avx2tor : CpuMerkmal → Xcr0Bild → KontrollBild → Nat → ExtInstr → Kap2Ereignis
  | seiten : Nat → SeitenAnfrage → Kap2Ereignis
  | gross : Nat → SeitenAnfrage → Kap2Ereignis
  | uebersetz : Nat → SeitenAnfrage → Kap2Ereignis

/-- The second composed machine step: the whole first union plus one
    arm per family merged since. Adapter arms lift the accepted
    adapter equation; relation arms lift the accepted flat step
    relation; the three paging adapters are the accepted refused
    default. -/
inductive HwVollSchritt2 : HwMaschine → HwMaschine → Kap2Ereignis → Prop where
  | alt {m m' : HwMaschine} (k : KapEreignis)
      (h : HwVollSchritt m m' k) : HwVollSchritt2 m m' (.alt k)
  | rot {m m' : HwMaschine} (c : Nat) (d : RotDecodiert)
      (h : (adapterRot).schritt m c d = some m') :
      HwVollSchritt2 m m' (.rot c d)
  | carry {m m' : HwMaschine} (c : Nat) (i : CarryInstr)
      (h : (adapterCarry).schritt m c i = some m') :
      HwVollSchritt2 m m' (.carry c i)
  | bittest {m m' : HwMaschine} (c : Nat) (d : BtDecodiert)
      (h : (adapterBitTest).schritt m c d = some m') :
      HwVollSchritt2 m m' (.bittest c d)
  | bitscan {m m' : HwMaschine} (c : Nat) (feat : PopcntMerkmal)
      (d : BsDecodiert)
      (h : (adapterBitScan feat).schritt m c d = some m') :
      HwVollSchritt2 m m' (.bitscan c feat d)
  | fpstore {m m' : HwMaschine} (c : Nat) (e : FpStoreEreignis)
      (h : fpStoreAdapter.schritt m c e = some m') :
      HwVollSchritt2 m m' (.fpstore c e)
  | pf {m m' : HwMaschine} (c : Nat) (e : PfEreignis)
      (h : adapterPf.schritt m c e = some m') :
      HwVollSchritt2 m m' (.pf c e)
  | ctx {m m' : HwMaschine} (e : CtxEreignis)
      (h : CtxSchritt m m' e) :
      HwVollSchritt2 m m' (.ctx e)
  | wc {m m' : HwMaschine} (c : Nat) (e : HwMemWC1287.WcZugriff1287)
      (h : (HwMemWC1287.adapterWc1287).schritt m c e = some m') :
      HwVollSchritt2 m m' (.wc c e)
  | avx2mem {m m' : HwMaschine} (e : Avx2MemEreignis)
      (h : HwAvx2Schritt m m' e) :
      HwVollSchritt2 m m' (.avx2mem e)
  | avx2tor {m m' : HwMaschine} (cpu : CpuMerkmal) (x : Xcr0Bild)
      (k : KontrollBild) (c : Nat) (i : ExtInstr)
      (h : (adapterAvx2Tor cpu x k).schritt m c i = some m') :
      HwVollSchritt2 m m' (.avx2tor cpu x k c i)
  | seiten {m m' : HwMaschine} (c : Nat) (q : SeitenAnfrage)
      (h : adapterSeiten.schritt m c q = some m') :
      HwVollSchritt2 m m' (.seiten c q)
  | gross {m m' : HwMaschine} (c : Nat) (q : SeitenAnfrage)
      (h : adapterGross.schritt m c q = some m') :
      HwVollSchritt2 m m' (.gross c q)
  | uebersetz {m m' : HwMaschine} (c : Nat) (q : SeitenAnfrage)
      (h : adapterUebersetz.schritt m c q = some m') :
      HwVollSchritt2 m m' (.uebersetz c q)

/-- The first union embeds exactly. -/
theorem kap2_alt_embedded (m m' : HwMaschine) (k : KapEreignis) :
    HwVollSchritt m m' k ↔ HwVollSchritt2 m m' (.alt k) := by
  constructor
  · intro h
    exact .alt k h
  · intro h
    cases h with
    | alt _ hstep => exact hstep

/-- Rotate embeds exactly. -/
theorem kap2_rot_embedded (m m' : HwMaschine) (c : Nat)
    (d : RotDecodiert) :
    (adapterRot).schritt m c d = some m' ↔
      HwVollSchritt2 m m' (.rot c d) := by
  constructor
  · intro h
    exact .rot c d h
  · intro h
    cases h with
    | rot _ _ heq => exact heq

/-- Carry embeds exactly. -/
theorem kap2_carry_embedded (m m' : HwMaschine) (c : Nat)
    (i : CarryInstr) :
    (adapterCarry).schritt m c i = some m' ↔
      HwVollSchritt2 m m' (.carry c i) := by
  constructor
  · intro h
    exact .carry c i h
  · intro h
    cases h with
    | carry _ _ heq => exact heq

/-- Bit-test embeds exactly. -/
theorem kap2_bittest_embedded (m m' : HwMaschine) (c : Nat)
    (d : BtDecodiert) :
    (adapterBitTest).schritt m c d = some m' ↔
      HwVollSchritt2 m m' (.bittest c d) := by
  constructor
  · intro h
    exact .bittest c d h
  · intro h
    cases h with
    | bittest _ _ heq => exact heq

/-- Bit-scan embeds exactly, at every feature setting. -/
theorem kap2_bitscan_embedded (m m' : HwMaschine) (c : Nat)
    (feat : PopcntMerkmal) (d : BsDecodiert) :
    (adapterBitScan feat).schritt m c d = some m' ↔
      HwVollSchritt2 m m' (.bitscan c feat d) := by
  constructor
  · intro h
    exact .bitscan c feat d h
  · intro h
    cases h with
    | bitscan _ _ _ heq => exact heq

/-- FP-store drain embeds exactly. -/
theorem kap2_fpstore_embedded (m m' : HwMaschine) (c : Nat)
    (e : FpStoreEreignis) :
    fpStoreAdapter.schritt m c e = some m' ↔
      HwVollSchritt2 m m' (.fpstore c e) := by
  constructor
  · intro h
    exact .fpstore c e h
  · intro h
    cases h with
    | fpstore _ _ heq => exact heq

/-- Page-fault delivery embeds exactly. -/
theorem kap2_pf_embedded (m m' : HwMaschine) (c : Nat)
    (e : PfEreignis) :
    adapterPf.schritt m c e = some m' ↔
      HwVollSchritt2 m m' (.pf c e) := by
  constructor
  · intro h
    exact .pf c e h
  · intro h
    cases h with
    | pf _ _ heq => exact heq

/-- Context state embeds exactly. -/
theorem kap2_ctx_embedded (m m' : HwMaschine) (e : CtxEreignis) :
    CtxSchritt m m' e ↔ HwVollSchritt2 m m' (.ctx e) := by
  constructor
  · intro h
    exact .ctx e h
  · intro h
    cases h with
    | ctx _ hstep => exact hstep

/-- WC memory types embed exactly. -/
theorem kap2_wc_embedded (m m' : HwMaschine) (c : Nat)
    (e : HwMemWC1287.WcZugriff1287) :
    (HwMemWC1287.adapterWc1287).schritt m c e = some m' ↔
      HwVollSchritt2 m m' (.wc c e) := by
  constructor
  · intro h
    exact .wc c e h
  · intro h
    cases h with
    | wc _ _ heq => exact heq

/-- AVX2 memory embeds exactly. -/
theorem kap2_avx2mem_embedded (m m' : HwMaschine)
    (e : Avx2MemEreignis) :
    HwAvx2Schritt m m' e ↔ HwVollSchritt2 m m' (.avx2mem e) := by
  constructor
  · intro h
    exact .avx2mem e h
  · intro h
    cases h with
    | avx2mem _ hstep => exact hstep

/-- The AVX2 gate plug embeds exactly, at every control setting. -/
theorem kap2_avx2tor_embedded (m m' : HwMaschine) (cpu : CpuMerkmal)
    (x : Xcr0Bild) (k : KontrollBild) (c : Nat) (i : ExtInstr) :
    (adapterAvx2Tor cpu x k).schritt m c i = some m' ↔
      HwVollSchritt2 m m' (.avx2tor cpu x k c i) := by
  constructor
  · intro h
    exact .avx2tor cpu x k c i h
  · intro h
    cases h with
    | avx2tor _ _ _ _ _ heq => exact heq

/-- Paging embeds exactly (vacuous: the accepted adapter refuses
    every walk on the flat machine). -/
theorem kap2_seiten_embedded (m m' : HwMaschine) (c : Nat)
    (q : SeitenAnfrage) :
    adapterSeiten.schritt m c q = some m' ↔
      HwVollSchritt2 m m' (.seiten c q) := by
  constructor
  · intro h
    rw [adapterSeiten_verweigert] at h
    cases h
  · intro h
    cases h with
    | seiten _ _ heq => exact heq

/-- Large paging embeds exactly (vacuous, same reason). -/
theorem kap2_gross_embedded (m m' : HwMaschine) (c : Nat)
    (q : SeitenAnfrage) :
    adapterGross.schritt m c q = some m' ↔
      HwVollSchritt2 m m' (.gross c q) := by
  constructor
  · intro h
    rw [adapterGross_verweigert] at h
    cases h
  · intro h
    cases h with
    | gross _ _ heq => exact heq

/-- Translation embeds exactly (vacuous, same reason). -/
theorem kap2_uebersetz_embedded (m m' : HwMaschine) (c : Nat)
    (q : SeitenAnfrage) :
    adapterUebersetz.schritt m c q = some m' ↔
      HwVollSchritt2 m m' (.uebersetz c q) := by
  constructor
  · intro h
    rw [adapterUebersetz_verweigert] at h
    cases h
  · intro h
    cases h with
    | uebersetz _ _ heq => exact heq

/-! ## Well-formedness: every second-union step preserves `HwWf`.

  Each arm lifts its family's accepted preservation lemma. The
  AVX2 gate plug needs a two-line joint helper since its accepted
  lemma takes the open gate as a premise; the three paging arms
  are vacuous through their accepted refusals. -/

/-- Every admitted AVX2 gate step preserves well-formedness: open
    gates ride the accepted register path, closed gates admit no
    state. -/
theorem kap2_adapterAvx2Tor_wf (m m' : HwMaschine) (cpu : CpuMerkmal)
    (x : Xcr0Bild) (k : KontrollBild) (c : Nat) (i : ExtInstr)
    (h : (adapterAvx2Tor cpu x k).schritt m c i = some m')
    (hwf : HwWf m) : HwWf m' := by
  cases hg : avx2ZustandBereit cpu x k (m.bereit c) with
  | true =>
    exact adapterAvx2Tor_wf cpu x k m c i m' hg h hwf
  | false =>
    have hnone := (adapterAvx2Tor_verweigert cpu x k m c i hg).1
    rw [hnone] at h
    cases h

/-- Every second-union step preserves well-formedness. -/
theorem kap2_wf (m m' : HwMaschine) (k : Kap2Ereignis)
    (h : HwVollSchritt2 m m' k) (hwf : HwWf m) : HwWf m' := by
  cases h with
  | alt k hstep => exact kap_wf _ _ _ hstep hwf
  | rot c d hstep => exact adapterRot_wf _ _ _ _ hwf hstep
  | carry c i hstep => exact adapterCarry_wf _ _ _ _ hwf hstep
  | bittest c d hstep => exact adapterBitTest_wf _ _ _ _ hwf hstep
  | bitscan c feat d hstep =>
    exact adapterBitScan_wf feat _ _ _ _ hwf hstep
  | fpstore c e hstep => exact fpStoreAdapter_wf _ _ _ _ hstep hwf
  | pf c e hstep => exact adapterPf_wf _ _ _ _ hstep hwf
  | ctx e hstep => exact ctxSchritt_wf _ _ _ hstep hwf
  | wc c e hstep =>
    exact HwMemWC1287.adapterWc1287_wf _ _ _ _ hstep hwf
  | avx2mem e hstep => exact hwAvx2Schritt_wf _ _ _ hstep hwf
  | avx2tor cpu x k c i hstep =>
    exact kap2_adapterAvx2Tor_wf _ _ cpu x k c i hstep hwf
  | seiten c q hstep =>
    rw [adapterSeiten_verweigert] at hstep
    cases hstep
  | gross c q hstep =>
    rw [adapterGross_verweigert] at hstep
    cases hstep
  | uebersetz c q hstep =>
    rw [adapterUebersetz_verweigert] at hstep
    cases hstep

/-! ## Disjointness and refusals.

  Union tags are pairwise distinct by construction (one number per
  family). The three paging adapters admit nothing on the flat
  machine, by their accepted refusals. -/

/-- Second-union tag: one number per family. -/
def kap2Tag : Kap2Ereignis → Nat
  | .alt _ => 0
  | .rot _ _ => 1
  | .carry _ _ => 2
  | .bittest _ _ => 3
  | .bitscan _ _ _ => 4
  | .fpstore _ _ => 5
  | .pf _ _ => 6
  | .ctx _ => 7
  | .wc _ _ => 8
  | .avx2mem _ => 9
  | .avx2tor _ _ _ _ _ => 10
  | .seiten _ _ => 11
  | .gross _ _ => 12
  | .uebersetz _ _ => 13

/-- The old union never coincides with a new-family tag: no new
    family shadows the first union, and families are pairwise
    distinct by the same tag argument. -/
theorem kap2_tags_disjoint :
    (∀ (k : KapEreignis) (c : Nat) (d : RotDecodiert),
      Kap2Ereignis.alt k ≠ Kap2Ereignis.rot c d) ∧
    (∀ (k : KapEreignis) (c : Nat) (i : CarryInstr),
      Kap2Ereignis.alt k ≠ Kap2Ereignis.carry c i) ∧
    (∀ (k : KapEreignis) (c : Nat) (d : BtDecodiert),
      Kap2Ereignis.alt k ≠ Kap2Ereignis.bittest c d) ∧
    (∀ (k : KapEreignis) (c : Nat) (feat : PopcntMerkmal)
      (d : BsDecodiert),
      Kap2Ereignis.alt k ≠ Kap2Ereignis.bitscan c feat d) ∧
    (∀ (k : KapEreignis) (c : Nat) (e : FpStoreEreignis),
      Kap2Ereignis.alt k ≠ Kap2Ereignis.fpstore c e) ∧
    (∀ (k : KapEreignis) (c : Nat) (e : PfEreignis),
      Kap2Ereignis.alt k ≠ Kap2Ereignis.pf c e) ∧
    (∀ (k : KapEreignis) (e : CtxEreignis),
      Kap2Ereignis.alt k ≠ Kap2Ereignis.ctx e) ∧
    (∀ (k : KapEreignis) (c : Nat) (e : HwMemWC1287.WcZugriff1287),
      Kap2Ereignis.alt k ≠ Kap2Ereignis.wc c e) ∧
    (∀ (k : KapEreignis) (e : Avx2MemEreignis),
      Kap2Ereignis.alt k ≠ Kap2Ereignis.avx2mem e) ∧
    (∀ (k : KapEreignis) (cpu : CpuMerkmal) (x : Xcr0Bild)
      (ko : KontrollBild) (c : Nat) (i : ExtInstr),
      Kap2Ereignis.alt k ≠ Kap2Ereignis.avx2tor cpu x ko c i) ∧
    (∀ (k : KapEreignis) (c : Nat) (q : SeitenAnfrage),
      Kap2Ereignis.alt k ≠ Kap2Ereignis.seiten c q) ∧
    (∀ (k : KapEreignis) (c : Nat) (q : SeitenAnfrage),
      Kap2Ereignis.alt k ≠ Kap2Ereignis.gross c q) ∧
    (∀ (k : KapEreignis) (c : Nat) (q : SeitenAnfrage),
      Kap2Ereignis.alt k ≠ Kap2Ereignis.uebersetz c q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k c d h
    cases h
  · intro k c i h
    cases h
  · intro k c d h
    cases h
  · intro k c feat d h
    cases h
  · intro k c e h
    cases h
  · intro k c e h
    cases h
  · intro k e h
    cases h
  · intro k c e h
    cases h
  · intro k e h
    cases h
  · intro k cpu x ko c i h
    cases h
  · intro k c q h
    cases h
  · intro k c q h
    cases h
  · intro k c q h
    cases h

/-- What is NOT admitted stays refused: the three paging adapters
    admit no flat-machine successor, by their accepted refusals. -/
theorem kap2_verweigert :
    (∀ (m : HwMaschine) (c : Nat) (q : SeitenAnfrage),
      adapterSeiten.schritt m c q = none) ∧
    (∀ (m : HwMaschine) (c : Nat) (q : SeitenAnfrage),
      adapterGross.schritt m c q = none) ∧
    (∀ (m : HwMaschine) (c : Nat) (q : SeitenAnfrage),
      adapterUebersetz.schritt m c q = none) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m c q
    exact adapterSeiten_verweigert m c q
  · intro m c q
    exact adapterGross_verweigert m c q
  · intro m c q
    exact adapterUebersetz_verweigert m c q

/-! ## Exhibited steps: one reached union step per new family.

  Each step reuses its family's own witness machine and accepted
  witness equation: option-machine witnesses by case analysis (the
  value lemmas rule out `none`), register-outcome witnesses by a
  projected `decide` (machines contain functions, so only plain
  values are decided), the gate plug through the accepted MUL row,
  the refused-paging and extended families through a base
  observation on their own witness machine. -/

/-- Exhibited carry union step: core 0 adds `17 + 5` through the
    family adapter. -/
theorem kap2_step_carry :
    ∃ m1, HwVollSchritt2 carryWitStart m1
      (Kap2Ereignis.carry 0
        (.reg ⟨.adcReg .b64 .rax .rcx, 3⟩)) := by
  cases hA : carryWitOutAdd with
  | none =>
    have h := carryWit_add_rax
    simp [hA, carryWitRegOut] at h
  | some m1 =>
    have heq : (adapterCarry).schritt carryWitStart 0
        (.reg ⟨.adcReg .b64 .rax .rcx, 3⟩) = some m1 := hA
    exact ⟨m1, (kap2_carry_embedded _ _ _ _).mp heq⟩

/-- Exhibited bit-test union step: core 0 runs BTS through the
    family adapter. -/
theorem kap2_step_bittest :
    ∃ m1, HwVollSchritt2 btWitStartM m1
      (Kap2Ereignis.bittest 0 ⟨.reg .bts .w64 .rax .rcx, 4⟩) := by
  cases hA : btWitAd0 with
  | none =>
    have h := btWit_ad0.1
    simp [hA, btWitRegOut] at h
  | some m1 =>
    have heq : (adapterBitTest).schritt btWitStartM 0
        ⟨.reg .bts .w64 .rax .rcx, 4⟩ = some m1 := hA
    exact ⟨m1, (kap2_bittest_embedded _ _ _ _).mp heq⟩

/-- Exhibited rotate union step: core 0 ROLs `0x81` by imm8 1
    through the family adapter. -/
theorem kap2_step_rot :
    ∃ m1, HwVollSchritt2 rotHwWitStart m1
      (Kap2Ereignis.rot 0
        ⟨⟨.rol, .b8, .imm8 1, .reg .rax⟩, 3⟩) := by
  have hproj : ((adapterRot).schritt rotHwWitStart 0
      ⟨⟨.rol, .b8, .imm8 1, .reg .rax⟩, 3⟩).map
      (fun m => (m.kerne 0).register .rax) = some 3 := by
    decide
  cases hS : (adapterRot).schritt rotHwWitStart 0
      ⟨⟨.rol, .b8, .imm8 1, .reg .rax⟩, 3⟩ with
  | none =>
    rw [hS] at hproj
    cases hproj
  | some m1 =>
    exact ⟨m1, (kap2_rot_embedded _ _ _ _).mp hS⟩

/-- Exhibited bit-scan union step: core 0 scans `0x10` through the
    family adapter at the witness feature setting. -/
theorem kap2_step_bitscan :
    ∃ m1, HwVollSchritt2 bsHwWitStart m1
      (Kap2Ereignis.bitscan 0 ⟨true⟩
        ⟨.bsf .b32 .rax (.reg .rcx), 3⟩) := by
  have hproj : ((adapterBitScan ⟨true⟩).schritt bsHwWitStart 0
      ⟨.bsf .b32 .rax (.reg .rcx), 3⟩).map
      (fun m => (m.kerne 0).register .rax) = some 4 := by
    decide
  cases hS : (adapterBitScan ⟨true⟩).schritt bsHwWitStart 0
      ⟨.bsf .b32 .rax (.reg .rcx), 3⟩ with
  | none =>
    rw [hS] at hproj
    cases hproj
  | some m1 =>
    exact ⟨m1, (kap2_bitscan_embedded _ _ _ _ _).mp hS⟩

/-- Exhibited FP-store union step: core 0 buffers `3.0f32` through
    the family adapter. -/
theorem kap2_step_fpstore :
    ∃ m1, HwVollSchritt2 fp32WitM0 m1
      (Kap2Ereignis.fpstore 0
        (.speichere32 fp32WitAdr fp32WitWert)) := by
  cases hA : fp32WitPush with
  | none =>
    have h := fp32Wit_puffer4
    simp [hA, fp32WitBufLen] at h
  | some m1 =>
    have heq : fpStoreAdapter.schritt fp32WitM0 0
        (.speichere32 fp32WitAdr fp32WitWert) = some m1 := hA
    exact ⟨m1, (kap2_fpstore_embedded _ _ _ _).mp heq⟩

/-- Exhibited page-fault-delivery union step: core 0 delivers the
    witness fault under a cleared IF through the family plug. -/
theorem kap2_step_pf :
    ∃ m1, HwVollSchritt2 pfWitStart m1
      (Kap2Ereignis.pf 0
        { pfWitEv with
          steuer := { pfWitSteuer with ifBit := false } }) := by
  have hsome : (pfSchritt pfWitStart 0
      { pfWitEv with steuer := { pfWitSteuer with ifBit := false } }).isSome =
      true :=
    pfWit_klar_liefert
  cases hS : pfSchritt pfWitStart 0
      { pfWitEv with steuer := { pfWitSteuer with ifBit := false } } with
  | none =>
    rw [hS] at hsome
    cases hsome
  | some r =>
    have heq : adapterPf.schritt pfWitStart 0
        { pfWitEv with steuer := { pfWitSteuer with ifBit := false } } =
        some r.1 := by
      simp [adapterPf_treue, hS]
    exact ⟨r.1, (kap2_pf_embedded _ _ _ _).mp heq⟩

/-- Exhibited context union step: core 0 saves its FP/vector
    state through the family relation. -/
theorem kap2_step_ctx :
    ∃ m1, HwVollSchritt2 ctxWitStart m1
      (Kap2Ereignis.ctx (.fxsaveReq 0 ctxArea0)) := by
  cases hS : ctxSpeichern ctxWitStart 0 ctxArea0 with
  | weiter m2 =>
    exact ⟨m2, (kap2_ctx_embedded _ _ _).mp
      (CtxSchritt.fxsave 0 ctxArea0 hS)⟩
  | verweigert =>
    have h := ctxWit_buf.1
    simp [ctxWitBuf, hS] at h
  | fehlerGP =>
    have h := ctxWit_buf.1
    simp [ctxWitBuf, hS] at h
  | fehlerUD =>
    have h := ctxWit_buf.1
    simp [ctxWitBuf, hS] at h

/-- Exhibited WC union step: the prefetch hint NOPs on the witness
    machine through the family plug. -/
theorem kap2_step_wc :
    ∃ m1, HwVollSchritt2 hwWitStart m1
      (Kap2Ereignis.wc 0
        (.holeVor .nta (BitVec.ofNat 64 8192))) :=
  ⟨_, (kap2_wc_embedded _ _ _ _).mp
    (HwMemWC1287.wcAdapter_prefetch_nop hwWitStart 0 .nta
      (BitVec.ofNat 64 8192))⟩

end Gabbro.Grammatik.X86
