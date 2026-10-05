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

end Gabbro.Grammatik.X86
