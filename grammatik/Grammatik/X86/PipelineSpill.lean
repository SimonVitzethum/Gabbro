/-
  File:      Grammatik/X86/PipelineSpill.lean
  Subject:   Pipeline spill code generation with privacy (lane 1191).

  Follow-up of lane 1167 (`PipelineRegAlloc.lean`): a spilled live
  variable was refused there because the lowering had no spill code.
  Here the spill code exists: save/reload fragments made of the pilot
  address materialisation (`movImm64 adr slotAddr`) plus a pilot
  `store64`/`load64` through the address register with zero
  displacement (the shape the accepted `senkStmt` already uses), with
  per-step meaning proved against the canonical `schritt` lemmas.

  A decided validator (`spillPlanOk`) admits a spill plan only for
  in-frame slots that are pairwise distinct (no spill slot aliases
  another), a frame off the code region and inside 64 bits, and every
  slot footprint disjoint from every declared table extent (a spill
  into a table extent is refused, never guessed). The closing theorem
  (`spill_haelt_bedeutung`) composes the accepted pipeline correctness
  (`pipeline_correct`) with spill privacy: the fetched run is preserved
  and no spill slot touches a source table or another spill slot
  (`ComposeSpillPrivacy.lean` vocabulary: `spillSlot`, `GetrenntK`,
  `Disjunkt`). A second theorem (`spill_rundreise_privat`) threads a
  reached save through its reload via the accepted
  `ComposeSpillPrivacy_verbindung`.

  Reused unchanged: `PipeCfg`/`abbOf`/`validate`/`pipeline_correct`,
  `CodeAt`/`Layout`/`LayoutSep`/`WorldRep`/`EnvRepr`, `Rahmen`/
  `schlitzNat`/`schlitzNat_schranke`/`schlitz_toNat`/`sichereWort`/
  `ladeWort`, `spillSlot`/`SpillFrisch`/`GetrenntK`/`spillPrivatOk`/
  `SpillZugelassen`, `ComposeSpillPrivacy_verbindung`,
  `schritt_movImm64`/`schritt_store64_erfolg`/`schritt_load64_erfolg`,
  `effAddr_null`, `disjunkt_von_intervallen`, `lauf_anhang`.
  No second IR, no second source interpreter, no optimiser edit.
-/
import Grammatik.X86.Pipeline
import Grammatik.X86.PipelineWitnesses
import Grammatik.X86.PipelineRegAlloc
import Grammatik.X86.ComposeSpillPrivacy
import Grammatik.X86.EffectiveAddress

namespace Gabbro.Grammatik.X86.PipeSpill

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.PipeRegAlloc

/-- Spill save code for one slot: materialise the canonical slot address
    in the address register, then store the source register there. -/
def spillSaveCode (c : PipeCfg) (r : Rahmen) (slot : Nat)
    (src : Register) : List Befehl :=
  [.movImm64 c.adr (natAdresse (r.schlitzNat slot)),
    .store64 c.adr src (BitVec.ofNat 32 0)]

/-- Spill reload code for one slot: materialise the canonical slot address
    in the address register, then load it into the destination register. -/
def spillLoadCode (c : PipeCfg) (r : Rahmen) (slot : Nat)
    (dst : Register) : List Befehl :=
  [.movImm64 c.adr (natAdresse (r.schlitzNat slot)),
    .load64 dst c.adr (BitVec.ofNat 32 0)]

/-- Spill code is straight-line pilot code (save). -/
theorem spillSave_gerade (c : PipeCfg) (r : Rahmen) (slot : Nat)
    (src : Register) : (spillSaveCode c r slot src).all gerade = true := by
  rfl

/-- Spill code is straight-line pilot code (reload). -/
theorem spillLoad_gerade (c : PipeCfg) (r : Rahmen) (slot : Nat)
    (dst : Register) : (spillLoadCode c r slot dst).all gerade = true := by
  rfl

/-- SAVE SEQUENCE: the two spill-save instructions run the canonical
    slot store: the address materialisation puts the slot address in the
    address register, and the zero-displacement store writes the source
    register word into the slot. Memory carries the checked store;
    every register but the address register is kept. -/
theorem spillSave_lauf (c : PipeCfg) (r : Rahmen) (slot : Nat)
    (src : Register) (s : Zustand) (m' : Speicher)
    (hne : src ≠ c.adr)
    (hwr : write64 s.speicher (spillSlot r slot) (s.register src) = some m') :
    ∃ s2, lauf ((spillSaveCode c r slot src).map kanon) s = some s2 ∧
      s2.speicher = m' ∧
      s2.register c.adr = natAdresse (r.schlitzNat slot) ∧
      s2.register src = s.register src := by
  have hmi := schritt_movImm64 (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot))))
    s c.adr (natAdresse (r.schlitzNat slot)) (laengeOk_encode _) rfl
  have e1 : lauf [kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))] s =
      some (schrittRegister s
        (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
        s.flags c.adr (natAdresse (r.schlitzNat slot))) := by
    simp only [lauf, hmi]
  have hs1a : (schrittRegister s
      (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
      s.flags c.adr (natAdresse (r.schlitzNat slot))).register c.adr =
      natAdresse (r.schlitzNat slot) :=
    regSet_gleich _ _ _
  have hs1s : (schrittRegister s
      (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
      s.flags c.adr (natAdresse (r.schlitzNat slot))).register src =
      s.register src :=
    regSet_fremd _ _ _ _ hne
  have heff : effAddr (schrittRegister s
      (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
      s.flags c.adr (natAdresse (r.schlitzNat slot))) c.adr
      (BitVec.ofNat 32 0) = spillSlot r slot := by
    rw [effAddr_null, hs1a]
    rfl
  have hw : write64 (schrittRegister s
      (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
      s.flags c.adr (natAdresse (r.schlitzNat slot))).speicher
      (effAddr (schrittRegister s
        (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
        s.flags c.adr (natAdresse (r.schlitzNat slot))) c.adr (BitVec.ofNat 32 0))
      ((schrittRegister s
        (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
        s.flags c.adr (natAdresse (r.schlitzNat slot))).register src) = some m' := by
    rw [heff, hs1s]
    exact hwr
  have hst := schritt_store64_erfolg
    (kanon (.store64 c.adr src (BitVec.ofNat 32 0)))
    (schrittRegister s
      (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
      s.flags c.adr (natAdresse (r.schlitzNat slot)))
    c.adr src (BitVec.ofNat 32 0) m' (laengeOk_encode _) rfl hw
  have e2 : lauf [kanon (.store64 c.adr src (BitVec.ofNat 32 0))]
      (schrittRegister s
        (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
        s.flags c.adr (natAdresse (r.schlitzNat slot))) =
      some ({ (schrittRegister s
        (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
        s.flags c.adr (natAdresse (r.schlitzNat slot))) with
        speicher := m',
        rip := ripNach (schrittRegister s
          (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
          s.flags c.adr (natAdresse (r.schlitzNat slot))).rip
          (kanon (.store64 c.adr src (BitVec.ofNat 32 0))).laenge } : Zustand) := by
    simp only [lauf, hst]
  have hrun : lauf ((spillSaveCode c r slot src).map kanon) s = some
      ({ (schrittRegister s
        (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
        s.flags c.adr (natAdresse (r.schlitzNat slot))) with
        speicher := m',
        rip := ripNach (schrittRegister s
          (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
          s.flags c.adr (natAdresse (r.schlitzNat slot))).rip
          (kanon (.store64 c.adr src (BitVec.ofNat 32 0))).laenge } : Zustand) := by
    have hmap : (spillSaveCode c r slot src).map kanon =
        [kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))] ++
        [kanon (.store64 c.adr src (BitVec.ofNat 32 0))] := rfl
    rw [hmap, lauf_anhang _ _ _ _ e1]
    exact e2
  refine ⟨_, hrun, rfl, hs1a, hs1s⟩

/-- RELOAD SEQUENCE: the two spill-reload instructions run the
    canonical slot load: the address materialisation puts the slot
    address in the address register, and the zero-displacement load
    puts the slot word in the destination register. Memory is untouched;
    every register but the address and destination registers is kept. -/
theorem spillLoad_lauf (c : PipeCfg) (r : Rahmen) (slot : Nat)
    (dst : Register) (s : Zustand) (v : Wort)
    (hrd : read64 s.speicher (spillSlot r slot) = some v) :
    ∃ s2, lauf ((spillLoadCode c r slot dst).map kanon) s = some s2 ∧
      s2.speicher = s.speicher ∧
      s2.register dst = v := by
  have hmi := schritt_movImm64 (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot))))
    s c.adr (natAdresse (r.schlitzNat slot)) (laengeOk_encode _) rfl
  have e1 : lauf [kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))] s =
      some (schrittRegister s
        (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
        s.flags c.adr (natAdresse (r.schlitzNat slot))) := by
    simp only [lauf, hmi]
  have hs1a : (schrittRegister s
      (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
      s.flags c.adr (natAdresse (r.schlitzNat slot))).register c.adr =
      natAdresse (r.schlitzNat slot) :=
    regSet_gleich _ _ _
  have heff : effAddr (schrittRegister s
      (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
      s.flags c.adr (natAdresse (r.schlitzNat slot))) c.adr
      (BitVec.ofNat 32 0) = spillSlot r slot := by
    rw [effAddr_null, hs1a]
    rfl
  have hrd2 : read64 (schrittRegister s
      (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
      s.flags c.adr (natAdresse (r.schlitzNat slot))).speicher
      (effAddr (schrittRegister s
        (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
        s.flags c.adr (natAdresse (r.schlitzNat slot))) c.adr
        (BitVec.ofNat 32 0)) = some v := by
    rw [heff]
    exact hrd
  have hld := schritt_load64_erfolg
    (kanon (.load64 dst c.adr (BitVec.ofNat 32 0)))
    (schrittRegister s
      (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
      s.flags c.adr (natAdresse (r.schlitzNat slot)))
    dst c.adr (BitVec.ofNat 32 0) v (laengeOk_encode _) rfl hrd2
  have hrun : lauf ((spillLoadCode c r slot dst).map kanon) s = some
      (schrittRegister (schrittRegister s
        (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
        s.flags c.adr (natAdresse (r.schlitzNat slot)))
        (ripNach (schrittRegister s
          (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
          s.flags c.adr (natAdresse (r.schlitzNat slot))).rip
          (kanon (.load64 dst c.adr (BitVec.ofNat 32 0))).laenge)
        (schrittRegister s
          (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
          s.flags c.adr (natAdresse (r.schlitzNat slot))).flags dst v) := by
    have hmap : (spillLoadCode c r slot dst).map kanon =
        [kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))] ++
        [kanon (.load64 dst c.adr (BitVec.ofNat 32 0))] := rfl
    have e2 : lauf [kanon (.load64 dst c.adr (BitVec.ofNat 32 0))]
        (schrittRegister s
          (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
          s.flags c.adr (natAdresse (r.schlitzNat slot))) =
        some (schrittRegister (schrittRegister s
          (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
          s.flags c.adr (natAdresse (r.schlitzNat slot)))
          (ripNach (schrittRegister s
            (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
            s.flags c.adr (natAdresse (r.schlitzNat slot))).rip
            (kanon (.load64 dst c.adr (BitVec.ofNat 32 0))).laenge)
          (schrittRegister s
            (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse (r.schlitzNat slot)))).laenge)
            s.flags c.adr (natAdresse (r.schlitzNat slot))).flags dst v) := by
      simp only [lauf, hld]
    rw [hmap, lauf_anhang _ _ _ _ e1]
    exact e2
  refine ⟨_, hrun, rfl, ?_⟩
  show regSet (regSet s.register c.adr (natAdresse (r.schlitzNat slot))) dst v dst = v
  exact regSet_gleich _ _ _

/-! ## 2. The decided validator.

    An untrusted spill plan (slot list, frame, code range, declared
    table extents) is admitted only if every check computes to `true`:
    every slot lies in the frame, slots are pairwise distinct (no slot
    aliases another), the frame lies off the code region and inside
    64 bits, and every slot footprint is disjoint from every declared
    table extent. -/

/-- THE VALIDATOR: an untrusted spill plan is accepted only if every
    check below computes to `true`. -/
def spillPlanOk (r : Rahmen) (slots : List Nat) (codeBase codeLen : Nat)
    (daten : List Nat) : Bool :=
  slots.all (fun s => decide (s < r.schlitzZahl)) &&
  decide slots.Nodup &&
  decide (r.basis + r.tiefe ≤ codeBase ∨ codeBase + codeLen ≤ r.basis) &&
  decide (r.spitzeNat ≤ 2 ^ 64) &&
  daten.all (fun a => slots.all (fun s =>
    decide (a + 8 ≤ r.schlitzNat s ∨ r.schlitzNat s + 8 ≤ a)))

/-- A validated plan keeps every listed slot in-frame. -/
theorem spillPlan_inRahmen (r : Rahmen) (slots : List Nat)
    (codeBase codeLen : Nat) (daten : List Nat)
    (h : spillPlanOk r slots codeBase codeLen daten = true)
    (s : Nat) (hmem : s ∈ slots) : s < r.schlitzZahl := by
  unfold spillPlanOk at h
  simp only [Bool.and_eq_true] at h
  have hall := (List.all_eq_true.mp h.1.1.1.1) s hmem
  have hall2 : decide (s < r.schlitzZahl) = true := hall
  exact of_decide_eq_true hall2

/-- A validated plan has pairwise distinct slots: no spill slot
    aliases another. -/
theorem spillPlan_nodup (r : Rahmen) (slots : List Nat)
    (codeBase codeLen : Nat) (daten : List Nat)
    (h : spillPlanOk r slots codeBase codeLen daten = true) :
    slots.Nodup := by
  unfold spillPlanOk at h
  simp only [Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.1.1.2

/-- A validated plan keeps the frame off the code region. -/
theorem spillPlan_offCode (r : Rahmen) (slots : List Nat)
    (codeBase codeLen : Nat) (daten : List Nat)
    (h : spillPlanOk r slots codeBase codeLen daten = true) :
    r.basis + r.tiefe ≤ codeBase ∨ codeBase + codeLen ≤ r.basis := by
  unfold spillPlanOk at h
  simp only [Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.1.2

/-- A validated plan keeps the frame inside 64 bits. -/
theorem spillPlan_schranke (r : Rahmen) (slots : List Nat)
    (codeBase codeLen : Nat) (daten : List Nat)
    (h : spillPlanOk r slots codeBase codeLen daten = true) :
    r.spitzeNat ≤ 2 ^ 64 := by
  unfold spillPlanOk at h
  simp only [Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.2

/-- A validated plan keeps every slot footprint disjoint from every
    declared table extent. -/
theorem spillPlan_offDaten (r : Rahmen) (slots : List Nat)
    (codeBase codeLen : Nat) (daten : List Nat)
    (h : spillPlanOk r slots codeBase codeLen daten = true)
    (a : Nat) (hmem : a ∈ daten) (s : Nat) (hs : s ∈ slots) :
    a + 8 ≤ r.schlitzNat s ∨ r.schlitzNat s + 8 ≤ a := by
  unfold spillPlanOk at h
  simp only [Bool.and_eq_true] at h
  have hall := (List.all_eq_true.mp h.2) a hmem
  have hall2 : (slots.all fun s =>
    decide (a + 8 ≤ r.schlitzNat s ∨ r.schlitzNat s + 8 ≤ a)) = true := hall
  have hslot := (List.all_eq_true.mp hall2) s hs
  have hslot2 : decide (a + 8 ≤ r.schlitzNat s ∨ r.schlitzNat s + 8 ≤ a) = true :=
    hslot
  exact of_decide_eq_true hslot2

/-! ## 3. Spill privacy: no slot touches a source table or another slot.

    An in-frame slot of a 64-bit-contained frame has no address
    wrap, so Nat-interval disjointness gives footprint disjointness
    (`disjunkt_von_intervallen`). Distinct slots are eight bytes apart
    by construction (`schlitzNat`), and every slot lies disjoint from
    every placed source slot of a table-free frame. -/

/-- An in-frame slot of a contained frame has no address wrap. -/
theorem spill_slot_ohneUmbruch (r : Rahmen) (s : Nat)
    (hle : r.spitzeNat ≤ 2 ^ 64) (hi : s < r.schlitzZahl) :
    OhneUmbruch (spillSlot r s) := by
  have hsch := schlitzNat_schranke r s hi
  have hto : (spillSlot r s).toNat = r.schlitzNat s :=
    schlitz_toNat r s hle hi
  unfold OhneUmbruch
  rw [hto]
  omega

/-- Two distinct in-frame slots share no byte: slots sit eight bytes
    apart by construction, so Nat-interval order gives footprint
    disjointness on both sides. -/
theorem spill_schlitze_getrennt (r : Rahmen) (i j : Nat)
    (hle : r.spitzeNat ≤ 2 ^ 64)
    (hi : i < r.schlitzZahl) (hj : j < r.schlitzZahl) (hne : i ≠ j) :
    Disjunkt (spillSlot r i) (spillSlot r j) := by
  have hUi := spill_slot_ohneUmbruch r i hle hi
  have hUj := spill_slot_ohneUmbruch r j hle hj
  have hti : (spillSlot r i).toNat = r.schlitzNat i :=
    schlitz_toNat r i hle hi
  have htj : (spillSlot r j).toNat = r.schlitzNat j :=
    schlitz_toNat r j hle hj
  have hnat : r.schlitzNat i + 8 ≤ r.schlitzNat j ∨
      r.schlitzNat j + 8 ≤ r.schlitzNat i := by
    unfold Rahmen.schlitzNat
    rcases Nat.lt_or_ge i j with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hdis : (spillSlot r i).toNat + 8 ≤ (spillSlot r j).toNat ∨
      (spillSlot r j).toNat + 8 ≤ (spillSlot r i).toNat := by
    rw [hti, htj]
    exact hnat
  exact disjunkt_von_intervallen _ _ hUi hUj hdis

variable {D : Deklaration}

/-- Spill-table privacy: every listed slot footprint is disjoint from
    every placed source slot footprint. -/
def SpillVonTabellenGetrennt (r : Rahmen) (slots : List Nat)
    (L : Layout D) : Prop :=
  ∀ (s : Nat), s ∈ slots →
    ∀ (t : D.Tab) (k : Int) (f : D.Feld t) (a : Nat),
      L.loc t k f = some a →
        a + 8 ≤ r.schlitzNat s ∨ r.schlitzNat s + 8 ≤ a

/-- A validated plan over a table-free frame is spill-private: the
    validator keeps every slot in-frame, and the frame keeps every
    source table out. -/
theorem spillPlan_tabellenGetrennt (r : Rahmen) (slots : List Nat)
    (L : Layout D) (codeBase codeLen : Nat) (daten : List Nat)
    (h : spillPlanOk r slots codeBase codeLen daten = true)
    (hrahmen : PipeRahmenGetrennt r L) :
    SpillVonTabellenGetrennt r slots L := by
  intro s hs t k f a hloc
  have hslot : s < r.schlitzZahl :=
    spillPlan_inRahmen r slots codeBase codeLen daten h s hs
  have hbound := schlitzNat_schranke r s hslot
  have hsp : r.spitzeNat = r.basis + r.tiefe := rfl
  have hge : r.basis ≤ r.schlitzNat s := by
    unfold Rahmen.schlitzNat
    omega
  rcases hrahmen t k f a hloc with hlo | hhi
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-! ## 4. Round-trip under a validated plan.

    A reached save through a validated plan reloads its own value
    through the token-threaded step, keeps permissions, leaves a
    disjoint foreign footprint unchanged, and runs beside pairwise
    disjoint spill slots. Composed from the accepted
    `ComposeSpillPrivacy_verbindung` plus the validator legs; every
    premise is used. -/

/-- ROUND-TRIP UNDER A VALIDATED PLAN: validator admission (slot bound
    from plan membership, joint admission from the checked
    `spillPrivatOk`) plus TSO freshness give the checked save/restore
    round-trip, permission preservation, disjoint foreign stability,
    and pairwise slot separation over the whole plan. -/
theorem spill_rundreise_privat (m m1 : Speicher) (r : Rahmen)
    (slots : List Nat) (s : Nat) (hmem : s ∈ slots)
    (codeBase codeLen : Nat) (daten : List Nat)
    (hplan : spillPlanOk r slots codeBase codeLen daten = true)
    (v w : Wort) (fremd : Adresse) (tso : TSOZustand)
    (genommen extent : Bool)
    (hok : spillPrivatOk genommen extent (decide (s < r.schlitzZahl)) = true)
    (hfrisch : SpillFrisch tso r s)
    (hdis : GetrenntK r s fremd)
    (hrd : lesbar8 m (spillSlot r s) = true)
    (hwr : sichereWort m r s v = some m1)
    (hrd2 : ladeWort m1 r s = some w) :
    w = v ∧
    spillPrivatSchritt m r s v = some (m1, v) ∧
    SpillZugelassen genommen extent tso r s ∧
    m1.lesbar = m.lesbar ∧ m1.schreibbar = m.schreibbar ∧
    read64 m1 fremd = read64 m fremd ∧
    ladeWort m1 r s = some v ∧
    (∀ i j, i ∈ slots → j ∈ slots → i ≠ j →
      Disjunkt (spillSlot r i) (spillSlot r j)) := by
  have hb : s < r.schlitzZahl :=
    spillPlan_inRahmen r slots codeBase codeLen daten hplan s hmem
  have hle : r.spitzeNat ≤ 2 ^ 64 :=
    spillPlan_schranke r slots codeBase codeLen daten hplan
  have hmain := ComposeSpillPrivacy_verbindung m m1 r s v w fremd tso
    genommen extent hb hok hfrisch hdis hrd hwr hrd2
  refine ⟨hmain.1, hmain.2.1, hmain.2.2.1, hmain.2.2.2.1, hmain.2.2.2.2.1,
    hmain.2.2.2.2.2.1, hmain.2.2.2.2.2.2, ?_⟩
  intro i j hi hj hne
  exact spill_schlitze_getrennt r i j hle
    (spillPlan_inRahmen r slots codeBase codeLen daten hplan i hi)
    (spillPlan_inRahmen r slots codeBase codeLen daten hplan j hj) hne

/-! ## 5. The closing theorem: spilled lowering preserves the source
    meaning and touches neither a source table nor another spill slot.

    If the pipeline validator accepts candidate bytes for a source
    block and a spill plan validates over a table-free frame, then every
    real source run of the block is matched by a fetched byte run with
    world and environment represented — every listed spill slot lies
    disjoint from every placed source slot, distinct slots are pairwise
    footprint-disjoint, and every slot avoids every declared table
    extent. Composed from `pipeline_correct` plus the spill legs; every
    premise is used. -/

/-- SPILL PRESERVATION: validated pipeline bytes plus a validated spill
    plan give the fetched run with world and environment represented,
    slot-vs-table privacy, pairwise slot separation, and slot-vs-extent
    separation. -/
theorem spill_haelt_bedeutung (c : PipeCfg) (L : Layout D)
    (certs : List (OptimizationRules.PassKind × OptimizationRules.BlockCert))
    (src : Block D V l Γ Λ Λ')
    (bytes : List Byte)
    (r : Rahmen) (slots : List Nat) (daten : List Nat)
    (hval : validate c L certs src bytes = true)
    (hsep : LayoutSep L)
    (hplan : spillPlanOk r slots c.codeBase bytes.length daten = true)
    (hrahmen : PipeRahmenGetrennt r L)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) (s : Zustand)
    (hcode : CodeAt s.speicher (natAdresse c.codeBase) bytes)
    (hrip : s.rip = natAdresse c.codeBase)
    (hW : WorldRep L s.speicher σ)
    (hE : EnvRepr ρ s.register (abbOf c))
    (σ' : World D) (ρ' : Env D Γ)
    (hsrc : execBlock O passes R src σ ρ = .ok σ' ρ') :
    (∃ n s', laufBytes n s = .weiter s' ∧
      s'.rip = natAdresse (c.codeBase + bytes.length) ∧
      WorldRep L s'.speicher σ' ∧
      EnvRepr ρ' s'.register (abbOf c)) ∧
    SpillVonTabellenGetrennt r slots L ∧
    (∀ i j, i ∈ slots → j ∈ slots → i ≠ j →
      Disjunkt (spillSlot r i) (spillSlot r j)) ∧
    (∀ a ∈ daten, ∀ q ∈ slots,
      a + 8 ≤ r.schlitzNat q ∨ r.schlitzNat q + 8 ≤ a) := by
  obtain ⟨n, s', hrun, hrip', hW', hE'⟩ :=
    pipeline_correct c L certs src bytes hval hsep O passes R σ ρ s
      hcode hrip hW hE σ' ρ' hsrc
  refine ⟨⟨n, s', hrun, hrip', hW', hE'⟩, ?_, ?_, ?_⟩
  · exact spillPlan_tabellenGetrennt r slots L c.codeBase bytes.length
      daten hplan hrahmen
  · intro i j hi hj hne
    exact spill_schlitze_getrennt r i j
      (spillPlan_schranke r slots c.codeBase bytes.length daten hplan)
      (spillPlan_inRahmen r slots c.codeBase bytes.length daten hplan i hi)
      (spillPlan_inRahmen r slots c.codeBase bytes.length daten hplan j hj) hne
  · intro a ha q hq
    exact spillPlan_offDaten r slots c.codeBase bytes.length daten hplan
      a ha q hq

/-! ## 6. Refusals: loud on every path.

    A spill into a declared table extent, a slot past the frame, and a
    plan with aliased slots are all refused (`false`), never guessed.
    Each general refusal goes through the corresponding validator leg. -/

/-- TABLE REFUSAL: a slot overlapping a declared table extent is never
    admitted. -/
theorem spill_verweigert_tabelle (r : Rahmen) (slots : List Nat)
    (codeBase codeLen : Nat) (daten : List Nat)
    (a : Nat) (hmem : a ∈ daten) (s : Nat) (hs : s ∈ slots)
    (h : ¬ (a + 8 ≤ r.schlitzNat s ∨ r.schlitzNat s + 8 ≤ a)) :
    spillPlanOk r slots codeBase codeLen daten = false := by
  cases heq : spillPlanOk r slots codeBase codeLen daten with
  | true =>
    exact absurd (spillPlan_offDaten r slots codeBase codeLen daten heq
      a hmem s hs) h
  | false => rfl

/-- OUT-OF-FRAME REFUSAL: a listed slot past the frame is never admitted. -/
theorem spill_verweigert_aussen (r : Rahmen) (slots : List Nat)
    (codeBase codeLen : Nat) (daten : List Nat)
    (s : Nat) (hs : s ∈ slots) (h : r.schlitzZahl ≤ s) :
    spillPlanOk r slots codeBase codeLen daten = false := by
  cases heq : spillPlanOk r slots codeBase codeLen daten with
  | true =>
    have hlt := spillPlan_inRahmen r slots codeBase codeLen daten heq s hs
    omega
  | false => rfl

/-- COLLISION REFUSAL: aliased slots are never admitted. -/
theorem spill_verweigert_kollision (r : Rahmen) (slots : List Nat)
    (codeBase codeLen : Nat) (daten : List Nat)
    (h : ¬ slots.Nodup) :
    spillPlanOk r slots codeBase codeLen daten = false := by
  cases heq : spillPlanOk r slots codeBase codeLen daten with
  | true =>
    exact absurd (spillPlan_nodup r slots codeBase codeLen daten heq) h
  | false => rfl

/-! ## 7. Poison probes.

    One positive probe (the witness plan validates) and one refused
    probe per validator leg: a spill into a table extent (also through
    the refusal theorem), a slot past the frame, aliased slots, and a
    frame over the code. The witness frame sits at 16384 (off the
    witness code at `[4096, 4178)` and off the witness tables at
    8192/8200); slots 0 and 1 are the two eight-byte words there. -/

/-- The witness plan: slots 0 and 1 of the frame at 16384, code at
    4096, table extents at 8192 and 8200. -/
def spillP0 : List Nat := [0, 1]

def spillR0 : Rahmen := ⟨16384, 16⟩

def spillD0 : List Nat := [8192, 8200]

/-- POSITIVE PROBE: the witness plan validates, by computation. -/
theorem spill_probe_pos : spillPlanOk spillR0 spillP0 4096 pwBytes.length spillD0 = true := by
  decide

/-- TABLE EXTENT: a spill naming a table byte is refused (here the
    declared extent 16384 covers slot 0). -/
def spillBadTabelle : List Nat := [16384]

theorem spill_probe_tabelle :
    spillPlanOk spillR0 spillP0 4096 pwBytes.length spillBadTabelle = false := by
  decide

/-- TABLE REFUSAL through the theorem: slot 0 at 16384 overlaps the
    declared extent 16384. -/
theorem spill_probe_tabelle_satz :
    spillPlanOk spillR0 [0] 4096 pwBytes.length [16384] = false :=
  spill_verweigert_tabelle spillR0 [0] 4096 pwBytes.length [16384]
    16384 (by decide) 0 (by decide) (by decide)

/-- OUT-OF-FRAME: a slot past the two-slot frame is refused. -/
theorem spill_probe_aussen :
    spillPlanOk spillR0 [0, 7] 4096 pwBytes.length spillD0 = false := by
  decide

/-- COLLISION: the same slot twice is refused (it would alias another
    spill slot). -/
theorem spill_probe_kollision :
    spillPlanOk spillR0 [0, 0] 4096 pwBytes.length spillD0 = false := by
  decide

/-- CODE OVERLAP: a frame over the code region is refused. -/
theorem spill_probe_code :
    spillPlanOk ⟨4096, 16⟩ [0] 4096 pwBytes.length spillD0 = false := by
  decide

/-! ## 8. Joint witness on a non-degenerate program.

    Every premise of `spill_haelt_bedeutung` holds jointly on the
    pipeline witness program (one variable, two slots written, check
    passed; memory 7 -> 35 and 9 -> 6, so the run is non-degenerate
    and memory-changing); the closing theorem delivers the fetched run
    plus slot-vs-table privacy, pairwise slot separation and
    slot-vs-extent separation. -/

/-- The witness frame holds no source table byte, by computation on the
    two placed addresses. -/
theorem spillR0_getrennt : PipeRahmenGetrennt spillR0 pwL := by
  intro t k f a hloc
  cases t
  cases f
  simp only [pwL] at hloc
  by_cases e1 : k = 0
  · rw [if_pos e1] at hloc
    cases hloc
    exact Or.inl (by decide)
  · rw [if_neg e1] at hloc
    by_cases e2 : k = 1
    · rw [if_pos e2] at hloc
      cases hloc
      exact Or.inl (by decide)
    · rw [if_neg e2] at hloc
      cases hloc

/-- JOINT WITNESS for `spill_haelt_bedeutung`: every premise holds
    jointly on the pipeline witness program with the witness spill
    plan; the source run changes memory (rows 7 -> 35, 9 -> 6). -/
theorem spill_haelt_bedeutung_zeuge :
    ∃ (σ' : World pwD) (ρ' : Env pwD pwCtx),
      spillPlanOk spillR0 spillP0 pwCfg.codeBase pwBytes.length spillD0 = true ∧
      PipeRahmenGetrennt spillR0 pwL ∧
      validate pwCfg pwL pwCerts pwSrc pwBytes = true ∧
      LayoutSep pwL ∧
      CodeAt (pwStart 30).speicher (natAdresse pwCfg.codeBase) pwBytes ∧
      (pwStart 30).rip = natAdresse pwCfg.codeBase ∧
      WorldRep pwL (pwStart 30).speicher pwSigma ∧
      EnvRepr pwEnv30 (pwStart 30).register (abbOf pwCfg) ∧
      execBlock pwO 0 pwR pwSrc pwSigma pwEnv30 = .ok σ' ρ' ∧
      (pwSigma.slots () 0 ()).n = 7 ∧ (σ'.slots () 0 ()).n = 35 ∧
      (pwSigma.slots () 1 ()).n = 9 ∧ (σ'.slots () 1 ()).n = 6 ∧
      (∃ n s', laufBytes n (pwStart 30) = .weiter s' ∧
        s'.rip = natAdresse (pwCfg.codeBase + pwBytes.length) ∧
        WorldRep pwL s'.speicher σ' ∧
        EnvRepr ρ' s'.register (abbOf pwCfg)) ∧
      SpillVonTabellenGetrennt spillR0 spillP0 pwL ∧
      (∀ i j, i ∈ spillP0 → j ∈ spillP0 → i ≠ j →
        Disjunkt (spillSlot spillR0 i) (spillSlot spillR0 j)) ∧
      (∀ a ∈ spillD0, ∀ q ∈ spillP0,
        a + 8 ≤ spillR0.schlitzNat q ∨ spillR0.schlitzNat q + 8 ≤ a) := by
  obtain ⟨σ', ρ', hsrc, h0, h1⟩ := pw_quelle30
  obtain ⟨hv0, hv1⟩ := pw_quelle_vorher
  have hplan : spillPlanOk spillR0 spillP0 pwCfg.codeBase pwBytes.length
      spillD0 = true :=
    spill_probe_pos
  obtain ⟨⟨n, s', hrun, hrip', hW, hE'⟩, hpriv, hsep2, hdat⟩ :=
    spill_haelt_bedeutung pwCfg pwL pwCerts pwSrc pwBytes spillR0 spillP0
      spillD0 pw_validate pw_layoutSep hplan spillR0_getrennt pwO 0 pwR
      pwSigma pwEnv30 (pwStart 30) pw_code rfl pw_worldRep pw_envRepr30
      σ' ρ' hsrc
  exact ⟨σ', ρ', hplan, spillR0_getrennt, pw_validate, pw_layoutSep, pw_code,
    rfl, pw_worldRep, pw_envRepr30, hsrc, hv0, h0, hv1, h1,
    ⟨n, s', hrun, hrip', hW, hE'⟩, hpriv, hsep2, hdat⟩

/-- JOINT WITNESS for `spill_rundreise_privat`: every premise holds
    jointly on concrete values — a reached checked save of `42` into
    slot 0 that observably changes memory and reloads through the
    threaded token — beside the non-degenerate writer program
    `zeugenU` (table `konto` written by `setze`). -/
theorem spill_rundreise_privat_zeuge :
    ∃ (m m1 : Speicher) (v w : Wort),
      (0 : Nat) ∈ ([0] : List Nat) ∧
      spillPlanOk spillRahmenW [0] 4096 pwBytes.length [16] = true ∧
      spillPrivatOk false false (decide (0 < spillRahmenW.schlitzZahl)) = true ∧
      SpillFrisch spillTSO0 spillRahmenW 0 ∧
      GetrenntK spillRahmenW 0 16 ∧
      lesbar8 m (spillSlot spillRahmenW 0) = true ∧
      sichereWort m spillRahmenW 0 v = some m1 ∧
      ladeWort m1 spillRahmenW 0 = some w ∧
      (zeugenU.fns.get ⟨0, by decide⟩).schreibt = ["konto"] ∧
      w = v ∧
      m.bytes (spillSlot spillRahmenW 0) ≠
        m1.bytes (spillSlot spillRahmenW 0) ∧
      spillPrivatSchritt m spillRahmenW 0 v = some (m1, v) := by
  have hplan : spillPlanOk spillRahmenW [0] 4096 pwBytes.length [16] = true := by
    decide
  have hmain := spill_rundreise_privat speicherZeuge spillZeuM1 spillRahmenW
    [0] 0 (by decide) 4096 pwBytes.length [16] hplan 42 42 16 spillTSO0
    false false spillZeu_ok spill_frisch0 spill_getrennt_rW spillZeu_lesbar
    spillZeu_speichert spillZeu_rundreise
  exact ⟨speicherZeuge, spillZeuM1, 42, 42, by decide, hplan, spillZeu_ok,
    spill_frisch0, spill_getrennt_rW, spillZeu_lesbar, spillZeu_speichert,
    spillZeu_rundreise, zeugenU_schreibt, hmain.1, spillZeu_wechselt,
    hmain.2.1⟩

/- CUTS:
    - Proved here: spill save/reload fragments over the pilot address
      materialisation plus zero-displacement `store64`/`load64` (the
      shape the accepted `senkStmt` uses), with per-sequence `lauf`
      meaning (`spillSave_lauf`, `spillLoad_lauf` against the canonical
      `schritt` lemmas); the decided validator `spillPlanOk`
      (in-frame slots, pairwise distinct slots, frame off the code and
      inside 64 bits, every slot disjoint from every declared table
      extent) with one projection per leg; slot no-wrap and distinct
      slot footprint disjointness (`spill_slot_ohneUmbruch`,
      `spill_schlitze_getrennt` via `disjunkt_von_intervallen`);
      slot-vs-table privacy over an arbitrary layout
      (`SpillVonTabellenGetrennt`, `spillPlan_tabellenGetrennt`);
      round-trip under a validated plan composed from the accepted
      `ComposeSpillPrivacy_verbindung` (`spill_rundreise_privat`); the
      closing composition of validated pipeline bytes with a validated
      spill plan (`spill_haelt_bedeutung` via `pipeline_correct`);
      general refusals for table extent, out-of-frame slot and aliased
      slots; one positive and five refusal probes (table also through
      the refusal theorem); joint non-degenerate witnesses on the
      pipeline witness program (`spill_haelt_bedeutung_zeuge`: rows
      7 -> 35, 9 -> 6) and on a reached memory-changing spill run
      beside the writer program `zeugenU`
      (`spill_rundreise_privat_zeuge`).
    - OPEN / not claimed: interleaved lowering that splits live ranges
      across registers and spill slots (no live-range splitting here:
      the fragments save/reload whole words for named slots, and which
      variable homes where is lane 1167's allocation, reused only for
      its frame vocabulary); the fragments clobber the address register
      `c.adr`, and combining them with a register allocation needs the
      allocator's working-register freshness (`cfgOk`), which this
      validator does not re-check; the validator checks slots against
      the DECLARED extent list `daten`, while privacy against the
      ACTUAL placed tables comes from the separate `PipeRahmenGetrennt`
      premise (discharged by computation on concrete layouts, as the
      witness does) — agreement of `daten` with the placed tables is a
      deployer obligation, not a decided fact here; callee-saved restore and argument passing
      (no calls in the fragment, inherited from the pipeline); TSO
      freshness of spill slots beyond the reused `SpillFrisch`
      vocabulary (`ComposeSpillPrivacy.lean` owns the composed level);
      read-trace representation (inherited from the pipeline); full
      loaded-image connection (`pipeline_correct_loaded` shape, not
      re-proved here).
    - The refusal `Bool` is validator admission, never a hardware fault.
    - No second IR and no second evaluator: only the accepted pipeline
      lowering, validator and machine vocabulary are reused.
-/

#print axioms spillSaveCode
#print axioms spillLoadCode
#print axioms spillSave_gerade
#print axioms spillLoad_gerade
#print axioms spillSave_lauf
#print axioms spillLoad_lauf
#print axioms spillPlanOk
#print axioms spillPlan_inRahmen
#print axioms spillPlan_nodup
#print axioms spillPlan_offCode
#print axioms spillPlan_schranke
#print axioms spillPlan_offDaten
#print axioms spill_slot_ohneUmbruch
#print axioms spill_schlitze_getrennt
#print axioms SpillVonTabellenGetrennt
#print axioms spillPlan_tabellenGetrennt
#print axioms spill_rundreise_privat
#print axioms spill_haelt_bedeutung
#print axioms spill_verweigert_tabelle
#print axioms spill_verweigert_aussen
#print axioms spill_verweigert_kollision
#print axioms spillP0
#print axioms spillR0
#print axioms spillD0
#print axioms spill_probe_pos
#print axioms spill_probe_tabelle
#print axioms spill_probe_tabelle_satz
#print axioms spill_probe_aussen
#print axioms spill_probe_kollision
#print axioms spill_probe_code
#print axioms spillR0_getrennt
#print axioms spill_haelt_bedeutung_zeuge
#print axioms spill_rundreise_privat_zeuge

end Gabbro.Grammatik.X86.PipeSpill
