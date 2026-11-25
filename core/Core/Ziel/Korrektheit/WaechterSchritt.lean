/-
  File:      core/Core/Ziel/Korrektheit/WaechterSchritt.lean
  Subject:   GENERIC transfer lemmas for the joined environments: single-slot writes with static
             or poisoned contributions, unchanged frames, halts, calls and returns.

  The master preservation theorem over all instructions lives in `WaechterErhalt.lean`; every
  case there is one application of a lemma below. Calls reset temporaries (vacuous) and save
  the acting frame (covered by the hypothesis); returns restore a saved frame (covered by
  the saved-continuation conjunct).
-/
module

public import Core.Ziel.Korrektheit.WaechterTransfer

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse

open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Ast

/-- Transfer through a single-slot write with unknown contributions on both sides. -/
theorem transfer_schreibe_unbekannt (code : List Befehl) (frame : Rahmen) (live : Nat → Bool)
    (b : Befehl) (s : Nat) (hmem : b ∈ code) (h : RahmenErfuellt code frame)
    (V : Option Dynamisch)
    (hschreibe : b.auswerten frame live = frame.schreibe s V)
    (hI : beitragInt b s = some .unbekannt) (hT : beitragText b s = some .unbekannt) :
    RahmenErfuellt code (b.auswerten frame live) := by
  have hnoneI : umgebungInt code s = none :=
    umgebungInt_unbekannt code s (unbekanntInt_mem code s b hI hmem)
  have hnoneT : umgebungText code s = none :=
    umgebungText_unbekannt code s (unbekanntText_mem code s b hT hmem)
  have htemp : ∀ slot, (b.auswerten frame live).temp slot =
      if slot = s then V else frame.temp slot := by
    intro slot
    rw [hschreibe]
    by_cases heq : slot = s
    · subst heq
      simp only [Rahmen.schreibe, Function.update_self, eq_self_iff_true, if_true]
    · simp only [Rahmen.schreibe, Function.update_of_ne heq]
      rw [if_neg heq]
  have hfort : (b.auswerten frame live).fortsetzungen = frame.fortsetzungen := by
    rw [hschreibe]
    simp only [Rahmen.schreibe]
  refine ⟨?_, ?_, ?_⟩
  · intro slot lo hi hlook g hg
    rw [htemp slot] at hg
    by_cases heq : slot = s
    · subst heq
      simp only [eq_self_iff_true, if_true] at hg
      rw [hnoneI] at hlook
      cases hlook
    · rw [if_neg heq] at hg
      exact h.1 slot lo hi hlook g hg
  · intro slot l hh hlook d hd cap txt hdt
    rw [htemp slot] at hd
    by_cases heq : slot = s
    · subst heq
      simp only [eq_self_iff_true, if_true] at hd
      rw [hnoneT] at hlook
      cases hlook
    · rw [if_neg heq] at hd
      exact h.2.1 slot l hh hlook d hd cap txt hdt
  · intro k hk
    rw [hfort] at hk
    exact h.2.2 k hk

/-- Transfer through a single-slot write with a static integer contribution. -/
theorem transfer_schreibe_statischInt (code : List Befehl) (frame : Rahmen) (live : Nat → Bool)
    (b : Befehl) (s : Nat) (hmem : b ∈ code) (h : RahmenErfuellt code frame)
    (V : Option Dynamisch)
    (hschreibe : b.auswerten frame live = frame.schreibe s V)
    (hV : ∀ g : Ganzzahl, (((b.auswerten frame live).temp s).bind alsGanzzahl) = some g →
      ∀ L H : Int, umgebungInt code s = some (L, H) → L ≤ g.zahl.wert ∧ g.zahl.wert ≤ H)
    (hT : beitragText b s = some .unbekannt) :
    RahmenErfuellt code (b.auswerten frame live) := by
  have hnoneT : umgebungText code s = none :=
    umgebungText_unbekannt code s (unbekanntText_mem code s b hT hmem)
  have htemp : ∀ slot, (b.auswerten frame live).temp slot =
      if slot = s then V else frame.temp slot := by
    intro slot
    rw [hschreibe]
    by_cases heq : slot = s
    · subst heq
      simp only [Rahmen.schreibe, Function.update_self, eq_self_iff_true, if_true]
    · simp only [Rahmen.schreibe, Function.update_of_ne heq]
      rw [if_neg heq]
  have hfort : (b.auswerten frame live).fortsetzungen = frame.fortsetzungen := by
    rw [hschreibe]
    simp only [Rahmen.schreibe]
  refine ⟨?_, ?_, ?_⟩
  · intro slot lo hi hlook g hg
    by_cases heq : slot = s
    · subst heq
      exact hV g hg lo hi hlook
    · rw [htemp slot, if_neg heq] at hg
      exact h.1 slot lo hi hlook g hg
  · intro slot l hh hlook d hd cap txt hdt
    rw [htemp slot] at hd
    by_cases heq : slot = s
    · subst heq
      simp only [eq_self_iff_true, if_true] at hd
      rw [hnoneT] at hlook
      cases hlook
    · rw [if_neg heq] at hd
      exact h.2.1 slot l hh hlook d hd cap txt hdt
  · intro k hk
    rw [hfort] at hk
    exact h.2.2 k hk

/-- Transfer through a single-slot write with a static text contribution. -/
theorem transfer_schreibe_statischText (code : List Befehl) (frame : Rahmen) (live : Nat → Bool)
    (b : Befehl) (s : Nat) (hmem : b ∈ code) (h : RahmenErfuellt code frame)
    (V : Option Dynamisch)
    (hschreibe : b.auswerten frame live = frame.schreibe s V)
    (hI : beitragInt b s = some .unbekannt)
    (hV : ∀ (d : Dynamisch), (((b.auswerten frame live).temp s) = some d) →
      ∀ (cap : Nat) (t : TextValue cap), d = ⟨.text cap, t⟩ → ∀ L H : Nat,
      umgebungText code s = some (L, H) → L ≤ t.bytes.size ∧ t.bytes.size ≤ H) :
    RahmenErfuellt code (b.auswerten frame live) := by
  have hnoneI : umgebungInt code s = none :=
    umgebungInt_unbekannt code s (unbekanntInt_mem code s b hI hmem)
  have htemp : ∀ slot, (b.auswerten frame live).temp slot =
      if slot = s then V else frame.temp slot := by
    intro slot
    rw [hschreibe]
    by_cases heq : slot = s
    · subst heq
      simp only [Rahmen.schreibe, Function.update_self, eq_self_iff_true, if_true]
    · simp only [Rahmen.schreibe, Function.update_of_ne heq]
      rw [if_neg heq]
  have hfort : (b.auswerten frame live).fortsetzungen = frame.fortsetzungen := by
    rw [hschreibe]
    simp only [Rahmen.schreibe]
  refine ⟨?_, ?_, ?_⟩
  · intro slot lo hi hlook g hg
    rw [htemp slot] at hg
    by_cases heq : slot = s
    · subst heq
      simp only [eq_self_iff_true, if_true] at hg
      rw [hnoneI] at hlook
      cases hlook
    · rw [if_neg heq] at hg
      exact h.1 slot lo hi hlook g hg
  · intro slot l hh hlook d hd cap txt hdt
    by_cases heq : slot = s
    · subst heq
      exact hV d hd cap txt hdt l hh hlook
    · rw [htemp slot, if_neg heq] at hd
      exact h.2.1 slot l hh hlook d hd cap txt hdt
  · intro k hk
    rw [hfort] at hk
    exact h.2.2 k hk

/-- Transfer through an instruction that touches neither temporaries nor continuations. -/
theorem transfer_unveraendert (code : List Befehl) (frame : Rahmen) (live : Nat → Bool)
    (b : Befehl) (hmem : b ∈ code) (h : RahmenErfuellt code frame)
    (htemp : (b.auswerten frame live).temp = frame.temp)
    (hfort : (b.auswerten frame live).fortsetzungen = frame.fortsetzungen) :
    RahmenErfuellt code (b.auswerten frame live) := by
  refine ⟨?_, ?_, ?_⟩
  · intro slot lo hi hlook g hg
    rw [htemp] at hg
    exact h.1 slot lo hi hlook g hg
  · intro slot l hh hlook d hd cap txt hdt
    rw [htemp] at hd
    exact h.2.1 slot l hh hlook d hd cap txt hdt
  · intro k hk
    rw [hfort] at hk
    exact h.2.2 k hk

/-- A halt preserves temporaries and continuations. -/
theorem halt_erfuellt (code : List Befehl) (frame : Rahmen) (reason : Abschluss)
    (h : RahmenErfuellt code frame) :
    RahmenErfuellt code (frame.halt reason) := by
  have ht : (frame.halt reason).temp = frame.temp := rfl
  have hf : (frame.halt reason).fortsetzungen = frame.fortsetzungen := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro slot lo hi hlook g hg
    rw [ht] at hg
    exact h.1 slot lo hi hlook g hg
  · intro slot l hh hlook d hd cap txt hdt
    rw [ht] at hd
    exact h.2.1 slot l hh hlook d hd cap txt hdt
  · intro k hk
    rw [hf] at hk
    exact h.2.2 k hk

/-- A call either keeps the acting temporary or resets it. -/
theorem Rahmen.ruf_temp_cases (frame : Rahmen) (name : Identifier)
    (sources : List (Ty .value)) (bind : Option (Ty .value)) (slot : Nat) :
    (frame.ruf name sources bind).temp slot = frame.temp slot ∨
      (frame.ruf name sources bind).temp slot = none := by
  cases hfind : Funktion.finde frame.funktionen name with
  | none =>
    left
    simp only [Rahmen.ruf, hfind]
    show (frame.halt _).temp slot = _
    rfl
  | some callee =>
    cases hargs : frame.rufArgumente 0 sources callee.parameter with
    | none =>
      left
      simp only [Rahmen.ruf, hfind, hargs]
      show (frame.halt _).temp slot = _
      rfl
    | some args =>
      cases hbind : bind with
      | none =>
        by_cases hab : ((⟨frame.pc + 1, frame.temp, frame.lokale, frame.zaehler,
            frame.obergrenzen, frame.funktion, frame.mass, (none : Option (Ty .value))⟩ :
            Fortsetzung) :: frame.fortsetzungen).any
            (fun k => (k.funktion.map Subtype.val) == some name.val) &&
            !callee.misstAbstieg
        · left
          simp only [Rahmen.ruf, hfind, hargs, hbind, hab, if_true]
          show (frame.halt _).temp slot = _
          rfl
        · right
          simp only [Rahmen.ruf, hfind, hargs, hbind, hab, Bool.not_true, Bool.false_eq_true, ↓reduceIte, if_true, if_false, Id.run]
          show ((fun _ : Nat => none) : Nat → Option Dynamisch) slot = none
          rfl
      | some target =>
        cases hres : callee.result with
        | none =>
          left
          simp only [Rahmen.ruf, hfind, hargs, hbind, hres]
          show (frame.halt _).temp slot = _
          rfl
        | some source =>
          cases hfits : tyFits source target with
          | false =>
            left
            simp only [Rahmen.ruf, hfind, hargs, hbind, hres, hfits]
            show (frame.halt _).temp slot = _
            rfl
          | true =>
            by_cases hab : ((⟨frame.pc + 1, frame.temp, frame.lokale, frame.zaehler,
                frame.obergrenzen, frame.funktion, frame.mass,
                (some target : Option (Ty .value))⟩ : Fortsetzung) ::
                frame.fortsetzungen).any
                (fun k => (k.funktion.map Subtype.val) == some name.val) &&
                !callee.misstAbstieg
            · left
              simp only [Rahmen.ruf, hfind, hargs, hbind, hres, hfits, hab, if_true]
              show (frame.halt _).temp slot = _
              rfl
            · right
              simp only [Rahmen.ruf, hfind, hargs, hbind, hres, hfits, hab, Bool.not_true, Bool.false_eq_true, ↓reduceIte, if_true, if_false, Id.run]
              show ((fun _ : Nat => none) : Nat → Option Dynamisch) slot = none
              rfl

/-- A call either keeps the saved continuations or pushes the acting frame. -/
theorem Rahmen.ruf_fort_cases (frame : Rahmen) (name : Identifier)
    (sources : List (Ty .value)) (bind : Option (Ty .value)) :
    (frame.ruf name sources bind).fortsetzungen = frame.fortsetzungen ∨
      ∃ kont : Fortsetzung, (frame.ruf name sources bind).fortsetzungen =
        kont :: frame.fortsetzungen ∧ kont.temp = frame.temp := by
  cases hfind : Funktion.finde frame.funktionen name with
  | none =>
    left
    simp only [Rahmen.ruf, hfind]
    show (frame.halt _).fortsetzungen = _
    rfl
  | some callee =>
    cases hargs : frame.rufArgumente 0 sources callee.parameter with
    | none =>
      left
      simp only [Rahmen.ruf, hfind, hargs]
      show (frame.halt _).fortsetzungen = _
      rfl
    | some args =>
      cases hbind : bind with
      | none =>
        by_cases hab : ((⟨frame.pc + 1, frame.temp, frame.lokale, frame.zaehler,
            frame.obergrenzen, frame.funktion, frame.mass, (none : Option (Ty .value))⟩ :
            Fortsetzung) :: frame.fortsetzungen).any
            (fun k => (k.funktion.map Subtype.val) == some name.val) &&
            !callee.misstAbstieg
        · left
          simp only [Rahmen.ruf, hfind, hargs, hbind, hab, if_true]
          show (frame.halt _).fortsetzungen = _
          rfl
        · right
          refine ⟨⟨frame.pc + 1, frame.temp, frame.lokale, frame.zaehler, frame.obergrenzen,
            frame.funktion, frame.mass, none⟩, ?_, rfl⟩
          simp only [Rahmen.ruf, hfind, hargs, hbind, hab, Bool.not_true, Bool.false_eq_true, ↓reduceIte, if_true, if_false]
          show ((⟨frame.pc + 1, frame.temp, frame.lokale, frame.zaehler, frame.obergrenzen,
            frame.funktion, frame.mass, (none : Option (Ty .value))⟩ : Fortsetzung) ::
            frame.fortsetzungen) = _
          rfl
      | some target =>
        cases hres : callee.result with
        | none =>
          left
          simp only [Rahmen.ruf, hfind, hargs, hbind, hres]
          show (frame.halt _).fortsetzungen = _
          rfl
        | some source =>
          cases hfits : tyFits source target with
          | false =>
            left
            simp only [Rahmen.ruf, hfind, hargs, hbind, hres, hfits]
            show (frame.halt _).fortsetzungen = _
            rfl
          | true =>
            by_cases hab : ((⟨frame.pc + 1, frame.temp, frame.lokale, frame.zaehler,
                frame.obergrenzen, frame.funktion, frame.mass,
                (some target : Option (Ty .value))⟩ : Fortsetzung) ::
                frame.fortsetzungen).any
                (fun k => (k.funktion.map Subtype.val) == some name.val) &&
                !callee.misstAbstieg
            · left
              simp only [Rahmen.ruf, hfind, hargs, hbind, hres, hfits, hab, if_true]
              show (frame.halt _).fortsetzungen = _
              rfl
            · right
              refine ⟨⟨frame.pc + 1, frame.temp, frame.lokale, frame.zaehler, frame.obergrenzen,
                frame.funktion, frame.mass, some target⟩, ?_, rfl⟩
              simp only [Rahmen.ruf, hfind, hargs, hbind, hres, hfits, hab, Bool.not_true, Bool.false_eq_true, ↓reduceIte, if_true, if_false]
              show ((⟨frame.pc + 1, frame.temp, frame.lokale, frame.zaehler, frame.obergrenzen,
                frame.funktion, frame.mass, (some target : Option (Ty .value))⟩ : Fortsetzung) ::
                frame.fortsetzungen) = _
              rfl

/-- A call preserves the joined environments. -/
theorem Rahmen.ruf_erfuellt (code : List Befehl) (frame : Rahmen) (name : Identifier)
    (sources : List (Ty .value)) (bind : Option (Ty .value))
    (h : RahmenErfuellt code frame) :
    RahmenErfuellt code (frame.ruf name sources bind) := by
  have htemp := Rahmen.ruf_temp_cases frame name sources bind
  have hfort := Rahmen.ruf_fort_cases frame name sources bind
  refine ⟨?_, ?_, ?_⟩
  · intro slot lo hi hlook g hg
    rcases htemp slot with hsame | hnone
    · rw [hsame] at hg
      exact h.1 slot lo hi hlook g hg
    · rw [hnone] at hg
      simp only [Option.bind_none] at hg
      cases hg
  · intro slot l hh hlook d hd cap txt hdt
    rcases htemp slot with hsame | hnone
    · rw [hsame] at hd
      exact h.2.1 slot l hh hlook d hd cap txt hdt
    · rw [hnone] at hd
      cases hd
  · intro k hk
    rcases hfort with hsame | ⟨kont, hpush, hkont⟩
    · rw [hsame] at hk
      exact h.2.2 k hk
    · rw [hpush] at hk
      rcases List.mem_cons.mp hk with rfl | hmem
      · rw [hkont]
        exact ⟨h.1, h.2.1⟩
      · exact h.2.2 k hmem

/-- A return preserves the joined environments. -/
theorem Rahmen.rueckkehr_erfuellt (code : List Befehl) (frame : Rahmen)
    (result : Option Dynamisch) (h : RahmenErfuellt code frame) :
    RahmenErfuellt code (frame.rueckkehr result) := by
  cases hstack : frame.fortsetzungen with
  | nil =>
    have ht : (frame.rueckkehr result).temp = frame.temp := by
      simp only [Rahmen.rueckkehr, hstack]
    have hf : (frame.rueckkehr result).fortsetzungen = frame.fortsetzungen := by
      simp only [Rahmen.rueckkehr, hstack]
    refine ⟨?_, ?_, ?_⟩
    · intro slot lo hi hlook g hg
      rw [ht] at hg
      exact h.1 slot lo hi hlook g hg
    · intro slot l hh hlook d hd cap txt hdt
      rw [ht] at hd
      exact h.2.1 slot l hh hlook d hd cap txt hdt
    · intro k hk
      rw [hf] at hk
      exact h.2.2 k hk
  | cons kont stack =>
    have ht : (frame.rueckkehr result).temp = kont.temp := by
      simp only [Rahmen.rueckkehr, hstack]
    have hf : (frame.rueckkehr result).fortsetzungen = stack := by
      simp only [Rahmen.rueckkehr, hstack]
    have hk : kont ∈ frame.fortsetzungen := by
      rw [hstack]
      exact List.mem_cons_self
    obtain ⟨hki, hkt⟩ := h.2.2 kont hk
    refine ⟨?_, ?_, ?_⟩
    · intro slot lo hi hlook g hg
      rw [ht] at hg
      exact hki slot lo hi hlook g hg
    · intro slot l hh hlook d hd cap txt hdt
      rw [ht] at hd
      exact hkt slot l hh hlook d hd cap txt hdt
    · intro k hk'
      rw [hf] at hk'
      have hmem : k ∈ frame.fortsetzungen := by
        rw [hstack]
        exact List.mem_cons_of_mem _ hk'
      exact h.2.2 k hmem

/-- Entry argument frames preserve the joined environments: they keep the acting
    temporaries or hold no integers and no texts. -/
theorem eintrittArgumente_erfuellt (code : List Befehl) (frame : Rahmen)
    (types : List (Ty .value)) (out : Rahmen)
    (h : frame.eintrittArgumente types = some out)
    (hf : TempSatInt code frame.temp) (hfT : TempSatText code frame.temp) :
    TempSatInt code out.temp ∧ TempSatText code out.temp := by
  have hI : TempSatInt code
      (fun slot => if slot < types.length
        then some (⟨.ownedRegion, slot⟩ : Dynamisch) else none) := by
    intro slot lo hi hlook g hg
    by_cases hlt : slot < types.length
    · simp only [if_pos hlt] at hg
      have hnone : (alsGanzzahl (⟨.ownedRegion, slot⟩ : Dynamisch)) = none := rfl
      have hg2 : alsGanzzahl (⟨.ownedRegion, slot⟩ : Dynamisch) = some g := hg
      rw [hnone] at hg2
      cases hg2
    · simp only [if_neg hlt] at hg
      cases hg
  have hT : TempSatText code
      (fun slot => if slot < types.length
        then some (⟨.ownedRegion, slot⟩ : Dynamisch) else none) := by
    intro slot l hh hlook d hd cap txt hdt
    by_cases hlt : slot < types.length
    · simp only [if_pos hlt] at hd
      cases hd
      have hty := congrArg Sigma.fst hdt
      cases hty
    · simp only [if_neg hlt] at hd
      cases hd
  rcases types with _ | ⟨t, ts⟩
  · cases hdec : decide (([] : List (Ty .value)) = []) with
    | true =>
      have h2 := h
      simp only [Rahmen.eintrittArgumente, hdec] at h2
      cases h2
      exact ⟨hf, hfT⟩
    | false =>
      have hdecT : decide (([] : List (Ty .value)) = []) = true := rfl
      rw [hdecT] at hdec
      cases hdec
  · cases hdec : decide ((t :: ts : List (Ty .value)) = []) with
    | true =>
      have hdecF : decide ((t :: ts : List (Ty .value)) = []) = false := rfl
      rw [hdecF] at hdec
      cases hdec
    | false =>
      have h2 := h
      simp only [Rahmen.eintrittArgumente, hdec] at h2
      by_cases hcond : ((((t :: ts).all fun x => x == Ty.ownedRegion) &&
          decide ((t :: ts).length ≤ frame.arrivalRegions.length)) = true)
      · simp only [hcond] at h2
        cases h2
        exact ⟨hI, hT⟩
      · simp only [hcond] at h2
        cases h2

end Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse
