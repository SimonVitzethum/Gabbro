/- C16 inventory items 9 and 12: declared-check identity, completed reports for
   both verdicts, and linear Duty discharge.

   * `CheckIdentitaet` (item 9): the resolved descriptor names unit functions --
     the probe and every gate are members, the probe is none of its gates, and
     the gates are pairwise distinct. It follows from the admission
     (`identitaet_aus_zulassung`); the fixture pins it (`pruef_identitaet_zeuge`).
   * `CheckAbschluss` (item 12): a completed report. Duty records a completed
     measurement with its verdict, never proof of the prose claim: the probe
     produces the Duty on every normal return (`CheckExpansion.produziert`),
     including `false`. A report completes the check when every sample was
     actually observed (`vollstaendig`) and every declared floor has exactly one
     evaluated outcome (`berichtTraegt`). Both verdicts complete
     (`abschluss_wahr_zeuge`, `abschluss_falsch_zeuge`); an unread sample or a
     surplus outcome does not.
   * `CheckEntladung` (item 12): the consuming gate discharges that same report
     once -- the gate consumes the Duty and is one of the declared gates. A
     success-only gate needs the explicit user-logic precondition
     (`CheckEntladungErfolg`): the verdict is `true` and every floor holds. The
     discharged report travels on as the consumed evidence entry of the goal leg
     (`entladung_eintrag`, `Zielsatz/Kern/Spec/Teil4`). -/
module

public import Grammatik.Kern.Syntax.Satz.Pruefung
public import Grammatik.Kern.Syntax.Satz.PruefungMessung

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Abschluss

variable [DecidableEq D.Fn]

/-- The declared-check identity: the resolved descriptor names functions of the
    unit -- the probe and every gate are members, the probe is none of its
    gates, and the gates are pairwise distinct. -/
def CheckIdentitaet (fs : List D.Fn) (c : CheckDecl D) : Prop :=
  c.probe ∈ fs ∧ (∀ g ∈ c.gates, g ∈ fs) ∧ c.probe ∉ c.gates ∧ c.gates.Nodup

/-- The identity follows from the admission. -/
theorem identitaet_aus_zulassung {P : Programm D} {fs : List D.Fn}
    {checks : List (CheckDecl D)} {c : CheckDecl D}
    (hA : CheckAdmission P fs checks) (hc : c ∈ checks) :
    CheckIdentitaet fs c := by
  obtain ⟨hexp, _, hprobe, hgates, _⟩ := hA
  obtain ⟨_, _, _, _, _, _, _, hfrisch, hnodup⟩ := hexp c hc
  exact ⟨hprobe c hc, hgates c hc, hfrisch, hnodup⟩

/-- Every declared floor has exactly one evaluated outcome in the report. -/
def berichtTraegt (r : CheckReport) (c : CheckDecl D) : Prop :=
  r.boeden.length = c.boden.length

/-- A completed report: the probe expands exactly, every sample was actually
    observed, and every declared floor has its evaluated outcome. -/
def CheckAbschluss (P : Programm D) (c : CheckDecl D) (r : CheckReport) : Prop :=
  CheckExpansion P c ∧ r.vollstaendig ∧ berichtTraegt r c

/-- The consuming gate discharges that same report once: the gate consumes the
    Duty and is one of the declared gates. -/
def CheckEntladung (P : Programm D) (c : CheckDecl D) (r : CheckReport)
    (g : D.Fn) : Prop :=
  CheckAbschluss P c r ∧ c.duty ∈ (D.signatur g).konsumiert ∧ g ∈ c.gates

/-- A success-only gate needs the explicit user-logic precondition: the
    verdict is `true` and every applicable floor holds. -/
def CheckEntladungErfolg (P : Programm D) (c : CheckDecl D) (r : CheckReport)
    (g : D.Fn) : Prop :=
  CheckEntladung P c r g ∧ r.urteil = true ∧ bodenHalten r

/-- The discharged report travels on as the consumed evidence entry of the goal
    leg: the same producer, the same report, no longer live, consumed by exactly
    the discharging gate. -/
theorem entladung_eintrag {P : Programm D} {c : CheckDecl D} {r : CheckReport}
    {g : D.Fn} (h : CheckEntladung P c r g) :
    (⟨c.probe, r, false, some g⟩ : CheckEvidenz D).lebt = false ∧
      ∃ g' ∈ c.gates, (⟨c.probe, r, false, some g⟩ : CheckEvidenz D).tor = some g' := by
  obtain ⟨_, _, hg⟩ := h
  exact ⟨rfl, g, hg, rfl⟩

/-! ## The fixture: the identity, both verdicts completed, the gate discharge -/

/-- The fixture identity: the probe and its gate are the unit's functions,
    distinctly. -/
theorem pruef_identitaet_zeuge : CheckIdentitaet [true, false] pruefC := by
  refine ⟨List.mem_cons.mpr (Or.inl rfl), ?_, by decide, by decide⟩
  · intro g hg
    have hf : g = false := List.mem_singleton.mp hg
    subst hf
    exact List.Mem.tail _ (List.Mem.head _)

/-- The fixture check with one declared floor: the expansion is verdict-free,
    so the same proof shape admits it. -/
def pruefC1 : CheckDecl pruefD :=
  { pruefC with boden := [("g", true)] }

/-- The floored fixture expands exactly. -/
theorem pruef1_expansion : CheckExpansion pruefP pruefC1 := by
  refine ⟨rfl, rfl, rfl, rfl, fun t => t.elim, fun g => g.elim, ?_, ?_, ?_⟩
  · intro g hg
    change Bool at g
    have hf : g = false := List.mem_singleton.mp hg
    subst hf
    exact by decide
  · change ¬ (true : Bool) ∈ ([false] : List Bool)
    decide
  · change ([false] : List Bool).Nodup
    decide

/-- The completed report with a positive verdict: the sample was read, the
    floor holds, the Duty is produced. -/
theorem abschluss_wahr_zeuge : CheckAbschluss pruefP pruefC1 messBerichtWahr :=
  ⟨pruef1_expansion, by decide, rfl⟩

/-- The completed report with a negative verdict: the sample was read, the
    floor failed, the verdict records it -- and the same Duty is produced. -/
theorem abschluss_falsch_zeuge : CheckAbschluss pruefP pruefC1 messBerichtFalsch :=
  ⟨pruef1_expansion, by decide, rfl⟩

/-- The failed floor stays a distinguishable negative outcome. -/
theorem abschluss_falsch_boden_zeuge : ¬ bodenHalten messBerichtFalsch := by decide

/-- An unread sample completes nothing. -/
theorem abschluss_luecke_zeuge :
    ¬ CheckAbschluss pruefP pruefC1 { proben := [{ ort := "x", punkt := 0, wert := 3,
      gelesen := false }], boeden := [true], urteil := true } := by
  intro h
  exact berichtUnvollstaendig_zeuge h.2.1

/-- A surplus floor outcome completes nothing: every declared floor has exactly
    one evaluated outcome. -/
theorem abschluss_ueberhang_zeuge :
    ¬ CheckAbschluss pruefP pruefC1 { proben := [], boeden := [true, true],
      urteil := true } := by
  intro h
  exact absurd h.2.2 (by decide)

/-- The gate discharges the completed positive report. -/
theorem entladung_wahr_zeuge : CheckEntladung pruefP pruefC1 messBerichtWahr false :=
  ⟨abschluss_wahr_zeuge, by decide, List.mem_singleton_self _⟩

/-- The gate discharges the completed negative report too: the Duty threads
    through `false` returns, and the failure stays report data. -/
theorem entladung_falsch_zeuge : CheckEntladung pruefP pruefC1 messBerichtFalsch false :=
  ⟨abschluss_falsch_zeuge, by decide, List.mem_singleton_self _⟩

/-- The success-only gate admits the held positive report. -/
theorem entladung_erfolg_zeuge :
    CheckEntladungErfolg pruefP pruefC1 messBerichtWahr false :=
  ⟨entladung_wahr_zeuge, rfl, by decide⟩

/-- The success-only gate refuses the negative report: its explicit
    user-logic precondition fails. -/
theorem entladung_erfolg_abgelehnt_zeuge :
    ¬ CheckEntladungErfolg pruefP pruefC1 messBerichtFalsch false := by
  intro h
  exact absurd h.2.1 (by decide)

/-- The discharged negative report travels on as the consumed evidence entry. -/
theorem entladung_eintrag_zeuge :
    (⟨pruefC1.probe, messBerichtFalsch, false, some false⟩ : CheckEvidenz pruefD).lebt = false ∧
      ∃ g' ∈ pruefC1.gates,
        (⟨pruefC1.probe, messBerichtFalsch, false, some false⟩ : CheckEvidenz pruefD).tor = some g' :=
  entladung_eintrag entladung_falsch_zeuge

end Abschluss

end Gabbro.Grammatik
