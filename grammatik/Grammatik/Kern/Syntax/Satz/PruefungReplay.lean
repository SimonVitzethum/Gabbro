/- C16 inventory item 14: G/GX replay and ownership conservation.

    The check machinery neither creates nor drops the linear Duty:
    `CheckErhaltung` is the exact one-in-one-out signature shape (the probe
    produces exactly the Duty it consumes), and `erhaltung_kreislauf` runs it
    once round the completed cycle (probe produces, admitted gate consumes).
    `replayEintrag` is the replay half: folding the same completed cycle on G
    or on GX yields the same evidence entry, because the entry is a pure
    function of probe, report and gate -- never of the memory model or the
    interleaving. The machine-indexed fold (reading the evidence off the
    ghost history at the reached machine, through the C08/C09 transport) is
    the lead's build step; this file fixes the statement that fold proves. -/
module

public import Grammatik.Kern.Syntax.Satz.Pruefung
public import Grammatik.Kern.Syntax.Satz.PruefungAbschluss

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Erhaltung

variable [DecidableEq D.Fn]

/-- Ownership conservation at the signature: the probe produces exactly the
    Duty it consumes -- one completed run moves one Duty in and one Duty out,
    creating none and dropping none. -/
def CheckErhaltung (P : Programm D) (c : CheckDecl D) : Prop :=
  (D.signatur c.probe).produziert = [c.duty] ∧
    (D.signatur c.probe).konsumiert = [c.duty]

/-- Conservation follows from the exact expansion. -/
theorem erhaltung_aus_expansion {P : Programm D} {c : CheckDecl D}
    (h : CheckExpansion P c) : CheckErhaltung P c :=
  ⟨CheckExpansion.produziert h, CheckExpansion.konsumiert h⟩

/-- One completed cycle preserves the Duty: the probe produces it, the
    discharging gate consumes that same report once. -/
theorem erhaltung_kreislauf {P : Programm D} {c : CheckDecl D}
    {r : CheckReport} {g : D.Fn} (h : CheckEntladung P c r g) :
    (D.signatur c.probe).produziert = [c.duty] ∧
      c.duty ∈ (D.signatur g).konsumiert :=
  ⟨CheckExpansion.produziert h.1, h.2.1⟩

/-- The replayed entry: folding the same completed cycle on G or on GX yields
    the same evidence -- the entry is a pure function of probe, report and
    gate, never of the memory model or the interleaving. -/
def replayEintrag (c : CheckDecl D) (r : CheckReport) (g : D.Fn) :
    CheckEvidenz D :=
  ⟨c.probe, r, false, some g⟩

/-- The replayed entry is stable: whoever folds the same completed cycle
    reads the same producer, the same report and the same consumer. -/
theorem replayEintrag_stabil (c : CheckDecl D) (r : CheckReport) (g : D.Fn)
    (e : CheckEvidenz D) (h : e = replayEintrag c r g) :
    e.erzeuger = c.probe ∧ e.bericht = r ∧ e.tor = some g := by
  subst h
  exact ⟨rfl, rfl, rfl⟩

/-! ## Witnesses: conservation and replay on the fixture -/

/-- The fixture probe conserves its Duty. -/
theorem erhaltung_zeuge : CheckErhaltung pruefP pruefC :=
  erhaltung_aus_expansion pruef_expansion

/-- The completed negative cycle preserves the Duty into the same gate. -/
theorem erhaltung_kreislauf_zeuge :
    (pruefD.signatur pruefC1.probe).produziert = [pruefC1.duty] ∧
      pruefC1.duty ∈ (pruefD.signatur false).konsumiert :=
  erhaltung_kreislauf entladung_falsch_zeuge

/-- The replayed negative entry is the consumed one, by computation. -/
theorem replayEintrag_zeuge :
    replayEintrag pruefC1 messBerichtFalsch false =
      (⟨true, messBerichtFalsch, false, some false⟩ : CheckEvidenz pruefD) := rfl

end Erhaltung

end Gabbro.Grammatik
