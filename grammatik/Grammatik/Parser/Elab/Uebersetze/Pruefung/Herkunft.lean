/- C16 inventory item 13: report/token provenance through call push and
    normal return, over the real call machine.

    The report a caller receives is the one the callee produced: `istPush`
    spots the probe activation on the call log (`eintritt`), `istPop` its
    normal pop (`rueck`), and `rueckUrteil` reads the verdict -- the `Bool`
    answer of the generated producer -- off that pop. Pushes, other
    functions' pops and error-channel returns (`why`) yield no verdict: no
    completed report is synthesized there. `rueckPasst` ties the verdict to
    the report, and `herkunft_aus_entladung` carries it into the discharged
    evidence entry. This file is registered in `Alle/Teil1` (not `Satz`),
    because the call machine sits above `Satz.lean` in the import order. -/
module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineF.T1Basis
public import Grammatik.Kern.Syntax.Satz.Pruefung
public import Grammatik.Kern.Syntax.Satz.PruefungAbschluss

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

section HerkunftMaschine

variable [DecidableEq D.Fn]

/-- Whether the event pushes the check's probe activation. -/
def istPush (c : CheckDecl D) : RufEreignisF D → Bool
  | .eintritt f _ _ => decide (f = c.probe)
  | _ => false

/-- Whether the event is the probe's normal pop. -/
def istPop (c : CheckDecl D) : RufEreignisF D → Bool
  | .rueck f _ _ _ _ => decide (f = c.probe)
  | _ => false

/-- A `Bool` answer read as a verdict. -/
def urteilAusErg (v : ErgVal D (some .bool)) : CheckUrteil := v

/-- The verdict the probe returned: the `Bool` answer of the generated
    producer, read off its normal-pop event. `none` on pushes, on other
    functions' pops and on error-channel returns -- no completed report is
    synthesized there. -/
def rueckUrteil (c : CheckDecl D) : RufEreignisF D → Option CheckUrteil
  | .rueck f _ v _ _ =>
    match he : D.erg f with
    | some .bool => if f = c.probe then some (urteilAusErg (he ▸ v)) else none
    | _ => none
  | _ => none

/-- The event's verdict is the report's: the report a caller receives is the
    one the callee produced. -/
def rueckPasst (c : CheckDecl D) (ev : RufEreignisF D)
    (r : CheckReport) : Prop :=
  rueckUrteil c ev = some r.urteil

/-- The discharged entry carries the callee-produced verdict. -/
theorem herkunft_aus_entladung {P : Programm D} {c : CheckDecl D}
    {r : CheckReport} {g : D.Fn} {ev : RufEreignisF D}
    (h : CheckEntladung P c r g) (hp : rueckPasst c ev r) :
    (⟨c.probe, r, false, some g⟩ : CheckEvidenz D).bericht.urteil = r.urteil ∧
      rueckUrteil c ev = some r.urteil :=
  ⟨rfl, hp⟩

/-! ## Witnesses: push and pop on the fixture, refusals elsewhere -/

/-- The probe activation pushes. -/
theorem herkunft_push_fixture (rho : Env pruefD (pruefD.params true))
    (s0 : World pruefD) :
    istPush pruefC (.eintritt true rho s0) = true := rfl

/-- The probe's normal return pops. -/
theorem herkunft_pop_fixture (rho : Env pruefD (pruefD.params true))
    (v : ErgVal pruefD (pruefD.erg true)) (s0 s1 : World pruefD) :
    istPop pruefC (.rueck true rho v s0 s1) = true := rfl

/-- Another function's push is not this check's activation. -/
theorem herkunft_fremd_push (rho : Env pruefD (pruefD.params false))
    (s0 : World pruefD) :
    istPush pruefC (.eintritt false rho s0) = false := rfl

/-- An error-channel return pops nothing and yields no verdict: a halted
    path synthesizes no completed report. -/
theorem herkunft_grund_kein_pop (rho : Env pruefD (pruefD.params true))
    (r : Fin (pruefD.gruende true)) (s0 s1 : World pruefD) :
    istPop pruefC (.why true rho r s0 s1) = false ∧
      rueckUrteil pruefC (.why true rho r s0 s1) = none := ⟨rfl, rfl⟩

/-- The verdict off the normal pop is the probe's answer. -/
theorem herkunft_fixture_pop (rho : Env pruefD (pruefD.params true))
    (v : ErgVal pruefD (pruefD.erg true)) (s0 s1 : World pruefD) :
    rueckUrteil pruefC (.rueck true rho v s0 s1) =
      some (urteilAusErg (CheckExpansion.erg pruef_expansion ▸ v)) := rfl

end HerkunftMaschine

end Gabbro.Grammatik
