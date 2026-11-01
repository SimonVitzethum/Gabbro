module

public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Kern.Syntax.Fehler.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
variable {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
variable {V : Vertrag D} {l : Bool}

/-- A raised ground does not continue. -/
theorem AusF.folge_grund (σ : World D) (r : Fin V.gruende)
    (nach : World D → Env D Γ → AusF V l Γ) :
    (AusF.widen (.why σ r) : AusF V l Γ).folge nach =
      .widen (.why σ r) :=
  by rfl

/-- A consumed `leave` does not continue. -/
theorem AusF.folge_leave (h : l = true) (σ : World D) (ρ : Env D Γ)
    (nach : World D → Env D Γ → AusF V l Γ) :
    (AusF.widen (.leave h σ ρ) : AusF V l Γ).folge nach =
      .widen (.leave h σ ρ) :=
  by rfl

/-- A consumed `next` does not continue. -/
theorem AusF.folge_next (h : l = true) (σ : World D) (ρ : Env D Γ)
    (nach : World D → Env D Γ → AusF V l Γ) :
    (AusF.widen (.next h σ ρ) : AusF V l Γ).folge nach =
      .widen (.next h σ ρ) :=
  by rfl

/-! ## 9. Stuck-or-fault implies own logic or named fault -/

/-- Stuck: the run carries no post-state. In `Semantik.lean` there is no stuck
    VALUE -- `eval` is total, `exec` always answers -- so stuck is the ABSENCE
    of a post-state, which a named fault shares (`endZustandF_fehler`). -/
def IstStecken : AusF V l Γ → Prop
  | a => endZustandF a = none

/-- Stuck implies named: a run without post-state is the author's logic or a
    named fault -- the `exec_sicher` shape of S3 design A, §6, proved on the
    parallel outcome without touching `Ausgang`. -/
theorem stecken_heisst_benannt (a : AusF V l Γ) (h : IstStecken a) :
    IstBenannt a := by
  cases a with
  | fehler k => trivial
  | widen o =>
      cases o with
      | ok σ ρ => exact absurd h (by simp only [IstStecken, endZustandF, reduceCtorEq, not_false_eq_true])
      | zurueck σ v => exact absurd h (by simp only [IstStecken, endZustandF, reduceCtorEq, not_false_eq_true])
      | why σ r => exact absurd h (by simp only [IstStecken, endZustandF, reduceCtorEq, not_false_eq_true])
      | leave h' σ ρ => exact absurd h (by simp only [IstStecken, endZustandF, reduceCtorEq, not_false_eq_true])
      | next h' σ ρ => exact absurd h (by simp only [IstStecken, endZustandF, reduceCtorEq, not_false_eq_true])
      | logik e => trivial
      | hardware e => trivial

/-- Named implies stuck: the converse -- together they say stuck MEANS named. -/
theorem benannt_heisst_stecken (a : AusF V l Γ) (h : IstBenannt a) :
    IstStecken a := by
  cases a with
  | fehler k => rfl
  | widen o =>
      cases o with
      | ok σ ρ => exact False.elim h
      | zurueck σ v => exact False.elim h
      | why σ r => exact False.elim h
      | leave h' σ ρ => exact False.elim h
      | next h' σ ρ => exact False.elim h
      | logik e => rfl
      | hardware e => rfl


end Gabbro.Grammatik
