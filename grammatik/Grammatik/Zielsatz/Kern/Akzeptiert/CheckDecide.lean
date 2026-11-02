/- C16: admission of declared checks -- the decider and the Prop.

   `checkOkB` decides one check: the probe answers `Bool` on a reason-free channel,
   threads exactly the Duty, is read-only over the declared carriers, every gate
   consumes the Duty, the gates are pairwise distinct, the probe is none of its
   gates, and every other function the probe may call is read-only and forges no
   Duty. `checkB` lifts this over the unit with pairwise-distinct check names.
   `CheckAdmission` is the same as a Prop, with the call-graph closure
   (`CheckRahmen`, through `reachB`) beside the exact expansion. The iff between
   Bool and Prop (`checkB_iff`, `checkOkB_iff`) and the site duty
   (`CheckSitePflicht`, `Akzeptiert/Teil3`) build on these. -/
module

public import Grammatik.Kern.Syntax.Satz.Pruefung
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtMehrfaden

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Pruefung

variable [DecidableEq D.Fn]

/-- The member tables of a carrier list. -/
def tabsOf (cs : List (D.Tab ⊕ D.Glob)) : List D.Tab :=
  cs.filterMap fun | .inl t => some t | .inr _ => none

/-- The member statics of a carrier list. -/
def globsOf (cs : List (D.Tab ⊕ D.Glob)) : List D.Glob :=
  cs.filterMap fun | .inr g => some g | .inl _ => none

/-- Gate names are pairwise distinct: one Duty is never duplicated across them. -/
def toreEindeutig : List D.Fn → Bool
  | [] => true
  | g :: rest => decide (∀ x ∈ rest, x ≠ g) && toreEindeutig rest

/-- Every other function the probe may call is read-only and forges no Duty. -/
def rahmenOkB (P : Programm D) (tabs : List D.Tab) (globs : List D.Glob) (fns : List D.Fn)
    (c : CheckDecl D) : Bool :=
  fns.all fun f => !(reachB P fns c.probe f) || decide (f = c.probe) ||
    (tabs.all (fun t => !((D.signatur f).schreibt t)) &&
     globs.all (fun g => !((D.signatur f).gschreibt g)) &&
      decide (c.duty ∉ (D.signatur f).produziert))

/-- One check, decided. -/
def checkOkB (P : Programm D) (tabs : List D.Tab) (globs : List D.Glob) (fns : List D.Fn)
    (c : CheckDecl D) : Bool :=
  decide (D.erg c.probe = some .bool) &&
  decide ((D.signatur c.probe).gruende = 0) &&
  decide ((D.signatur c.probe).konsumiert = [c.duty]) &&
  decide ((D.signatur c.probe).produziert = [c.duty]) &&
  tabs.all (fun t => !((D.signatur c.probe).schreibt t)) &&
  globs.all (fun g => !((D.signatur c.probe).gschreibt g)) &&
  c.gates.all (fun g => decide (c.duty ∈ (D.signatur g).konsumiert) && decide (g ∈ fns)) &&
  toreEindeutig c.gates &&
  decide (c.probe ∉ c.gates) &&
  decide (c.probe ∈ fns) &&
  rahmenOkB P tabs globs fns c

/-- Check names are pairwise distinct. -/
def eindeutigeNamen : List (CheckDecl D) → Bool
  | [] => true
  | c :: rest => decide (∀ d ∈ rest, d.name ≠ c.name) && eindeutigeNamen rest

/-- The checks of a unit, decided. -/
def checkB (P : Programm D) (tabs : List D.Tab) (globs : List D.Glob) (fns : List D.Fn)
    (checks : List (CheckDecl D)) : Bool :=
  checks.all (checkOkB P tabs globs fns) && eindeutigeNamen checks

/-- The call-graph closure of one check: whatever the probe may call (other than
    itself) is read-only and produces no Duty. -/
def CheckRahmen (P : Programm D) (fs : List D.Fn) (c : CheckDecl D) : Prop :=
  ∀ f, reachB P fs c.probe f = true → f ≠ c.probe →
    (∀ t, (D.signatur f).schreibt t = false) ∧
    (∀ g, (D.signatur f).gschreibt g = false) ∧
    c.duty ∉ (D.signatur f).produziert

/-- The admission of declared checks: every check expands exactly, its call graph
    keeps the frame, probe and gates are functions of the unit, and no two checks
    share a name. -/
def CheckAdmission (P : Programm D) (fs : List D.Fn) (checks : List (CheckDecl D)) : Prop :=
  (∀ c ∈ checks, CheckExpansion P c) ∧
  (∀ c ∈ checks, CheckRahmen P fs c) ∧
  (∀ c ∈ checks, c.probe ∈ fs) ∧
  (∀ c ∈ checks, ∀ g ∈ c.gates, g ∈ fs) ∧
  List.Nodup (checks.map CheckDecl.name)

/-- No check is vacuously admitted: the admission over the empty list holds. -/
theorem CheckAdmission.nil (P : Programm D) (fs : List D.Fn) : CheckAdmission P fs [] :=
  ⟨fun c hc => absurd hc List.not_mem_nil, fun c hc => absurd hc List.not_mem_nil, fun c hc => absurd hc List.not_mem_nil, fun c hc _ _ => absurd hc List.not_mem_nil, List.nodup_nil⟩

end Pruefung

end Gabbro.Grammatik
