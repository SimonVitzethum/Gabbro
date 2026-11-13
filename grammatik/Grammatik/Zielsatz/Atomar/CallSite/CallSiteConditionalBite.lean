/- C08: the conditional class is strictly larger even when a global summary
   is realizable. A body returning an off-pre software answer is refused. -/
module

public import Grammatik.Zielsatz.Atomar.CallSite.CallSiteReplayBlocker

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.CallSiteConditionalBite

/-- One boolean-returning function and software item, with the zero argument. -/
def decl : Deklaration :=
  { CallSiteZeuge.decl with
    sigNr := fun _ => { CallSiteZeuge.sig with erg := some .bool }
    aerg := fun _ => some .bool }

def contract : CallContract decl (decl.asignatur ()) where
  pre := .fls
  post := .tru

def args : Args decl [] [] (decl.aparams ()) :=
  .cons (.widen (by decide) (by decide) (.lit 0)) .nil

/-- The returned boolean depends directly on the off-pre software answer. -/
def body : Endblock decl (vertragVon decl ()) false [] [] :=
  .bindAxiom () args rfl (fun t => nomatch t) (fun g => nomatch g)
    (fun t => nomatch t) (fun g => nomatch g)
    (.ret (.val (.var .here)) List.Perm.nil)

def program : Programm decl where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .var .here
  rumpf := fun _ => body
  axVertrag := fun _ => contract

/-- The summary promises a true result; the interface pre never holds. -/
def summary : AxEns decl := fun _ _ v => v

def oracle (answer : Int) : Orakel decl where
  wirktL := fun _ σ _ => ({ σ with spur := [] }, answer)
  regLiesL := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbarL := fun g => nomatch g

def world : World decl :=
  { slots := fun t => nomatch t
    globs := fun g => nomatch g
    spur := [] }

def rho : Env decl (decl.aparams ()) :=
  .cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil

theorem oracle_frame (answer : Int) : RahmenO (oracle answer) :=
  fun _ _ _ => rahmen_gleich rfl rfl

/-- This is not an empty-global-class exhibit: the constant-one oracle
    satisfies the unconditional summary at every query. -/
theorem global_summary : AxVertragO summary (oracle 1) := by
  intro a σ ρ v hv
  have he : some true = some v := hv
  cases he
  rfl

theorem conditional_summary : AxVertragOP (PreQ program) summary (oracle 0) := by
  intro a σ ρ v hp
  have hf : PreQ program a (σ.fragt (.inl a)) ρ = false := by
    rw [preQ_sw program (by cases a; rfl)]
    rfl
  rw [hf] at hp
  exact False.elim (Bool.false_ne_true hp)

theorem not_global_summary : ¬ AxVertragO summary (oracle 0) := by
  intro h
  exact Bool.false_ne_true (h () world rho false rfl)

/-- An off-pre result cannot establish the function's true-result post. -/
theorem off_pre_body_refused : ¬ KoerperGutA program 0 summary () := by
  intro h
  have hk := h (oracle 0) (oracle_frame 0) conditional_summary (rufAusV [])
    (rufAusV_rahmen (vertraegeOkR_nil program)).1
    (rufAusV_ohneVorbedingung (vertraegeOkR_nil program).1) world .nil rfl
  exact Bool.false_ne_true (hk.1 _ false rfl)

/-- Both classes are inhabited, but only the conditional one admits the
    off-pre bad answer, which makes the answer-dependent body inadmissible. -/
theorem oracle_class_strict :
    AxVertragO summary (oracle 1) ∧
      AxVertragOP (PreQ program) summary (oracle 1) ∧
      AxVertragOP (PreQ program) summary (oracle 0) ∧
      ¬ AxVertragO summary (oracle 0) ∧ ¬ KoerperGutA program 0 summary () :=
  ⟨global_summary, axVertragOP_of_O _ global_summary, conditional_summary,
    not_global_summary, off_pre_body_refused⟩

end Gabbro.Grammatik.Zielsatz.CallSiteConditionalBite

#print axioms Gabbro.Grammatik.Zielsatz.CallSiteConditionalBite.oracle_class_strict
