/- C08 R3b: the binding contract covers question worlds, whereas the body
   oracle class also quantifies over worlds without a question. A trace-faithful
   binding separates these statements even with a satisfiable software pre.
   The on-pre body really calls the item and uses its result-dependent summary. -/
module

public import Grammatik.Zielsatz.Atomar.CallSiteConditionalBite

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.CallSiteQuestionBlocker

abbrev decl := CallSiteConditionalBite.decl

def contract : CallContract decl (decl.asignatur ()) where
  pre := .not (.eq (.var .here) (.lit 0))
  post := .var .here

def args : Args decl [] [] (decl.aparams ()) :=
  .cons (.widen (by decide) (by decide) (.lit 1)) .nil

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

def summary : AxEns decl := fun _ _ v => v

def world : World decl :=
  { slots := fun t => nomatch t
    globs := fun g => nomatch g
    spur := [] }

def rho (b : Bool) : Env decl (decl.aparams ()) :=
  .cons (if b then ⟨1, by decide, by decide⟩ else ⟨0, by decide, by decide⟩) .nil

/-- Actual queries always carry their question. The empty-trace answer is
    deliberately different, while memory and the complete trace are preserved. -/
def oracle : Orakel decl where
  wirkt := fun _ σ _ => (σ, if σ.spur.isEmpty then 0 else 1)
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun g => nomatch g

def unit : Einheit decl where
  P := program
  S := SperrInv.leer decl
  Q := summary
  starts := [⟨(), .nil⟩]
  sp0 := world.speicher

theorem pre_true (σ : World decl) : AxVor program.axVertrag () σ (rho true) := by
  rfl

theorem pre_false (σ : World decl) : ¬ AxVor program.axVertrag () σ (rho false) := by
  change ¬ false = true
  exact Bool.false_ne_true

theorem oracle_gut : GutO oracle := by
  intro a σ ρ
  refine ⟨rahmen_gleich rfl rfl, rfl, ?_⟩
  intro hgt hgg
  refine ⟨[], [], [], ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro t
    exact nomatch t
  · intro g
    exact nomatch g
  · intro t
    exact nomatch t
  · intro g
    exact nomatch g
  · intro m
    exact nomatch m
  · intro L
    exact nomatch L

theorem binding : ForeignVertrag unit oracle := by
  constructor
  · intro a hsw σ ρ hp v hv
    have he : some true = some v := hv
    cases he
    rfl
  · intro a hsw σ ρ
    change some (Sum.inl true) ≠ none
    intro h
    cases h

theorem post_cover : PostDeckt unit := by
  intro a hsw σ0 ρ σ1 v hp
  exact hp

theorem hardware [RootNativeFloat.Hardware] : HardwareAnnahmenHw oracle unit.Q :=
  ⟨oracle_gut, ⟨fun r => nomatch r, fun g => nomatch g⟩,
    (fun a hsw => absurd rfl hsw), inferInstance⟩

/-- A real call with argument one establishes the caller's true-result post.
    Its proof consumes the conditional summary at that call; the pre is neither
    constant true nor unsatisfiable. The budget and handler are arbitrary. -/
theorem on_pre_body (passes : Nat) : KoerperGutA program passes summary () := by
  intro O hr hQ R hR hOV σ ρ hreq
  have hρ : ρ = .nil := by cases ρ; rfl
  subst hρ
  have hpre : PreQ program () (σ.fragt (.inl ())) (rho true) = true := by
    rw [preQ_sw program rfl]
    rfl
  have hs := hQ () (σ.fragt (.inl ())) (rho true)
    (decide ((O.wirkt () (σ.fragt (.inl ())) (rho true)).2 ≠ 0)) hpre rfl
  refine ⟨?_, ?_⟩
  · intro σ' v hrun
    change (EndAusgang.zurueck (O.wirkt () (σ.fragt (.inl ())) (rho true)).1
      (decide ((O.wirkt () (σ.fragt (.inl ())) (rho true)).2 ≠ 0)) :
      EndAusgang (vertragVon decl ()) false []) =
      EndAusgang.zurueck σ' v at hrun
    cases hrun
    exact hs
  · intro g hrun
    change (EndAusgang.zurueck (O.wirkt () (σ.fragt (.inl ())) (rho true)).1
      (decide ((O.wirkt () (σ.fragt (.inl ())) (rho true)).2 ≠ 0)) :
      EndAusgang (vertragVon decl ()) false []) =
      EndAusgang.logik (Logik.vorbedingung g) at hrun
    cases hrun

/-- The on-pre call actually returns true under the lawful binding. -/
theorem on_pre_execution :
    execEnd oracle 0 (rufAusV []) body world .nil =
      EndAusgang.zurueck (world.fragt (.inl ())) true := by
  rfl

/-- The stronger class asks about an empty trace too. The pre still holds
    there, but this unasked query returns false, refuting class membership. -/
theorem not_conditional : ¬ AxVertragOP (PreQ unit.P) unit.Q oracle := by
  intro h
  have hp : PreQ unit.P () world (rho true) = true := by
    rw [preQ_sw unit.P rfl]
    rfl
  exact Bool.false_ne_true (h () world (rho true) false hp rfl)

/-- R3b's proposed actual-binding membership implication is false, even with
    the hardware premise, a nontrivial passing pre, and a substantive body duty.
    This refutes the proposed proof step, not the eventual call-site goal. -/
theorem actual_binding_class_blocker [RootNativeFloat.Hardware] :
    ForeignVertrag unit oracle ∧ PostDeckt unit ∧ HardwareAnnahmenHw oracle unit.Q ∧
      AxVor program.axVertrag () world (rho true) ∧
      ¬ AxVor program.axVertrag () world (rho false) ∧
      (∀ passes, KoerperGutA program passes summary ()) ∧
      ¬ AxVertragOP (PreQ unit.P) unit.Q oracle :=
  ⟨binding, post_cover, hardware, pre_true world, pre_false world, on_pre_body, not_conditional⟩

end Gabbro.Grammatik.Zielsatz.CallSiteQuestionBlocker

#print axioms Gabbro.Grammatik.Zielsatz.CallSiteQuestionBlocker.on_pre_body
#print axioms Gabbro.Grammatik.Zielsatz.CallSiteQuestionBlocker.actual_binding_class_blocker
