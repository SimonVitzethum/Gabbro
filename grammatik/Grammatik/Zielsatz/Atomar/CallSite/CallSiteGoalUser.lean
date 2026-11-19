/- C08 body duties for the accepted literal-post unit and its stronger companion.

   Wave E's checked unit has a literal-true function post. The same body's
   functional result = 1 post remains a separate program-logic proof: it holds
   with the conditional foreign summary and fails without it. No acceptance
   claim is made for that stronger companion. -/
module

public import Grammatik.Zielsatz.Atomar.CallSite.CallSiteGoalFixture

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.CallSiteGoal

open Gabbro.Grammatik Speichermodell

/-- A summary fact read off an answered question whose pre held. -/
theorem antwort_Q {D : Deklaration} {P : Programm D} {Q : AxEns D} {O : Orakel D}
    (hQ : AxVertragOP (PreQ P) Q O) {a : D.Ax} {σ1 : World D} {ρ1 : Env D (D.aparams a)}
    {σ' : World D} {v : ErgVal D (D.aerg a)} (h : axiomAntwort O a σ1 ρ1 = (σ', some v))
    (hp : PreQ P a (σ1.fragt (.inl a)) ρ1 = true) : Q a σ' v = true := by
  have h1 : (O.wirkt a (σ1.fragt (.inl a)) ρ1).1 = σ' := congrArg Prod.fst h
  have h2 : einpassenErg O.zeiger (D.aerg a) (O.wirkt a (σ1.fragt (.inl a)) ρ1).2 = some v :=
    congrArg Prod.snd h
  rw [← h1]
  exact hQ a σ1 ρ1 v hp h2

/-- **The body's outcomes** against every oracle of the class: a return of `1`, or the named
    hardware stop of an undecodable answer. -/
theorem body_out (O' : Orakel wD) (hQ : AxVertragOP (PreQ wP) wQ O') (S : SperrInv wD)
    (U : Umwelt wD) (A : AUmwelt wD) (passes : Nat)
    (R : ∀ f : wD.Fn, World wD → Env wD (wD.params f) → RufAusgang f)
    (σ : World wD) (ρ : Env wD (wD.params ())) :
    (∃ σ' v, zahl v = 1 ∧
      execEndHA (V := vertragVon wD ()) S O' U A passes R (wP.rumpf ()) σ ρ = .zurueck σ' v) ∨
    execEndHA (V := vertragVon wD ()) S O' U A passes R (wP.rumpf ()) σ ρ =
      .hardware (.annahme ()) := by
  simp only [wP, body, execEndHA]
  split
  · rename_i σ' v heq
    have hq := antwort_Q hQ heq ((preQ_sw wP rfl _ _).trans rfl)
    refine Or.inl ⟨_, _, ?_, rfl⟩
    exact of_decide_eq_true hq
  · exact Or.inr rfl

/-- The same executable body with the original functional postcondition. -/
def summaryProgram : Programm wD :=
  { wP with ensures := fun _ => .eq (.var .here) (.lit 1) }

private theorem body_duties (P : Programm wD)
    (sameBody : P.rumpf () = wP.rumpf ()) (samePre : PreQ P = PreQ wP)
    (post : ∀ (σ σ' : World wD) (ρ : Env wD (wD.params ()))
      (v : ErgVal wD (wD.erg ())), zahl v = 1 → EnsAmRueck P () σ σ' ρ v)
    (passes : Nat) (T : wD.Tab ⊕ wD.Glob → Prop) :
    KoerperGutSA P passes wQ (SperrInv.leer wD) T () := by
  refine ⟨?_, ?_⟩
  · intro O' _ _ hQ U _ A _ R _ _ σ ρ _
    rw [samePre] at hQ
    refine ⟨fun σ' v h => ?_, fun g h => ?_⟩
    · rw [sameBody] at h
      rcases body_out O' hQ (SperrInv.leer wD) U A passes R σ ρ with ⟨σ'', v', hv, he⟩ | he
      · rw [he] at h
        cases h
        exact post _ _ _ _ hv
      · rw [he] at h
        cases h
    · rw [sameBody] at h
      rcases body_out O' hQ (SperrInv.leer wD) U A passes (torRuf P R) σ ρ with
        ⟨σ'', v', _, he⟩ | he <;> rw [he] at h <;> cases h
  · intro O' _ _ hQ U _ A _ R _ _ σ ρ _ e h
    rw [samePre] at hQ
    rw [sameBody] at h
    rcases body_out O' hQ (SperrInv.leer wD) U A passes R σ ρ with
      ⟨σ'', v', _, he⟩ | he <;> rw [he] at h <;> cases h

/-- The accepted unit's literal post, caller duty and absence of logic outcomes. -/
theorem koerper (passes : Nat) (T : wD.Tab ⊕ wD.Glob → Prop) :
    KoerperGutSA wP passes wQ (SperrInv.leer wD) T () :=
  body_duties wP rfl rfl (fun _ _ _ _ _ => rfl) passes T

/-- The original functional post is proved over the same body and foreign contract. -/
theorem summary_koerper (passes : Nat) (T : wD.Tab ⊕ wD.Glob → Prop) :
    KoerperGutSA summaryProgram passes wQ (SperrInv.leer wD) T () :=
  body_duties summaryProgram rfl rfl (fun _ _ _ _ h => decide_eq_true h) passes T

theorem invRueck (passes : Nat) (T : wD.Tab ⊕ wD.Glob → Prop) :
    InvGutSA wP passes wQ (SperrInv.leer wD) T () := by
  intro O' _ _ _ U _ A _ R _ _ σ ρ _ σ' v _ i
  exact nomatch i

theorem invGrund (passes : Nat) (T : wD.Tab ⊕ wD.Glob → Prop) :
    InvGutGrundA wP passes wQ (SperrInv.leer wD) T () := by
  intro O' _ _ _ U _ A _ R _ _ σ ρ _ σ' r
  exact r.elim0

/-- **(b), the user's logic with the rely**, and the start duty. -/
theorem user : NutzerPflichtA wE where
  logik := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro passes f
      cases f
      exact ⟨koerper passes _, invRueck passes _, invGrund passes _⟩
    · intro L
      exact nomatch L
    · exact fun _ _ _ _ _ _ => rfl
    · exact ptrVerfeinert_trivial (P := wP) (fun _ _ _ => rfl) (fun _ => rfl)
  start :=
    { sperren := fun L => nomatch L
      req := fun _ _ => rfl }

/-- An oracle that answers `0`: frame-respecting, outside `g`'s summary. -/
def zeroO : Orakel wD where
  wirktL := fun _ σ _ => ({ σ with spur := [] }, 0)
  regLiesL := fun e => nomatch e
  regSchreib := fun e => nomatch e
  sichtbarL := fun e => nomatch e

theorem zeroO_gut : GutO zeroO := by
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

/-- **THE DUTY USES `g`'s SUMMARY**: with the empty summary (`true`) in place of `wQ`, the body
    duty of the stronger companion is false -- `zeroO` is then in the class and the body returns `0`
    against `ensures result == 1`. -/
theorem summary_used (T : wD.Tab ⊕ wD.Glob → Prop) :
    ¬ KoerperGutSA summaryProgram 0 (fun _ _ _ => true) (SperrInv.leer wD) T () := by
  intro h
  have hk := h.1 zeroO (gutO_rahmenO zeroO_gut) ⟨(fun r => nomatch r), (fun g => nomatch g)⟩
    (fun _ _ _ _ _ _ => rfl) (fun _ σ => σ) (fun L => nomatch L) idA (havocA_id _)
    (rufAusV []) (rufAusV_rahmen (vertraegeOkR_nil summaryProgram))
    (rufAusV_ohneVorbedingung (vertraegeOkR_nil summaryProgram).1) world .nil rfl
  exact absurd (hk.1 _ _ rfl) (by unfold EnsAmRueck; decide)

end Gabbro.Grammatik.Zielsatz.CallSiteGoal
