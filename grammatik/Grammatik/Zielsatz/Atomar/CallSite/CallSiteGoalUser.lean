/- C08 R3b: THE BODY DUTIES OF THE WITNESS UNIT (premise (b), `NutzerPflichtA`).

   The body `let r = g(1); return r` proves `ensures result == 1` against every frame-respecting
   oracle of the conditional class `AxVertragOP (PreQ wP) wQ`: at the call the pre `1 != 0` holds,
   so the class grants `g`'s summary "the answer is 1" (`body_out`). The duty USES that summary:
   with the empty summary in its place the same duty is false (`summary_used`), since an oracle
   answering `0` is then admitted and the body returns `0`. -/
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

/-- The body triple, the caller duty, and no `logik` outcome. -/
theorem koerper (passes : Nat) (T : wD.Tab ⊕ wD.Glob → Prop) :
    KoerperGutSA wP passes wQ (SperrInv.leer wD) T () := by
  refine ⟨?_, ?_⟩
  · intro O' _ _ hQ U _ A _ R _ _ σ ρ _
    refine ⟨fun σ' v h => ?_, fun g h => ?_⟩
    · rcases body_out O' hQ (SperrInv.leer wD) U A passes R σ ρ with ⟨σ'', v', hv, he⟩ | he
      · rw [he] at h
        cases h
        exact decide_eq_true hv
      · rw [he] at h
        cases h
    · rcases body_out O' hQ (SperrInv.leer wD) U A passes (torRuf wP R) σ ρ with
        ⟨σ'', v', _, he⟩ | he <;> rw [he] at h <;> cases h
  · intro O' _ _ hQ U _ A _ R _ _ σ ρ _ e h
    rcases body_out O' hQ (SperrInv.leer wD) U A passes R σ ρ with
      ⟨σ'', v', _, he⟩ | he <;> rw [he] at h <;> cases h

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
    duty of the same program is false -- `zeroO` is then in the class and the body returns `0`
    against `ensures result == 1`. -/
theorem summary_used (T : wD.Tab ⊕ wD.Glob → Prop) :
    ¬ KoerperGutSA wP 0 (fun _ _ _ => true) (SperrInv.leer wD) T () := by
  intro h
  have hk := h.1 zeroO (gutO_rahmenO zeroO_gut) ⟨(fun r => nomatch r), (fun g => nomatch g)⟩
    (fun _ _ _ _ _ _ => rfl) (fun _ σ => σ) (fun L => nomatch L) idA (havocA_id _)
    (rufAusV []) (rufAusV_rahmen (vertraegeOkR_nil wP))
    (rufAusV_ohneVorbedingung (vertraegeOkR_nil wP).1) world .nil rfl
  exact absurd (hk.1 _ _ rfl) (by unfold EnsAmRueck; decide)

end Gabbro.Grammatik.Zielsatz.CallSiteGoal
