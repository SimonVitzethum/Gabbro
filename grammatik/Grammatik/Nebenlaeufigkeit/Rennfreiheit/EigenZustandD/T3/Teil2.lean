module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD.T2
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD.T3.Teil1

@[expose] public section

namespace Gabbro.Grammatik.EZD
open Gabbro.Grammatik
variable {D : Deklaration}

theorem blattSlots_dispatch (O : Orakel D) (hO : GutO O)
    (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hleaf : s.istBlatt = true)
    (σ σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf s σ ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ σ.spur)
    (t : D.Tab) :
    (∃ ev ∈ neu, ev.traeger = some (Sum.inl t)) ∨
      (∀ k f, σ'.slots t k f = σ.slots t k f) ∨
      (∃ (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
        (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
        (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
        (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
        (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ),
        (execStmt O passes keinRuf
          (Stmt.axiomCall (V := V) (l := l) a args h hw hg hd hgd) σ ρ).welt =
          some σ' ∧
          D.aschreibt a t = true) := by
  cases s with
  | assignSlot t2 f2 i e hw hL =>
      by_cases ht : t2 = t
      · subst ht
        exact Or.inl ⟨_, assignSlot_neu (Λ' := Λ) O passes σ ρ σ' neu hstep hneu, rfl⟩
      · exact Or.inr (Or.inl fun k f =>
          assignSlot_andere_fest (Λ' := Λ) O passes σ ρ σ' hstep t ht k f)
  | assignThru p t2 ht2 f2 i e hw hL =>
      by_cases ht : t2 = t
      · subst ht
        exact Or.inl ⟨_, assignDurch_neu (Λ' := Λ) O passes σ ρ σ' neu hstep hneu, rfl⟩
      · exact Or.inr (Or.inl fun k f =>
          assignDurch_andere_fest (Λ' := Λ) O passes σ ρ σ' hstep t ht k f)
  | assignSlotRef r t2 ht2 ho f2 e hw hL =>
      by_cases ht : t2 = t
      · subst ht
        exact Or.inl ⟨_, assignSlotRef_neu (Λ' := Λ) O passes σ ρ σ' neu hstep hneu, rfl⟩
      · exact Or.inr (Or.inl fun k f =>
          assignSlotRef_andere_fest (Λ' := Λ) O passes σ ρ σ' hstep t ht k f)
  | assignGlob g e hw hL =>
      exact Or.inr (Or.inl fun k f =>
        assignGlob_slots_fest O passes σ ρ σ' hstep t k f)
  | putBytes t2 f2 hf2 n i hlo hhi e hw hL =>
      by_cases ht : t2 = t
      · subst ht
        by_cases hn : 0 < n
        · obtain ⟨ev, hmem, htr⟩ :=
            schreibBytes_neu (Λ' := Λ) O passes hn σ ρ σ' neu hstep hneu
          exact Or.inl ⟨ev, hmem, htr⟩
        · have hn0 : n = 0 := by omega
          subst hn0
          exact Or.inr (Or.inl fun k f =>
            schreibBytes_null_fest (Λ' := Λ) O passes σ ρ σ' hstep k f)
      · exact Or.inr (Or.inl fun k f =>
          schreibBytes_andere_fest (Λ' := Λ) O passes σ ρ σ' hstep t ht k f)
  | assignVar x e =>
      exact Or.inr (Or.inl fun k f =>
        assignVar_slots_fest O passes σ ρ σ' hstep t k f)
  | shift t2 f2 hτ i von nach hn he hw hL =>
      by_cases ht : t2 = t
      · subst ht
        exact Or.inl ⟨_, uebergang_neu (Λ' := Λ) O passes σ ρ σ' neu hstep hneu, rfl⟩
      · exact Or.inr (Or.inl fun k f =>
          uebergang_andere_fest (Λ' := Λ) O passes σ ρ σ' hstep t ht k f)
  | ite c tb eb => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | onOption o p a => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | onTag v arms => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | onWhy r arms => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | call fn args hp hr =>
      exact Or.inr (Or.inl fun k f =>
        call_slots_fest O passes (Stmt.call fn args hp hr) rfl σ ρ σ' hstep t k f)
  | callInd p args hp hr =>
      exact Or.inr (Or.inl fun k f =>
        callInd_slots_fest O passes (Stmt.callInd p args hp hr) rfl σ ρ σ' hstep t k f)
  | callIndElse p args he hp hr err =>
      exact Or.inr (Or.inl fun k f =>
        callIndElse_slots_fest O passes (Stmt.callIndElse p args he hp hr err) rfl σ ρ σ' hstep t k f)
  | locks L hr body => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | breaking ii body => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | consumeTraverse => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | traverse tt inv body => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | retry n bis body ueb => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | forever a inv body => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | axiomCallElse => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | axiomCall a args h hw hg hd hgd =>
      by_cases ht : D.aschreibt a t = true
      · exact Or.inr (Or.inr ⟨a, args, h, hw, hg, hd, hgd, hstep, ht⟩)
      · have htF : D.aschreibt a t = false := by
          cases hT : D.aschreibt a t with
          | true => exact absurd hT (by simp only [ht, Bool.false_eq_true, not_false_eq_true])
          | false => rfl
        exact Or.inr (Or.inl fun k f =>
          axiomCall_nichtschreibt_fest (Λ' := Λ) O hO passes (Stmt.axiomCall (V := V) (l := l) a args h hw hg hd hgd) rfl t htF σ ρ σ' hstep k f)
  | regWrite r hk e =>
      exact Or.inr (Or.inl fun k f =>
        regSchreib_slots_fest O passes σ ρ σ' hstep t k f)
  | transition r hk m hm hl maske bits =>
      exact Or.inr (Or.inl fun k f =>
        transition_slots_fest O passes (Stmt.transition r hk m hm hl maske bits) rfl σ ρ σ' hstep t k f)
  | publish g e payload hp hw hL =>
      exact Or.inr (Or.inl fun k f =>
        publish_slots_fest O passes σ ρ σ' hstep t k f)
  | advances mm a h hs =>
      exact Or.inr (Or.inl fun k f =>
        advances_slots_fest (Λ' := ((Λ.erase (.marke mm a)) ++ [.marke mm (a + 1)])) O passes (Stmt.advances (V := V) (l := l) mm a h hs) rfl σ ρ σ' hstep t k f)
  | retires mm s2 h a =>
      exact Or.inr (Or.inl fun k f =>
        retires_slots_fest (Λ' := (Λ.erase (.marke mm s2))) O passes (Stmt.retires (V := V) (l := l) mm s2 h a) rfl σ ρ σ' hstep t k f)
  | ret e hΛ =>
      exact Or.inr (Or.inl fun k f =>
        ret_slots_fest O passes σ ρ σ' hstep t k f)
  | retWhy r hΛ =>
      exact Or.inr (Or.inl fun k f =>
        retGrund_slots_fest O passes (Stmt.retWhy r hΛ) rfl σ ρ σ' hstep t k f)
  | leave h =>
      exact Or.inr (Or.inl fun k f =>
        leave_slots_fest O passes (Stmt.leave h) rfl σ ρ σ' hstep t k f)
  | next h =>
      exact Or.inr (Or.inl fun k f =>
        next_slots_fest O passes (Stmt.next h) rfl σ ρ σ' hstep t k f)
  | retScoped e R =>
      refine Or.inr (Or.inl fun k f => ?_)
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rw [(World.gibt_foldl_speicher _ _).1]
      try rfl
  | retWhyScoped r R =>
      refine Or.inr (Or.inl fun k f => ?_)
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rw [(World.gibt_foldl_speicher _ _).1]
      try rfl

/-! ## 10. The step theorem: a foreign step keeps the slots of `t`.

  `pcSchritt_fremd_fest`: invert the `PCSchritt`. Take/release keep
  `M.speicher` by construction (`rfl` after `cases`). For a leaf, run the
  dispatch (§9): a recorded write for `t` contradicts `hNurG` via `hcar`
  (the event's carrier lies in the fired atom's carriers, and the atom is
  in `prog h` at `pc h`); slots kept is the goal; a declared oracle write
  to `t` contradicts `hNurG` the same way when the oracle's declared writes
  are covered by the atom carriers -- since `stmtTraeger` covers them, but
  the fired atom is ARBITRARY `prog` (not `progAus`), the oracle arm needs
  the atom to actually carry `inl t`: it does NOT by `hNurG`. Hence the
  oracle-write arm is impossible under `hNurG` ONLY IF the atom carriers
  cover the oracle writes -- which `hcar` does not guarantee (it constrains
  RECORDED events, and `GutO` records none for the oracle). So the oracle
  arm stays open: the step theorem takes it as an explicit existential
  hypothesis discharged by the witness (whose oracle writes nothing). -/


end Gabbro.Grammatik.EZD
