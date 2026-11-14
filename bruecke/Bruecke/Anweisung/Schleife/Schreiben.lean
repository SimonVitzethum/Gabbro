module
public import Bruecke.Anweisung.Schleife.Kopf
public import Bruecke.Kette.Schritt
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

/-- Admitted world and local writes have a normal canonical outcome in every related state. -/
theorem loopWrite_ok {loopMode : Bool} (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn}
    {ns : BodyNames} {Λ Λ' : List (Res (declOf u))} {st : UStmt} {ss : List UStmt}
    {gst : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ'} {b : Gabbro.Body.Stmt}
    (hg : loopWritesB (st :: ss) = true) (hmark : st ≠ .blkEnd)
    (hlow : lowStmtL (l := loopMode) u c Γ fn Λ st = .ok ⟨Λ', gst⟩)
    (hb : schrittB u fn ns st = some (b, fn, ns)) (hU : UmfangB Γ fn ns)
    (hT : TabEindeutig u) (hN : NumericStatics u) (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    ∃ σ' ρ', execStmt O passes R gst σ ρ = .ok σ' ρ' := by
  cases st
  case blkEnd => exact (hmark rfl).elim
  case assign p fld i v =>
    obtain ⟨hb', _, _⟩ := schrittB_stmt hb (fun _ _ _ h => by cases h)
      (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)
    rw [lowStmtL_assign hT c Γ fn Λ p fld i v] at hlow
    cases hs : lowAssignDurchL (l := loopMode) u c Γ fn Λ p fld i v with
    | error e => simp only [hs, Except.map] at hlow; cases hlow
    | ok g =>
      simp only [hs, Except.map] at hlow
      cases hlow
      obtain ⟨σ', _, _, _, _, hex, _⟩ := lowAssignDurch_named_sim c hs hb' hU hT O passes R σ ρ s hW hL
      exact ⟨σ', ρ, hex⟩
  case assignTab t fld i v =>
    obtain ⟨hb', _, _⟩ := schrittB_stmt hb (fun _ _ _ h => by cases h)
      (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)
    rw [lowStmtL_assignTab hT c Γ fn Λ t fld i v] at hlow
    cases hs : lowAssignTabL (l := loopMode) u c Γ fn Λ t fld i v with
    | error e => simp only [hs, Except.map] at hlow; cases hlow
    | ok g =>
      simp only [hs, Except.map] at hlow
      cases hlow
      obtain ⟨σ', _, _, _, _, hex, _⟩ := lowAssignTab_named_sim c hs hb' hU hT O passes R σ ρ s hW hL
      exact ⟨σ', ρ, hex⟩
  case assignGlob name v =>
    obtain ⟨hb', _, _⟩ := schrittB_stmt hb (fun _ _ _ h => by cases h)
      (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)
    simp only [lowStmtL] at hlow
    cases hs : lowAssignGlobL (l := loopMode) u c Γ fn Λ name v with
    | error e => simp only [hs, Except.map] at hlow; cases hlow
    | ok g =>
      simp only [hs, Except.map] at hlow
      cases hlow
      obtain ⟨σ', _, hex, _⟩ := lowAssignGlob_sim c hs hb' hN hU hT O passes R σ ρ s hW hL
      exact ⟨σ', ρ, hex⟩
  case setVar x v =>
    obtain ⟨hn, id, e, hid, he, rfl, _, _⟩ := schrittB_setVar hb
    simp only [lowStmtL] at hlow
    cases hs : lowSetVarL (l := loopMode) u c Γ fn Λ x v with
    | error err => simp only [hs, Except.map] at hlow; cases hlow
    | ok st =>
      simp only [hs, Except.map] at hlow
      cases hlow
      obtain ⟨σ', ρ', _, hex, _⟩ :=
        lowSetVar_named_sim c hs hn hid he hU hT O passes R σ ρ s hW hL
      exact ⟨σ', ρ', hex⟩
  case setVarB x v =>
    obtain ⟨id, e, hid, he, rfl, _, _⟩ := schrittB_setVarB hb
    simp only [lowStmtL] at hlow
    cases hs : lowSetVarBL (l := loopMode) u c Γ fn Λ x v with
    | error err => simp only [hs, Except.map] at hlow; cases hlow
    | ok st =>
      simp only [hs, Except.map] at hlow
      cases hlow
      obtain ⟨σ', ρ', _, hex, _⟩ :=
        lowSetVarB_named_sim c hs hid he hU hT O passes R σ ρ s hW hL
      exact ⟨σ', ρ', hex⟩
  all_goals cases hg

/-- A whole admitted iteration has a normal outcome; no loop-control outcome is discarded. -/
theorem loopWrites_sim {P : Programm (declOf u)} (G : GesenktC u C P) (S : Getragen u C)
    (c : Fin u.fns.length) (hc : C c) (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (hRR : RespektiertRahmen P R) :
    ∀ n k ss {Γ : Ctx} (fn ft : UFn) (ns : BodyNames) {Λ Λ' : List (Res (declOf u))}
      (block : Block (declOf u) (verOf u c) true Γ Λ Λ') (tail : List UStmt)
      (bs : List Gabbro.Body.Stmt) (used : List String),
      UmfangB Γ fn ns → Sicht u ft fn → (∀ st ∈ ss, st ∈ (fnAt u c).body) → loopWritesB ss = true →
      lowSeqL (l := true) u c Γ fn n Λ [] ss = .ok (⟨Λ', block⟩, .blkEnd :: tail) →
      seqZ u k ft ns ss = some (bs, .blkEnd :: tail, used) →
      ∀ σ ρ s, WGRel u σ s.world → PositionalLRel fn ns.active 0 ρ s.local' →
        ∃ σ' ρ' s', execBlock O passes R block σ ρ = .ok σ' ρ' ∧
          (∃ A, Strecke_G u C A s s' bs) ∧ WGRel u σ' s'.world ∧
          PositionalLRel fn ns.active 0 ρ' s'.local'
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _ => by cases h
  | _ + 1, 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by cases h
  | _ + 1, _ + 1, [], _, _, _, _, _, _, _, _, _, _, _, _, _, hg, _, _ => by cases hg
  | n + 1, k + 1, st :: ss, Γ, fn, ft, ns, Λ, Λ', block, tail, bs, used, hU, hV, hm, hg, hG, hB => by
    cases st
    case blkEnd =>
      rw [lowSeq_blkEnd] at hG
      cases hG
      simp only [seqZ, Option.some.injEq, Prod.mk.injEq] at hB
      obtain ⟨rfl, _, _⟩ := hB
      intro σ ρ s hW hL
      exact ⟨σ, ρ, s, rfl, ⟨[], Strecke_G.leer s⟩, hW, hL⟩
    case assign | assignTab | assignGlob | setVar | setVarB =>
      obtain ⟨b, ft', ns', ys, hb, hy, rfl⟩ := seqZ_schritt_some hB (by exact True.intro)
      obtain ⟨hbN, hft, hns⟩ := schrittB_einzeln_sicht hV hb (by exact True.intro)
      subst ft' ns'
      obtain ⟨Λ₁, gs, ⟨Λ₂, restBlock⟩, hgs, hq, hblock⟩ :=
        lowSeq_einzeln_ok hG (by exact True.intro)
      have hΛ : Λ' = Λ₂ := congrArg Sigma.fst hblock
      subst Λ'
      have hcons : block = Block.cons gs restBlock := by cases hblock; rfl
      subst block
      intro σ ρ s hW hL
      obtain ⟨σ₁, ρ₁, he⟩ := loopWrite_ok c hg (by intro h; cases h) hgs hbN hU S.tab S.statics
        O passes R σ ρ s hW hL
      have hSim := stmtZiel_einzeln_G G S c hc O passes R hRR (hm _ (List.mem_cons_self ..))
        (by exact True.intro) hgs hbN hU σ ρ s hW hL
      obtain ⟨A₁, s₁, hStretch, hW₁, hL₁⟩ := hSim.2.2 σ₁ ρ₁ he
      obtain ⟨σ₂, ρ₂, s₂, hex, ⟨A₂, hStretch₂⟩, hW₂, hL₂⟩ :=
        loopWrites_sim G S c hc O passes R hRR n k ss fn ft ns restBlock tail ys used hU hV
          (fun st h => hm st (List.mem_cons_of_mem _ h)) hg hq hy σ₁ ρ₁ s₁ hW₁ hL₁
      refine ⟨σ₂, ρ₂, s₂, ?_, ⟨A₁ ++ A₂, Strecke_G.cons hStretch hStretch₂⟩, hW₂, hL₂⟩
      rw [execBlockZ_cons_ok O passes R _ _ he]
      exact hex
    all_goals cases hg

end Gabbro.Bruecke
