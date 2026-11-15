module
public import Bruecke.Kette.Block
public import Bruecke.Anweisung.Match.ReasonKopf
@[expose] public section
namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg} {C : Fin u.fns.length → Prop}
variable {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
  {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}

/-- Every case is related, including cases that the current input does not select. -/
inductive ReasonRelated (u : UProg) (C : Fin u.fns.length → Prop) (c : Fin u.fns.length)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    {Γ : Ctx} (fn : UFn) (ids : List String) (Λ : List (Res (declOf u))) :
    (n : Nat) → Nat → GrundArms (declOf u) (verOf u c) false Γ Λ Λ n →
      List (String × List Gabbro.Body.Stmt) → Prop where
  | nil (offset : Nat) : ReasonRelated u C c O passes R fn ids Λ 0 offset .nil []
  | cons {n offset : Nat} {b : Block (declOf u) (verOf u c) false Γ Λ Λ}
      {rest : GrundArms (declOf u) (verOf u c) false Γ Λ Λ n} {bb : List Gabbro.Body.Stmt}
      {bs : List (String × List Gabbro.Body.Stmt)} :
      (∀ σ ρ s, WGRel u σ s.world → PositionalLRel fn ids 0 ρ s.local' →
        BlockZiel_G u C c O passes R fn ids b σ ρ s bb) →
      ReasonRelated u C c O passes R fn ids Λ n (offset + 1) rest bs →
      ReasonRelated u C c O passes R fn ids Λ (n + 1) offset (.cons b rest) ((caseLabel offset, bb) :: bs)

theorem reasonArms_G {P : Programm (declOf u)} (G : GesenktC u C P) (S : Getragen u C)
    (hc : C c) (hRR : RespektiertRahmen P R) :
    ∀ fuel count k offset ss {Γ : Ctx} (fn ft : UFn) (ns : BodyNames)
      (Λ : List (Res (declOf u))) (ga : GrundArms (declOf u) (verOf u c) false Γ Λ Λ count)
      tail bs tailZ used,
      UmfangB Γ fn ns → Sicht u ft fn → (∀ st ∈ ss, st ∈ (fnAt u c).body) →
      BindFrischL (protectedNames fn.params fn.kinds) ss →
      lowGArmsL u c Γ fn fuel Λ [] count ss = .ok (ga, tail) →
      reasonArmsZ u k ft count offset ns ss = some (bs, tailZ, used) →
      tailZ = tail ∧ tail <:+ ss ∧ ReasonRelated u C c O passes R fn ns.active Λ count offset ga bs := by
  intro fuel
  induction fuel with
  | zero =>
    intro count k offset ss Γ fn ft ns Λ ga tail bs tailZ used hU hV hm hF hG hB
    cases hG
  | succ fuel ih =>
    intro count k offset ss Γ fn ft ns Λ ga tail bs tailZ used hU hV hm hF hG hB
    cases count with
    | zero =>
      change Except.ok (GrundArms.nil, ss) = .ok (ga, tail) at hG
      cases hG
      simp only [reasonArmsZ, Option.some.injEq, Prod.mk.injEq] at hB
      obtain ⟨rfl, rfl, _⟩ := hB
      exact ⟨rfl, List.suffix_refl _, .nil offset⟩
    | succ count =>
      obtain ⟨gbody, grest, remaining, hg, hcG, rfl⟩ := lowGArms_succ hG
      obtain ⟨bbody, remainingZ, allocated, hb, hcB⟩ := reasonArmsZ_succ hB
      obtain ⟨hr, hsuf, hBody⟩ := laufSeq_G G S c hc O passes R hRR fuel k ss fn ft ns
        ⟨Λ, gbody⟩ remaining bbody remainingZ allocated hU hV hm hF hg hb
      subst remainingZ
      rcases hcG with ⟨rfl, rfl⟩ | ⟨m, rest, rfl, hrG, hgrest⟩
      · rcases hcB with ⟨_, rfl, rfl, _⟩ | ⟨m, rest, bs, hn, _⟩
        · cases grest
          exact ⟨rfl, hsuf, .cons hBody (.nil _)⟩
        · cases hn
      · rcases hcB with ⟨hn, _⟩ | ⟨m', restZ, bs', hn, hrB, hbrest, rfl⟩
        · cases hn
        · cases hn
          subst hrG
          cases hrB
          have hsuf' : rest <:+ ss := (List.suffix_cons _ _).trans hsuf
          obtain ⟨htail, hsufTail, hRelated⟩ := ih (m + 1) k
            (offset + 1) rest fn ft (ns.resume allocated) Λ grest tail bs' tailZ used
            (hU.afterSeq hb) hV (fun st h => hm st (mem_of_suffix hsuf' h))
            (bindFrischL_suffix hF hsuf') hgrest hbrest
          exact ⟨htail, hsufTail.trans hsuf', .cons hBody hRelated⟩

/-- Selection uses the ordinal position, never an accidentally equal source case name. -/
theorem ReasonRelated.select {Γ : Ctx} {fn : UFn} {ids : List String} {Λ : List (Res (declOf u))}
    {count offset : Nat} {ga : GrundArms (declOf u) (verOf u c) false Γ Λ Λ count}
    {bs : List (String × List Gabbro.Body.Stmt)}
    (h : ReasonRelated u C c O passes R fn ids Λ count offset ga bs) (i : Fin count) :
    ∃ (b : Block (declOf u) (verOf u c) false Γ Λ Λ) (bb : List Gabbro.Body.Stmt),
      (∀ σ ρ, execGrund O passes R ga i σ ρ = execBlock O passes R b σ ρ) ∧
      (∀ ρB s, Gabbro.Body.pickArm ρB bs (caseLabel (offset + i.val)) s = Gabbro.Body.exec ρB bb s) ∧
      (∀ σ ρ s, WGRel u σ s.world → PositionalLRel fn ids 0 ρ s.local' →
        BlockZiel_G u C c O passes R fn ids b σ ρ s bb) := by
  induction h with
  | nil => exact (Nat.not_lt_zero _ i.isLt).elim
  | @cons n offset b rest bb bs hBody hRest ih =>
    rcases i with ⟨i, hi⟩
    cases i with
    | zero =>
      refine ⟨b, bb, fun σ ρ => rfl, fun ρB s => ?_, hBody⟩
      simp only [Nat.add_zero, Gabbro.Body.pickArm, ↓reduceIte]
    | succ i =>
      obtain ⟨b', bb', hG, hB, hRelated⟩ := ih ⟨i, Nat.lt_of_succ_lt_succ hi⟩
      refine ⟨b', bb', fun σ ρ => hG σ ρ, fun ρB s => ?_, hRelated⟩
      have hne : caseLabel offset ≠ caseLabel (offset + (i + 1)) := by
        intro he
        have := caseLabel_injective he
        omega
      simp only [Gabbro.Body.pickArm, hne, ↓reduceIte]
      have heq : offset + (i + 1) = (offset + 1) + i := by omega
      rw [heq]
      exact hB ρB s

end Gabbro.Bruecke
