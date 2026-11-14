module
public import Bruecke.Kette.Formen.Tag
public import Bruecke.Kette.Formen.ReasonRelation
@[expose] public section
namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg} {C : Fin u.fns.length → Prop}
variable {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
  {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}

theorem reasonArms_G_with {loopMode : Bool} (bound : Nat)
    (hseq : ∀ fuel, fuel < bound → ∀ k ss {Γ : Ctx} (fn ft : UFn) (ns : BodyNames)
      {Λ : List (Res (declOf u))} (p : Σ Λ', Block (declOf u) (verOf u c) loopMode Γ Λ Λ')
      tail bs tailZ used,
      UmfangB Γ fn ns → Sicht u ft fn → (∀ st ∈ ss, st ∈ (fnAt u c).body) →
      BindFrischL (protectedNames fn.params fn.kinds) ss →
      lowSeqL u c Γ fn fuel Λ [] ss = .ok (p, tail) →
      seqZ u k ft ns ss = some (bs, tailZ, used) →
      tailZ = tail ∧ tail <:+ ss ∧
      ∀ σ ρ s, WGRel u σ s.world → PositionalLRel fn ns.active 0 ρ s.local' →
        BlockZiel_G u C c O passes R fn ns.active p.2 σ ρ s bs) :
    ∀ fuel, fuel ≤ bound → ∀ count k offset ss {Γ : Ctx} (fn ft : UFn) (ns : BodyNames)
      (Λ : List (Res (declOf u))) (ga : GrundArms (declOf u) (verOf u c) loopMode Γ Λ Λ count)
      tail bs tailZ used,
      UmfangB Γ fn ns → Sicht u ft fn → (∀ st ∈ ss, st ∈ (fnAt u c).body) →
      BindFrischL (protectedNames fn.params fn.kinds) ss →
      lowGArmsL u c Γ fn fuel Λ [] count ss = .ok (ga, tail) →
      reasonArmsZ u k ft count offset ns ss = some (bs, tailZ, used) →
      tailZ = tail ∧ tail <:+ ss ∧ ReasonRelated u C c O passes R fn ns.active Λ count offset ga bs := by
  intro fuel
  induction fuel with
  | zero =>
    intro hbound count k offset ss Γ fn ft ns Λ ga tail bs tailZ used hU hV hm hF hG hB
    cases hG
  | succ fuel ih =>
    intro hbound count k offset ss Γ fn ft ns Λ ga tail bs tailZ used hU hV hm hF hG hB
    cases count with
    | zero =>
      change Except.ok (GrundArms.nil, ss) = .ok (ga, tail) at hG
      cases hG
      simp only [reasonArmsZ, readReasonArms, Option.some.injEq, Prod.mk.injEq] at hB
      obtain ⟨rfl, rfl, _⟩ := hB
      exact ⟨rfl, List.suffix_refl _, .nil offset⟩
    | succ count =>
      obtain ⟨gbody, grest, remaining, hg, hcG, rfl⟩ := lowGArms_succ hG
      obtain ⟨bbody, remainingZ, allocated, hb, hcB⟩ := reasonArmsZ_succ hB
      obtain ⟨hr, hsuf, hBody⟩ := hseq fuel (by omega) k ss fn ft ns
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
          rw [hrG] at hrB
          cases hrB
          have hsuf' : rest <:+ ss := (List.suffix_cons _ _).trans hsuf
          obtain ⟨htail, hsufTail, hRelated⟩ := ih (by omega) (m + 1) k
            (offset + 1) rest fn ft (ns.resume allocated) Λ grest tail bs' tailZ used
            (hU.afterSeq hb) hV (fun st h => hm st (mem_of_suffix hsuf' h))
            (bindFrischL_suffix hF hsuf') hgrest hbrest
          exact ⟨htail, hsufTail.trans hsuf', .cons hBody hRelated⟩

end Gabbro.Bruecke
