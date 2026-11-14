module
public import Bruecke.Kette.RahmenBlock
public import Bruecke.Anweisung.Match.ReasonKopf
public import Bruecke.Anweisung.Match.ReasonRahmen
@[expose] public section
namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg} {C : Fin u.fns.length → Prop} {c : Fin u.fns.length}

theorem reasonArms_statisch (S : Getragen u C) (hc : C c) (ρB : Gabbro.Body.Env) :
    ∀ fuel count k offset ss {Γ : Ctx} (fn ft : UFn) (ns : BodyNames)
      (Λ : List (Res (declOf u))) (ga : GrundArms (declOf u) (verOf u c) false Γ Λ Λ count)
      tail bs tailZ used,
      Γ = fn.params.map (·.2) → Sicht u ft fn → (∀ st ∈ ss, st ∈ (fnAt u c).body) →
      lowGArmsL u c Γ fn fuel Λ [] count ss = .ok (ga, tail) →
      reasonArmsZ u k ft count offset ns ss = some (bs, tailZ, used) →
      (∀ name gf, fnSuch u name = some gf → (∃ args, CallsIn ss name args) →
        Gabbro.Body.Frame ρB name (writesU gf)) →
      tailZ = tail ∧ tail <:+ ss ∧ (∀ arm ∈ bs, Statisch ρB (writesU (fnAt u c)) arm.2) := by
  intro fuel
  induction fuel with
  | zero =>
    intro count k offset ss Γ fn ft ns Λ ga tail bs tailZ used hΓ hV hm hG hB hF
    cases hG
  | succ fuel ih =>
    intro count k offset ss Γ fn ft ns Λ ga tail bs tailZ used hΓ hV hm hG hB hF
    cases count with
    | zero =>
      change Except.ok (GrundArms.nil, ss) = .ok (ga, tail) at hG
      cases hG
      simp only [reasonArmsZ, Option.some.injEq, Prod.mk.injEq] at hB
      obtain ⟨rfl, rfl, _⟩ := hB
      exact ⟨rfl, List.suffix_refl _, fun _ h => by cases h⟩
    | succ count =>
      obtain ⟨gbody, grest, remaining, hg, hcG, rfl⟩ := lowGArms_succ hG
      obtain ⟨bbody, remainingZ, allocated, hb, hcB⟩ := reasonArmsZ_succ hB
      obtain ⟨hr, hsuf, hBody⟩ := statischSeq_G S c hc ρB fuel k ss fn ft ns
        ⟨Λ, gbody⟩ remaining bbody remainingZ allocated hΓ hV hm hg hb hF
      subst remainingZ
      rcases hcG with ⟨rfl, rfl⟩ | ⟨m, rest, rfl, hrG, hgrest⟩
      · rcases hcB with ⟨_, rfl, rfl, _⟩ | ⟨m, rest, bs, hn, _⟩
        · exact ⟨rfl, hsuf, fun arm h => by rcases List.mem_singleton.mp h with rfl; exact hBody⟩
        · cases hn
      · rcases hcB with ⟨hn, _⟩ | ⟨m', restZ, bs', hn, hrB, hbrest, rfl⟩
        · cases hn
        · cases hn
          rw [hrG] at hrB
          cases hrB
          have hsuf' : rest <:+ ss :=
            (List.suffix_cons UStmt.ifElse rest).trans (by simpa only [hrG] using hsuf)
          obtain ⟨htail, hsufTail, hFrames⟩ := ih (m + 1) k (offset + 1) rest fn ft
            (ns.resume allocated) Λ grest tail bs' tailZ used hΓ hV
            (fun st h => hm st (mem_of_suffix hsuf' h)) hgrest hbrest
            (fun name gf hgf ⟨args, hc⟩ => hF name gf hgf ⟨args, hc.mono (fun _ h => mem_of_suffix hsuf' h)⟩)
          refine ⟨htail, hsufTail.trans hsuf', fun arm h => ?_⟩
          rcases List.mem_cons.mp h with rfl | h
          · exact hBody
          · exact hFrames arm h

end Gabbro.Bruecke
