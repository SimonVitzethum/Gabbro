module
public import Bruecke.Anweisung.Bereich.Ende
public import Bruecke.Kette.Formen.StatischSchritt
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {c : Fin u.fns.length} {C : Fin u.fns.length → Prop}

theorem retZ_form {fn : UFn} {ns : BodyNames} {r : URet} {b : Gabbro.Body.Stmt}
    (h : retZ u fn ns r = some b) : ∃ e, b = .ret e := by
  cases r
  case empty => cases h; exact ⟨none, rfl⟩
  case val sd =>
    simp only [retZ] at h
    cases he : namedSide u fn ns sd with
    | none => rw [he] at h; cases h
    | some e => rw [he] at h; cases h; exact ⟨some e, rfl⟩
  case bool sd =>
    simp only [retZ] at h
    cases he : condZ u fn ns sd with
    | none => rw [he] at h; cases h
    | some e => rw [he] at h; cases h; exact ⟨some e, rfl⟩
  all_goals cases h

theorem endBodyZ_statisch {loopMode : Bool} (S : Getragen u C) (hc : C c) (ρB : Gabbro.Body.Env) :
    ∀ n k ss {Γ : Ctx} (fn ft : UFn) (ns : BodyNames) {Λ : List (Res (declOf u))}
      (ending : Endblock (declOf u) (verOf u c) loopMode Γ Λ) (rest : List UStmt) (bs : List Gabbro.Body.Stmt),
      Γ = fn.params.map (·.2) → Sicht u ft fn → (∀ st ∈ ss, st ∈ (fnAt u c).body) →
      lowEndL (l := loopMode) u c Γ fn n Λ [] ss = .ok (ending, rest) →
      endBodyZ u k ft ns ss = some (bs, rest) →
      (∀ g gf, fnSuch u g = some gf → (∃ args, CallsIn ss g args) → Gabbro.Body.Frame ρB g (writesU gf)) →
      Statisch ρB (writesU (fnAt u c)) bs
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _, _ => by cases h
  | _ + 1, 0, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _ => by cases h
  | _ + 1, _ + 1, [], _, _, _, _, _, _, _, _, _, _, _, _, h, _ => by cases h
  | n + 1, k + 1, st :: ss, Γ, fn, ft, ns, Λ, ending, rest, bs, hΓ, hV, hm, hG, hB, hF => by
    rcases endBodyZ_cases hB with ⟨r, b, rfl, hr, rfl, _⟩ | ⟨b, ys, hleaf, hs, hys, rfl⟩
    · obtain ⟨e, rfl⟩ := retZ_form hr
      exact .ret _ _ .nil
    · obtain ⟨hsN, _, _⟩ := schrittB_einzeln_sicht hV hs (endLeafB_ok hleaf)
      obtain ⟨Λ', gs, nextB, hgs, hnext, rfl⟩ := lowEndL_leaf_ok (endLeafB_ok hleaf) hG
      have ih := endBodyZ_statisch S hc ρB n k ss fn ft ns nextB rest ys hΓ hV
        (fun st h => hm st (List.mem_cons_of_mem _ h)) hnext hys
        (fun g gf hgf ⟨args, hc⟩ => hF g gf hgf ⟨args, hc.cons _⟩)
      cases st
      case setVar =>
        obtain ⟨_, id, e, _, _, rfl, _, _⟩ := schrittB_setVar hsN
        exact .bindName _ _ _ ih
      case setVarB =>
        obtain ⟨id, e, _, _, rfl, _, _⟩ := schrittB_setVarB hsN
        exact .bindName _ _ _ ih
      all_goals try cases hleaf
      all_goals
        obtain ⟨hb, _, _⟩ := schrittB_stmt hsN (fun _ _ _ h => by cases h)
          (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
          (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)
        exact statisch_schritt_G S c hc ρB hΓ _ ss (hm _ (List.mem_cons_self ..)) hgs hb hF ih

end Gabbro.Bruecke
