module
public import Bruecke.Anweisung.Match.ReasonLesen
@[expose] public section
namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

theorem tagSubject_some {fn : UFn} {ns : BodyNames} {x : String} {cs : List (Option Ty)}
    {e : Gabbro.Body.Expr} (h : tagSubject fn ns x = some (cs, e)) :
    ∃ id, valueParamTy fn x = some (.sum cs) ∧ cs.all Option.isNone = true ∧
      ns.lookup fn x = some id ∧ e = .name id := by
  simp only [tagSubject, bind, Option.bind] at h
  split at h
  · rename_i fields ht
    split at h
    · cases h
    · rename_i hBare
      cases hi : ns.lookup fn x with
      | none => simp only [hi, bind, Option.bind_none, Option.bind] at h <;> cases h
      | some id =>
        simp only [hi, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨id, ht, by simpa using hBare, hi, rfl⟩
  · cases h

theorem stmtsBodyZ_tag_some {k sidx : Nat} {fn : UFn} {ns : BodyNames} {x : String}
    {binders : List String} {ss : List UStmt} {r : URet} {bs : List Gabbro.Body.Stmt}
    (h : stmtsBodyZ u (k + 1) fn ns (.matchTagBeg sidx x binders :: ss) r = some bs) :
    ∃ cs e arms tail allocated ys, sidx < u.sums.length ∧ tagSubject fn ns x = some (cs, e) ∧
      reasonArmsZ u k fn cs.length 0 ns ss = some (arms, .blkEnd :: tail, allocated) ∧
      stmtsBodyZ u k fn (ns.resume allocated) tail r = some ys ∧ bs = .onTag e (tagArms arms) :: ys := by
  simp only [stmtsBodyZ] at h
  split at h
  · rename_i hn
    cases he : tagSubject fn ns x with
    | none => simp only [he, Option.bind_none] at h; cases h
    | some pair =>
      obtain ⟨cs, e⟩ := pair
      simp only [he, bind, Option.bind_some, Option.bind] at h
      split at h
      · rename_i arms tail allocated ha
        cases hy : stmtsBodyZ u k fn (ns.resume allocated) tail r with
        | none => simp only [hy, Option.bind_none] at h; cases h
        | some ys =>
          simp only [hy, Option.bind_some, pure, Option.some.injEq] at h
          subst bs
          exact ⟨cs, e, arms, tail, allocated, ys, hn, he, ha, hy, rfl⟩
      · cases h
  · cases h

theorem pickTag_bare (ρB : Gabbro.Body.Env) : ∀ arms label payload s,
    Gabbro.Body.pickTag ρB (tagArms arms) label payload s = Gabbro.Body.pickArm ρB arms label s
  | [], _, _, _ => rfl
  | (name, body) :: arms, label, payload, s => by
    simp only [tagArms, List.map_cons, Gabbro.Body.pickTag, Gabbro.Body.pickArm]
    split
    · rfl
    · exact pickTag_bare ρB arms label payload s

end Gabbro.Bruecke
