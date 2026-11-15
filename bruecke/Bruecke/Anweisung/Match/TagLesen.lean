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
  unfold tagSubject at h
  cases ht : valueParamTy fn x with
  | none => simp only [ht, bind, Option.bind_none] at h <;> cases h
  | some ty =>
    simp only [ht, bind, Option.bind_some] at h
    cases ty <;> try { cases h }
    case sum fields =>
      cases hBare : fields.all Option.isNone with
      | false => simp only [hBare, Bool.not_false, ↓reduceIte] at h <;> cases h
      | true =>
        simp only [hBare, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        cases hi : ns.lookup fn x with
        | none => simp only [hi, bind, Option.bind_none] at h <;> cases h
        | some id =>
          simp only [hi, bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨id, (by first | exact ht | rfl), hBare,
            (by first | exact hi | rfl), rfl⟩

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
    | none => simp only [he, bind, Option.bind_none] at h <;> cases h
    | some pair =>
      obtain ⟨cs, e⟩ := pair
      simp only [he, bind, Option.bind_some] at h
      cases ha : reasonArmsZ u k fn cs.length 0 ns ss with
      | none => simp only [ha, bind, Option.bind_none] at h <;> cases h
      | some out =>
        obtain ⟨arms, ending, allocated⟩ := out
        simp only [ha, bind, Option.bind_some] at h
        cases ending with
        | nil => cases h
        | cons marker tail =>
          cases marker <;> try { cases h }
          case blkEnd =>
            cases hy : stmtsBodyZ u k fn (ns.resume allocated) tail r with
            | none => simp only [hy, bind, Option.bind_none] at h <;> cases h
            | some ys =>
              simp only [hy, bind, Option.bind_some, pure, Option.some.injEq] at h
              exact ⟨cs, e, arms, tail, allocated, ys, hn,
                (by first | exact he | rfl), ha, hy, h.symm⟩
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
