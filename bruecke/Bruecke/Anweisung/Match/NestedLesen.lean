module
public import Bruecke.Anweisung.Match.Lesen
@[expose] public section
namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

theorem seqZ_option_some {k : Nat} {fn : UFn} {ns : BodyNames} {num : Nat}
    {v : UOpt} {x : String} {ss : List UStmt} {tail : List UStmt} {used : List String} {bs : List Gabbro.Body.Stmt}
    (h : seqZ u (k + 1) fn ns (.matchBeg num v x :: ss) = some (bs, tail, used)) :
    ∃ (hn : num < u.tabs.length), ∃ e pb ab r1 r2 ys used1 used2,
      optionZ fn ns v = some e ∧
      seqZ u k (fn.mitIndex x num ((declOf u).count ⟨num, hn⟩)) (ns.push x) ss =
        some (pb, .ifElse :: r1, used1) ∧
      seqZ u k fn (ns.resume used1) r1 = some (ab, .blkEnd :: r2, used2) ∧
      seqZ u k fn (ns.resume used2) r2 = some (ys, tail, used) ∧
      bs = .onOption e (ns.fresh x) pb ab :: ys := by
  simp only [seqZ] at h
  by_cases hn : num < u.tabs.length
  · simp only [hn, ↓reduceDIte] at h
    cases he : optionZ fn ns v with
    | none => simp only [he, bind, Option.bind_none] at h; cases h
    | some e =>
      simp only [he, bind, Option.bind_some] at h
      cases hp : seqZ u k (fn.mitIndex x num ((declOf u).count ⟨num, hn⟩)) (ns.push x) ss with
      | none => simp only [hp, bind, Option.bind_none] at h; cases h
      | some p =>
        obtain ⟨pb, ending, used1⟩ := p
        simp only [hp, bind, Option.bind_some] at h
        cases ending with
        | nil => cases h
        | cons marker r1 =>
          cases marker <;> try { cases h }
          case ifElse =>
            cases ha : seqZ u k fn (ns.resume used1) r1 with
            | none => simp only [ha, bind, Option.bind_none] at h; cases h
            | some p =>
              obtain ⟨ab, ending, used2⟩ := p
              simp only [ha, bind, Option.bind_some] at h
              cases ending with
              | nil => cases h
              | cons marker r2 =>
                cases marker <;> try { cases h }
                case blkEnd =>
                  cases hy : seqZ u k fn (ns.resume used2) r2 with
                  | none => simp only [hy, bind, Option.bind_none] at h; cases h
                  | some out =>
                    obtain ⟨ys, tail', used'⟩ := out
                    simp only [hy, bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
                    exact ⟨hn, e, pb, ab, r1, r2, ys, used1, used2, (by first | exact he | rfl | simp_all), hp, ha, ?_, ?_⟩
                    all_goals first | exact hy | simp_all
  · simp only [hn, ↓reduceDIte] at h; cases h

end Gabbro.Bruecke
