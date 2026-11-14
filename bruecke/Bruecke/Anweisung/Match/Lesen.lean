module
public import Bruecke.Anweisung.Zweig.Lesen
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

theorem stmtsBodyZ_option_some {k : Nat} {fn : UFn} {ns : BodyNames} {num : Nat}
    {v : UOpt} {x : String} {ss : List UStmt} {r : URet} {bs : List Gabbro.Body.Stmt}
    (h : stmtsBodyZ u (k + 1) fn ns (.matchBeg num v x :: ss) r = some bs) :
    ∃ (hn : num < u.tabs.length), ∃ e pb ab r1 r2 ys used1 used2,
      optionZ fn ns v = some e ∧
      seqZ u k (fn.mitIndex x num ((declOf u).count ⟨num, hn⟩)) (ns.push x) ss =
        some (pb, .ifElse :: r1, used1) ∧
      seqZ u k fn (ns.resume used1) r1 = some (ab, .blkEnd :: r2, used2) ∧
      stmtsBodyZ u k fn (ns.resume used2) r2 r = some ys ∧
      bs = .onOption e (ns.fresh x) pb ab :: ys := by
  simp only [stmtsBodyZ] at h
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
                  cases hy : stmtsBodyZ u k fn (ns.resume used2) r2 r with
                  | none => simp only [hy, bind, Option.bind_none] at h; cases h
                  | some ys =>
                    simp only [hy, bind, Option.bind_some, pure, Option.some.injEq] at h
                    exact ⟨hn, e, pb, ab, r1, r2, ys, used1, used2, (by first | exact he | rfl | simp_all), hp, ha, hy, h.symm⟩
  · simp only [hn, ↓reduceDIte] at h; cases h

end Gabbro.Bruecke
