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
    ∃ (hn : num < u.tabs.length) e pb ab r1 r2 ys used1 used2,
      optionZ fn ns v = some e ∧
      seqZ u k (fn.mitIndex x num ((declOf u).count ⟨num, hn⟩)) (ns.push x) ss =
        some (pb, .ifElse :: r1, used1) ∧
      seqZ u k fn (ns.resume used1) r1 = some (ab, .blkEnd :: r2, used2) ∧
      stmtsBodyZ u k fn (ns.resume used2) r2 r = some ys ∧
      bs = .onOption e (ns.fresh x) pb ab :: ys := by
  simp only [stmtsBodyZ] at h
  split at h
  · rename_i hn
    cases he : optionZ fn ns v with
    | none => simp only [he, Option.bind_none] at h; cases h
    | some e =>
      simp only [he, Option.bind_some] at h
      split at h
      · rename_i pb r1 used1 hp
        split at h
        · rename_i ab r2 used2 ha
          cases hy : stmtsBodyZ u k fn (ns.resume used2) r2 r with
          | none => simp only [hy, Option.bind_none] at h; cases h
          | some ys =>
            simp only [hy, Option.bind_some, pure, Option.some.injEq] at h
            subst bs
            exact ⟨hn, e, pb, ab, r1, r2, ys, used1, used2, he, hp, ha, hy, rfl⟩
        · cases h
      · cases h
  · cases h

end Gabbro.Bruecke
