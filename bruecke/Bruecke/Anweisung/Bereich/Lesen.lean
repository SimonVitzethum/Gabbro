module
public import Bruecke.Anweisung.Zweig.Lesen
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze

variable {u : UProg}

theorem seqZ_narrow_some {k : Nat} {fn : UFn} {ns : BodyNames} {x : String} {lo hi : Int}
    {ss rest : List UStmt} {bs : List Gabbro.Body.Stmt} {used : List String}
    (h : seqZ u (k + 1) fn ns (.narrowBeg x lo hi :: ss) = some (bs, rest, used)) :
    ∃ e err tail ys, narrowName fn ns x = some e ∧
      endBodyZ u k fn ns ss = some (err, .blkEnd :: tail) ∧
      seqZ u k (fn.mitBindung x (lo, hi)) (ns.push x) tail = some (ys, rest, used) ∧
      bs = narrowStep ns x lo hi e err :: ys := by
  simp only [seqZ, bind, Option.bind] at h
  split at h
  · cases h
  · rename_i e he
    split at h
    · rename_i err tail herr
      cases hq : seqZ u k (fn.mitBindung x (lo, hi)) (ns.push x) tail with
      | none => rw [hq] at h; cases h
      | some p =>
        obtain ⟨ys, r, us⟩ := p
        rw [hq] at h
        cases h
        exact ⟨e, err, tail, ys, he, herr, hq, rfl⟩
    · cases h

theorem stmtsBodyZ_narrow_some {k : Nat} {fn : UFn} {ns : BodyNames} {x : String} {lo hi : Int}
    {ss : List UStmt} {r : URet} {bs : List Gabbro.Body.Stmt}
    (h : stmtsBodyZ u (k + 1) fn ns (.narrowBeg x lo hi :: ss) r = some bs) :
    ∃ e err tail ys, narrowName fn ns x = some e ∧
      endBodyZ u k fn ns ss = some (err, .blkEnd :: tail) ∧
      stmtsBodyZ u k (fn.mitBindung x (lo, hi)) (ns.push x) tail r = some ys ∧
      bs = narrowStep ns x lo hi e err :: ys := by
  simp only [stmtsBodyZ, bind, Option.bind] at h
  split at h
  · cases h
  · rename_i e he
    split at h
    · rename_i err tail herr
      cases hq : stmtsBodyZ u k (fn.mitBindung x (lo, hi)) (ns.push x) tail r with
      | none => rw [hq] at h; cases h
      | some ys =>
        rw [hq] at h
        cases h
        exact ⟨e, err, tail, ys, he, herr, hq, rfl⟩
    · cases h

/-- A successful ending reader either returns now or consumes one supported leaf. -/
theorem endBodyZ_cases {k : Nat} {fn : UFn} {ns : BodyNames} {st : UStmt}
    {ss tail : List UStmt} {bs : List Gabbro.Body.Stmt}
    (h : endBodyZ u (k + 1) fn ns (st :: ss) = some (bs, tail)) :
    (∃ r b, st = .ret r ∧ retZ u fn ns r = some b ∧ bs = [b] ∧ tail = ss) ∨
    (∃ b ys, endLeafB st = true ∧ schrittB u fn ns st = some (b, fn, ns) ∧
      endBodyZ u k fn ns ss = some (ys, tail) ∧ bs = b :: ys) := by
  cases st
  case ret r =>
    simp only [endBodyZ] at h
    cases hb : retZ u fn ns r with
    | none => rw [hb] at h; cases h
    | some b =>
      rw [hb] at h
      cases h
      exact .inl ⟨r, b, rfl, hb, rfl, rfl⟩
  all_goals
    simp only [endBodyZ] at h
    split at h
    · rename_i hleaf
      split at h
      · rename_i b fn' ns' hstep
        obtain ⟨_, rfl, rfl⟩ := schrittB_einzeln_sicht (Sicht.refl fn) hstep (endLeafB_ok hleaf)
        cases hr : endBodyZ u k fn ns ss with
        | none => simp only [hr, Option.bind_none] at h; cases h
        | some p =>
          obtain ⟨ys, tail'⟩ := p
          simp only [hr, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .inr ⟨b, ys, hleaf, hstep, hr, rfl⟩
      · cases h
    · cases h

/-- The unread tail is a suffix, including the marker after a mandatory return. -/
theorem endBodyZ_suffix : ∀ (k : Nat) (fn : UFn) (ns : BodyNames) (ss : List UStmt)
    (bs : List Gabbro.Body.Stmt) (tail : List UStmt),
    endBodyZ u k fn ns ss = some (bs, tail) → tail <:+ ss
  | 0, _, _, _, _, _, h => by cases h
  | _ + 1, _, _, [], _, _, h => by cases h
  | k + 1, fn, ns, st :: ss, bs, tail, h => by
    rcases endBodyZ_cases h with ⟨r, b, rfl, _, _, rfl⟩ | ⟨b, ys, _, _, hr, _⟩
    · exact List.suffix_cons _ _
    · exact (endBodyZ_suffix k fn ns ss ys tail hr).trans (List.suffix_cons _ _)

end Gabbro.Bruecke
