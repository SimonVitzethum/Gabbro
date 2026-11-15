module
public import Bruecke.Anweisung.Zweig.Lesen
public import Bruecke.Anweisung.Bereich.Ansicht
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
  simp only [seqZ] at h
  cases he : narrowName fn ns x with
  | none => simp only [he, bind, Option.bind_none] at h; cases h
  | some e =>
    simp only [he, bind, Option.bind_some] at h
    cases herr : endBodyZ u k fn ns ss with
    | none => simp only [herr, bind, Option.bind_none] at h; cases h
    | some p =>
      obtain ⟨err, ending⟩ := p
      simp only [herr, bind, Option.bind_some] at h
      cases ending with
      | nil => cases h
      | cons marker tail =>
        cases marker <;> try { cases h }
        case blkEnd =>
          cases hq : seqZ u k (fn.mitBindung x (lo, hi)) (ns.push x) tail with
          | none => simp only [hq, bind, Option.bind_none] at h; cases h
          | some p =>
            obtain ⟨ys, r, us⟩ := p
            simp only [hq, bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact ⟨e, err, tail, ys, (by first | exact he | rfl | simp_all), (by first | exact herr | rfl | simp_all), hq, rfl⟩

theorem stmtsBodyZ_narrow_some {k : Nat} {fn : UFn} {ns : BodyNames} {x : String} {lo hi : Int}
    {ss : List UStmt} {r : URet} {bs : List Gabbro.Body.Stmt}
    (h : stmtsBodyZ u (k + 1) fn ns (.narrowBeg x lo hi :: ss) r = some bs) :
    ∃ e err tail ys, narrowName fn ns x = some e ∧
      endBodyZ u k fn ns ss = some (err, .blkEnd :: tail) ∧
      stmtsBodyZ u k (fn.mitBindung x (lo, hi)) (ns.push x) tail r = some ys ∧
      bs = narrowStep ns x lo hi e err :: ys := by
  simp only [stmtsBodyZ] at h
  cases he : narrowName fn ns x with
  | none => simp only [he, bind, Option.bind_none] at h; cases h
  | some e =>
    simp only [he, bind, Option.bind_some] at h
    cases herr : endBodyZ u k fn ns ss with
    | none => simp only [herr, bind, Option.bind_none] at h; cases h
    | some p =>
      obtain ⟨err, ending⟩ := p
      simp only [herr, bind, Option.bind_some] at h
      cases ending with
      | nil => cases h
      | cons marker tail =>
        cases marker <;> try { cases h }
        case blkEnd =>
          cases hq : stmtsBodyZ u k (fn.mitBindung x (lo, hi)) (ns.push x) tail r with
          | none => simp only [hq, bind, Option.bind_none] at h; cases h
          | some ys =>
            simp only [hq, bind, Option.bind_some, pure, Option.some.injEq] at h
            exact ⟨e, err, tail, ys, (by first | exact he | rfl | simp_all), (by first | exact herr | rfl | simp_all), hq, h.symm⟩

end Gabbro.Bruecke
