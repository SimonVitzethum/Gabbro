module
public import Bruecke.Anweisung.Zweig.Lesen
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg

variable {u : UProg}

theorem seqZ_loop_some {k : Nat} {fn : UFn} {ns : BodyNames} {x tab : String} {inv : UEns}
    {ss rest : List UStmt} {bs : List Gabbro.Body.Stmt} {used : List String}
    (h : seqZ u (k + 1) fn ns (.loopBeg x tab inv :: ss) = some (bs, rest, used)) :
    inv = .tru ∧ ∃ t body tail allocated ys,
      tabIdx u.tabs tab = .ok t ∧
      seqZ u k (fn.mitIndex x t.val ((declOf u).count t)) (ns.push x) ss =
      some (body, .blkEnd :: tail, allocated) ∧
      seqZ u k fn (ns.resume allocated) tail = some (ys, rest, used) ∧
      bs = .forEach (ns.fresh x) (loopIndices u t) body :: ys := by
  cases inv
  case tru =>
    simp only [seqZ] at h
    cases ht : tabIdx u.tabs tab with
    | error e => simp only [ht, Except.toOption, bind, Option.bind_none] at h; cases h
    | ok t =>
      simp only [ht, Except.toOption, bind, Option.bind_some] at h
      cases hbody : seqZ u k (fn.mitIndex x t.val ((declOf u).count t)) (ns.push x) ss with
      | none => simp only [hbody, bind, Option.bind_none] at h; cases h
      | some p =>
        obtain ⟨body, ending, allocated⟩ := p
        simp only [hbody, bind, Option.bind_some] at h
        cases ending with
        | nil => cases h
        | cons marker tail =>
          cases marker <;> try { cases h }
          case blkEnd =>
            cases hy : seqZ u k fn (ns.resume allocated) tail with
            | none => simp only [hy, bind, Option.bind_none] at h; cases h
            | some p =>
              obtain ⟨ys, tail', used'⟩ := p
              simp only [hy, bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact ⟨rfl, t, body, tail, allocated, ys, (by first | exact ht | rfl | simp_all), hbody, hy, rfl⟩
  all_goals simp only [seqZ, schrittB, namedStmt, stmtBody, bind, Option.bind_none, Option.map_none, reduceCtorEq] at h

theorem stmtsBodyZ_loop_some {k : Nat} {fn : UFn} {ns : BodyNames} {x tab : String} {inv : UEns}
    {ss : List UStmt} {r : URet} {bs : List Gabbro.Body.Stmt}
    (h : stmtsBodyZ u (k + 1) fn ns (.loopBeg x tab inv :: ss) r = some bs) :
    inv = .tru ∧ ∃ t body tail allocated ys,
      tabIdx u.tabs tab = .ok t ∧
      seqZ u k (fn.mitIndex x t.val ((declOf u).count t)) (ns.push x) ss =
      some (body, .blkEnd :: tail, allocated) ∧
      stmtsBodyZ u k fn (ns.resume allocated) tail r = some ys ∧
      bs = .forEach (ns.fresh x) (loopIndices u t) body :: ys := by
  cases inv
  case tru =>
    simp only [stmtsBodyZ] at h
    cases ht : tabIdx u.tabs tab with
    | error e => simp only [ht, Except.toOption, bind, Option.bind_none] at h; cases h
    | ok t =>
      simp only [ht, Except.toOption, bind, Option.bind_some] at h
      cases hbody : seqZ u k (fn.mitIndex x t.val ((declOf u).count t)) (ns.push x) ss with
      | none => simp only [hbody, bind, Option.bind_none] at h; cases h
      | some p =>
        obtain ⟨body, ending, allocated⟩ := p
        simp only [hbody, bind, Option.bind_some] at h
        cases ending with
        | nil => cases h
        | cons marker tail =>
          cases marker <;> try { cases h }
          case blkEnd =>
            cases hy : stmtsBodyZ u k fn (ns.resume allocated) tail r with
            | none => simp only [hy, bind, Option.bind_none] at h; cases h
            | some ys =>
              simp only [hy, bind, Option.bind_some, pure, Option.some.injEq] at h
              exact ⟨rfl, t, body, tail, allocated, ys, (by first | exact ht | rfl | simp_all), hbody, hy, h.symm⟩
  all_goals simp only [stmtsBodyZ, schrittB, namedStmt, stmtBody, bind, Option.bind_none, Option.map_none, reduceCtorEq] at h

/-- A control leaf keeps reading the unreachable suffix for structural agreement. -/
theorem seqZ_control_some {k : Nat} {fn : UFn} {ns : BodyNames} {leave : Bool} {x : String}
    {ss rest : List UStmt} {bs : List Gabbro.Body.Stmt} {used : List String}
    (h : seqZ u (k + 1) fn ns (controlU leave x :: ss) = some (bs, rest, used)) :
    ∃ ys, seqZ u k fn ns ss = some (ys, rest, used) ∧ bs = controlStmtB leave :: ys := by
  cases leave <;> simp only [controlU, Bool.false_eq_true, ↓reduceIte, seqZ] at h
  all_goals
    cases hy : seqZ u k fn ns ss with
    | none => simp only [hy, Option.map_none, reduceCtorEq] at h
    | some p =>
      obtain ⟨ys, tail, allocated⟩ := p
      simp only [hy, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨ys, hy, rfl⟩

end Gabbro.Bruecke
