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
    inv = .tru ∧ loopWritesB ss = true ∧ ∃ t body tail allocated ys,
      tabIdx u.tabs tab = .ok t ∧
      seqZ u k (fn.mitIndex x t.val ((declOf u).count t)) (ns.push x) ss =
        some (body, .blkEnd :: tail, allocated) ∧
      seqZ u k fn (ns.resume allocated) tail = some (ys, rest, used) ∧
      bs = .forEach (ns.fresh x) (loopIndices u t) body :: ys := by
  cases inv
  case tru =>
    cases hg : loopWritesB ss with
    | false => simp only [seqZ, hg, Bool.not_false, ↓reduceIte] at h; cases h
    | true =>
      simp only [seqZ, hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
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
                exact ⟨rfl, (by first | exact hg | rfl | simp_all), t, body, tail, allocated, ys, (by first | exact ht | rfl | simp_all), hbody, hy, rfl⟩
  all_goals simp only [seqZ, schrittB, namedStmt, stmtBody, bind, Option.bind_none, Option.map_none, reduceCtorEq] at h

theorem stmtsBodyZ_loop_some {k : Nat} {fn : UFn} {ns : BodyNames} {x tab : String} {inv : UEns}
    {ss : List UStmt} {r : URet} {bs : List Gabbro.Body.Stmt}
    (h : stmtsBodyZ u (k + 1) fn ns (.loopBeg x tab inv :: ss) r = some bs) :
    inv = .tru ∧ loopWritesB ss = true ∧ ∃ t body tail allocated ys,
      tabIdx u.tabs tab = .ok t ∧
      seqZ u k (fn.mitIndex x t.val ((declOf u).count t)) (ns.push x) ss =
        some (body, .blkEnd :: tail, allocated) ∧
      stmtsBodyZ u k fn (ns.resume allocated) tail r = some ys ∧
      bs = .forEach (ns.fresh x) (loopIndices u t) body :: ys := by
  cases inv
  case tru =>
    cases hg : loopWritesB ss with
    | false => simp only [stmtsBodyZ, hg, Bool.not_false, ↓reduceIte] at h; cases h
    | true =>
      simp only [stmtsBodyZ, hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
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
                exact ⟨rfl, (by first | exact hg | rfl | simp_all), t, body, tail, allocated, ys, (by first | exact ht | rfl | simp_all), hbody, hy, h.symm⟩
  all_goals simp only [stmtsBodyZ, schrittB, namedStmt, stmtBody, bind, Option.bind_none, Option.map_none, reduceCtorEq] at h

/-- The admitted loop body is a sequence of writes, so all calls lie after its marker. -/
theorem loopWrites_calls : ∀ k fn ns ss bs tail used,
    loopWritesB ss = true → seqZ u k fn ns ss = some (bs, .blkEnd :: tail, used) →
    ∀ g args, CallsIn ss g args → CallsIn tail g args
  | 0, _, _, _, _, _, _, _, h, _, _, _ => by cases h
  | k + 1, fn, ns, [], _, _, _, hg, _, _, _, _ => by cases hg
  | k + 1, fn, ns, st :: ss, bs, tail, used, hg, h, g, args, hc => by
    cases st
    case blkEnd =>
      simp only [seqZ, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, hr, _⟩ := h
      cases hr
      exact CallsIn.tail (by rfl) hc
    case assign | assignTab | assignGlob | setVar | setVarB =>
      obtain ⟨b, fn', ns', ys, hs, hy, _⟩ := seqZ_schritt_some h (by exact True.intro)
      exact loopWrites_calls k fn' ns' ss ys tail used hg hy g args (CallsIn.tail (by rfl) hc)
    all_goals cases hg

end Gabbro.Bruecke
