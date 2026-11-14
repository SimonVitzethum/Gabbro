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
    simp only [seqZ, bind, Option.bind] at h
    split at h
    · cases h
    · rename_i hgood
      have hg : loopWritesB ss = true := by cases hh : loopWritesB ss <;> simp_all
      cases ht : tabIdx u.tabs tab with
      | error e => simp only [ht, Except.toOption] at h; cases h
      | ok t =>
        simp only [ht, Except.toOption] at h
        split at h
        · rename_i body tail allocated hbody
          cases hy : seqZ u k fn (ns.resume allocated) tail with
          | none => rw [hy] at h; cases h
          | some p =>
            obtain ⟨ys, tail', used'⟩ := p
            rw [hy] at h
            cases h
            exact ⟨rfl, hg, t, body, tail, allocated, ys, ht, hbody, hy, rfl⟩
        · cases h
  all_goals simp only [seqZ, schrittB, namedStmt, stmtBody, Option.bind_none, Option.map_none, reduceCtorEq] at h

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
    simp only [stmtsBodyZ, bind, Option.bind] at h
    split at h
    · cases h
    · rename_i hgood
      have hg : loopWritesB ss = true := by cases hh : loopWritesB ss <;> simp_all
      cases ht : tabIdx u.tabs tab with
      | error e => simp only [ht, Except.toOption] at h; cases h
      | ok t =>
        simp only [ht, Except.toOption] at h
        split at h
        · rename_i body tail allocated hbody
          cases hy : stmtsBodyZ u k fn (ns.resume allocated) tail r with
          | none => rw [hy] at h; cases h
          | some ys =>
            rw [hy] at h
            cases h
            exact ⟨rfl, hg, t, body, tail, allocated, ys, ht, hbody, hy, rfl⟩
        · cases h
  all_goals simp only [stmtsBodyZ, schrittB, namedStmt, stmtBody, Option.bind_none, Option.map_none, reduceCtorEq] at h

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
      obtain ⟨_, rfl, rfl⟩ := schrittB_einzeln_sicht (Sicht.refl fn) hs (by exact True.intro)
      exact loopWrites_calls k fn ns ss ys tail used hg hy g args (CallsIn.tail (by rfl) hc)
    all_goals cases hg

end Gabbro.Bruecke
