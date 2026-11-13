module
public import Bruecke.Anweisung.Lokal.Kopf
@[expose] public section

/-!
# C6, part 1: `if`/`else` in the Body translation

The elaborator writes a conditional flat: `ifBeg c`, the then-statements, `ifElse`, the
else-statements (none for an absent `else`), `blkEnd` (`uCondPlain`). The lowering reads it back
as `Stmt.ite` of two `Block`s (`lowStructStep`), each read by the block reader `lowSeqStep` up to
the marker that ends it, in the scope at the `if`: a binder inside a branch is not in scope after
the `blkEnd`. Inside a block `ifEnde c` (a terminal `if`) is read as `ifBeg c`.

`seqZ` is the block reader of the translation (fuel-bounded, as the lowering's), `stmtsBodyZ` the
body reader: both read a conditional to Body's `ite` and thread the scope exactly as the lowering
does. A branch condition is read by the `ensures` reader with an empty accumulator and must read
no `old` and no `result` (`condZ`); a `return` inside a block is Body's `ret` (`retZ`).
`zuBodyZ` agrees with `zuBodyB` on bodies without branches (`zuBodyZ_of_zuBodyB`).
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-! ## 1. The translation -/

/-- A branch condition: the `ensures` reading with an empty accumulator; it must read no `old`
    and no `result`. -/
def condZ (u : UProg) (fn : UFn) (c : UEns) : Option Gabbro.Body.Expr :=
  match ensExpr u fn {} c with
  | some (x, a) => if a.olds.length = 0 ∧ a.result = false then some x else none
  | none => none

/-- `return [v];` inside a block. -/
def retZ (u : UProg) (fn : UFn) : URet → Option Gabbro.Body.Stmt
  | .empty => some (.ret none)
  | .val v => (sideExpr u fn v).map (fun e => .ret (some e))
  | _ => none

/-- The block reader: the statements up to the marker that ends the block (`ifElse`, `blkEnd`) or
    the end of the list, and what is left. -/
def seqZ (u : UProg) : Nat → UFn → List UStmt → Option (List Gabbro.Body.Stmt × List UStmt)
  | 0, _, _ => none
  | _ + 1, _, [] => some ([], [])
  | _ + 1, _, .blkEnd :: rest => some ([], .blkEnd :: rest)
  | _ + 1, _, .ifElse :: rest => some ([], .ifElse :: rest)
  | k + 1, fn, .ifBeg cnd :: rest =>
      match condZ u fn cnd with
      | none => none
      | some ce =>
        match seqZ u k fn rest with
        | some (t, .ifElse :: rest1) =>
          match seqZ u k fn rest1 with
          | some (e, .blkEnd :: rest2) =>
            (seqZ u k fn rest2).map (fun p => (Gabbro.Body.Stmt.ite ce t e :: p.1, p.2))
          | _ => none
        | _ => none
  | k + 1, fn, .ifEnde cnd :: rest =>
      match condZ u fn cnd with
      | none => none
      | some ce =>
        match seqZ u k fn rest with
        | some (t, .ifElse :: rest1) =>
          match seqZ u k fn rest1 with
          | some (e, .blkEnd :: rest2) =>
            (seqZ u k fn rest2).map (fun p => (Gabbro.Body.Stmt.ite ce t e :: p.1, p.2))
          | _ => none
        | _ => none
  | k + 1, fn, .ret r :: rest =>
      match retZ u fn r with
      | none => none
      | some b => (seqZ u k fn rest).map (fun p => (b :: p.1, p.2))
  | k + 1, fn, s :: rest =>
      match schrittB u fn s with
      | some (b, fn') => (seqZ u k fn' rest).map (fun p => (b :: p.1, p.2))
      | none => none

/-- The body reader: the statements, a conditional read by `seqZ`, the scope threaded through
    every binder, and the trailing return. -/
def stmtsBodyZ (u : UProg) : Nat → UFn → List UStmt → URet → Option (List Gabbro.Body.Stmt)
  | 0, _, _, _ => none
  | _ + 1, fn, [], r => endBody u fn r
  | k + 1, fn, .ifBeg cnd :: rest, r =>
      match condZ u fn cnd with
      | none => none
      | some ce =>
        match seqZ u k fn rest with
        | some (t, .ifElse :: rest1) =>
          match seqZ u k fn rest1 with
          | some (e, .blkEnd :: rest2) =>
            (stmtsBodyZ u k fn rest2 r).map (Gabbro.Body.Stmt.ite ce t e :: ·)
          | _ => none
        | _ => none
  | k + 1, fn, s :: rest, r =>
      match schrittB u fn s with
      | some (b, fn') => (stmtsBodyZ u k fn' rest r).map (b :: ·)
      | none => none

/-- **`zuBodyZ`** -- the body of `f` with its local bindings and conditionals, as `Gabbro.Body`
    sees it. -/
def zuBodyZ (u : UProg) (f : UFn) : Option (List Gabbro.Body.Stmt) :=
  stmtsBodyZ u (f.body.length + 1) f f.body f.ret

/-! ## 2. Reading a translation back -/

/-- The statements `schrittB` reads. -/
def LeseZ : UStmt → Prop
  | .bind .. | .bindMut .. | .setVar .. | .assign .. | .assignTab .. | .call .. => True
  | _ => False

theorem leseZ_of_schrittB {fn : UFn} {s : UStmt} {p : Gabbro.Body.Stmt × UFn}
    (h : schrittB u fn s = some p) : LeseZ s := by
  cases s
  case bind | bindMut | setVar | assign | assignTab | call => exact True.intro
  all_goals simp [schrittB, stmtBody] at h

theorem seqZ_schritt {k : Nat} {fn : UFn} {s : UStmt} {rest : List UStmt} (hs : LeseZ s) :
    seqZ u (k + 1) fn (s :: rest) =
      (match schrittB u fn s with
       | some (b, fn') => (seqZ u k fn' rest).map (fun p => (b :: p.1, p.2))
       | none => none) := by
  cases s
  case bind | bindMut | setVar | assign | assignTab | call => first | rfl | simp only [seqZ]
  all_goals simp [LeseZ] at hs

theorem stmtsBodyZ_schritt {k : Nat} {fn : UFn} {s : UStmt} {rest : List UStmt} {r : URet}
    (hs : LeseZ s) :
    stmtsBodyZ u (k + 1) fn (s :: rest) r =
      (match schrittB u fn s with
       | some (b, fn') => (stmtsBodyZ u k fn' rest r).map (b :: ·)
       | none => none) := by
  cases s
  case bind | bindMut | setVar | assign | assignTab | call => first | rfl | simp only [stmtsBodyZ]
  all_goals simp [LeseZ] at hs

theorem seqZ_schritt_some {k : Nat} {fn : UFn} {s : UStmt} {rest : List UStmt}
    {xs : List Gabbro.Body.Stmt} {r : List UStmt}
    (h : seqZ u (k + 1) fn (s :: rest) = some (xs, r)) (hs : LeseZ s) :
    ∃ b fn' ys, schrittB u fn s = some (b, fn') ∧ seqZ u k fn' rest = some (ys, r) ∧
      xs = b :: ys := by
  rw [seqZ_schritt hs] at h
  split at h
  · rename_i b fn' hsb
    cases hq : seqZ u k fn' rest with
    | none => rw [hq] at h; cases h
    | some p =>
      rw [hq] at h
      obtain ⟨ys, r'⟩ := p
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨b, fn', ys, hsb, hq, rfl⟩
  · cases h

theorem stmtsBodyZ_schritt_some {k : Nat} {fn : UFn} {s : UStmt} {rest : List UStmt} {r : URet}
    {bs : List Gabbro.Body.Stmt} (h : stmtsBodyZ u (k + 1) fn (s :: rest) r = some bs)
    (hs : LeseZ s) :
    ∃ b fn' bs', schrittB u fn s = some (b, fn') ∧ stmtsBodyZ u k fn' rest r = some bs' ∧
      bs = b :: bs' := by
  rw [stmtsBodyZ_schritt hs] at h
  split at h
  · rename_i b fn' hsb
    cases hq : stmtsBodyZ u k fn' rest r with
    | none => rw [hq] at h; cases h
    | some bs' =>
      rw [hq] at h
      simp only [Option.map_some, Option.some.injEq] at h
      exact ⟨b, fn', bs', hsb, hq, h.symm⟩
  · cases h

theorem seqZ_wenn_some {k : Nat} {fn : UFn} {s : UStmt} {cnd : UEns} {rest : List UStmt}
    {xs : List Gabbro.Body.Stmt} {r : List UStmt}
    (h : seqZ u (k + 1) fn (s :: rest) = some (xs, r))
    (hk : s = .ifBeg cnd ∨ s = .ifEnde cnd) :
    ∃ ce t e rest1 rest2 ys, condZ u fn cnd = some ce ∧
      seqZ u k fn rest = some (t, .ifElse :: rest1) ∧
      seqZ u k fn rest1 = some (e, .blkEnd :: rest2) ∧
      seqZ u k fn rest2 = some (ys, r) ∧ xs = .ite ce t e :: ys := by
  rcases hk with rfl | rfl
  all_goals
    simp only [seqZ] at h
    split at h
    · cases h
    · rename_i ce hce
      split at h
      · rename_i t rest1 hT
        split at h
        · rename_i e rest2 hE
          cases hY : seqZ u k fn rest2 with
          | none => rw [hY] at h; cases h
          | some p =>
            rw [hY] at h
            obtain ⟨ys, r'⟩ := p
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨ce, t, e, rest1, rest2, ys, hce, hT, hE, hY, rfl⟩
        · cases h
      · cases h

theorem stmtsBodyZ_ifBeg_some {k : Nat} {fn : UFn} {cnd : UEns} {rest : List UStmt} {r : URet}
    {bs : List Gabbro.Body.Stmt} (h : stmtsBodyZ u (k + 1) fn (.ifBeg cnd :: rest) r = some bs) :
    ∃ ce t e rest1 rest2 bs', condZ u fn cnd = some ce ∧
      seqZ u k fn rest = some (t, .ifElse :: rest1) ∧
      seqZ u k fn rest1 = some (e, .blkEnd :: rest2) ∧
      stmtsBodyZ u k fn rest2 r = some bs' ∧ bs = .ite ce t e :: bs' := by
  simp only [stmtsBodyZ] at h
  split at h
  · cases h
  · rename_i ce hce
    split at h
    · rename_i t rest1 hT
      split at h
      · rename_i e rest2 hE
        cases hY : stmtsBodyZ u k fn rest2 r with
        | none => rw [hY] at h; cases h
        | some bs' =>
          rw [hY] at h
          simp only [Option.map_some, Option.some.injEq] at h
          exact ⟨ce, t, e, rest1, rest2, bs', hce, hT, hE, hY, h.symm⟩
      · cases h
    · cases h

theorem seqZ_ret_some {k : Nat} {fn : UFn} {r0 : URet} {rest : List UStmt}
    {xs : List Gabbro.Body.Stmt} {r : List UStmt}
    (h : seqZ u (k + 1) fn (.ret r0 :: rest) = some (xs, r)) :
    ∃ b ys, retZ u fn r0 = some b ∧ seqZ u k fn rest = some (ys, r) ∧ xs = b :: ys := by
  simp only [seqZ] at h
  split at h
  · cases h
  · rename_i b hb
    cases hY : seqZ u k fn rest with
    | none => rw [hY] at h; cases h
    | some p =>
      rw [hY] at h
      obtain ⟨ys, r'⟩ := p
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨b, ys, hb, rfl, rfl⟩

theorem condZ_some {fn : UFn} {cnd : UEns} {ce : Gabbro.Body.Expr} (h : condZ u fn cnd = some ce) :
    ∃ a : Acc, ensExpr u fn {} cnd = some (ce, a) ∧ a.olds.length = 0 ∧ a.result = false := by
  unfold condZ at h
  split at h
  · rename_i x a hx
    split at h
    · rename_i hc
      cases h
      exact ⟨a, hx, hc.1, hc.2⟩
    · cases h
  · cases h

/-! ## 3. Agreement with `zuBodyB` -/

theorem stmtsBodyZ_of_B (r : URet) : ∀ (k : Nat) (fn : UFn) (ss : List UStmt)
    (bs : List Gabbro.Body.Stmt), ss.length < k → stmtsBodyB u fn ss r = some bs →
    stmtsBodyZ u k fn ss r = some bs
  | 0, _, _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | k + 1, fn, [], bs, _, h => by
      simp only [stmtsBodyB] at h
      simp only [stmtsBodyZ]
      exact h
  | k + 1, fn, s :: ss, bs, hk, h => by
      obtain ⟨b, fn', bs', hs, hr, rfl⟩ := stmtsBodyB_cons h
      have ih := stmtsBodyZ_of_B r k fn' ss bs'
        (by simp only [List.length_cons] at hk; omega) hr
      rw [stmtsBodyZ_schritt (leseZ_of_schrittB hs), hs]
      simp only [ih, Option.map_some]

/-- **`zuBodyZ` extends `zuBodyB`**: on a body without conditionals both give the same
    program. -/
theorem zuBodyZ_of_zuBodyB {f : UFn} {b : List Gabbro.Body.Stmt} (h : zuBodyB u f = some b) :
    zuBodyZ u f = some b :=
  stmtsBodyZ_of_B f.ret _ f f.body b (Nat.lt_succ_self _) h

/-! ## 4. The view of a scope -/

theorem ensSide_sicht {fT fn : UFn} (h : Sicht u fT fn) (a : Acc) (sd : USide) :
    ensSide u fT a sd = ensSide u fn a sd := by
  cases sd <;> simp [ensSide, slotPlace_sicht h, sideExpr_sicht h]

theorem ensExpr_sicht {fT fn : UFn} (h : Sicht u fT fn) (e : UEns) (a : Acc) :
    ensExpr u fT a e = ensExpr u fn a e := by
  have recurse (e' : UEns) (hlt : sizeOf e' < sizeOf e) (a' : Acc) :
      ensExpr u fT a' e' = ensExpr u fn a' e' :=
    ensExpr_sicht h e' a'
  cases e with
  | cmp op l r =>
    simp only [ensExpr, ensSide_sicht h]
  | and x y =>
    have hx := recurse x (by simp_wf <;> omega)
    have hy := recurse y (by simp_wf <;> omega)
    simp only [ensExpr]
    rw [hx a]
    cases ensExpr u fn a x with
    | none => rfl
    | some p =>
      obtain ⟨xe, a1⟩ := p
      (try dsimp only)
      rw [hy a1]
  | or x y =>
    have hx := recurse x (by simp_wf <;> omega)
    have hy := recurse y (by simp_wf <;> omega)
    simp only [ensExpr]
    rw [hx a]
    cases ensExpr u fn a x with
    | none => rfl
    | some p =>
      obtain ⟨xe, a1⟩ := p
      (try dsimp only)
      rw [hy a1]
  | not x =>
    have hx := recurse x (by simp_wf <;> omega)
    simp only [ensExpr]
    rw [hx a]
  | _ => rfl
termination_by sizeOf e
decreasing_by assumption

theorem condZ_sicht {fT fn : UFn} (h : Sicht u fT fn) (c : UEns) :
    condZ u fT c = condZ u fn c := by
  unfold condZ
  rw [ensExpr_sicht h]

theorem retZ_sicht {fT fn : UFn} (h : Sicht u fT fn) (r : URet) : retZ u fT r = retZ u fn r := by
  cases r <;> simp [retZ, sideExpr_sicht h]

/-- A statement the body reader passes to `lowStmtL`, read in the translation's scope, is read
    alike in the lowering's scope, and keeps the scope. -/
theorem schrittB_einzeln_sicht {fT fn : UFn} (hS : Sicht u fT fn) {s : UStmt}
    {b : Gabbro.Body.Stmt} {fT' : UFn} (h : schrittB u fT s = some (b, fT')) (hs : LeseEinzeln s) :
    schrittB u fn s = some (b, fn) ∧ fT' = fT := by
  cases s
  case setVar x v =>
    obtain ⟨hn, e, he, rfl, rfl⟩ := schrittB_setVar h
    refine ⟨?_, rfl⟩
    have hn' : numericParam fn x = true := (hS.1 x).symm.trans hn
    have he' : sideExpr u fn v = some e := (sideExpr_sicht hS v).symm.trans he
    show (if numericParam fn x then (sideExpr u fn v).map
      (fun e => (Gabbro.Body.Stmt.bindName x e, fn)) else none) = _
    rw [if_pos hn', he']
    try rfl
  case assign | assignTab | call =>
    obtain ⟨hx, rfl⟩ := schrittB_stmt h (fun _ _ _ h => by cases h)
      (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
    exact ⟨schrittB_sonst ((stmtBody_sicht hS _).symm.trans hx), rfl⟩
  all_goals simp [LeseEinzeln] at hs

end Gabbro.Bruecke
