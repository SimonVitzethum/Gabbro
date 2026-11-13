module
public import Bruecke.Anweisung.Zweig.Benannt
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

def LeseZ : UStmt → Prop
  | .bind .. | .bindMut .. | .setVar .. | .assign .. | .assignTab .. | .assignGlob .. | .call .. => True
  | _ => False

theorem seqZ_schritt {k : Nat} {fn : UFn} {ns : BodyNames} {s : UStmt} {rest : List UStmt}
    (hs : LeseZ s) :
    seqZ u (k + 1) fn ns (s :: rest) =
      (match schrittB u fn ns s with
       | some (b, fn', ns') => (seqZ u k fn' ns' rest).map
           (fun p => (b :: p.1, p.2.1, p.2.2))
       | none => none) := by
  cases s
  case bind | bindMut | setVar | assign | assignTab | assignGlob | call => rfl
  all_goals cases hs

theorem stmtsBodyZ_schritt {k : Nat} {fn : UFn} {ns : BodyNames} {s : UStmt}
    {rest : List UStmt} {r : URet} (hs : LeseZ s) :
    stmtsBodyZ u (k + 1) fn ns (s :: rest) r =
      (match schrittB u fn ns s with
       | some (b, fn', ns') => (stmtsBodyZ u k fn' ns' rest r).map (b :: ·)
       | none => none) := by
  cases s
  case bind | bindMut | setVar | assign | assignTab | assignGlob | call => rfl
  all_goals cases hs

theorem seqZ_schritt_some {k : Nat} {fn : UFn} {ns : BodyNames} {s : UStmt}
    {rest r : List UStmt} {xs : List Gabbro.Body.Stmt} {used : List String}
    (h : seqZ u (k + 1) fn ns (s :: rest) = some (xs, r, used)) (hs : LeseZ s) :
    ∃ b fn' ns' ys, schrittB u fn ns s = some (b, fn', ns') ∧
      seqZ u k fn' ns' rest = some (ys, r, used) ∧ xs = b :: ys := by
  rw [seqZ_schritt hs] at h
  split at h
  · rename_i b fn' ns' hsb
    cases hq : seqZ u k fn' ns' rest with
    | none => rw [hq] at h; cases h
    | some p =>
      obtain ⟨ys, r', used'⟩ := p
      rw [hq] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨b, fn', ns', ys, hsb, hq, rfl⟩
  · cases h

theorem stmtsBodyZ_schritt_some {k : Nat} {fn : UFn} {ns : BodyNames} {s : UStmt}
    {rest : List UStmt} {r : URet} {bs : List Gabbro.Body.Stmt}
    (h : stmtsBodyZ u (k + 1) fn ns (s :: rest) r = some bs) (hs : LeseZ s) :
    ∃ b fn' ns' bs', schrittB u fn ns s = some (b, fn', ns') ∧
      stmtsBodyZ u k fn' ns' rest r = some bs' ∧ bs = b :: bs' := by
  rw [stmtsBodyZ_schritt hs] at h
  split at h
  · rename_i b fn' ns' hsb
    cases hq : stmtsBodyZ u k fn' ns' rest r with
    | none => rw [hq] at h; cases h
    | some bs' =>
      rw [hq] at h
      simp only [Option.map_some, Option.some.injEq] at h
      exact ⟨b, fn', ns', bs', hsb, hq, h.symm⟩
  · cases h

theorem seqZ_wenn_some {k : Nat} {fn : UFn} {ns : BodyNames} {s : UStmt} {cnd : UEns}
    {rest r : List UStmt} {xs : List Gabbro.Body.Stmt} {used : List String}
    (h : seqZ u (k + 1) fn ns (s :: rest) = some (xs, r, used))
    (hk : s = .ifBeg cnd ∨ s = .ifEnde cnd) :
    ∃ ce t e rest1 rest2 ys used1 used2, condZ u fn ns cnd = some ce ∧
      seqZ u k fn ns rest = some (t, .ifElse :: rest1, used1) ∧
      seqZ u k fn (ns.resume used1) rest1 = some (e, .blkEnd :: rest2, used2) ∧
      seqZ u k fn (ns.resume used2) rest2 = some (ys, r, used) ∧ xs = .ite ce t e :: ys := by
  rcases hk with rfl | rfl
  all_goals
    simp only [seqZ] at h
    split at h
    · cases h
    · rename_i ce hce
      split at h
      · rename_i t rest1 used1 hT
        split at h
        · rename_i e rest2 used2 hE
          cases hY : seqZ u k fn (ns.resume used2) rest2 with
          | none => rw [hY] at h; cases h
          | some p =>
            obtain ⟨ys, r', used'⟩ := p
            rw [hY] at h
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact ⟨ce, t, e, rest1, rest2, ys, used1, used2, hce, hT, hE, hY, rfl⟩
        · cases h
      · cases h

theorem stmtsBodyZ_ifBeg_some {k : Nat} {fn : UFn} {ns : BodyNames} {cnd : UEns}
    {rest : List UStmt} {r : URet} {bs : List Gabbro.Body.Stmt}
    (h : stmtsBodyZ u (k + 1) fn ns (.ifBeg cnd :: rest) r = some bs) :
    ∃ ce t e rest1 rest2 bs' used1 used2, condZ u fn ns cnd = some ce ∧
      seqZ u k fn ns rest = some (t, .ifElse :: rest1, used1) ∧
      seqZ u k fn (ns.resume used1) rest1 = some (e, .blkEnd :: rest2, used2) ∧
      stmtsBodyZ u k fn (ns.resume used2) rest2 r = some bs' ∧ bs = .ite ce t e :: bs' := by
  simp only [stmtsBodyZ] at h
  split at h
  · cases h
  · rename_i ce hce
    split at h
    · rename_i t rest1 used1 hT
      split at h
      · rename_i e rest2 used2 hE
        cases hY : stmtsBodyZ u k fn (ns.resume used2) rest2 r with
        | none => rw [hY] at h; cases h
        | some bs' =>
          rw [hY] at h
          simp only [Option.map_some, Option.some.injEq] at h
          exact ⟨ce, t, e, rest1, rest2, bs', used1, used2, hce, hT, hE, hY, h.symm⟩
      · cases h
    · cases h

theorem seqZ_ret_some {k : Nat} {fn : UFn} {ns : BodyNames} {r0 : URet}
    {rest r : List UStmt} {xs : List Gabbro.Body.Stmt} {used : List String}
    (h : seqZ u (k + 1) fn ns (.ret r0 :: rest) = some (xs, r, used)) :
    ∃ b ys, retZ u fn ns r0 = some b ∧
      seqZ u k fn ns rest = some (ys, r, used) ∧ xs = b :: ys := by
  simp only [seqZ] at h
  split at h
  · cases h
  · rename_i b hb
    cases hY : seqZ u k fn ns rest with
    | none => rw [hY] at h; cases h
    | some p =>
      obtain ⟨ys, r', used'⟩ := p
      rw [hY] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨b, ys, hb, rfl, rfl⟩

theorem condZ_some {fn : UFn} {ns : BodyNames} {cnd : UEns} {ce : Gabbro.Body.Expr}
    (h : condZ u fn ns cnd = some ce) :
    ∃ raw, ∃ a : Acc, ensExpr u fn {} cnd = some (raw, a) ∧
      a.olds.length = 0 ∧ a.result = false ∧ renameScalar (ns.lookup fn) raw = some ce := by
  unfold condZ at h
  cases hr : rawCond u fn cnd with
  | none => rw [hr] at h; cases h
  | some raw =>
    rw [hr] at h
    unfold rawCond at hr
    split at hr
    · rename_i x a hx
      split at hr
      · rename_i hc
        cases hr
        exact ⟨raw, a, hx, hc.1, hc.2, h⟩
      · cases hr
    · cases hr

theorem condZ_sicht {fT fn : UFn} (h : Sicht u fT fn) (ns : BodyNames) (c : UEns) :
    condZ u fT ns c = condZ u fn ns c := by
  have hn : ns.lookup fT = ns.lookup fn := funext (BodyNames.lookup_sicht h ns)
  unfold condZ rawCond
  rw [ensExpr_sicht h, hn]

theorem schrittB_einzeln_sicht {fT fn : UFn} {ns ns' : BodyNames}
    (hS : Sicht u fT fn) {s : UStmt} {b : Gabbro.Body.Stmt} {fT' : UFn}
    (h : schrittB u fT ns s = some (b, fT', ns')) (hs : LeseEinzeln s) :
    schrittB u fn ns s = some (b, fn, ns) ∧ fT' = fT ∧ ns' = ns := by
  cases s
  case setVar x v =>
    obtain ⟨hn, id, e, hid, he, rfl, hfT, hns⟩ := schrittB_setVar h
    refine ⟨?_, hfT, hns⟩
    have hn' : numericParam fn x = true := (hS.1 x).symm.trans hn
    have hid' := (BodyNames.lookup_sicht hS ns x).symm.trans hid
    have he' := (namedSide_sicht hS ns v).symm.trans he
    simp only [schrittB, hn', ↓reduceIte, hid', he']
  case assign | assignTab | assignGlob | call =>
    obtain ⟨hb, hfT, hns⟩ := schrittB_stmt h (fun _ _ _ h => by cases h)
      (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
    have hb' := (namedStmt_sicht hS ns _).symm.trans hb
    exact ⟨by simp only [schrittB, hb', Option.map_some], hfT, hns⟩
  all_goals cases hs

end Gabbro.Bruecke
