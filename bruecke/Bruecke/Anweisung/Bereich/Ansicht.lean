module
public import Bruecke.Anweisung.Bereich.Basis
public import Bruecke.Anweisung.Zweig.Lesen
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
variable {u : UProg}

/-- One successful read step, retaining recursive reader equations for induction. -/
inductive EndRead (u : UProg) (k : Nat) (fn : UFn) (ns : BodyNames) :
    List UStmt → List Gabbro.Body.Stmt → List UStmt → Prop where
  | ret {r ss b} : retZ u fn ns r = some b → EndRead u k fn ns (.ret r :: ss) [b] ss
  | control (leave : Bool) (x : String) (ss : List UStmt) :
      EndRead u k fn ns (controlU leave x :: ss) [controlStmtB leave] ss
  | leaf {st ss b ys tail} : endLeafB st = true → schrittB u fn ns st = some (b, fn, ns) →
      endBodyZ u k fn ns ss = some (ys, tail) → EndRead u k fn ns (st :: ss) (b :: ys) tail
  | binding {st ss b fn' ns' ys tail} : endLocalB st = true →
      schrittB u fn ns st = some (b, fn', ns') → endBodyZ u k fn' ns' ss = some (ys, tail) →
      EndRead u k fn ns (st :: ss) (b :: ys) tail
  | record {x d v ss id fs e ys tail} :
      recordBinderType u fn d v = some (.prod id fs) → namedSide u fn ns v = some e →
      endBodyZ u k (fn.mitWert x (.prod id fs)) (ns.push x) ss = some (ys, tail) →
      EndRead u k fn ns (.bindW x d v :: ss) (.bindName (ns.fresh x) e :: ys) tail

/-- The view is derived from the executable reader, never an extra admission premise. -/
theorem endBodyZ_view {k : Nat} {fn : UFn} {ns : BodyNames} {ss tail : List UStmt}
    {bs : List Gabbro.Body.Stmt} (h : endBodyZ u (k + 1) fn ns ss = some (bs, tail)) :
    EndRead u k fn ns ss bs tail := by
  have binding (st : UStmt) (rest : List UStmt) (hl : endLocalB st = true)
      (h : (do
        let (b, fn', ns') ← schrittB u fn ns st
        let (ys, tail') ← endBodyZ u k fn' ns' rest
        pure (b :: ys, tail')) = some (bs, tail)) :
      EndRead u k fn ns (st :: rest) bs tail := by
    cases hs : schrittB u fn ns st with
    | none => simp [hs] at h
    | some p =>
      rcases p with ⟨b, fn', ns'⟩
      cases hy : endBodyZ u k fn' ns' rest with
      | none => simp [hs, hy] at h
      | some p =>
        rcases p with ⟨ys, rest'⟩
        simp only [hs, hy, bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .binding hl hs hy
  have leaf (st : UStmt) (rest : List UStmt) (hl : endLeafB st = true)
      (h : (do
        let (b, _, _) ← schrittB u fn ns st
        let (ys, tail') ← endBodyZ u k fn ns rest
        pure (b :: ys, tail')) = some (bs, tail)) :
      EndRead u k fn ns (st :: rest) bs tail := by
    cases hs : schrittB u fn ns st with
    | none => simp [hs] at h
    | some p =>
      rcases p with ⟨b, fn', ns'⟩
      have hs' := schrittB_einzeln_sicht (Sicht.refl fn) hs (endLeafB_ok hl)
      cases hy : endBodyZ u k fn ns rest with
      | none => simp [hs, hy] at h
      | some p =>
        rcases p with ⟨ys, rest'⟩
        simp only [hs, hy, bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .leaf hl hs'.1 hy
  cases ss with
  | nil => cases h
  | cons st ss =>
    cases st
    case ret r =>
      simp only [endBodyZ] at h
      cases hb : retZ u fn ns r with
      | none => rw [hb] at h; cases h
      | some b => rw [hb] at h; cases h; exact .ret hb
    case leave x => cases h; exact .control true x ss
    case next x => cases h; exact .control false x ss
    case bindW x d v =>
      simp only [endBodyZ] at h
      cases ht : recordBinderType u fn d v with
      | none => simp [ht] at h
      | some ty =>
        obtain ⟨id, fs, rfl⟩ := recordBinderType_prod ht
        cases he : namedSide u fn ns v with
        | none => simp [ht, he] at h
        | some e =>
          cases hy : endBodyZ u k (fn.mitWert x (.prod id fs)) (ns.push x) ss with
          | none => simp [ht, he, hy] at h
          | some p =>
            rcases p with ⟨ys, rest⟩
            simp only [ht, he, hy, bind, Option.bind_some, pure, Option.some.injEq,
              Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .record ht he hy
    all_goals
      simp only [endBodyZ] at h
      split at h
      · rename_i hl
        exact binding _ _ hl h
      · split at h
        · rename_i hl
          exact leaf _ _ hl h
        · cases h

/-- Every mandatory ending leaves a suffix of its input. -/
theorem endBodyZ_suffix : ∀ (k : Nat) (fn : UFn) (ns : BodyNames) (ss : List UStmt)
    (bs : List Gabbro.Body.Stmt) (tail : List UStmt),
    endBodyZ u k fn ns ss = some (bs, tail) → tail <:+ ss
  | 0, _, _, _, _, _, h => by cases h
  | k + 1, fn, ns, ss, bs, tail, h => by
    cases endBodyZ_view h with
    | ret => exact List.suffix_cons _ _
    | control leave x ss => cases leave <;> exact List.suffix_cons _ _
    | leaf hl hs hy | binding hl hs hy | record ht he hy =>
      exact (endBodyZ_suffix k _ _ _ _ _ hy).trans (List.suffix_cons _ _)

end Gabbro.Bruecke
