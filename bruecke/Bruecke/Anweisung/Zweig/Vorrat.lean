module
public import Bruecke.Anweisung.Zweig.Lesen
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik.Parser.Uebersetze

variable {u : UProg}

/-- Every successful statement retains the complete allocation history. -/
theorem schrittB_used {fn fn' : UFn} {ns ns' : BodyNames} {st : UStmt}
    {b : Gabbro.Body.Stmt} (h : schrittB u fn ns st = some (b, fn', ns')) :
    ∀ x ∈ ns.used, x ∈ ns'.used := by
  cases st
  case bind x d v =>
    obtain ⟨e, _, _, _, rfl⟩ := schrittB_bind h
    exact BodyNames.used_push ns x
  case bindMut x lo hi v =>
    obtain ⟨e, _, _, _, rfl⟩ := schrittB_bindMut h
    exact BodyNames.used_push ns x
  case setVar x v =>
    obtain ⟨_, id, e, _, _, _, _, rfl⟩ := schrittB_setVar h
    exact fun _ hx => hx
  all_goals
    obtain ⟨_, _, rfl⟩ := schrittB_stmt h (fun _ _ _ h => by cases h)
      (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
    exact fun _ hx => hx

/-- Returned histories include allocations from both arms and the continuation. -/
theorem seqZ_used : ∀ (k : Nat) (fn : UFn) (ns : BodyNames) (ss : List UStmt)
    (t : List Gabbro.Body.Stmt) (rest : List UStmt) (used : List String),
    seqZ u k fn ns ss = some (t, rest, used) → ∀ x ∈ ns.used, x ∈ used
  | 0, _, _, _, _, _, _, h => by cases h
  | k + 1, _, ns, [], _, _, _, h => by
      simp only [seqZ, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact fun _ hx => hx
  | k + 1, fn, ns, st :: ss, t, rest, used, h => by
      cases st
      case blkEnd | ifElse =>
        simp only [seqZ, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact fun _ hx => hx
      case ifBeg cnd | ifEnde cnd =>
        obtain ⟨ce, tb, eb, r1, r2, ys, used1, used2, _, hT, hE, hY, _⟩ :=
          seqZ_wenn_some (cnd := cnd) h (by first | exact .inl rfl | exact .inr rfl)
        have ht := seqZ_used k fn ns ss tb _ used1 hT
        have he := seqZ_used k fn (ns.resume used1) r1 eb _ used2 hE
        have hy := seqZ_used k fn (ns.resume used2) r2 ys rest used hY
        exact fun x hx => hy x (he x (ht x hx))
      case ret r =>
        obtain ⟨b, ys, _, hY, _⟩ := seqZ_ret_some h
        exact seqZ_used k fn ns ss ys rest used hY
      all_goals
        simp only [seqZ] at h
        split at h
        · rename_i b fn' ns' hs
          cases hY : seqZ u k fn' ns' ss with
          | none => rw [hY] at h; cases h
          | some p =>
            obtain ⟨ys, r', used'⟩ := p
            rw [hY] at h
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            have hy := seqZ_used k fn' ns' ss ys _ _ hY
            exact fun x hx => hy x (schrittB_used hs x hx)
        · cases h

theorem UmfangB.afterSeq {Γ : Gabbro.Grammatik.Ctx} {fn fT : UFn} {ns : BodyNames}
    (hU : UmfangB Γ fn ns) {k : Nat} {ss rest : List UStmt}
    {t : List Gabbro.Body.Stmt} {used : List String}
    (h : seqZ u k fT ns ss = some (t, rest, used)) : UmfangB Γ fn (ns.resume used) :=
  hU.resume (seqZ_used k fT ns ss t rest used h)

end Gabbro.Bruecke
