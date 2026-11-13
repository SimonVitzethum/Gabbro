module
public import Bruecke.Anweisung.Bereich.Lesen
public import Bruecke.Anweisung.Zweig.Kopf
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {c : Fin u.fns.length}

theorem lowBodyF_narrow_ok {Γ : Ctx} {fn : UFn} {n : Nat} {Λ : List (Res (declOf u))}
    {x : String} {lo hi : Int} {ss : List UStmt} {r : URet}
    {b0 : Endblock (declOf u) (verOf u c) false Γ Λ}
    (hn : numericParam fn x = true)
    (h : lowBodyF u c Γ fn (n + 1) Λ (.narrowBeg x lo hi :: ss) r = .ok b0) :
    ∃ (j : Nat) (a b : Int) (v : Var Γ (.int a b))
      (err : Endblock (declOf u) (verOf u c) false Γ Λ) (tail : List UStmt)
      (rest : Endblock (declOf u) (verOf u c) false (.int lo hi :: Γ) Λ),
      paramPos fn.params x = .ok j ∧ lowVar Γ j (.int a b) = .ok v ∧
      lowEndL (l := false) u c Γ fn blockFuel Λ [] ss = .ok (err, .blkEnd :: tail) ∧
      lowBodyF u c (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) n Λ tail r = .ok rest ∧
      b0 = .narrow (.var v) lo hi err rest := by
  simp only [lowBodyF] at h
  split at h
  · cases h
  · rename_i j hj
    have hnum := hn
    unfold numericParam at hnum
    rw [paramPos_find _ _ _ hj] at hnum
    cases hp : fn.params[j]? with
    | none => rw [hp] at h; cases h
    | some p =>
      obtain ⟨nm, ty⟩ := p
      rw [hp] at h hnum
      cases ty
      case int a b =>
        split at h
        · cases h
        · rename_i v hv
          split at h
          · cases h
          · rename_i err tail herr
            split at h
            · cases h
            · rename_i rest hrest
              cases h
              exact ⟨j, a, b, v, err, tail, rest, hj, hv, herr, hrest, rfl⟩
          · cases h
      all_goals cases hnum

theorem lowSeq_narrow_ok {loopMode : Bool} {Γ : Ctx} {fn : UFn} {n : Nat} {Λ : List (Res (declOf u))}
    {x : String} {lo hi : Int} {ss tail : List UStmt}
    {p : Σ Λ', Block (declOf u) (verOf u c) loopMode Γ Λ Λ'}
    (hn : numericParam fn x = true)
    (h : lowSeqL (l := loopMode) u c Γ fn (n + 1) Λ [] (.narrowBeg x lo hi :: ss) = .ok (p, tail)) :
    ∃ (j : Nat) (a b : Int) (v : Var Γ (.int a b))
      (err : Endblock (declOf u) (verOf u c) loopMode Γ Λ) (remaining : List UStmt)
      (q : Σ Λ', Block (declOf u) (verOf u c) loopMode (.int lo hi :: Γ) Λ Λ'),
      paramPos fn.params x = .ok j ∧ lowVar Γ j (.int a b) = .ok v ∧
      lowEndL (l := loopMode) u c Γ fn n Λ [] ss = .ok (err, .blkEnd :: remaining) ∧
      lowSeqL (l := loopMode) u c (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) n Λ [] remaining = .ok (q, tail) ∧
      p = ⟨q.1, .narrow (.var v) lo hi err q.2⟩ := by
  rw [lowSeqL_succ] at h
  simp only [lowSeqStep, lowStufe_seq, lowStufe_ende] at h
  cases hj : paramPos fn.params x with
  | error e => simp only [hj, Except.bind] at h; cases h
  | ok j =>
    simp only [hj, Except.bind] at h
    have hnum := hn
    unfold numericParam at hnum
    rw [paramPos_find _ _ _ hj] at hnum
    cases hp : fn.params[j]? with
    | none => rw [hp] at h; cases h
    | some entry =>
      obtain ⟨nm, ty⟩ := entry
      rw [hp] at h hnum
      cases ty
      case int a b =>
        cases hv : lowVar Γ j (.int a b) with
        | error e => simp only [hv, Except.bind] at h; cases h
        | ok v =>
          simp only [hv, Except.bind] at h
          split at h
          · cases h
          · rename_i err remaining herr
            cases hq : lowSeqL (l := loopMode) u c (.int lo hi :: Γ)
                (fn.mitBindung x (lo, hi)) n Λ [] remaining with
            | error e => simp only [hq, Except.bind] at h; cases h
            | ok pair =>
              obtain ⟨⟨Λ', rest⟩, tail'⟩ := pair
              simp only [hq, Except.bind] at h
              cases h
              exact ⟨j, a, b, v, err, remaining, ⟨Λ', rest⟩, hj, hv, herr, hq, rfl⟩
          · cases h
      all_goals cases hnum

/-- Leaf statements in an explicit ending use the same canonical single-statement reader. -/
theorem lowEndL_leaf_ok {loopMode : Bool} {Γ : Ctx} {fn : UFn} {n : Nat} {Λ : List (Res (declOf u))}
    {st : UStmt} {ss tail : List UStmt} {endB : Endblock (declOf u) (verOf u c) loopMode Γ Λ}
    (hs : LeseEinzeln st)
    (h : lowEndL (l := loopMode) u c Γ fn (n + 1) Λ [] (st :: ss) = .ok (endB, tail)) :
    ∃ Λ' (gs : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ')
      (rest : Endblock (declOf u) (verOf u c) loopMode Γ Λ'),
      lowStmtL (l := loopMode) u c Γ fn Λ st = .ok ⟨Λ', gs⟩ ∧
      lowEndL (l := loopMode) u c Γ fn n Λ' [] ss = .ok (rest, tail) ∧ endB = .cons gs rest := by
  rw [lowEndL_succ] at h
  have hd : lowEndStep (l := loopMode) u c (lowStufe u c n) Γ fn Λ [] (st :: ss) =
      (lowStmtL (l := loopMode) u c Γ fn Λ st).bind (fun p =>
        (lowEndL (l := loopMode) u c Γ fn n p.1 [] ss).bind (fun e => .ok (.cons p.2 e.1, e.2))) := by
    cases st
    case assign | assignTab | assignGlob | call | setVar | setVarB => rfl
    all_goals cases hs
  rw [hd] at h
  cases hg : lowStmtL (l := loopMode) u c Γ fn Λ st with
  | error e => simp only [hg, Except.bind] at h; cases h
  | ok pair =>
    obtain ⟨Λ', gs⟩ := pair
    simp only [hg, Except.bind] at h
    cases he : lowEndL (l := loopMode) u c Γ fn n Λ' [] ss with
    | error e => simp only [he, Except.bind] at h; cases h
    | ok pair =>
      obtain ⟨rest, tail'⟩ := pair
      simp only [he, Except.bind] at h
      cases h
      exact ⟨Λ', gs, rest, hg, he, rfl⟩

theorem endBodyZ_rest {loopMode : Bool} : ∀ n k ss {Γ : Ctx} (fn ft : UFn) (ns : BodyNames)
    {Λ : List (Res (declOf u))} (ending : Endblock (declOf u) (verOf u c) loopMode Γ Λ)
    (rest tail : List UStmt) (bs : List Gabbro.Body.Stmt),
    lowEndL (l := loopMode) u c Γ fn n Λ [] ss = .ok (ending, rest) →
    endBodyZ u k ft ns ss = some (bs, tail) → rest = tail
  | 0, _, _, _, _, _, _, _, _, _, _, _, h, _ => by cases h
  | _ + 1, 0, _, _, _, _, _, _, _, _, _, _, _, h => by cases h
  | _ + 1, _ + 1, [], _, _, _, _, _, _, _, _, _, _, h => by cases h
  | n + 1, k + 1, st :: ss, Γ, fn, ft, ns, Λ, ending, rest, tail, bs, hG, hB => by
    rcases endBodyZ_cases hB with ⟨r, b, rfl, _, _, rfl⟩ | ⟨b, ys, hleaf, _, hys, _⟩
    · rw [lowEndL_succ] at hG
      simp only [lowEndStep] at hG
      cases hg : lowRetEnd (l := loopMode) u c Γ fn Λ [] r with
      | error e => simp only [hg, Except.map] at hG; cases hG
      | ok e => simp only [hg, Except.map] at hG; cases hG; rfl
    · obtain ⟨Λ', gs, nextB, _, hnext, _⟩ := lowEndL_leaf_ok (endLeafB_ok hleaf) hG
      exact endBodyZ_rest n k ss fn ft ns nextB rest tail ys hnext hys

end Gabbro.Bruecke
