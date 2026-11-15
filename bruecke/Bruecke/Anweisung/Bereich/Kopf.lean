module
public import Bruecke.Anweisung.Bereich.Bindung
public import Bruecke.Anweisung.Zweig.Kopf
public import Bruecke.Anweisung.Schleife.Kontrolle
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
  cases hj : paramPos fn.params x with
  | error e => simp only [hj] at h <;> cases h
  | ok j =>
    simp only [hj] at h
    have hnum := hn
    unfold numericParam at hnum
    rw [paramPos_find _ _ _ hj] at hnum
    cases hp : fn.params[j]? with
    | none => rw [hp] at h <;> cases h
    | some p =>
      obtain ⟨nm, ty⟩ := p
      rw [hp] at hnum
      cases ty
      case int a b =>
        simp only [hp] at h
        cases hv : lowVar Γ j (.int a b) with
        | error e => simp only [hv] at h <;> cases h
        | ok v =>
          simp only [hv] at h
          cases herr : lowEndL (l := false) u c Γ fn blockFuel Λ [] ss with
          | error e => simp only [herr] at h <;> cases h
          | ok pair =>
            obtain ⟨err, ending⟩ := pair
            simp only [herr] at h
            cases ending with
            | nil => cases h
            | cons marker tail =>
              cases marker <;> try { cases h }
              case blkEnd =>
                cases hrest : lowBodyF u c (.int lo hi :: Γ)
                    (fn.mitBindung x (lo, hi)) n Λ tail r with
                | error e => simp only [hrest] at h <;> cases h
                | ok rest =>
                  simp only [hrest] at h
                  cases h
                  exact ⟨j, a, b, v, err, tail, rest,
                    (by first | exact hj | rfl), (by first | exact hv | rfl),
                    (by first | exact herr | rfl | simp_all), hrest, rfl⟩
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
  | error e => simp only [hj, Except.bind] at h <;> cases h
  | ok j =>
    simp only [hj, Except.bind] at h
    have hnum := hn
    unfold numericParam at hnum
    rw [paramPos_find _ _ _ hj] at hnum
    cases hp : fn.params[j]? with
    | none => rw [hp] at h <;> cases h
    | some entry =>
      obtain ⟨nm, ty⟩ := entry
      rw [hp] at hnum
      cases ty
      case int a b =>
        simp only [hp] at h
        cases hv : lowVar Γ j (.int a b) with
        | error e => simp only [hv, Except.bind] at h <;> cases h
        | ok v =>
          simp only [hv, Except.bind] at h
          cases herr : lowEndL (l := loopMode) u c Γ fn n Λ [] ss with
          | error e => simp only [herr] at h <;> cases h
          | ok pair =>
            obtain ⟨err, ending⟩ := pair
            simp only [herr] at h
            cases ending with
            | nil => cases h
            | cons marker remaining =>
              cases marker <;> try { cases h }
              case blkEnd =>
                cases hq : lowSeqL (l := loopMode) u c (.int lo hi :: Γ)
                    (fn.mitBindung x (lo, hi)) n Λ [] remaining with
                | error e => simp only [hq, Except.bind] at h <;> cases h
                | ok pair =>
                  obtain ⟨⟨Λ', rest⟩, tail'⟩ := pair
                  simp only [hq, Except.bind] at h
                  cases h
                  exact ⟨j, a, b, v, err, remaining, ⟨Λ', rest⟩,
                    (by first | exact hj | rfl), (by first | exact hv | rfl), (by first | exact herr | rfl | simp_all), hq, rfl⟩
      all_goals cases hnum

/-- Leaf statements in an explicit ending use the same canonical single-statement reader. -/
theorem lowEndL_leaf_ok {loopMode : Bool} {Γ : Ctx} {fn : UFn} {n : Nat} {Λ : List (Res (declOf u))}
    {st : UStmt} {ss tail : List UStmt} {endB : Endblock (declOf u) (verOf u c) loopMode Γ Λ}
    (hs : LeseEinzeln st)
    (h : lowEndL (l := loopMode) u c Γ fn (n + 1) Λ [] (st :: ss) = .ok (endB, tail)) :
    ∃ Λ', ∃ (gs : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ')
      (rest : Endblock (declOf u) (verOf u c) loopMode Γ Λ'),
      lowStmtL (l := loopMode) u c Γ fn Λ st = .ok ⟨Λ', gs⟩ ∧
      lowEndL (l := loopMode) u c Γ fn n Λ' [] ss = .ok (rest, tail) ∧ endB = .cons gs rest := by
  rw [lowEndL_succ] at h
  have hd : lowEndStep (l := loopMode) u c (lowStufe u c n) Γ fn Λ [] (st :: ss) =
      (lowStmtL (l := loopMode) u c Γ fn Λ st).bind (fun p =>
        (lowEndL (l := loopMode) u c Γ fn n p.1 [] ss).bind (fun e => .ok (.cons p.2 e.1, e.2))) := by
    cases st
    case assign | assignTab | assignOpt | assignTabOpt | assignGlob | assignGlobB | call | setVar | setVarB | setVarOpt => rfl
    all_goals cases hs
  rw [hd] at h
  cases hg : lowStmtL (l := loopMode) u c Γ fn Λ st with
  | error e => simp only [hg, Except.bind] at h <;> cases h
  | ok pair =>
    obtain ⟨Λ', gs⟩ := pair
    simp only [hg, Except.bind] at h
    cases he : lowEndL (l := loopMode) u c Γ fn n Λ' [] ss with
    | error e => simp only [he, Except.bind] at h <;> cases h
    | ok pair =>
      obtain ⟨rest, tail'⟩ := pair
      simp only [he, Except.bind] at h
      cases h
      exact ⟨Λ', gs, rest, (by first | exact hg | rfl), he, rfl⟩

def controlEnd {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (leave : Bool) (hl : l = true) : Endblock D V l Γ Λ :=
  if leave then .leave hl else .next hl

theorem lowEnd_control_ok {loopMode : Bool} {Γ : Ctx} {fn : UFn} {n : Nat}
    {Λ : List (Res (declOf u))} {leave : Bool} {x : String} {ss tail : List UStmt}
    {ending : Endblock (declOf u) (verOf u c) loopMode Γ Λ}
    (h : lowEndL (l := loopMode) u c Γ fn (n + 1) Λ [] (controlU leave x :: ss) = .ok (ending, tail)) :
    ∃ hl : loopMode = true, ending = controlEnd leave hl ∧ tail = ss := by
  cases leave <;> rw [lowEndL_succ] at h <;>
    simp only [controlU, Bool.false_eq_true, ↓reduceIte, lowEndStep] at h
  all_goals
    split at h
    · rename_i hl
      cases h
      exact ⟨hl, rfl, rfl⟩
    · cases h

theorem endBodyZ_rest {loopMode : Bool} : ∀ n k ss {Γ : Ctx} (fn ft : UFn) (ns : BodyNames)
    {Λ : List (Res (declOf u))} (ending : Endblock (declOf u) (verOf u c) loopMode Γ Λ)
    (rest tail : List UStmt) (bs : List Gabbro.Body.Stmt),
    lowEndL (l := loopMode) u c Γ fn n Λ [] ss = .ok (ending, rest) →
    endBodyZ u k ft ns ss = some (bs, tail) → rest = tail
  | 0, _, _, _, _, _, _, _, _, _, _, _, h, _ => by cases h
  | _ + 1, 0, _, _, _, _, _, _, _, _, _, _, _, h => by cases h
  | _ + 1, _ + 1, [], _, _, _, _, _, _, _, _, _, _, h => by cases h
  | n + 1, k + 1, st :: ss, Γ, fn, ft, ns, Λ, ending, rest, tail, bs, hG, hB => by
    cases endBodyZ_view hB with
    | @ret r ss b hr =>
      rw [lowEndL_succ] at hG
      simp only [lowEndStep] at hG
      cases hg : lowRetEnd (l := loopMode) u c Γ fn Λ [] r with
      | error e => simp only [hg, Except.map] at hG; cases hG
      | ok e => simp only [hg, Except.map] at hG; cases hG; rfl
    | control leave x ss =>
      obtain ⟨_, _, rfl⟩ := lowEnd_control_ok hG
      rfl
    | leaf hleaf hs hys =>
      obtain ⟨Λ', gs, nextB, _, hnext, _⟩ := lowEndL_leaf_ok (endLeafB_ok hleaf) hG
      exact endBodyZ_rest n k _ fn ft ns nextB rest tail _ hnext hys
    | @binding st ss b ft' ns' ys tail hl hs hys =>
      cases st
      case bind x d v =>
        obtain ⟨e, _, _, rfl, rfl⟩ := schrittB_bind hs
        obtain ⟨ls, nextB, _, hnext, _⟩ := lowEnd_bind_ok hG
        exact endBodyZ_rest n k ss (fn.mitBindung x ls.range) (ft.mitBindung x (0, 0))
          (ns.push x) nextB rest tail ys hnext hys
      case bindMut x lo hi v =>
        obtain ⟨e, _, _, rfl, rfl⟩ := schrittB_bindMut hs
        obtain ⟨ev, nextB, _, hnext, _⟩ := lowEnd_bindMut_ok hG
        exact endBodyZ_rest n k ss (fn.mitBindung x (lo, hi)) (ft.mitBindung x (lo, hi))
          (ns.push x) nextB rest tail ys hnext hys
      case bindB x v =>
        obtain ⟨e, _, _, rfl, rfl⟩ := schrittB_bindB hs
        obtain ⟨ev, nextB, _, hnext, _⟩ := lowEnd_bindB_ok hG
        exact endBodyZ_rest n k ss (fn.mitBindungB x) (ft.mitBindungB x)
          (ns.push x) nextB rest tail ys hnext hys
      all_goals cases hl
    | @record x d v ss id fs e ys tail ht he hys =>
      obtain ⟨w, nextB, _, hnext, _⟩ := lowEnd_bindW_ok hG
      exact endBodyZ_rest n k ss (fn.mitWert x w.ty) (ft.mitWert x (.prod id fs))
        (ns.push x) nextB rest tail ys hnext hys


end Gabbro.Bruecke
