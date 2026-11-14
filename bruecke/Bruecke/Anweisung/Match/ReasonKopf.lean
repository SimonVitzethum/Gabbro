module
public import Bruecke.Anweisung.Match.ReasonLesen
public import Bruecke.Anweisung.Match.Kopf
@[expose] public section
namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg} {c : Fin u.fns.length}

theorem lowGArms_succ {fuel n : Nat} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {ss tail : List UStmt} {arms : GrundArms (declOf u) (verOf u c) false Γ Λ Λ (n + 1)}
    (h : lowGArmsL u c Γ fn (fuel + 1) Λ [] (n + 1) ss = .ok (arms, tail)) :
    ∃ (body : Block (declOf u) (verOf u c) false Γ Λ Λ)
      (restArms : GrundArms (declOf u) (verOf u c) false Γ Λ Λ n), ∃ remaining,
      lowSeqL u c Γ fn fuel Λ [] ss = .ok (⟨Λ, body⟩, remaining) ∧
      ((n = 0 ∧ remaining = tail) ∨
       ∃ m rest, n = m + 1 ∧ remaining = .ifElse :: rest ∧
         lowGArmsL u c Γ fn fuel Λ [] n rest = .ok (restArms, tail)) ∧
      arms = .cons body restArms := by
  change lowGArmsStep u c (lowStufe u c fuel) Γ fn Λ [] (n + 1) ss = .ok (arms, tail) at h
  simp only [lowGArmsStep, lowStufe_seq, lowStufe_garms] at h
  cases hb : lowSeqL (l := false) u c Γ fn fuel Λ [] ss with
  | error err => simp only [hb, bind, Except.bind] at h <;> cases h
  | ok result =>
    obtain ⟨⟨out, body⟩, remaining⟩ := result
    simp only [hb, bind, Except.bind] at h
    cases n with
    | zero =>
      by_cases same : out = Λ
      · subst out
        simp only [↓reduceDIte] at h
        change Except.ok (GrundArms.cons body .nil, remaining) = .ok (arms, tail) at h
        obtain ⟨harms, htail⟩ := Prod.mk.inj (Except.ok.inj h)
        exact ⟨body, .nil, remaining, (by simp only [hb]), .inl ⟨rfl, htail⟩, harms.symm⟩
      · simp only [same, ↓reduceDIte] at h <;> cases h
    | succ m =>
      cases remaining with
      | nil => cases h
      | cons marker rest =>
        cases marker <;> try { cases h }
        case ifElse =>
          cases hrest : lowGArmsL (l := false) u c Γ fn fuel Λ [] (m + 1) rest with
          | error err => simp only [hrest, bind, Except.bind] at h <;> cases h
          | ok result =>
            obtain ⟨restArms, remaining'⟩ := result
            by_cases same : out = Λ
            · subst out
              simp only [hrest, bind, Except.bind, ↓reduceDIte] at h
              change Except.ok (GrundArms.cons body restArms, remaining') = .ok (arms, tail) at h
              obtain ⟨harms, htail⟩ := Prod.mk.inj (Except.ok.inj h)
              exact ⟨body, restArms, .ifElse :: rest, (by simp only [hb]),
                .inr ⟨m, rest, rfl, rfl, (by simp only [hrest, htail])⟩, harms.symm⟩
            · simp only [hrest, bind, Except.bind, same, ↓reduceDIte] at h <;> cases h

theorem lowBodyF_reason_ok {Γ : Ctx} {fn : UFn} {n : Nat} {Λ : List (Res (declOf u))}
    {x : String} {ss : List UStmt} {r : URet} {b0 : Endblock (declOf u) (verOf u c) false Γ Λ}
    (h : lowBodyF u c Γ fn (n + 1) Λ (.matchWhyBeg x :: ss) r = .ok b0) :
    ∃ Λ₁, ∃ (st : Stmt (declOf u) (verOf u c) false Γ Λ Λ₁), ∃ tail,
      ∃ (rest : Endblock (declOf u) (verOf u c) false Γ Λ₁),
      lowStructL u c Γ fn blockFuel Λ [] (.matchWhyBeg x) ss = .ok (⟨Λ₁, st⟩, tail) ∧
      lowBodyF u c Γ fn n Λ₁ tail r = .ok rest ∧ b0 = .cons st rest := by
  simp only [lowBodyF] at h
  split at h
  · cases h
  · rename_i Λ₁ st tail hs
    split at h
    · cases h
    · rename_i rest hr
      cases h
      exact ⟨Λ₁, st, tail, rest, hs, hr, rfl⟩

theorem lowStruct_reason_ok {fuel count : Nat} {Γ : Ctx} {fn : UFn}
    {Λ Λ' : List (Res (declOf u))} {x : String} {ss tail : List UStmt}
    {st : Stmt (declOf u) (verOf u c) false Γ Λ Λ'}
    (ht : valueParamTy fn x = some (.why count))
    (h : lowStructL u c Γ fn (fuel + 1) Λ [] (.matchWhyBeg x) ss = .ok (⟨Λ', st⟩, tail)) :
    ∃ j, ∃ (v : Var Γ (.why count))
      (arms : GrundArms (declOf u) (verOf u c) false Γ Λ Λ count),
      paramPos fn.params x = .ok j ∧ lowVar Γ j (.why count) = .ok v ∧
      lowGArmsL u c Γ fn fuel Λ [] count ss = .ok (arms, .blkEnd :: tail) ∧
      Λ' = Λ ∧ HEq st (Stmt.onWhy (Expr.var v) arms) := by
  rw [lowStructL_succ] at h
  simp only [lowStructStep, lowStufe_garms] at h
  cases hj : paramPos fn.params x with
  | error err => simp only [hj] at h; cases h
  | ok j =>
    simp only [hj] at h
    unfold valueParamTy at ht
    rw [paramPos_find _ _ _ hj] at ht
    cases hp : fn.params[j]? with
    | none => simp only [hp] at ht; cases ht
    | some entry =>
      obtain ⟨name, ty⟩ := entry
      rw [hp] at ht
      cases ty
      case why cnt =>
        simp only [Option.some.injEq, Ty.why.injEq] at ht
        subst cnt
        simp only [hp] at h
        cases hv : lowVar Γ j (.why count) with
        | error err => simp only [hv] at h <;> cases h
        | ok v =>
          simp only [hv] at h
          cases ha : lowGArmsL (l := false) u c Γ fn fuel Λ [] count ss with
          | error err => simp only [ha] at h <;> cases h
          | ok result =>
            obtain ⟨arms, remaining⟩ := result
            simp only [ha] at h
            cases remaining with
            | nil => cases h
            | cons marker rest =>
              cases marker <;> try { cases h }
              case blkEnd =>
                cases h
                exact ⟨j, v, arms, (by first | exact hj | rfl),
                  (by first | exact hv | rfl), (by first | exact ha | rfl | simp_all),
                  rfl, HEq.rfl⟩
      all_goals cases ht

end Gabbro.Bruecke
