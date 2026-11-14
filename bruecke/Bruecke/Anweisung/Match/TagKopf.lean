module
public import Bruecke.Anweisung.Match.ReasonKopf
@[expose] public section
namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg} {c : Fin u.fns.length}

/-- The common finite dispatch mechanism applies precisely to cases without payloads. -/
inductive BareArms {D : Deklaration} {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)} :
    {cs : List (Option Ty)} → Arms D V false Γ Λ Λ cs → GrundArms D V false Γ Λ Λ cs.length → Prop where
  | nil : BareArms .nil .nil
  | cons {cs : List (Option Ty)} {b : Block D V false Γ Λ Λ}
      {arms : Arms D V false Γ Λ Λ cs} {reasons : GrundArms D V false Γ Λ Λ cs.length} :
      BareArms arms reasons → BareArms (cs := none :: cs) (.cons b arms) (.cons b reasons)

theorem BareArms.exec {D : Deklaration} {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {cs : List (Option Ty)} {arms : Arms D V false Γ Λ Λ cs}
    {reasons : GrundArms D V false Γ Λ Λ cs.length} (h : BareArms arms reasons)
    (v : Wert D (.sum cs)) (σ : World D) (ρ : Env D Γ) :
    execArms O passes R arms v σ ρ = execGrund O passes R reasons v.1 σ ρ := by
  induction h with
  | nil => exact (Nat.not_lt_zero _ v.1.isLt).elim
  | @cons cs b arms reasons h ih =>
    rcases v with ⟨⟨i, hi⟩, payload⟩
    cases i with
    | zero => rfl
    | succ i => exact ih ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, payload⟩

/-- The canonical readers of bare tag arms and reason arms lower identical blocks. -/
theorem lowArms_bare : ∀ fuel {Γ : Ctx} (fn : UFn) (Λ : List (Res (declOf u))),
    ∀ cs binders ss, ∀ (arms : Arms (declOf u) (verOf u c) false Γ Λ Λ cs), ∀ tail,
    cs.all Option.isNone = true →
    lowArmsT u c Γ fn fuel Λ [] cs binders ss = .ok (arms, tail) →
    ∃ reasons : GrundArms (declOf u) (verOf u c) false Γ Λ Λ cs.length,
      lowGArmsL u c Γ fn fuel Λ [] cs.length ss = .ok (reasons, tail) ∧ BareArms arms reasons := by
  intro fuel
  induction fuel with
  | zero =>
    intro Γ fn Λ cs binders ss arms tail hBare h
    cases h
  | succ fuel ih =>
    intro Γ fn Λ cs binders ss arms tail hBare h
    cases cs with
    | nil =>
      change Except.ok (Arms.nil, ss) = .ok (arms, tail) at h
      cases h
      exact ⟨.nil, rfl, .nil⟩
    | cons head cs =>
      cases head with
      | some ty => cases hBare
      | none =>
        have hBare' : cs.all Option.isNone = true := by simpa only [List.all_cons, Option.isNone_none, Bool.true_and] using hBare
        change lowArmsStep u c (lowStufe u c fuel) Γ fn Λ [] (none :: cs) binders ss = .ok (arms, tail) at h
        simp only [lowArmsStep, lowStufe_seq, lowStufe_arms] at h
        cases hb : lowSeqL (l := false) u c Γ fn fuel Λ [] ss with
        | error err => simp only [hb, bind, Except.bind] at h <;> cases h
        | ok result =>
          obtain ⟨⟨out, body⟩, remaining⟩ := result
          simp only [hb, bind, Except.bind] at h
          cases cs with
          | nil =>
            by_cases same : out = Λ
            · subst out
              simp only [↓reduceDIte] at h
              change Except.ok (Arms.cons body .nil, remaining) = .ok (arms, tail) at h
              obtain ⟨harms, htail⟩ := Prod.mk.inj (Except.ok.inj h)
              subst arms
              subst tail
              refine ⟨.cons body .nil, ?_, .cons .nil⟩
              unfold lowGArmsL lowStufe
              simp only [List.length_cons, List.length_nil, lowGArmsStep, lowStufe_seq,
                hb, bind, Except.bind, ↓reduceDIte]
            · simp only [same, ↓reduceDIte] at h <;> cases h
          | cons head cs =>
            cases remaining with
            | nil => cases h
            | cons marker rest =>
              cases marker <;> try { cases h }
              case ifElse =>
                cases hrest : lowArmsT (l := false) u c Γ fn fuel Λ [] (head :: cs) (binders.drop 1) rest with
                | error err => simp only [hrest, bind, Except.bind] at h <;> cases h
                | ok result =>
                  obtain ⟨restArms, restTail⟩ := result
                  by_cases same : out = Λ
                  · subst out
                    simp only [hrest, bind, Except.bind, ↓reduceDIte] at h
                    change Except.ok (Arms.cons body restArms, restTail) = .ok (arms, tail) at h
                    obtain ⟨harms, htail⟩ := Prod.mk.inj (Except.ok.inj h)
                    subst arms
                    subst tail
                    obtain ⟨reasons, hReasons, hRel⟩ := ih fn Λ (head :: cs) (binders.drop 1)
                      rest restArms restTail hBare' (by first | exact hrest | rfl | simp_all)
                    refine ⟨.cons body reasons, ?_, .cons hRel⟩
                    simp only [List.length_cons] at hReasons
                    unfold lowGArmsL lowStufe
                    simp only [List.length_cons, lowGArmsStep, lowStufe_seq,
                      lowStufe_garms, hb, bind, Except.bind, hReasons, ↓reduceDIte]
                  · simp only [hrest, bind, Except.bind, same, ↓reduceDIte] at h <;> cases h

/-- Only local, bare tag subjects enter this reader; statics and payload cases remain refused. -/
theorem lowStruct_tag_ok {fuel sidx : Nat} {Γ : Ctx} {fn : UFn}
    {Λ Λ' : List (Res (declOf u))} {x : String} {binders : List String} {cs : List (Option Ty)}
    {ss tail : List UStmt} {st : Stmt (declOf u) (verOf u c) false Γ Λ Λ'}
    (hn : sidx < u.sums.length) (ht : valueParamTy fn x = some (.sum cs))
    (h : lowStructL u c Γ fn (fuel + 1) Λ [] (.matchTagBeg sidx x binders) ss = .ok (⟨Λ', st⟩, tail)) :
    ∃ j, ∃ (v : Var Γ (.sum cs)) (arms : Arms (declOf u) (verOf u c) false Γ Λ Λ cs),
      paramPos fn.params x = .ok j ∧ lowVar Γ j (.sum cs) = .ok v ∧
      lowArmsT u c Γ fn fuel Λ [] cs binders ss = .ok (arms, .blkEnd :: tail) ∧
      Λ' = Λ ∧ HEq st (Stmt.onTag (Expr.var v) arms) := by
  rw [lowStructL_succ] at h
  simp only [lowStructStep, dif_pos hn, lowStufe_arms] at h
  cases hj : paramPos fn.params x with
  | error err =>
    unfold valueParamTy at ht
    rw [paramPos_find_none _ _ _ hj] at ht
    cases ht
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
      case sum actual =>
        simp only [Option.some.injEq, Ty.sum.injEq] at ht
        subst actual
        simp only [hp] at h
        cases hv : lowVar Γ j (.sum cs) with
        | error err => simp only [hv] at h <;> cases h
        | ok v =>
          simp only [hv] at h
          cases ha : lowArmsT (l := false) u c Γ fn fuel Λ [] cs binders ss with
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

theorem lowBodyF_tag_ok {Γ : Ctx} {fn : UFn} {n sidx : Nat} {Λ : List (Res (declOf u))}
    {x : String} {binders : List String} {ss : List UStmt} {r : URet}
    {b0 : Endblock (declOf u) (verOf u c) false Γ Λ}
    (h : lowBodyF u c Γ fn (n + 1) Λ (.matchTagBeg sidx x binders :: ss) r = .ok b0) :
    ∃ Λ₁, ∃ (st : Stmt (declOf u) (verOf u c) false Γ Λ Λ₁), ∃ tail,
      ∃ (rest : Endblock (declOf u) (verOf u c) false Γ Λ₁),
      lowStructL u c Γ fn blockFuel Λ [] (.matchTagBeg sidx x binders) ss = .ok (⟨Λ₁, st⟩, tail) ∧
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
end Gabbro.Bruecke
