module
public import Bruecke.Anweisung.Zweig.Uebersetzung
@[expose] public section

/-!
# C6, part 2: the shape of the block reader, the G facts of a block, freshness through branches

The lowering reads the two arms of a conditional with the block reader `lowSeqL` (one fuel level
below the structured reader `lowStructL`, which the body reader `lowBodyF` calls at `blockFuel`).
These are the dispatch lemmas of the forms the bridge carries inside a block (`let`, `let mut`,
the statements `lowStmtL` reads, `return`, a nested conditional, the closing markers), the G
equations of a block, the inversions of `Ausgang.schrumpf`, kind-sensitive admission of every suffix of a body
(`bindFrischL_suffix`).
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {c : Fin u.fns.length}

/-! ## 1. The block reader -/

theorem lowSeqL_succ {l : Bool} (n : Nat) (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (pe : AtTop u c Λ) (ss : List UStmt) :
    lowSeqL (l := l) u c Γ fn (n + 1) Λ pe ss = lowSeqStep u c (lowStufe u c n) Γ fn Λ pe ss :=
  rfl

theorem lowSeqL_zero {l : Bool} (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (pe : AtTop u c Λ) (ss : List UStmt) :
    lowSeqL (l := l) u c Γ fn 0 Λ pe ss = .error "lower: blocks nested too deep" :=
  rfl

theorem lowStructL_zero {l : Bool} (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (pe : AtTop u c Λ) (s : UStmt) (ss : List UStmt) :
    lowStructL (l := l) u c Γ fn 0 Λ pe s ss = .error "lower: blocks nested too deep" :=
  rfl

theorem lowSeq_nil {n : Nat} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {pe : AtTop u c Λ} :
    lowSeqL (l := false) u c Γ fn (n + 1) Λ pe [] = .ok (⟨Λ, Block.nil⟩, []) :=
  rfl

theorem lowSeq_blkEnd {n : Nat} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {pe : AtTop u c Λ} {ss : List UStmt} :
    lowSeqL (l := false) u c Γ fn (n + 1) Λ pe (.blkEnd :: ss) =
      .ok (⟨Λ, Block.nil⟩, .blkEnd :: ss) :=
  rfl

theorem lowSeq_ifElse {n : Nat} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {pe : AtTop u c Λ} {ss : List UStmt} :
    lowSeqL (l := false) u c Γ fn (n + 1) Λ pe (.ifElse :: ss) =
      .ok (⟨Λ, Block.nil⟩, .ifElse :: ss) :=
  rfl

theorem lowSeq_bind_ok {n : Nat} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {pe : AtTop u c Λ} {x : String} {d : Option (Int × Int)} {v : USide} {ss rest : List UStmt}
    {p : Σ Λ' : List (Res (declOf u)), Block (declOf u) (verOf u c) false Γ Λ Λ'}
    (h : lowSeqL (l := false) u c Γ fn (n + 1) Λ pe (.bind x d v :: ss) = .ok (p, rest)) :
    ∃ (ls : LowSide u Γ Λ) (q : Σ Λ' : List (Res (declOf u)),
        Block (declOf u) (verOf u c) false (.int ls.range.1 ls.range.2 :: Γ) Λ Λ'),
      lowBindWert u Γ Λ fn d v = .ok ls ∧
      lowSeqL (l := false) u c (.int ls.range.1 ls.range.2 :: Γ) (fn.mitBindung x ls.range) n Λ pe
        ss = .ok (q, rest) ∧
      p = ⟨q.1, Block.bind ls.term q.2⟩ := by
  rw [lowSeqL_succ] at h
  simp only [lowSeqStep, lowStufe_seq] at h
  cases hls : lowBindWert u Γ Λ fn d v with
  | error e => simp only [hls, Except.bind] at h <;> cases h
  | ok ls =>
    simp only [hls, Except.bind] at h
    cases hq : lowSeqL (l := false) u c (.int ls.range.1 ls.range.2 :: Γ)
        (fn.mitBindung x ls.range) n Λ pe ss with
    | error e => simp only [hq] at h <;> cases h
    | ok res =>
      obtain ⟨⟨Λ', b⟩, r⟩ := res
      simp only [hq] at h
      cases h
      exact ⟨ls, ⟨Λ', b⟩, rfl, hq, rfl⟩

theorem lowSeq_bindMut_ok {n : Nat} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {pe : AtTop u c Λ} {x : String} {lo hi : Int} {v : USide} {ss rest : List UStmt}
    {p : Σ Λ' : List (Res (declOf u)), Block (declOf u) (verOf u c) false Γ Λ Λ'}
    (h : lowSeqL (l := false) u c Γ fn (n + 1) Λ pe (.bindMut x lo hi v :: ss) = .ok (p, rest)) :
    ∃ (ev : Expr (declOf u) Γ Λ (.int lo hi)) (q : Σ Λ' : List (Res (declOf u)),
        Block (declOf u) (verOf u c) false (.int lo hi :: Γ) Λ Λ'),
      lowWertAt u Γ Λ fn lo hi v = .ok ev ∧
      lowSeqL (l := false) u c (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) n Λ pe ss =
        .ok (q, rest) ∧
      p = ⟨q.1, Block.bind ev q.2⟩ := by
  rw [lowSeqL_succ] at h
  simp only [lowSeqStep, lowStufe_seq] at h
  cases hev : lowWertAt u Γ Λ fn lo hi v with
  | error e => simp only [hev, Except.bind] at h <;> cases h
  | ok ev =>
    simp only [hev, Except.bind] at h
    cases hq : lowSeqL (l := false) u c (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) n Λ pe ss with
    | error e => simp only [hq] at h <;> cases h
    | ok res =>
      obtain ⟨⟨Λ', b⟩, r⟩ := res
      simp only [hq] at h
      cases h
      exact ⟨ev, ⟨Λ', b⟩, rfl, rfl, rfl⟩

/-- The statements the block reader passes to `lowStmtL` (its last case). -/
theorem lowSeqStep_einzeln {l : Bool} (R : LowStufe u c) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (pe : AtTop u c Λ) (s : UStmt) (ss : List UStmt)
    (hs : LeseEinzeln s) :
    lowSeqStep (l := l) u c R Γ fn Λ pe (s :: ss) =
      (lowStmtL (l := l) u c Γ fn Λ s).bind fun ⟨Λ₁, st⟩ =>
        (R.seq (l := l) Γ fn Λ₁ pe ss).bind fun (⟨Λ₂, b⟩, r) => .ok (⟨Λ₂, Block.cons st b⟩, r) := by
  cases s
  case assign | assignTab | assignGlob | call | setVar => rfl
  all_goals simp [LeseEinzeln] at hs

theorem lowSeq_einzeln_ok {n : Nat} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {pe : AtTop u c Λ} {s : UStmt} {ss rest : List UStmt}
    {p : Σ Λ' : List (Res (declOf u)), Block (declOf u) (verOf u c) false Γ Λ Λ'}
    (h : lowSeqL (l := false) u c Γ fn (n + 1) Λ pe (s :: ss) = .ok (p, rest))
    (hs : LeseEinzeln s) :
    ∃ (Λ₁ : List (Res (declOf u))) (st : Stmt (declOf u) (verOf u c) false Γ Λ Λ₁)
      (q : Σ Λ' : List (Res (declOf u)), Block (declOf u) (verOf u c) false Γ Λ₁ Λ'),
      lowStmtL (l := false) u c Γ fn Λ s = .ok ⟨Λ₁, st⟩ ∧
      lowSeqL (l := false) u c Γ fn n Λ₁ pe ss = .ok (q, rest) ∧ p = ⟨q.1, Block.cons st q.2⟩ := by
  rw [lowSeqL_succ, lowSeqStep_einzeln _ _ _ _ _ _ _ hs] at h
  cases hst : lowStmtL (l := false) u c Γ fn Λ s with
  | error e => simp only [hst, Except.bind] at h <;> cases h
  | ok res =>
    obtain ⟨Λ₁, st⟩ := res
    simp only [hst, Except.bind, lowStufe_seq] at h
    cases hq : lowSeqL (l := false) u c Γ fn n Λ₁ pe ss with
    | error e => simp only [hq] at h <;> cases h
    | ok res2 =>
      obtain ⟨⟨Λ₂, b⟩, r⟩ := res2
      simp only [hq] at h
      cases h
      exact ⟨Λ₁, st, ⟨Λ₂, b⟩, rfl, hq, rfl⟩

theorem lowSeq_ret_ok {n : Nat} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {r0 : URet} {ss rest : List UStmt}
    {p : Σ Λ' : List (Res (declOf u)), Block (declOf u) (verOf u c) false Γ Λ Λ'}
    (h : lowSeqL (l := false) u c Γ fn (n + 1) Λ [] (.ret r0 :: ss) = .ok (p, rest)) :
    ∃ (st : Stmt (declOf u) (verOf u c) false Γ Λ Λ)
      (q : Σ Λ' : List (Res (declOf u)), Block (declOf u) (verOf u c) false Γ Λ Λ'),
      lowRetStmt (l := false) u c Γ fn Λ [] r0 = .ok st ∧
      lowSeqL (l := false) u c Γ fn n Λ [] ss = .ok (q, rest) ∧ p = ⟨q.1, Block.cons st q.2⟩ := by
  rw [lowSeqL_succ] at h
  simp only [lowSeqStep, lowStufe_seq] at h
  cases hst : lowRetStmt (l := false) u c Γ fn Λ [] r0 with
  | error e => simp only [hst, Except.bind] at h <;> cases h
  | ok st =>
    simp only [hst, Except.bind] at h
    cases hq : lowSeqL (l := false) u c Γ fn n Λ [] ss with
    | error e => simp only [hq] at h <;> cases h
    | ok res =>
      obtain ⟨⟨Λ', b⟩, r⟩ := res
      simp only [hq] at h
      cases h
      exact ⟨st, ⟨Λ', b⟩, rfl, rfl, rfl⟩

theorem lowSeq_wenn_ok {n : Nat} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {pe : AtTop u c Λ} {s : UStmt} {cnd : UEns} {ss rest : List UStmt}
    {p : Σ Λ' : List (Res (declOf u)), Block (declOf u) (verOf u c) false Γ Λ Λ'}
    (h : lowSeqL (l := false) u c Γ fn (n + 1) Λ pe (s :: ss) = .ok (p, rest))
    (hk : s = .ifBeg cnd ∨ s = .ifEnde cnd) :
    ∃ (Λ₁ : List (Res (declOf u))) (st : Stmt (declOf u) (verOf u c) false Γ Λ Λ₁)
      (rest' : List UStmt)
      (q : Σ Λ' : List (Res (declOf u)), Block (declOf u) (verOf u c) false Γ Λ₁ Λ'),
      lowStructL (l := false) u c Γ fn n Λ pe (.ifBeg cnd) ss = .ok (⟨Λ₁, st⟩, rest') ∧
      lowSeqL (l := false) u c Γ fn n Λ₁ pe rest' = .ok (q, rest) ∧
      p = ⟨q.1, Block.cons st q.2⟩ := by
  rcases hk with rfl | rfl
  all_goals
    rw [lowSeqL_succ] at h
    simp only [lowSeqStep, lowStufe_seq, lowStufe_struct] at h
    cases hst : lowStructL (l := false) u c Γ fn n Λ pe (.ifBeg cnd) ss with
    | error e => simp only [hst, Except.bind] at h <;> cases h
    | ok res =>
      obtain ⟨⟨Λ₁, st⟩, rest'⟩ := res
      simp only [hst, Except.bind] at h
      cases hq : lowSeqL (l := false) u c Γ fn n Λ₁ pe rest' with
      | error e => simp only [hq] at h <;> cases h
      | ok res2 =>
        obtain ⟨⟨Λ₂, b⟩, r⟩ := res2
        simp only [hq] at h
        cases h
        exact ⟨Λ₁, st, rest', ⟨Λ₂, b⟩, rfl, hq, rfl⟩

/-- **The conditional of a block**: the condition, the then-block up to `ifElse`, the else-block
    up to `blkEnd`, both ending at the same held marks, one fuel level below. -/
theorem lowStruct_ite_ok {n : Nat} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {pe : AtTop u c Λ} {cnd : UEns} {ss rest : List UStmt} {Λ₁ : List (Res (declOf u))}
    {st : Stmt (declOf u) (verOf u c) false Γ Λ Λ₁}
    (h : lowStructL (l := false) u c Γ fn (n + 1) Λ pe (.ifBeg cnd) ss = .ok (⟨Λ₁, st⟩, rest)) :
    ∃ (cv : Expr (declOf u) Γ Λ .bool) (tb eb : Block (declOf u) (verOf u c) false Γ Λ Λ₁)
      (rest1 : List UStmt),
      lowEns u Γ Λ fn none cnd = .ok cv ∧
      lowSeqL (l := false) u c Γ fn n Λ pe ss = .ok (⟨Λ₁, tb⟩, .ifElse :: rest1) ∧
      lowSeqL (l := false) u c Γ fn n Λ pe rest1 = .ok (⟨Λ₁, eb⟩, .blkEnd :: rest) ∧
      st = Stmt.ite cv tb eb := by
  rw [lowStructL_succ] at h
  simp only [lowStructStep, lowStufe_seq] at h
  cases hc : lowEns u Γ Λ fn none cnd with
  | error e => simp only [hc, Except.bind] at h <;> cases h
  | ok cv =>
    simp only [hc, Except.bind] at h
    split at h
    · cases h
    · rename_i Λa tb rest1 hT
      split at h
      · cases h
      · rename_i Λb eb rest2 hE
        split at h
        · rename_i hΛ
          subst hΛ
          cases h
          exact ⟨cv, tb, eb, rest1, rfl, hT, hE, rfl⟩
        · cases h
      · cases h
    · cases h

/-- **The conditional of a body**: the structured reader at `blockFuel`, the rest in the same
    scope. -/
theorem lowBodyF_ifBeg_ok {Γ : Ctx} {fn : UFn} {n : Nat} {Λ : List (Res (declOf u))}
    {cnd : UEns} {ss : List UStmt} {r : URet} {b0 : Endblock (declOf u) (verOf u c) false Γ Λ}
    (h : lowBodyF u c Γ fn (n + 1) Λ (.ifBeg cnd :: ss) r = .ok b0) :
    ∃ (Λ₁ : List (Res (declOf u))) (st : Stmt (declOf u) (verOf u c) false Γ Λ Λ₁)
      (rest : List UStmt) (e : Endblock (declOf u) (verOf u c) false Γ Λ₁),
      lowStructL (l := false) u c Γ fn blockFuel Λ [] (.ifBeg cnd) ss = .ok (⟨Λ₁, st⟩, rest) ∧
      lowBodyF u c Γ fn n Λ₁ rest r = .ok e ∧ b0 = Endblock.cons st e := by
  simp only [lowBodyF] at h
  split at h
  · cases h
  · rename_i Λ₁ st rest hS
    split at h
    · cases h
    · rename_i e he
      cases h
      exact ⟨Λ₁, st, rest, e, hS, he, rfl⟩

/-! ## 2. The G side of a block -/

section Gseite
variable {D : Deklaration} {V : Vertrag D} {Γ : Ctx} {Λ Λ₁ Λ' : List (Res D)}
variable (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

theorem execBlockZ_nil (σ : World D) (ρ : Env D Γ) :
    execBlock O passes R (Block.nil : Block D V false Γ Λ Λ) σ ρ = .ok σ ρ := by
  first
    | rfl
    | (simp only [execBlock]; done)

theorem execBlockZ_cons_ok (st : Stmt D V false Γ Λ Λ₁) (rest : Block D V false Γ Λ₁ Λ')
    {σ σ₁ : World D} {ρ ρ₁ : Env D Γ} (h : execStmt O passes R st σ ρ = .ok σ₁ ρ₁) :
    execBlock O passes R (Block.cons st rest) σ ρ = execBlock O passes R rest σ₁ ρ₁ := by
  simp only [execBlock, h]

theorem execBlockZ_cons_zurueck (st : Stmt D V false Γ Λ Λ₁) (rest : Block D V false Γ Λ₁ Λ')
    {σ σ' : World D} {ρ : Env D Γ} {v : ErgVal D V.erg}
    (h : execStmt O passes R st σ ρ = .zurueck σ' v) :
    execBlock O passes R (Block.cons st rest) σ ρ = .zurueck σ' v := by
  simp only [execBlock, h]

theorem execBlockZ_cons_logik (st : Stmt D V false Γ Λ Λ₁) (rest : Block D V false Γ Λ₁ Λ')
    {σ : World D} {ρ : Env D Γ} {e : Logik D} (h : execStmt O passes R st σ ρ = .logik e) :
    execBlock O passes R (Block.cons st rest) σ ρ = .logik e := by
  simp only [execBlock, h]

/-- A statement whose outcome is neither `ok`, `logik` nor `zurueck` ends the block with it. -/
theorem execBlockZ_cons_still (st : Stmt D V false Γ Λ Λ₁) (rest : Block D V false Γ Λ₁ Λ')
    {σ : World D} {ρ : Env D Γ}
    (h1 : ∀ σ₁ ρ₁, execStmt O passes R st σ ρ ≠ .ok σ₁ ρ₁) :
    execBlock O passes R (Block.cons st rest) σ ρ = execStmt O passes R st σ ρ := by
  cases hx : execStmt O passes R st σ ρ with
  | ok σ₁ ρ₁ => exact absurd hx (h1 σ₁ ρ₁)
  | _ => simp only [execBlock, hx]

theorem execBlockZ_bind {τ : Ty} (e : Expr D Γ Λ τ) (rest : Block D V false (τ :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) :
    execBlock O passes R (Block.bind e rest) σ ρ =
      (execBlock O passes R rest (σ.lese Λ e.orte)
        (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ)).schrumpf := by
  first
    | rfl
    | (simp only [execBlock]; done)

theorem execStmtZ_ite (cv : Expr D Γ Λ .bool) (tb eb : Block D V false Γ Λ Λ₁)
    (σ : World D) (ρ : Env D Γ) :
    execStmt O passes R (Stmt.ite cv tb eb) σ ρ =
      if wahr? (eval (σ.lese Λ cv.orte) cv (σ.lese Λ cv.orte) ρ) then
        execBlock O passes R tb (σ.lese Λ cv.orte) ρ
      else execBlock O passes R eb (σ.lese Λ cv.orte) ρ := by
  first
    | rfl
    | (simp only [execStmt]; done)

end Gseite

theorem schrumpfZ_ok {D : Deklaration} {V : Vertrag D} {Γ : Ctx} {τ : Ty}
    {a : Ausgang V false (τ :: Γ)} {σ' : World D} {ρ' : Env D Γ}
    (h : a.schrumpf = .ok σ' ρ') : ∃ ρ'' : Env D (τ :: Γ), a = .ok σ' ρ'' ∧ ρ' = ρ''.tail := by
  cases a with
  | ok σ ρ =>
    simp only [Ausgang.schrumpf, Ausgang.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ρ, rfl, rfl⟩
  | _ => simp only [Ausgang.schrumpf, reduceCtorEq] at h

theorem schrumpfZ_logik {D : Deklaration} {V : Vertrag D} {Γ : Ctx} {τ : Ty}
    {a : Ausgang V false (τ :: Γ)} {e : Logik D} (h : a.schrumpf = .logik e) : a = .logik e := by
  cases a with
  | logik e' =>
    simp only [Ausgang.schrumpf, Ausgang.logik.injEq] at h
    rw [h]
  | _ => simp only [Ausgang.schrumpf, reduceCtorEq] at h

theorem schrumpfZ_zurueck {D : Deklaration} {V : Vertrag D} {Γ : Ctx} {τ : Ty}
    {a : Ausgang V false (τ :: Γ)} {σ' : World D} {v : ErgVal D V.erg}
    (h : a.schrumpf = .zurueck σ' v) : a = .zurueck σ' v :=
  schrumpf_zurueck h

/-- Integer binders never add protected names; freshness is inherited by every suffix. -/
theorem bindFrischL_append : ∀ (pre : List UStmt) (ns : List String) (rest : List UStmt),
    BindFrischL ns (pre ++ rest) → BindFrischL ns rest
  | [], _, _, h => h
  | s :: pre, ns, rest, h => by
      cases hb : binderOf s with
      | none =>
        simp only [List.cons_append, BindFrischL, hb] at h
        exact bindFrischL_append pre ns rest h
      | some x =>
        simp only [List.cons_append, BindFrischL, hb] at h
        exact bindFrischL_append pre ns rest h.2

theorem bindFrischL_suffix {ns : List String} {ss rest : List UStmt} (h : BindFrischL ns ss)
    (hs : rest <:+ ss) : BindFrischL ns rest := by
  obtain ⟨pre, rfl⟩ := hs
  exact bindFrischL_append pre ns rest h

theorem mem_of_suffix {α : Type} {l₁ l₂ : List α} {a : α} (hs : l₁ <:+ l₂) (h : a ∈ l₁) :
    a ∈ l₂ := by
  obtain ⟨pre, rfl⟩ := hs
  exact List.mem_append_right pre h

end Gabbro.Bruecke
