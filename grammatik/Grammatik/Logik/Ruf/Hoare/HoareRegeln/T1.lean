/-
  File:      Grammatik/HoareRegeln.lean
  Subject:   SEQUENTIAL HOARE RULES OVER execBlock, blocks WITHOUT calls.

  `HTripel` is partial correctness over the actual sequential semantics:
  starting from any world/env where `Pre` holds, if the block ends normally
  (`.ok σ' ρ'`), then `Post` holds there. Contracts hold at their place
  with the actual values; pre/post are predicates over the actual world
  AND environment, never quantified over environments.

  `BlockOhneRuf` says a block performs no call: no `call`/`callInd` in any
  statement, no `bindCall`/`bindCallInd`/`bindCallElse`/`bindCallIndElse` in any block spine,
  and nested blocks preserve the property. Lemma `ohneRuf_Runabhaengig`
  proves the meaning: on such blocks `execBlock` is independent of the
  call-meaning parameter `R`.
-/
module
public import Grammatik.Logik.Ruf.Hoare.HoareRegeln.T1Basis
import all Grammatik.Logik.Ruf.Hoare.HoareRegeln.T1Basis
public import Grammatik.Kern.Semantik.Semantik
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}
/-! ## 2. The standard rules. -/

/-- Skip: the empty block preserves every assertion. -/
theorem hoare_skip (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (Pst : World D → Env D Γ → Prop) :
    HTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R .nil Pst Pst := by
  intro σ ρ hPre σ' ρ' hrun
  simp only [execBlock] at hrun
  cases hrun
  exact hPre

/-- Assignment to a local variable, backward (substitution) form: from a
    pre saying `Pst` will hold after the update, conclude `Pst` after. -/
theorem hoare_assignVar (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {τ : Ty} (x : Var Γ τ) (e : Expr D Γ Λ τ)
    (Pst : World D → Env D Γ → Prop) :
    STTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R (.assignVar x e)
      (fun σ ρ => Pst (σ.lese Λ e.orte) (ρ.set x (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)))
      (fun σ' ρ' => Pst σ' ρ') := by
  intro σ ρ hPre σ' ρ' hrun
  have hrun' : execStmt O passes R (.assignVar (V := V) (l := l) x e) σ ρ =
      Ausgang.ok σ' ρ' := hrun
  simp only [execStmt] at hrun'
  cases hrun'
  exact hPre

/-- Assignment to a local variable, forward form: after the update the
    environment equals the old one with `x` set to the old value of `e`. -/
theorem hoare_assignVar_fwd (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {τ : Ty} (x : Var Γ τ) (e : Expr D Γ Λ τ)
    (Pre : World D → Env D Γ → Prop) :
    STTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R (.assignVar x e) Pre
      (fun σ' ρ' => ∃ σ ρ, Pre σ ρ ∧
        σ' = σ.lese Λ e.orte ∧
        ρ' = ρ.set x (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) := by
  intro σ ρ hPre σ' ρ' hrun
  have hrun' : execStmt O passes R (.assignVar (V := V) (l := l) x e) σ ρ =
      Ausgang.ok σ' ρ' := hrun
  simp only [execStmt] at hrun'
  cases hrun'
  exact ⟨σ, ρ, hPre, rfl, rfl⟩

/-- Sequence: the statement ends normally in the mid assertion, the rest
    carries it to the post. `execBlock (.cons s rest)` performs no guard
    read between `s` and `rest`, so one mid assertion fits both sides. -/
theorem hoare_seq (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (s : Stmt D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'')
    (Pre Mid Pst : World D → Env D Γ → Prop)
    (hs : STTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R s Pre Mid)
    (hrest : HTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ') O passes R rest Mid Pst) :
    HTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R (.cons s rest) Pre Pst := by
  intro σ ρ hPre σ' ρ' hrun
  simp only [execBlock] at hrun
  cases hstep : execStmt O passes R s σ ρ with
  | ok σ1 ρ1 =>
      have hmid : Mid σ1 ρ1 := hs σ ρ hPre σ1 ρ1 hstep
      have hcont : execBlock O passes R rest σ1 ρ1 = Ausgang.ok σ' ρ' := by
        rw [hstep] at hrun
        exact hrun
      exact hrest σ1 ρ1 hmid σ' ρ' hcont
  | zurueck σ1 v => rw [hstep] at hrun; exact absurd hrun (by simp only [reduceCtorEq, not_false_eq_true])
  | why σ1 r => rw [hstep] at hrun; exact absurd hrun (by simp only [reduceCtorEq, not_false_eq_true])
  | leave h σ1 ρ1 => rw [hstep] at hrun; exact absurd hrun (by simp only [reduceCtorEq, not_false_eq_true])
  | next h σ1 ρ1 => rw [hstep] at hrun; exact absurd hrun (by simp only [reduceCtorEq, not_false_eq_true])
  | logik e => rw [hstep] at hrun; exact absurd hrun (by simp only [reduceCtorEq, not_false_eq_true])
  | hardware e => rw [hstep] at hrun; exact absurd hrun (by simp only [reduceCtorEq, not_false_eq_true])

/-- If-then-else: both branches satisfy the same triple. The branch
    condition reads its carriers first (`σ.lese`), so the branch
    hypotheses ask for the pre at the read world plus the actual
    condition value there. -/
theorem hoare_ite (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (c : Expr D Γ Λ .bool) (t e : Block D V l Γ Λ Λ')
    (Pre Pst : World D → Env D Γ → Prop)
    (ht : HTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R t
      (fun σ ρ => (∃ σ₀ ρ₀, Pre σ₀ ρ₀ ∧ σ = σ₀.lese Λ c.orte ∧ ρ = ρ₀) ∧
        wahr? (eval σ c σ ρ) = true) Pst)
    (he : HTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R e
      (fun σ ρ => (∃ σ₀ ρ₀, Pre σ₀ ρ₀ ∧ σ = σ₀.lese Λ c.orte ∧ ρ = ρ₀) ∧
        wahr? (eval σ c σ ρ) = false) Pst) :
    STTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R (.ite c t e)
      Pre Pst := by
  intro σ ρ hPre σ' ρ' hrun
  have hsplit : (let σr := σ.lese Λ c.orte
      if wahr? (eval σr c σr ρ) then execBlock O passes R t σr ρ
      else execBlock O passes R e σr ρ) = Ausgang.ok σ' ρ' := hrun
  cases hc : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) with
  | true =>
      have hmem : execBlock O passes R t (σ.lese Λ c.orte) ρ = Ausgang.ok σ' ρ' := by
        have := hsplit
        simp only [hc] at this
        exact this
      exact ht _ _ ⟨⟨σ, ρ, hPre, rfl, rfl⟩, hc⟩ _ _ hmem
  | false =>
      have hmem : execBlock O passes R e (σ.lese Λ c.orte) ρ = Ausgang.ok σ' ρ' := by
        have := hsplit
        simp only [hc] at this
        exact this
      exact he _ _ ⟨⟨σ, ρ, hPre, rfl, rfl⟩, hc⟩ _ _ hmem

/-- Consequence: strengthen the pre, weaken the post. -/
theorem hoare_konsequenz (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (b : Block D V l Γ Λ Λ')
    (Pre Pre' Pst Pst' : World D → Env D Γ → Prop)
    (h : HTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R b Pre' Pst')
    (hPre : ∀ σ ρ, Pre σ ρ → Pre' σ ρ)
    (hPst : ∀ σ ρ, Pst' σ ρ → Pst σ ρ) :
    HTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R b Pre Pst := by
  intro σ ρ hPR σ' ρ' hrun
  exact hPst σ' ρ' (h σ ρ (hPre σ ρ hPR) σ' ρ' hrun)

/-- Statement consequence: strengthen the pre, weaken the post. -/
theorem hoare_konsequenz_stmt (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (s : Stmt D V l Γ Λ Λ')
    (Pre Pre' Pst Pst' : World D → Env D Γ → Prop)
    (h : STTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R s Pre' Pst')
    (hPre : ∀ σ ρ, Pre σ ρ → Pre' σ ρ)
    (hPst : ∀ σ ρ, Pst' σ ρ → Pst σ ρ) :
    STTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R s Pre Pst := by
  intro σ ρ hPR σ' ρ' hrun
  exact hPst σ' ρ' (h σ ρ (hPre σ ρ hPR) σ' ρ' hrun)

/-! ## 3. Call-freedom means independence from the call meaning.

    On `BlockOhneRuf` blocks the executor never consults `R`: every case
    equation that mentions `R` is a call constructor, and those are absent.
    The statement version needs the block-level fact for `ite` branches
    (and the arms/lock/loop bodies), hence the mutual shape. -/


theorem armsOhneRuf_RunabhaengigAux {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {c : Option Ty} {cs' : List (Option Ty)}
    (b : Block D V l (ArmCtx Γ c) Λ Λ')
    (rest : Arms D V l Γ Λ Λ' cs')
    (hb : ∀ (σ : World D) (ρ : Env D _),
      execBlock O passes R₁ b σ ρ = execBlock O passes R₂ b σ ρ)
    (hr : ∀ (w : Wert D (.sum cs')) (σ : World D) (ρ : Env D Γ),
      execArms O passes R₁ rest w σ ρ = execArms O passes R₂ rest w σ ρ)
    (k : Nat) (hk : k < (c :: cs').length)
    (nutz : Nutzlast D.Fn D.passt ((c :: cs').get ⟨k, hk⟩))
    (σ : World D) (ρ : Env D Γ) :
    execArms O passes R₁ (Arms.cons b rest) ⟨⟨k, hk⟩, nutz⟩ σ ρ =
    execArms O passes R₂ (Arms.cons b rest) ⟨⟨k, hk⟩, nutz⟩ σ ρ := by
  cases k with
  | zero =>
      simp only [execArms, hb]
  | succ n =>
      have hk' : n < cs'.length := Nat.lt_of_succ_lt_succ hk
      have heq : (c :: cs').get ⟨n + 1, hk⟩ = cs'.get ⟨n, hk'⟩ := by
        simp only [List.get_cons_succ]
      have htail := hr ⟨⟨n, hk'⟩, heq ▸ nutz⟩ σ ρ
      simp only [execArms]
      exact htail


theorem grundArmsOhneRuf_RunabhaengigAux
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (blockEq : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (b : Block D V l Γ Λ Λ') (h : BlockOhneRuf b)
      (σ : World D) (ρ : Env D Γ),
      execBlock O passes R₁ b σ ρ = execBlock O passes R₂ b σ ρ)
    (σ : World D) (ρ : Env D Γ)
    {n' : Nat}
    (rest : GrundArms D V l Γ Λ Λ' n') (hr : GrundArmsOhneRuf rest)
    (k : Nat) (hk : k < n' + 1)
    (b : Block D V l Γ Λ Λ') (hb : BlockOhneRuf b) :
    execGrund O passes R₁ (GrundArms.cons b rest) ⟨k, hk⟩ σ ρ =
    execGrund O passes R₂ (GrundArms.cons b rest) ⟨k, hk⟩ σ ρ := by
  exact Nat.rec (motive := fun k => ∀ (n' : Nat)
      (rest : GrundArms D V l Γ Λ Λ' n') (hr : GrundArmsOhneRuf rest)
      (hk : k < n' + 1) (b : Block D V l Γ Λ Λ') (hb : BlockOhneRuf b),
      execGrund O passes R₁ (GrundArms.cons b rest) ⟨k, hk⟩ σ ρ =
      execGrund O passes R₂ (GrundArms.cons b rest) ⟨k, hk⟩ σ ρ)
    (fun n' rest hr hk b hb => by
      have hbeq := blockEq b hb σ ρ
      simp only [execGrund, hbeq])
    (fun n ih n' rest hr hk b hb => by
      have hk' : n < n' := Nat.lt_of_succ_lt_succ hk
      have hbeq := blockEq b hb σ ρ
      have hstep : execGrund O passes R₁ (GrundArms.cons b rest) ⟨n + 1, hk⟩ σ ρ =
          execGrund O passes R₁ rest ⟨n, hk'⟩ σ ρ := by
        simp only [execGrund]
      have hstep2 : execGrund O passes R₂ (GrundArms.cons b rest) ⟨n + 1, hk⟩ σ ρ =
          execGrund O passes R₂ rest ⟨n, hk'⟩ σ ρ := by
        simp only [execGrund]
      rw [hstep, hstep2]
      cases hr with
      | nil =>
          simp only [Nat.not_lt_zero] at hk'
      | cons _ _ hbTail hrTail =>
          exact ih _ _ hrTail hk' _ hbTail)
    k n' rest hr hk b hb

theorem grundArmsOhneRuf_Runabhaengig_end
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (blockEq : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (b : Block D V l Γ Λ Λ') (h : BlockOhneRuf b)
      (σ : World D) (ρ : Env D Γ),
      execBlock O passes R₁ b σ ρ = execBlock O passes R₂ b σ ρ)
    {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n) (h : GrundArmsOhneRuf arms)
    (r : Fin n) (σ : World D) (ρ : Env D Γ) :
    execGrund O passes R₁ arms r σ ρ = execGrund O passes R₂ arms r σ ρ := by
  cases h with
  | nil => exact r.elim0
  | cons b rest hb hr =>
      subst_vars
      cases r with
      | mk k hk =>
          exact grundArmsOhneRuf_RunabhaengigAux O passes R₁ R₂ blockEq σ ρ
            rest hr k hk b hb




