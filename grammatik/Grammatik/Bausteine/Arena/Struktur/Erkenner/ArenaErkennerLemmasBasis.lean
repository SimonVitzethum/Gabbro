/-
  File:      Grammatik/ArenaErkennerLemmas.lean
  Subject:   THE BOOKKEEPING of the recognizer's soundness proof (`ArenaErkennerBeweis.lean`): positions identify
             variables, the abstract state weakens, loses a binder, gains one, and changes the status of one variable
             (or of all members of one structure) soundly; the outcomes and the `else` branches that store nothing.
-/
module
public import Grammatik.Bausteine.Arena.Struktur.Erkenner.ArenaErkenner
public import Grammatik.Bausteine.Arena.Struktur.Formen.ArenaWachs
@[expose] public section


namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

variable {D : Deklaration}

/-! ## 1. Positions identify variables -/

theorem Var.pos_inj {Γ : Ctx} {τ : Ty} : ∀ (x y : Var Γ τ), x.pos = y.pos → x = y
  | .here, .here, _ => rfl
  | .here, .there _, h => by simp only [pos, Nat.right_eq_add, Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false] at h
  | .there _, .here, h => by simp only [pos, Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false] at h
  | .there x, .there y, h => by
      have := Var.pos_inj x y (by simpa [Var.pos] using h)
      rw [this]

/-! ## 2. The abstract state -/

theorem Abs.ext_null (a : Abs) (s : Status) : a.ext s 0 = s := by rfl

theorem Abs.ext_succ (a : Abs) (s : Status) (n : Nat) : a.ext s (n + 1) = a n := by rfl

theorem Abs.set_selbst (a : Abs) (m : Nat) (s : Status) : a.set m s m = s := by simp only [set, ↓reduceIte]

theorem Abs.set_anders (a : Abs) (m n : Nat) (s : Status) (h : n ≠ m) : a.set m s n = a n := by
  simp only [set, h, ↓reduceIte]

/-- What a status in `a.set m s` says: either the position is `m` and `s` is that status, or it is another position and
    `a` said so. -/
theorem Abs.set_eq {a : Abs} {m n : Nat} {s t : Status} (h : a.set m s n = t) :
    (n = m ∧ s = t) ∨ (n ≠ m ∧ a n = t) := by
  by_cases hn : n = m
  · rw [hn, Abs.set_selbst] at h; exact Or.inl ⟨hn, h⟩
  · rw [Abs.set_anders _ _ _ _ hn] at h; exact Or.inr ⟨hn, h⟩

/-- What a status in `a.forget s` says: a status other than `offen` is a status of `a` that is not the forgotten one. -/
theorem Abs.forget_eq {a : Abs} {s t : Status} {n : Nat} (h : a.forget s n = t) (ht : t ≠ .offen) :
    a n = t ∧ t ≠ s := by
  unfold Abs.forget at h
  by_cases e : a n = s
  · rw [if_pos e] at h; exact absurd h.symm ht
  · rw [if_neg e] at h; exact ⟨h, fun e' => e (h.trans e')⟩

theorem Abs.forget_schwacher (a : Abs) (s : Status) : Abs.Schwacher (a.forget s) a := by
  intro n
  unfold Abs.forget
  by_cases e : a n = s
  · exact Or.inr (if_pos e)
  · exact Or.inl (if_neg e)

/-! ## 3. What the abstract state means -/

section StrukturPasst
variable {A : FreiForm D} (K : Dekl A)

/-- The state loses a binder: what held for the longer context holds for the shorter one. -/
theorem StrukturPasst.tail {a : Abs} {τ : Ty} {Γ : Ctx} {σ : World D} {k : Wert D τ} {ρ : Env D Γ}
    (h : StrukturPasst K a σ (.cons k ρ)) : StrukturPasst K a.tail σ ρ :=
  ⟨fun x hx => h.1 (.there x) hx, fun x hx => h.2.1 (.there x) hx, fun x hx => h.2.2.1 (.there x) hx,
    fun x y hx hy hne => h.2.2.2 (.there x) (.there y) hx hy (by simpa [Var.pos] using hne)⟩

/-- A weaker state is met wherever a stronger one is. -/
theorem StrukturPasst.schwacher {a b : Abs} (hs : Abs.Schwacher b a) {Γ : Ctx} {σ : World D} {ρ : Env D Γ}
    (h : StrukturPasst K a σ ρ) : StrukturPasst K b σ ρ := by
  have key : ∀ (n : Nat) (s : Status), s ≠ .offen → b n = s → a n = s := by
    intro n s hne hb
    rcases hs n with e | e
    · rw [← e]; exact hb
    · rw [e] at hb; exact absurd hb.symm hne
  exact ⟨fun x hx => h.1 x (key _ _ (by decide) hx), fun x hx => h.2.1 x (key _ _ (by decide) hx),
    fun x hx => h.2.2.1 x (key _ _ (by decide) hx),
    fun x y hx hy hne => h.2.2.2 x y (key _ _ (by decide) hx) (key _ _ (by decide) hy) hne⟩

/-- A new binder with the status `offen` costs nothing, whatever it holds. -/
theorem StrukturPasst.ext_offen {a : Abs} {τ : Ty} {Γ : Ctx} {σ : World D} {k : Wert D τ} {ρ : Env D Γ}
    (h : StrukturPasst K a σ ρ) : StrukturPasst K (a.ext .offen) σ (.cons k ρ) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x y hx hy hne => ?_⟩
  · cases x with
    | here => exact absurd hx (by simp only [Abs.ext, Var.pos, reduceCtorEq, not_false_eq_true])
    | there y => exact h.1 y hx
  · cases x with
    | here => exact absurd hx (by simp only [Abs.ext, Var.pos, reduceCtorEq, not_false_eq_true])
    | there y => exact h.2.1 y hx
  · cases x with
    | here => exact absurd hx (by simp only [Abs.ext, Var.pos, reduceCtorEq, not_false_eq_true])
    | there y => exact h.2.2.1 y hx
  · cases x with
    | here => exact absurd hx (by simp only [Abs.ext, Var.pos, reduceCtorEq, not_false_eq_true])
    | there x' =>
      cases y with
      | here => exact absurd hy (by simp only [Abs.ext, Var.pos, reduceCtorEq, not_false_eq_true])
      | there y' => exact h.2.2.2 x' y' hx hy (by simpa [Var.pos] using hne)

/-- A new OWNED binder: it names a live slot in neither structure that differs from every owned slot. -/
theorem StrukturPasst.ext_frei {a : Abs} {Γ : Ctx} {σ : World D} {ρ : Env D Γ} (k : Wert D (Ty.index (D.count A.tab)))
    (hP : StrukturPasst K a σ ρ) (h1 : A.Lebt σ k.n) (h2 : ¬ K.InL σ k.n) (h2' : ¬ K.InB σ k.n)
    (h3 : ∀ y : Var Γ (Ty.index (D.count A.tab)), a y.pos = .frei → (ρ.get y).n ≠ k.n) :
    StrukturPasst K (a.ext .frei) σ (.cons k ρ) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x y hx hy hne => ?_⟩
  · cases x with
    | here => exact ⟨h1, h2, h2'⟩
    | there y => exact hP.1 y hx
  · cases x with
    | here => exact absurd hx (by simp only [Abs.ext, Var.pos, reduceCtorEq, not_false_eq_true])
    | there y => exact hP.2.1 y hx
  · cases x with
    | here => exact absurd hx (by simp only [Abs.ext, Var.pos, reduceCtorEq, not_false_eq_true])
    | there y => exact hP.2.2.1 y hx
  · cases x with
    | here =>
      cases y with
      | here => exact absurd rfl hne
      | there y' => exact fun e => h3 y' hy e.symm
    | there x' =>
      cases y with
      | here => exact fun e => h3 x' hx e
      | there y' => exact hP.2.2.2 x' y' hx hy (by simpa [Var.pos] using hne)

/-- A new LIST MEMBER binder. -/
theorem StrukturPasst.ext_liste {a : Abs} {Γ : Ctx} {σ : World D} {ρ : Env D Γ} (k : Wert D (Ty.index (D.count A.tab)))
    (hP : StrukturPasst K a σ ρ) (h1 : K.InL σ k.n) : StrukturPasst K (a.ext .liste) σ (.cons k ρ) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x y hx hy hne => ?_⟩
  · cases x with
    | here => exact absurd hx (by simp only [Abs.ext, Var.pos, reduceCtorEq, not_false_eq_true])
    | there y => exact hP.1 y hx
  · cases x with
    | here => exact h1
    | there y => exact hP.2.1 y hx
  · cases x with
    | here => exact absurd hx (by simp only [Abs.ext, Var.pos, reduceCtorEq, not_false_eq_true])
    | there y => exact hP.2.2.1 y hx
  · cases x with
    | here => exact absurd hx (by simp only [Abs.ext, Var.pos, reduceCtorEq, not_false_eq_true])
    | there x' =>
      cases y with
      | here => exact absurd hy (by simp only [Abs.ext, Var.pos, reduceCtorEq, not_false_eq_true])
      | there y' => exact hP.2.2.2 x' y' hx hy (by simpa [Var.pos] using hne)

/-- A new TREE MEMBER binder. -/
theorem StrukturPasst.ext_baum {a : Abs} {Γ : Ctx} {σ : World D} {ρ : Env D Γ} (k : Wert D (Ty.index (D.count A.tab)))
    (hP : StrukturPasst K a σ ρ) (h1 : K.InB σ k.n) : StrukturPasst K (a.ext .baum) σ (.cons k ρ) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x y hx hy hne => ?_⟩
  · cases x with
    | here => exact absurd hx (by simp only [Abs.ext, Var.pos, reduceCtorEq, not_false_eq_true])
    | there y => exact hP.1 y hx
  · cases x with
    | here => exact absurd hx (by simp only [Abs.ext, Var.pos, reduceCtorEq, not_false_eq_true])
    | there y => exact hP.2.1 y hx
  · cases x with
    | here => exact h1
    | there y => exact hP.2.2.1 y hx
  · cases x with
    | here => exact absurd hx (by simp only [Abs.ext, Var.pos, reduceCtorEq, not_false_eq_true])
    | there x' =>
      cases y with
      | here => exact absurd hy (by simp only [Abs.ext, Var.pos, reduceCtorEq, not_false_eq_true])
      | there y' => exact hP.2.2.2 x' y' hx hy (by simpa [Var.pos] using hne)

/-- **The status of some variables changes, the world moves.** The caller supplies the facts of the new state in the new
    world; what is `frei` afterwards was `frei` before, so two owned slots stay two slots. -/
theorem StrukturPasst.wechsel {a : Abs} {a' : Abs} {Γ : Ctx} {σ σ' : World D} {ρ : Env D Γ} (hP : StrukturPasst K a σ ρ)
    (hF : ∀ x : Var Γ (Ty.index (D.count A.tab)), a' x.pos = .frei → a x.pos = .frei ∧
      A.Lebt σ' (ρ.get x).n ∧ ¬ K.InL σ' (ρ.get x).n ∧ ¬ K.InB σ' (ρ.get x).n)
    (hL : ∀ x : Var Γ (Ty.index (D.count A.tab)), a' x.pos = .liste → K.InL σ' (ρ.get x).n)
    (hB : ∀ x : Var Γ (Ty.index (D.count A.tab)), a' x.pos = .baum → K.InB σ' (ρ.get x).n) :
    StrukturPasst K a' σ' ρ :=
  ⟨fun x hx => (hF x hx).2, hL, hB,
    fun x y hx hy hne => hP.2.2.2 x y (hF x hx).1 (hF y hy).1 hne⟩

/-- Recording a read changes no liveness. -/
theorem FreiForm.lebt_lese (A : FreiForm D) (σ : World D) (Λ : List (Res D)) (o : List (D.Tab ⊕ D.Glob)) (j : Int) :
    A.Lebt (σ.lese Λ o) j ↔ A.Lebt σ j :=
  FreiForm.lebt_gleich A (σ := σ) (σ' := σ.lese Λ o) rfl (fun _ => rfl) rfl j

theorem FreiForm.freiOk_lese (A : FreiForm D) (σ : World D) (Λ : List (Res D)) (o : List (D.Tab ⊕ D.Glob))
    (h : A.FreiOk σ) : A.FreiOk (σ.lese Λ o) :=
  FreiForm.freiOk_gleich A (σ := σ) (σ' := σ.lese Λ o) rfl (fun _ => rfl) rfl h

/-- A run that moves no word either structure reads, and keeps every live slot live, keeps the abstract state. -/
theorem StrukturPasst.gleich {σ σ' : World D} (hL : Dekl.GlL K σ σ') (hB : Dekl.GlB K σ σ')
    (hmono : ∀ j, A.Lebt σ j → A.Lebt σ' j) {a : Abs} {Γ : Ctx} {ρ : Env D Γ} (hp : StrukturPasst K a σ ρ) :
    StrukturPasst K a σ' ρ :=
  ⟨fun x hx => ⟨hmono _ (hp.1 x hx).1, fun hm => (hp.1 x hx).2.1 ((hL.inL _).mp hm),
      fun hm => (hp.1 x hx).2.2 ((hB.inB _).mp hm)⟩,
    fun x hx => (hL.inL _).mpr (hp.2.1 x hx), fun x hx => (hB.inB _).mpr (hp.2.2.1 x hx), hp.2.2.2⟩

/-- A recorded read keeps the state. -/
theorem StrukturPasst.lese {a : Abs} {Γ : Ctx} {σ : World D} {ρ : Env D Γ} (Λ : List (Res D))
    (o : List (D.Tab ⊕ D.Glob)) (hp : StrukturPasst K a σ ρ) : StrukturPasst K a (σ.lese Λ o) ρ :=
  StrukturPasst.gleich K (Dekl.GlL.lese σ Λ o) (Dekl.GlB.lese σ Λ o) (fun j h => (FreiForm.lebt_lese A σ Λ o j).mpr h) hp

/-- A recorded read keeps the invariant. -/
theorem Dekl.Ok.lese {σ : World D} (Λ : List (Res D)) (o : List (D.Tab ⊕ D.Glob)) (h : K.Ok σ) :
    K.Ok (σ.lese Λ o) :=
  Dekl.Ok.gleich (Dekl.GlL.lese σ Λ o) (Dekl.GlB.lese σ Λ o) (A.freiOk_lese σ Λ o h.1)
    (fun j hj => (FreiForm.lebt_lese A σ Λ o j).mpr (by
      rcases hj with hj | hj
      · exact Dekl.InL.lebt h.2.1 hj
      · exact Dekl.InB.lebt h.2.2.1 hj)) h

end StrukturPasst


end Gabbro.Grammatik
