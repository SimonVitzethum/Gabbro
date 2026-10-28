/-
  File:      Grammatik/ArenaErkennerLemmas.lean
  Subject:   THE BOOKKEEPING of the recognizer's soundness proof (`ArenaErkennerBeweis.lean`): positions identify
             variables, the abstract state weakens, loses a binder, gains one, and changes the status of one variable
             (or of all members of one structure) soundly; the outcomes and the `else` branches that store nothing.
-/
import Grammatik.Bausteine.Arena.Struktur.Erkenner.ArenaErkenner
import Grammatik.Bausteine.Arena.Struktur.Formen.ArenaWachs

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

theorem Abs.ext_null (a : Abs) (s : Status) : a.ext s 0 = s := rfl

theorem Abs.ext_succ (a : Abs) (s : Status) (n : Nat) : a.ext s (n + 1) = a n := rfl

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

/-! ## 3b. Runs that move none of the words the arena reads -/

section Gleich
variable {A : FreiForm D} (K : Dekl A)

/-- **`σ'` has the same free-list head, free links, counter and structure words as `σ`.** Nothing the arena invariant,
    the liveness or the abstract state reads has moved. -/
structure Dekl.Gleich (σ σ' : World D) : Prop where
  kopf : A.kopfSt σ' = A.kopfSt σ
  nxt : ∀ j, A.naechst σ' j = A.naechst σ j
  stand : A.stand σ' = A.stand σ
  l : Dekl.GlL K σ σ'
  b : Dekl.GlB K σ σ'

variable {K}

theorem Dekl.Gleich.lese (σ : World D) (Λ : List (Res D)) (o : List (D.Tab ⊕ D.Glob)) :
    Dekl.Gleich K σ (σ.lese Λ o) :=
  ⟨rfl, fun _ => rfl, rfl, Dekl.GlL.lese σ Λ o, Dekl.GlB.lese σ Λ o⟩

/-- A store into the PAYLOAD field moves none of them. -/
theorem Dekl.Gleich.nutzlast (σ : World D) (Λ : List (Res D)) (i : Int) (v : Wert D (D.typ A.tab A.feld)) :
    Dekl.Gleich K σ (σ.schreibSlot A.tab Λ i A.feld v) :=
  ⟨rfl, fun j => A.naechst_schreibSlot_feld σ Λ i j v, rfl, Dekl.GlL.nutzlast σ Λ i v, Dekl.GlB.nutzlast σ Λ i v⟩

theorem Dekl.Gleich.trans {σ σ' σ'' : World D} (h : Dekl.Gleich K σ σ') (h' : Dekl.Gleich K σ' σ'') :
    Dekl.Gleich K σ σ'' :=
  ⟨h'.kopf.trans h.kopf, fun j => (h'.nxt j).trans (h.nxt j), h'.stand.trans h.stand, h.l.trans h'.l,
    h.b.trans h'.b⟩

theorem Dekl.Gleich.lebt {σ σ' : World D} (h : Dekl.Gleich K σ σ') (j : Int) : A.Lebt σ' j ↔ A.Lebt σ j :=
  A.lebt_gleich h.kopf h.nxt h.stand j

theorem Dekl.Gleich.ok {σ σ' : World D} (h : Dekl.Gleich K σ σ') (hs : K.Ok σ) : K.Ok σ' :=
  Dekl.Ok.gleich h.l h.b (A.freiOk_gleich h.kopf h.nxt h.stand hs.1)
    (fun j hj => (h.lebt j).mpr (by
      rcases hj with hj | hj
      · exact Dekl.InL.lebt hs.2.1 hj
      · exact Dekl.InB.lebt hs.2.2.1 hj)) hs

theorem Dekl.Gleich.passt {σ σ' : World D} (h : Dekl.Gleich K σ σ') {a : Abs} {Γ : Ctx} {ρ : Env D Γ}
    (hp : StrukturPasst K a σ ρ) : StrukturPasst K a σ' ρ :=
  StrukturPasst.gleich K h.l h.b (fun j hj => (h.lebt j).mpr hj) hp

/-- **A commit moves the committed word and nothing the arena reads.** -/
theorem Dekl.Gleich.wachs (A : FreiForm D) (K : Dekl A) (n : Int) (Λ : List (Res D)) (σ : World D)
    (h0 : 0 ≤ A.komSt σ + n) (h : A.komSt σ + n ≤ D.count A.tab) :
    Dekl.Gleich K σ (nachGrow A.toDynForm n Λ σ h0 h) := by
  obtain ⟨hg, hs⟩ := nachGrow_rahmen A.toDynForm n Λ σ h0 h
  refine ⟨?_, fun j => ?_, ?_, ⟨fun d _ => ⟨fun j => ?_, ?_⟩⟩, ⟨fun b _ => ⟨fun j => ?_, fun j => ?_, ?_⟩⟩⟩
  · exact congrArg (fun w => (Wert.umTyp A.hkopf w).n) (hg A.kopf A.hk2)
  · simp only [FreiForm.naechst, hs]
  · exact congrArg (fun w => (Wert.umTyp A.hz w).n) (hg A.zaehl (Ne.symm A.hzwei))
  · simp only [LinkFeld.wert, hs]
  · exact congrArg (fun w => (Wert.umTyp ‹ListDekl A›.G.hg w).n) (hg _ ‹ListDekl A›.G.h3)
  · simp only [LinkFeld.wert, hs]
  · simp only [LinkFeld.wert, hs]
  · exact congrArg (fun w => (Wert.umTyp ‹BaumDekl A›.Wz.hg w).n) (hg _ ‹BaumDekl A›.Wz.h3)

end Gleich

/-! ## 4. The three ways the structure breaks (the model's reading of why `N586` refuses) -/

/-- A free list whose head links to itself has no finite chain. -/
theorem FreiForm.schleife_bricht (A : FreiForm D) (σ : World D) (i : Int) (hi : i < D.count A.tab)
    (hk : A.kopfSt σ = i) (hn : A.naechst σ i = i) : ¬ A.FreiOk σ := by
  have key : ∀ (k : Int) (Ls : List Int), FreiForm.Kette A σ k Ls → k = i → False := by
    intro k Ls h
    induction h with
    | nil => intro e; omega
    | cons k0 _ _ L _ ih => intro e; subst e; exact ih hn
  rintro ⟨Ls, hK, -, -⟩
  rw [hk] at hK
  exact key i Ls hK rfl

/-- The head of a non-empty free list is on it. -/
theorem FreiForm.aufListe_kopf (A : FreiForm D) {σ : World D} (hok : A.FreiOk σ) (hne : A.kopfSt σ < D.count A.tab) :
    A.AufListe σ (A.kopfSt σ) := by
  obtain ⟨L0, hk0, -, -⟩ := hok
  generalize hg : A.kopfSt σ = kk at hk0 hne ⊢
  cases hk0 with
  | nil => exact absurd hne (Int.lt_irrefl _)
  | cons k h0 hk1 L1 h1 =>
    refine ⟨kk :: L1, ?_, List.mem_cons_self⟩
    rw [hg]; exact FreiForm.Kette.cons kk h0 hk1 L1 h1

/-- A list whose head links to itself has no finite chain: **a slot linked twice** (the double push). -/
theorem liste_schleife_bricht (A : FreiForm D) (L : LinkFeld A) (G : LinkKopf A) (σ : World D) (i : Int)
    (hi : i < D.count A.tab) (hg : G.st σ = i) (hn : L.wert σ i = i) : ¬ ListOk A L G σ := by
  rintro ⟨Ls, hK, -, -⟩
  rw [hg] at hK
  have h0 : 0 ≤ i := hg ▸ (Wert.umTyp G.hg (σ.globs G.g)).lo_le
  exact push_doppelt_bricht h0 hi hn ⟨Ls, hK⟩

/-- A list whose head is also on the free list is not well formed: **a released slot linked in** (use after release). -/
theorem liste_freigegeben_bricht (A : FreiForm D) (L : LinkFeld A) (G : LinkKopf A) (σ : World D)
    (hne : G.st σ < D.count A.tab) (hauf : A.AufListe σ (G.st σ)) : ¬ ListOk A L G σ := by
  intro h
  have := h.lebt_auf (auf_kopf hne (by obtain ⟨Ls, hK, -, -⟩ := h; exact ⟨Ls, hK⟩))
  exact this.2.2 hauf

/-- A tree whose root links to itself has no finite shape: **a slot hung below itself** (hanging a member again). -/
theorem baum_schleife_bricht (A : FreiForm D) (Lf Rf : LinkFeld A) (Wz : LinkKopf A) (σ : World D) (i : Int)
    (hi : i < D.count A.tab) (hg : Wz.st σ = i) (hn : Lf.wert σ i = i) : ¬ BaumOk A Lf Rf Wz σ := by
  rintro ⟨S, hS, -, -⟩
  rw [hg] at hS
  exact einfuegen_doppelt_bricht hi hn ⟨S, hS⟩

/-- A tree whose root links to itself at the RIGHT has no finite shape (the mirror of `baum_schleife_bricht`). -/
theorem baum_schleife_rechts_bricht (A : FreiForm D) (Lf Rf : LinkFeld A) (Wz : LinkKopf A) (σ : World D) (i : Int)
    (hi : i < D.count A.tab) (hg : Wz.st σ = i) (hn : Rf.wert σ i = i) : ¬ BaumOk A Lf Rf Wz σ :=
  fun h => baum_schleife_bricht A Rf Lf Wz σ i hi hg hn (BaumOkF.spiegel h)

/-- **A slot hung at BOTH places of its parent is no tree:** the slot would occur twice in the shape. -/
theorem baum_doppelkind_bricht (A : FreiForm D) (Lf Rf : LinkFeld A) (Wz : LinkKopf A) (σ : World D) (w i : Int)
    (hw : w < D.count A.tab) (hg : Wz.st σ = w) (h1 : Lf.wert σ w = i) (h2 : Rf.wert σ w = i)
    (hi : i < D.count A.tab) (hl : Lf.wert σ i = D.count A.tab) (hr : Rf.wert σ i = D.count A.tab) :
    ¬ BaumOk A Lf Rf Wz σ := by
  rintro ⟨S, hS, hnd, -⟩
  rw [hg] at hS
  cases hS with
  | nil => exact absurd hw (Int.lt_irrefl _)
  | node _ _ _ S1 S2 hS1 hS2 =>
    rw [h1] at hS1
    rw [h2] at hS2
    have key : ∀ T : List Int, BaumF (D.count A.tab) (Lf.wert σ) (Rf.wert σ) i T → T = [i] := by
      intro T hT
      cases hT with
      | nil => exact absurd hi (Int.lt_irrefl _)
      | node _ _ _ T1 T2 hT1 hT2 =>
        rw [hl] at hT1
        rw [hr] at hT2
        rw [hT1.leer, hT2.leer]
        rfl
    rw [key S1 hS1, key S2 hS2] at hnd
    simp only [List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
  or_self, not_true_eq_false, not_false_eq_true, List.nodup_nil, and_self, and_true, and_false] at hnd

/-- A tree with a released slot as its root is not well formed: **use after release** in the tree. -/
theorem baum_freigegeben_bricht (A : FreiForm D) (Lf Rf : LinkFeld A) (Wz : LinkKopf A) (σ : World D)
    (hne : Wz.st σ < D.count A.tab) (hauf : A.AufListe σ (Wz.st σ)) : ¬ BaumOk A Lf Rf Wz σ := by
  intro h
  exact (BaumOkF.lebt_in h (InBaum.wurzel h hne)).2.2 hauf

/-! ## 5. The outcomes -/

section StrukturPost
variable {A : FreiForm D} (K : Dekl A) {V : Vertrag D} {l : Bool}

/-- A shorter context: the outcome of a sub-block is read in the outer context. -/
theorem StrukturPost.schrumpf {a : Abs} {τ : Ty} {Γ : Ctx} {o : Ausgang V l (τ :: Γ)}
    (h : StrukturPost K a o) : StrukturPost K a.tail o.schrumpf := by
  cases o with
  | ok σ ρ' =>
    cases ρ' with
    | cons k ρ => exact ⟨h.1, StrukturPasst.tail K h.2⟩
  | zurueck σ v => exact h
  | why σ r => exact h
  | leave hh σ ρ' => exact h
  | next hh σ ρ' => exact h
  | logik e => trivial
  | hardware e => trivial

/-- A weaker state is promised wherever a stronger one is. -/
theorem StrukturPost.schwacher {a b : Abs} (hs : Abs.Schwacher b a) {Γ : Ctx} {o : Ausgang V l Γ}
    (h : StrukturPost K a o) : StrukturPost K b o := by
  cases o with
  | ok σ ρ => exact ⟨h.1, StrukturPasst.schwacher K hs h.2⟩
  | zurueck σ v => exact h
  | why σ r => exact h
  | leave hh σ ρ' => exact h
  | next hh σ ρ' => exact h
  | logik e => trivial
  | hardware e => trivial

/-- **A statement followed by a block:** if the statement's outcome meets `a`, and every continuation from `a` meets
    `a'`, the sequence meets `a'`. -/
theorem StrukturPost.cons_stmt (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {a a' : Abs} {Γ : Ctx} {Λ Λ1 Λ' : List (Res D)}
    {s : Stmt D V l Γ Λ Λ1} {rest : Block D V l Γ Λ1 Λ'} {σ : World D} {ρ : Env D Γ}
    (hp : StrukturPost K a (execStmt O passes R s σ ρ))
    (ihr : ∀ (σ : World D) (ρ : Env D Γ), K.Ok σ → StrukturPasst K a σ ρ →
      StrukturPost K a' (execBlock O passes R rest σ ρ)) :
    StrukturPost K a' (execBlock O passes R (.cons s rest) σ ρ) := by
  simp only [execBlock]
  generalize execStmt O passes R s σ ρ = o at hp ⊢
  cases o with
  | ok σ' ρ' => exact ihr σ' ρ' hp.1 hp.2
  | zurueck σ' v => exact hp
  | why σ' r => exact hp
  | leave hh σ' ρ' => exact hp
  | next hh σ' ρ' => exact hp
  | logik e => trivial
  | hardware e => trivial

/-- **An `else` branch that stores nothing ends the run with the invariant intact.** -/
theorem Rein.post (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {a : Abs} {Γ : Ctx} {Λ : List (Res D)}
    {voll : Endblock D V l Γ Λ} (hv : Rein voll) (σ : World D) (ρ : Env D Γ) (h : K.Ok σ) :
    StrukturPost K a (execEnd O passes R voll σ ρ).zuAusgang := by
  cases hv with
  | ret e hΛ => exact Dekl.Ok.lese K Λ _ h
  | retWhy r hΛ => exact h

/-- **The shape of a case of the soundness proof:** from every world and environment that meet the state, the run of the
    block ends as the state promises. -/
def Folgt (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (a : Abs) {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (a' : Abs) : Prop :=
  ∀ (σ : World D) (ρ : Env D Γ), K.Ok σ → StrukturPasst K a σ ρ → StrukturPost K a' (execBlock O passes R b σ ρ)

/-- A slot at or above the counter is in neither structure (every member is live, below the counter). -/
theorem Dekl.nicht_in_stand {σ : World D} (hS : K.Ok σ) {j : Int} (hj : A.stand σ ≤ j) :
    ¬ K.InL σ j ∧ ¬ K.InB σ j :=
  ⟨fun h => by have := (Dekl.InL.lebt hS.2.1 h).2.1; omega,
   fun h => by have := (Dekl.InB.lebt hS.2.2.1 h).2.1; omega⟩

/-- A slot on the free list is in neither structure (every member is live). -/
theorem Dekl.nicht_in_frei {σ : World D} (hS : K.Ok σ) {j : Int} (hj : A.AufListe σ j) :
    ¬ K.InL σ j ∧ ¬ K.InB σ j :=
  ⟨fun h => (Dekl.InL.lebt hS.2.1 h).2.2 hj, fun h => (Dekl.InB.lebt hS.2.2.1 h).2.2 hj⟩

end StrukturPost

end Gabbro.Grammatik
