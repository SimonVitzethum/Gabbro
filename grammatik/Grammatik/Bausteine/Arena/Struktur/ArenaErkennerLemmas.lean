/-
  File:      Grammatik/ArenaErkennerLemmas.lean
  Subject:   THE BOOKKEEPING of the recognizer's soundness proof (`ArenaErkennerBeweis.lean`): positions identify
             variables, the abstract state weakens and loses a binder soundly, a run that changes none of the five
             quantities the structures read (`Gleich`) keeps the invariant and the abstract state, an `else` branch
             that stores nothing keeps the invariant, and the list survives a run that only touched the allocator's
             places.
-/
import Grammatik.Bausteine.Arena.Struktur.ArenaErkenner

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

variable {D : Deklaration}

/-! ## 1. Positions identify variables -/

theorem Var.pos_inj {Γ : Ctx} {τ : Ty} : ∀ (x y : Var Γ τ), x.pos = y.pos → x = y
  | .here, .here, _ => rfl
  | .here, .there _, h => by simp [Var.pos] at h
  | .there _, .here, h => by simp [Var.pos] at h
  | .there x, .there y, h => by
      have := Var.pos_inj x y (by simpa [Var.pos] using h)
      rw [this]

/-! ## 2. The abstract state -/

theorem Abs.ext_null (a : Abs) (s : Status) : a.ext s 0 = s := rfl

theorem Abs.ext_succ (a : Abs) (s : Status) (n : Nat) : a.ext s (n + 1) = a n := rfl

theorem Abs.set_selbst (a : Abs) (m : Nat) (s : Status) : a.set m s m = s := by simp [Abs.set]

theorem Abs.set_anders (a : Abs) (m n : Nat) (s : Status) (h : n ≠ m) : a.set m s n = a n := by
  simp [Abs.set, h]

theorem Abs.entglied_ne_glied (a : Abs) (n : Nat) : a.entglied n ≠ .glied := by
  unfold Abs.entglied; split <;> simp_all

theorem Abs.entglied_frei (a : Abs) (n : Nat) : a.entglied n = .frei ↔ a n = .frei := by
  unfold Abs.entglied; split <;> simp_all

theorem Abs.set_frei {a : Abs} {m n : Nat} {s : Status} (h : a.set m s n = .frei) (hs : s ≠ .frei) :
    n ≠ m ∧ a n = .frei := by
  by_cases hn : n = m
  · rw [hn, Abs.set_selbst] at h; exact absurd h hs
  · rw [Abs.set_anders _ _ _ _ hn] at h; exact ⟨hn, h⟩

theorem Abs.set_glied {a : Abs} {m n : Nat} {s : Status} (h : a.set m s n = .glied) :
    (n = m ∧ s = .glied) ∨ (n ≠ m ∧ a n = .glied) := by
  by_cases hn : n = m
  · rw [hn, Abs.set_selbst] at h; exact Or.inl ⟨hn, h⟩
  · rw [Abs.set_anders _ _ _ _ hn] at h; exact Or.inr ⟨hn, h⟩

/-! ## 3. What the abstract state means -/

section Passt
variable (A : FreiForm D) (L : LinkFeld A) (G : LinkKopf A)

/-- The state loses a binder: what held for the longer context holds for the shorter one. -/
theorem Passt.tail {a : Abs} {τ : Ty} {Γ : Ctx} {σ : World D} {k : Wert D τ} {ρ : Env D Γ}
    (h : Passt A L G a σ (.cons k ρ)) : Passt A L G a.tail σ ρ :=
  ⟨fun x hx => h.1 (.there x) hx, fun x hx => h.2.1 (.there x) hx,
    fun x y hx hy hne => h.2.2 (.there x) (.there y) hx hy (by simpa [Var.pos] using hne)⟩

/-- A weaker state is met wherever a stronger one is. -/
theorem Passt.schwacher {a b : Abs} (hs : Abs.Schwacher b a) {Γ : Ctx} {σ : World D} {ρ : Env D Γ}
    (h : Passt A L G a σ ρ) : Passt A L G b σ ρ := by
  have key : ∀ (n : Nat) (s : Status), s ≠ .offen → b n = s → a n = s := by
    intro n s hne hb
    rcases hs n with e | e
    · rw [← e]; exact hb
    · rw [e] at hb; exact absurd hb.symm hne
  exact ⟨fun x hx => h.1 x (key _ _ (by decide) hx), fun x hx => h.2.1 x (key _ _ (by decide) hx),
    fun x y hx hy hne => h.2.2 x y (key _ _ (by decide) hx) (key _ _ (by decide) hy) hne⟩

/-- A new binder with the status `offen` costs nothing, whatever it holds (a commit's new committed word). -/
theorem Passt.ext_offen {a : Abs} {τ : Ty} {Γ : Ctx} {σ : World D} {k : Wert D τ} {ρ : Env D Γ}
    (h : Passt A L G a σ ρ) : Passt A L G (a.ext .offen) σ (.cons k ρ) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x y hx hy hne => ?_⟩
  · cases x with
    | here => exact absurd hx (by simp [Var.pos, Abs.ext])
    | there y => exact h.1 y hx
  · cases x with
    | here => exact absurd hx (by simp [Var.pos, Abs.ext])
    | there y => exact h.2.1 y hx
  · cases x with
    | here => exact absurd hx (by simp [Var.pos, Abs.ext])
    | there x' =>
      cases y with
      | here => exact absurd hy (by simp [Var.pos, Abs.ext])
      | there y' => exact h.2.2 x' y' hx hy (by simpa [Var.pos] using hne)

/-- A new OWNED binder: it names a live, unlinked slot that differs from every owned slot. -/
theorem Passt.ext_frei {a : Abs} {Γ : Ctx} {σ : World D} {ρ : Env D Γ} (k : Wert D (Ty.index (D.count A.tab)))
    (hP : Passt A L G a σ ρ) (h1 : A.Lebt σ k.n) (h2 : ¬ Auf (D.count A.tab) (L.wert σ) (G.st σ) k.n)
    (h3 : ∀ y : Var Γ (Ty.index (D.count A.tab)), a y.pos = .frei → (ρ.get y).n ≠ k.n) :
    Passt A L G (a.ext .frei) σ (.cons k ρ) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x y hx hy hne => ?_⟩
  · cases x with
    | here => exact ⟨h1, h2⟩
    | there y => exact hP.1 y hx
  · cases x with
    | here => exact absurd hx (by simp [Var.pos, Abs.ext])
    | there y => exact hP.2.1 y hx
  · cases x with
    | here =>
      cases y with
      | here => exact absurd rfl hne
      | there y' => exact fun e => h3 y' hy e.symm
    | there x' =>
      cases y with
      | here => exact fun e => h3 x' hx e
      | there y' => exact hP.2.2 x' y' hx hy (by simpa [Var.pos] using hne)

/-- A new MEMBER binder. -/
theorem Passt.ext_glied {a : Abs} {Γ : Ctx} {σ : World D} {ρ : Env D Γ} (k : Wert D (Ty.index (D.count A.tab)))
    (hP : Passt A L G a σ ρ) (h1 : Auf (D.count A.tab) (L.wert σ) (G.st σ) k.n) :
    Passt A L G (a.ext .glied) σ (.cons k ρ) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x y hx hy hne => ?_⟩
  · cases x with
    | here => exact absurd hx (by simp [Var.pos, Abs.ext])
    | there y => exact hP.1 y hx
  · cases x with
    | here => exact h1
    | there y => exact hP.2.1 y hx
  · cases x with
    | here => exact absurd hx (by simp [Var.pos, Abs.ext])
    | there x' =>
      cases y with
      | here => exact absurd hy (by simp [Var.pos, Abs.ext])
      | there y' => exact hP.2.2 x' y' hx hy (by simpa [Var.pos] using hne)

/-- Members are forgotten; the owned slots keep their facts in the new world `σ'`. -/
theorem Passt.entglied {a : Abs} {Γ : Ctx} {σ σ' : World D} {ρ : Env D Γ} (hP : Passt A L G a σ ρ)
    (hfr : ∀ y : Var Γ (Ty.index (D.count A.tab)), a y.pos = .frei →
      A.Lebt σ' (ρ.get y).n ∧ ¬ Auf (D.count A.tab) (L.wert σ') (G.st σ') (ρ.get y).n) :
    Passt A L G a.entglied σ' ρ :=
  ⟨fun y hy => hfr y ((Abs.entglied_frei a y.pos).mp hy),
    fun y hy => absurd hy (Abs.entglied_ne_glied a y.pos),
    fun x y hx hy hne => hP.2.2 x y ((Abs.entglied_frei a _).mp hx) ((Abs.entglied_frei a _).mp hy) hne⟩

/-- One position becomes unknown; the other facts hold in the new world `σ'`. -/
theorem Passt.set_offen {a : Abs} {Γ : Ctx} {σ σ' : World D} {ρ : Env D Γ} (m : Nat) (hP : Passt A L G a σ ρ)
    (hfr : ∀ y : Var Γ (Ty.index (D.count A.tab)), a y.pos = .frei → y.pos ≠ m →
      A.Lebt σ' (ρ.get y).n ∧ ¬ Auf (D.count A.tab) (L.wert σ') (G.st σ') (ρ.get y).n)
    (hgl : ∀ y : Var Γ (Ty.index (D.count A.tab)), a y.pos = .glied →
      Auf (D.count A.tab) (L.wert σ') (G.st σ') (ρ.get y).n) :
    Passt A L G (a.set m .offen) σ' ρ :=
  ⟨fun y hy => by
      obtain ⟨hne, hy'⟩ := Abs.set_frei hy (by decide)
      exact hfr y hy' hne,
    fun y hy => by
      rcases Abs.set_glied hy with ⟨-, h⟩ | ⟨-, h⟩
      · cases h
      · exact hgl y h,
    fun x y hx hy hne => hP.2.2 x y (Abs.set_frei hx (by decide)).2 (Abs.set_frei hy (by decide)).2 hne⟩

end Passt

/-! ## 4. Runs that move none of the five quantities the structures read -/

section Gleich
variable (A : FreiForm D) (L : LinkFeld A) (G : LinkKopf A)

/-- **`σ'` has the same free-list head, free links, counter, list links and list head as `σ`.** Nothing the list
    invariant, the liveness or the abstract state reads has moved. -/
structure Gleich (σ σ' : World D) : Prop where
  kopf : A.kopfSt σ' = A.kopfSt σ
  nxt : ∀ j, A.naechst σ' j = A.naechst σ j
  stand : A.stand σ' = A.stand σ
  lnk : ∀ j, L.wert σ' j = L.wert σ j
  head : G.st σ' = G.st σ

theorem Gleich.lese (σ : World D) (Λ : List (Res D)) (o : List (D.Tab ⊕ D.Glob)) :
    Gleich A L G σ (σ.lese Λ o) := ⟨rfl, fun _ => rfl, rfl, fun _ => rfl, rfl⟩

/-- A store into the PAYLOAD field (not the link, not the free link) moves none of the five. -/
theorem Gleich.nutzlast (σ : World D) (Λ : List (Res D)) (i : Int) (v : Wert D (D.typ A.tab A.feld)) :
    Gleich A L G σ (σ.schreibSlot A.tab Λ i A.feld v) :=
  ⟨rfl, fun j => A.naechst_schreibSlot_feld σ Λ i j v, rfl,
    fun j => by simp only [LinkFeld.wert, World.slots_schreibSlot_ne _ _ _ _ _ _ _ _ L.h1], rfl⟩

theorem Gleich.trans {σ σ' σ'' : World D} (h : Gleich A L G σ σ') (h' : Gleich A L G σ' σ'') :
    Gleich A L G σ σ'' :=
  ⟨h'.kopf.trans h.kopf, fun j => (h'.nxt j).trans (h.nxt j), h'.stand.trans h.stand,
    fun j => (h'.lnk j).trans (h.lnk j), h'.head.trans h.head⟩

theorem Gleich.lebt {σ σ' : World D} (h : Gleich A L G σ σ') (j : Int) : A.Lebt σ' j ↔ A.Lebt σ j :=
  A.lebt_gleich h.kopf h.nxt h.stand j

theorem Gleich.listOk {σ σ' : World D} (h : Gleich A L G σ σ') (hl : ListOk A L G σ) : ListOk A L G σ' := by
  unfold ListOk at *
  rw [funext h.lnk, h.head]
  exact hl.rahmen (fun j hj => (h.lebt A L G j).mpr (hl.lebt_auf hj)) (fun _ _ => rfl)

theorem Gleich.strukturOk {σ σ' : World D} (h : Gleich A L G σ σ') (hs : StrukturOk A L G σ) :
    StrukturOk A L G σ' :=
  ⟨A.freiOk_gleich h.kopf h.nxt h.stand hs.1, h.listOk A L G hs.2⟩

theorem Gleich.auf {σ σ' : World D} (h : Gleich A L G σ σ') (j : Int) :
    Auf (D.count A.tab) (L.wert σ') (G.st σ') j ↔ Auf (D.count A.tab) (L.wert σ) (G.st σ) j := by
  rw [funext h.lnk, h.head]

theorem Gleich.passt {σ σ' : World D} (h : Gleich A L G σ σ') {a : Abs} {Γ : Ctx} {ρ : Env D Γ}
    (hp : Passt A L G a σ ρ) : Passt A L G a σ' ρ :=
  ⟨fun x hx => ⟨(h.lebt A L G _).mpr (hp.1 x hx).1, fun hm => (hp.1 x hx).2 ((h.auf A L G _).mp hm)⟩,
    fun x hx => (h.auf A L G _).mpr (hp.2.1 x hx), hp.2.2⟩

end Gleich

/-! ## 5. An allocator run keeps the list -/

section Fremd
variable (A : FreiForm D) (L : LinkFeld A) (G : LinkKopf A)

/-- **A run that only touched the allocator's places keeps the list**, as long as every member stays live. -/
theorem ListOk.fremd {σ σ' : World D} (hf : A.Fremd σ σ') (hmono : ∀ j, A.Lebt σ j → A.Lebt σ' j)
    (h : ListOk A L G σ) : ListOk A L G σ' := by
  unfold ListOk at *
  rw [L.wert_fremd' hf, G.st_fremd hf]
  exact h.rahmen (fun j hj => hmono j (h.lebt_auf hj)) (fun _ _ => rfl)

/-- The same, when one slot `i` that was not on the list dies. -/
theorem ListOk.fremd_frei {σ σ' : World D} (hf : A.Fremd σ σ') (i : Int)
    (hmono : ∀ j, A.Lebt σ j → j ≠ i → A.Lebt σ' j)
    (hnot : ¬ Auf (D.count A.tab) (L.wert σ) (G.st σ) i) (h : ListOk A L G σ) : ListOk A L G σ' := by
  unfold ListOk at *
  rw [L.wert_fremd' hf, G.st_fremd hf]
  exact h.rahmen (fun j hj => hmono j (h.lebt_auf hj) (fun e => hnot (e ▸ hj))) (fun _ _ => rfl)

/-- The list's members do not change under an allocator run. -/
theorem auf_fremd {σ σ' : World D} (hf : A.Fremd σ σ') (j : Int) :
    Auf (D.count A.tab) (L.wert σ') (G.st σ') j ↔ Auf (D.count A.tab) (L.wert σ) (G.st σ) j := by
  rw [L.wert_fremd' hf, G.st_fremd hf]

/-- The abstract state survives an allocator run, as long as every live slot stays live. -/
theorem Passt.fremd {σ σ' : World D} (hf : A.Fremd σ σ') (hmono : ∀ j, A.Lebt σ j → A.Lebt σ' j)
    {a : Abs} {Γ : Ctx} {ρ : Env D Γ} (hP : Passt A L G a σ ρ) : Passt A L G a σ' ρ :=
  ⟨fun x hx => ⟨hmono _ (hP.1 x hx).1, fun hm => (hP.1 x hx).2 ((auf_fremd A L G hf _).mp hm)⟩,
    fun x hx => (auf_fremd A L G hf _).mpr (hP.2.1 x hx), hP.2.2⟩

end Fremd

/-! ## 5b. The three ways the structure breaks (the model's reading of why `N586` refuses) -/

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

/-! ## 6. The outcomes -/

section Post
variable (A : FreiForm D) (L : LinkFeld A) (G : LinkKopf A) {V : Vertrag D} {l : Bool}

/-- A shorter context: the outcome of a sub-block is read in the outer context. -/
theorem Post.schrumpf {a : Abs} {τ : Ty} {Γ : Ctx} {o : Ausgang V l (τ :: Γ)}
    (h : Post A L G a o) : Post A L G a.tail o.schrumpf := by
  cases o with
  | ok σ ρ' =>
    cases ρ' with
    | cons k ρ => exact ⟨h.1, Passt.tail A L G h.2⟩
  | zurueck σ v => exact h
  | why σ r => exact h
  | leave hh σ ρ' => exact h
  | next hh σ ρ' => exact h
  | logik e => trivial
  | hardware e => trivial

/-- An outcome that does not fall off does not mention the abstract state. -/
theorem Post.nicht_ok {a b : Abs} {Γ : Ctx} {o : Ausgang V l Γ} (h : Post A L G a o)
    (hno : ∀ σ ρ, o ≠ .ok σ ρ) : Post A L G b o := by
  cases o with
  | ok σ ρ => exact absurd rfl (hno σ ρ)
  | zurueck σ v => exact h
  | why σ r => exact h
  | leave hh σ ρ' => exact h
  | next hh σ ρ' => exact h
  | logik e => trivial
  | hardware e => trivial

/-- A weaker state is promised wherever a stronger one is. -/
theorem Post.schwacher {a b : Abs} (hs : Abs.Schwacher b a) {Γ : Ctx} {o : Ausgang V l Γ}
    (h : Post A L G a o) : Post A L G b o := by
  cases o with
  | ok σ ρ => exact ⟨h.1, Passt.schwacher A L G hs h.2⟩
  | zurueck σ v => exact h
  | why σ r => exact h
  | leave hh σ ρ' => exact h
  | next hh σ ρ' => exact h
  | logik e => trivial
  | hardware e => trivial

/-- **A statement followed by a block:** if the statement's outcome meets `a`, and every continuation from `a` meets
    `a'`, the sequence meets `a'`. -/
theorem Post.cons_stmt (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {a a' : Abs} {Γ : Ctx} {Λ Λ1 Λ' : List (Res D)}
    {s : Stmt D V l Γ Λ Λ1} {rest : Block D V l Γ Λ1 Λ'} {σ : World D} {ρ : Env D Γ}
    (hp : Post A L G a (execStmt O passes R s σ ρ))
    (ihr : ∀ (σ : World D) (ρ : Env D Γ), StrukturOk A L G σ → Passt A L G a σ ρ →
      Post A L G a' (execBlock O passes R rest σ ρ)) :
    Post A L G a' (execBlock O passes R (.cons s rest) σ ρ) := by
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
    {voll : Endblock D V l Γ Λ} (hv : Rein voll) (σ : World D) (ρ : Env D Γ) (h : StrukturOk A L G σ) :
    Post A L G a (execEnd O passes R voll σ ρ).zuAusgang := by
  cases hv with
  | ret e hΛ => exact (Gleich.lese A L G σ Λ _).strukturOk A L G h
  | retWhy r hΛ => exact h
  | leave hh => exact h
  | next hh => exact h

end Post

end Gabbro.Grammatik
