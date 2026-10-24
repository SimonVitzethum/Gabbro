import Grammatik.Bausteine.Arena.Ownership.Source.Flow.Interface

/-! The invariant of the general ownership body judgment, at a statement
boundary of one activation. `Holds A fr s0 c σ ρ` says: some ghost ledger
`s` refines the actual G world `σ`, realises the source context `c` over the
actual environment `ρ`, accounts for every allocation the frame owns, and is
reached from the activation's entry ledger `s0` by a local, progressing
effect. Worlds that keep the allocator words and links keep the invariant. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source

variable {D : Deklaration}

/-! ## 1. Worlds that keep liveness -/

/-- The free-list head, every link and the used counter are unchanged. These
are exactly the words `FreiForm.Lebt` and `FreiForm.FreiOk` read. -/
def MetaSame (A : FreiForm D) (σ σ' : World D) : Prop :=
  A.kopfSt σ' = A.kopfSt σ ∧ (∀ j, A.naechst σ' j = A.naechst σ j) ∧ A.stand σ' = A.stand σ

theorem MetaSame.refl (A : FreiForm D) (σ : World D) : MetaSame A σ σ :=
  ⟨rfl, fun _ => rfl, rfl⟩

theorem MetaSame.trans {A : FreiForm D} {a b c : World D}
    (h1 : MetaSame A a b) (h2 : MetaSame A b c) : MetaSame A a c :=
  ⟨h2.1.trans h1.1, fun j => (h2.2.1 j).trans (h1.2.1 j), h2.2.2.trans h1.2.2⟩

theorem MetaSame.of_cells (A : FreiForm D) {σ σ' : World D}
    (hk : σ'.globs A.kopf = σ.globs A.kopf) (hz : σ'.globs A.zaehl = σ.globs A.zaehl)
    (hn : ∀ j, σ'.slots A.tab j A.nxt = σ.slots A.tab j A.nxt) : MetaSame A σ σ' := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [FreiForm.kopfSt, hk]
  · intro j; simp only [FreiForm.naechst, hn]
  · simp only [ArenaForm.stand, hz]

theorem MetaSame.reads (A : FreiForm D) (σ : World D) (Λ : List (Res D))
    (os : List (D.Tab ⊕ D.Glob)) : MetaSame A σ (σ.lese Λ os) :=
  MetaSame.of_cells A rfl rfl (fun _ => rfl)

theorem MetaSame.takes (A : FreiForm D) (σ : World D) (L : D.Lock) : MetaSame A σ (σ.nimmt L) :=
  MetaSame.of_cells A rfl rfl (fun _ => rfl)

theorem MetaSame.gives (A : FreiForm D) (σ : World D) (L : D.Lock) : MetaSame A σ (σ.gibt L) :=
  MetaSame.of_cells A rfl rfl (fun _ => rfl)

/-- A field other than the free-list link. Stated through the table equality
so it applies to every table, the arena's included. -/
def NotLink (A : FreiForm D) (t : D.Tab) (f : D.Feld t) : Prop :=
  ∀ h : A.tab = t, h ▸ A.nxt ≠ f

instance (A : FreiForm D) (t : D.Tab) (f : D.Feld t) : Decidable (NotLink A t f) :=
  if h : A.tab = t then
    if hf : h ▸ A.nxt = f then isFalse (fun hn => hn h hf)
    else isTrue (fun h' => by cases h'; exact hf)
  else isTrue (fun h' => absurd h' h)

theorem storeSlot_link (A : FreiForm D) (σ : World D) (t : D.Tab) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f)) (hn : NotLink A t f) (j : Int) :
    (σ.storeSlot t k f v).slots A.tab j A.nxt = σ.slots A.tab j A.nxt := by
  by_cases ht : A.tab = t
  · subst ht
    have hf : A.nxt ≠ f := hn rfl
    simp only [World.storeSlot, dite_true]
    split
    · simp [hf]
    · rfl
  · simp [World.storeSlot, ht]

theorem MetaSame.writeSlot (A : FreiForm D) (σ : World D) (t : D.Tab) (Λ : List (Res D)) (k : Int)
    (f : D.Feld t) (v : Wert D (D.typ t f)) (hn : NotLink A t f) :
    MetaSame A σ (σ.schreibSlot t Λ k f v) :=
  MetaSame.of_cells A rfl rfl (storeSlot_link A σ t k f v hn)

/-- A global that is neither the free-list head nor the used counter. -/
def NotMetaGlob (A : FreiForm D) (g : D.Glob) : Prop := g ≠ A.kopf ∧ g ≠ A.zaehl

instance (A : FreiForm D) (g : D.Glob) : Decidable (NotMetaGlob A g) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem MetaSame.writeGlob (A : FreiForm D) (σ : World D) (g : D.Glob) (Λ : List (Res D))
    (v : Wert D (D.gtyp g)) (hg : NotMetaGlob A g) : MetaSame A σ (σ.schreibGlob g Λ v) := by
  apply MetaSame.of_cells A
  · simp [World.schreibGlob, World.merke, World.storeGlob, Ne.symm hg.1]
  · simp [World.schreibGlob, World.merke, World.storeGlob, Ne.symm hg.2]
  · intro j; rfl

theorem MetaSame.writeBytes (A : FreiForm D) (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (Λ : List (Res D)) (hn : NotLink A t f) :
    ∀ (bs : List Byte) (σ : World D) (k : Int), MetaSame A σ (σ.schreibBytes t f hf Λ k bs)
  | [], σ, _ => MetaSame.refl A σ
  | b :: bs, σ, k =>
    (MetaSame.writeSlot A σ t Λ k f _ hn).trans (MetaSame.writeBytes A t f hf Λ hn bs _ (k + 1))

/-- A foreign body that writes no arena table and neither allocator word.
`GutO` is the existing named hardware assumption on the oracle's frame. -/
def AxiomFree (A : FreiForm D) (a : D.Ax) : Prop :=
  D.aschreibt a A.tab = false ∧ D.agschreibt a A.kopf = false ∧ D.agschreibt a A.zaehl = false

instance (A : FreiForm D) (a : D.Ax) : Decidable (AxiomFree A a) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem MetaSame.axiom {A : FreiForm D} {O : Orakel D} (hO : GutO O) {a : D.Ax}
    (ha : AxiomFree A a) (σ : World D) (ρ : Env D (D.aparams a)) :
    MetaSame A σ (O.wirkt a σ ρ).1 := by
  obtain ⟨hr, _⟩ := hO a σ ρ
  exact MetaSame.of_cells A (hr.2 _ ha.2.1) (hr.2 _ ha.2.2) (fun j => hr.1 _ ha.1 j A.nxt)

theorem State.agrees_meta {s : State} {A : FreiForm D} {σ σ' : World D}
    (ha : s.agrees A σ) (hm : MetaSame A σ σ') : s.agrees A σ' :=
  ⟨ha.1, fun i => (A.lebt_gleich hm.1 hm.2.1 hm.2.2 i).trans (ha.2 i)⟩

theorem freiOk_meta {A : FreiForm D} {σ σ' : World D} (hf : A.FreiOk σ) (hm : MetaSame A σ σ') :
    A.FreiOk σ' :=
  A.freiOk_gleich hm.1 hm.2.1 hm.2.2 hf

/-! ## 2. The invariant -/

/-- **The ledger at a statement boundary of the activation `fr`.** -/
def Holds (A : FreiForm D) (fr : Frame) (s0 : State) (c : Context) (σ : World D) {Γ : Ctx}
    (ρ : Env D Γ) : Prop :=
  ∃ g s, Realizes c g A fr s σ ρ ∧ Complete c g s fr ∧ s0.local s fr ∧ s0.progress s

variable {A : FreiForm D} {fr : Frame} {s0 : State}

theorem Holds.meta {c : Context} {σ σ' : World D} {Γ : Ctx} {ρ : Env D Γ}
    (h : Holds A fr s0 c σ ρ) (hm : MetaSame A σ σ') : Holds A fr s0 c σ' ρ := by
  obtain ⟨g, s, ⟨ha, hf, hr⟩, hc, hl, hp⟩ := h
  exact ⟨g, s, ⟨State.agrees_meta ha hm, freiOk_meta hf hm, hr⟩, hc, hl, hp⟩

theorem Holds.reads {c : Context} {σ : World D} {Γ : Ctx} {ρ : Env D Γ}
    (h : Holds A fr s0 c σ ρ) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    Holds A fr s0 c (σ.lese Λ os) ρ :=
  h.meta (MetaSame.reads A σ Λ os)

/-- A binder without provenance: computed values, register reads, foreign
answers and loaded words never carry a grant. -/
theorem Holds.bindNone {c : Context} {σ : World D} {Γ : Ctx} {τ : Ty} {ρ : Env D Γ}
    (h : Holds A fr s0 c σ ρ) (v : Wert D τ) : Holds A fr s0 (c.bind none) σ (.cons v ρ) := by
  obtain ⟨g, s, ⟨ha, hf, hb, href, hr⟩, hc, hl, hp⟩ := h
  refine ⟨g, s, ⟨ha, hf, Context.bind_bounded hb none (fun _ h => by cases h),
    References.bind href v none (fun _ h => by cases h), hr⟩, Complete.bind hc none, hl, hp⟩

/-- A binder copying a variable shares its origin, whatever the reading world. -/
theorem Holds.bindExpr {c : Context} {σ : World D} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} {ρ : Env D Γ}
    (h : Holds A fr s0 c σ ρ) (e : Expr D Γ Λ τ) (σa σb : World D) :
    Holds A fr s0 (c.bind (origin c e)) σ (.cons (eval σa e σb ρ) ρ) := by
  obtain ⟨g, s, ⟨ha, hf, hb, href, hr⟩, hc, hl, hp⟩ := h
  refine ⟨g, s, ⟨ha, hf, ?_, ?_, hr⟩, Complete.bind hc _, hl, hp⟩
  · apply Context.bind_bounded hb
    intro i hi
    exact hb.2 (some i) (origin_member c e i hi) i rfl
  · apply References.bind href _ (origin c e)
    intro i hi
    exact origin_sound c g ρ href e i hi σa σb

theorem Context.drop_reference (c : Context) {Γ : Ctx} {τ υ : Ty}
    (hlen : c.references.length = Γ.length + 1) (x : Var Γ τ) :
    c.drop.reference x = c.reference (.there x : Var (υ :: Γ) τ) := by
  have hx : x.unten < c.references.length - 1 := by rw [hlen]; simpa using Var.unten_lt x
  have hx' : x.unten < c.references.length := by omega
  simp [Context.reference, Context.drop, Var.unten, hx, List.getElem?_eq_getElem hx']

/-- Leaving a binder's scope forgets its name, never its right. -/
theorem Holds.drop {c : Context} {σ : World D} {Γ : Ctx} {τ : Ty} {v : Wert D τ} {ρ : Env D Γ}
    (h : Holds A fr s0 c σ (.cons v ρ)) : Holds A fr s0 c.drop σ ρ := by
  obtain ⟨g, s, ⟨ha, hf, hb, href, hr⟩, hc, hl, hp⟩ := h
  have hlen : c.references.length = Γ.length + 1 := by simpa using href.1
  refine ⟨g, s, ⟨ha, hf, ⟨hb.1, fun ref hm => hb.2 ref (List.dropLast_subset _ hm)⟩, ?_, hr⟩,
    Complete.drop hc, hl, hp⟩
  refine ⟨by simp [Context.drop, hlen], ?_⟩
  intro υ x i hi
  rw [Context.drop_reference c hlen x (υ := τ)] at hi
  exact href.2 (.there x) i hi

/-! ## 3. Weakening a context -/

/-- `k` knows no more than `c`: the same rights, and every name `k` ties to
an origin is tied to it in `c`. `k` is bounded by its own counter, so `c`
may have used (and given up) origins beyond it: a loop body that allocates
and releases returns to its head. Joins and loop heads use it. -/
def Weaker (k c : Context) : Prop :=
  (∀ i, k.rights i = c.rights i) ∧ (∀ i, k.next ≤ i → k.rights i = none) ∧
    k.references.length = c.references.length ∧
    ∀ (p o : Nat), k.references[p]? = some (some o) → c.references[p]? = some (some o) ∧ o < k.next

theorem Weaker.refl {c : Context} (hc : c.bounded) : Weaker c c :=
  ⟨fun _ => rfl, hc.1, rfl, fun p o h => ⟨h, hc.2 _ (List.mem_of_getElem? h) o rfl⟩⟩

theorem Weaker.trans {a b c : Context} (hab : Weaker a b) (hbc : Weaker b c) : Weaker a c :=
  ⟨fun i => (hab.1 i).trans (hbc.1 i), hab.2.1, hab.2.2.1.trans hbc.2.2.1,
    fun p o h => ⟨(hbc.2.2.2 p o (hab.2.2.2 p o h).1).1, (hab.2.2.2 p o h).2⟩⟩

theorem Holds.weaken {k c : Context} {σ : World D} {Γ : Ctx} {ρ : Env D Γ}
    (h : Holds A fr s0 c σ ρ) (hw : Weaker k c) : Holds A fr s0 k σ ρ := by
  obtain ⟨g, s, ⟨ha, hf, hb, href, hr⟩, hc, hl, hp⟩ := h
  refine ⟨g, s, ⟨ha, hf, ?_, ?_, ?_⟩, ?_, hl, hp⟩
  · constructor
    · exact hw.2.1
    · intro ref hm i he
      subst he
      obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hm
      exact (hw.2.2.2 p i hp).2
  · refine ⟨hw.2.2.1.trans href.1, ?_⟩
    intro υ x i hi
    apply href.2 x i
    unfold Context.reference at hi ⊢
    cases hk : k.references[x.unten]? with
    | none => simp [hk] at hi
    | some ref =>
      simp only [hk, Option.getD_some] at hi
      subst ref
      simp [(hw.2.2.2 _ _ hk).1]
  · exact ⟨fun i mode hi => hr.1 i mode (hw.1 i ▸ hi),
      fun i j p q hi hj => hr.2 i j p q (hw.1 i ▸ hi) (hw.1 j ▸ hj)⟩
  · intro slot cell hcell howner
    obtain ⟨hloans, i, h, hi, hrest⟩ := hc slot cell hcell howner
    exact ⟨hloans, i, h, (hw.1 i).trans hi, hrest⟩

/-- The context at a `leave` or `next` deep inside a loop body: below the
loop's binders it is at least as strong as the loop context `k`. -/
def ExitsTo (k c : Context) : Prop :=
  k.references.length ≤ c.references.length ∧
    Weaker k { c with references := c.references.take k.references.length }

theorem ExitsTo.drop {k c : Context} (h : ExitsTo k c)
    (hlt : k.references.length < c.references.length) : ExitsTo k c.drop := by
  refine ⟨by simp [Context.drop]; omega, ?_⟩
  have htake : c.references.dropLast.take k.references.length =
      c.references.take k.references.length := by
    rw [List.dropLast_eq_take, List.take_take]
    congr 1
    omega
  obtain ⟨_, hw⟩ := h
  show Weaker k { c with references := c.references.dropLast.take k.references.length }
  rw [htake]
  exact hw

theorem ExitsTo.weaker {k c : Context} (h : ExitsTo k c)
    (heq : c.references.length = k.references.length) : Weaker k c := by
  obtain ⟨_, hw⟩ := h
  have ht : c.references.take k.references.length = c.references := by
    rw [← heq]; exact List.take_length
  rw [ht] at hw
  exact hw

theorem ExitsTo.of_weaker {k c : Context} (h : Weaker k c) : ExitsTo k c := by
  refine ⟨h.2.2.1 ▸ Nat.le_refl _, ?_⟩
  have ht : c.references.take k.references.length = c.references := by
    rw [h.2.2.1]; exact List.take_length
  show Weaker k { c with references := c.references.take k.references.length }
  rw [ht]
  exact h

/-! ## 4. The activation's entry -/

/-- The callee side of an interface: at entry the parameter context holds. -/
theorem Holds.entry {A : FreiForm D} {f : D.Fn} (I : Flow.Interface A f) (frame : Frame) (s : State)
    (σ : World D) (ρ : Env D (D.params f)) (ha : s.agrees A σ) (hf : A.FreiOk σ)
    (hpre : (I.contract A).requires frame s ρ) :
    Holds A frame s (Flow.parameterContext I.parameters) σ ρ := by
  obtain ⟨g, href, hr, hc⟩ := hpre
  exact ⟨g, s, ⟨ha, hf, Flow.parameterContext_bounded _, href, hr⟩, hc, State.local_refl s frame,
    State.progress_refl s⟩

#print axioms Holds.weaken
#print axioms Holds.drop
#print axioms MetaSame.axiom

end Gabbro.Grammatik.ArenaOwnership.Body
