module

public import Grammatik.Kern.Syntax.Satz

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-! ## 1. `Treu`: the frame and the held locks, without the trace quality -/

/-- **The two facts of `Gut` that need no lock discipline**: `σ'` differs
    from `σ` only at carriers the contract may write, and holds exactly the
    locks `σ` held. -/
def Treu (W : D.Tab → Bool) (G : D.Glob → Bool) (σ σ' : World D) : Prop :=
  Rahmen W G σ σ' ∧ σ'.haelt = σ.haelt

theorem Treu.refl (W G) (σ : World D) : Treu W G σ σ := ⟨Rahmen.refl _ _ _, rfl⟩

theorem Treu.trans {W G} {a b c : World D} (h1 : Treu W G a b) (h2 : Treu W G b c) :
    Treu W G a c := ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩

theorem Treu.weiter {W W' : D.Tab → Bool} {G G' : D.Glob → Bool} {a b : World D}
    (hW : ∀ t, W t = true → W' t = true) (hG : ∀ g, G g = true → G' g = true)
    (h : Treu W G a b) : Treu W' G' a b := ⟨h.1.weiter hW hG, h.2⟩

/-- Asking outside the program changes no cell and no lock. -/
theorem treu_fragt {W G} (σ : World D) (q : D.Ax ⊕ D.Reg ⊕ D.Glob) : Treu W G σ (σ.fragt q) :=
  ⟨rahmen_gleich rfl rfl, rfl⟩

/-- Everything `Satz.lean` proves is at least this. -/
theorem Gut.treu {W G} {a b : World D} (h : Gut W G a b) : Treu W G a b := ⟨h.1, h.2.1⟩

/-! ## 2. The leaves: reading, writing, taking and giving a lock -/

theorem treu_merke {W G} (σ : World D) (es : List (Ereignis D))
    (hz : ∀ e ∈ es, e.zugriffMit σ.haelt) : Treu W G σ (σ.merke es) :=
  ⟨rahmen_gleich rfl rfl,
   show offen (es ++ σ.spur) = offen σ.spur from offen_append_zugriffe _ es σ.spur hz⟩

/-- **A read keeps everything.** No premise: `lese` appends `zugriff` events
    and changes no slot, no global and no held lock. -/
theorem treu_lese {W G} (σ : World D) (Λ : List (Res D)) (orte : List (D.Tab ⊕ D.Glob)) :
    Treu W G σ (σ.lese Λ orte) := ⟨rahmen_gleich rfl rfl, lese_haelt σ Λ orte⟩

theorem treu_schreibSlot {W G} (σ : World D) (t : D.Tab) (Λ : List (Res D)) (k : Int)
    (f : D.Feld t) (v : Wert D (D.typ t f)) (hw : W t = true) :
    Treu W G σ (σ.schreibSlot t Λ k f v) :=
  Treu.trans ⟨rahmen_storeSlot W G σ t k f v hw, rfl⟩
    (treu_merke _ _ (by intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he; subst he; simp only [Ereignis.zugriffMit]; rfl))

theorem treu_schreibGlob {W G} (σ : World D) (g : D.Glob) (Λ : List (Res D))
    (v : Wert D (D.gtyp g)) (hg : G g = true) : Treu W G σ (σ.schreibGlob g Λ v) :=
  Treu.trans ⟨rahmen_storeGlob W G σ g v hg, rfl⟩
    (treu_merke _ _ (by intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he; subst he; simp only [Ereignis.zugriffMit]; rfl))

theorem treu_schreibBytes {W G} (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ : List (Res D)) (hw : W t = true) :
    ∀ (bs : List Byte) (k : Int), Treu W G σ (σ.schreibBytes t f hf Λ k bs) := by
  intro bs
  induction bs generalizing σ with
  | nil => intro k; exact Treu.refl _ _ _
  | cons b bs ih =>
      intro k
      simp only [World.schreibBytes]
      exact (treu_schreibSlot (W := W) (G := G) σ t Λ k f
        (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255))) hw).trans (ih _ _)

/-- The owed invariants are READ at the return of a call; reading keeps the
    frame and the held locks. -/
theorem treu_foldl_lese {W G} (P : Programm D) :
    ∀ (is : List D.Inv) (σ : World D),
      Treu W G σ (is.foldl (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte) σ)
  | [], _ => Treu.refl _ _ _
  | i :: is, σ => (treu_lese σ (invSicht D i) (P.invariante i).orte).trans
      (treu_foldl_lese P is (σ.lese (invSicht D i) (P.invariante i).orte))

/-- **`locks L { .. }` gives back what it took, at EVERY world.** The `Gut`
    version (`gut_nimmt_gibt`) needs `L ∉ σ.haelt` and the rank order for the
    `nimmt` EVENT to be good; the held set itself survives without them,
    because `offen` erases the FIRST `L` and that is the one `nimmt` put
    there. -/
theorem treu_nimmt_gibt {W G} (σ σ1 : World D) (L : D.Lock)
    (h : Treu W G (σ.nimmt L) σ1) : Treu W G σ (σ1.gibt L) := by
  refine ⟨?_, ?_⟩
  · exact (rahmen_gleich (W := W) (G := G) (σ := σ) (σ' := σ.nimmt L) rfl rfl).trans
      (h.1.trans (rahmen_gleich rfl rfl))
  · show (offen σ1.spur).erase L = offen σ.spur
    have := h.2
    simp only [World.haelt, World.nimmt, offen] at this
    rw [this]; exact List.erase_cons_head _ _

/-! ## 3. Outcomes -/

def TreuAusgang (W : D.Tab → Bool) (G : D.Glob → Bool) (σ : World D) (o : Ausgang V l Γ) : Prop :=
  ∀ σ', o.welt = some σ' → Treu W G σ σ'

def TreuEnd (W : D.Tab → Bool) (G : D.Glob → Bool) (σ : World D) (o : EndAusgang V l Γ) : Prop :=
  ∀ σ', o.welt = some σ' → Treu W G σ σ'

theorem TreuAusgang.schrumpf {W G} {σ : World D} {o : Ausgang V l (τ :: Γ)}
    (h : TreuAusgang W G σ o) : TreuAusgang W G σ o.schrumpf := by
  intro σ' hs; cases o <;> simp only [Ausgang.welt, Ausgang.schrumpf, Option.some.injEq, reduceCtorEq] at hs ⊢ <;>
    (subst hs; exact h _ rfl)

theorem TreuAusgang.schrumpfArm {W G} {σ : World D} (c : Option Ty)
    {o : Ausgang V l (ArmCtx Γ c)} (h : TreuAusgang W G σ o) :
    TreuAusgang W G σ (o.schrumpfArm c) := by
  cases c with
  | none => exact h
  | some p => obtain ⟨_, _⟩ := p; exact h.schrumpf

theorem TreuEnd.schrumpf {W G} {σ : World D} {o : EndAusgang V l (τ :: Γ)}
    (h : TreuEnd W G σ o) : TreuEnd W G σ o.schrumpf := by
  intro σ' hs; cases o <;> simp only [EndAusgang.welt, EndAusgang.schrumpf, Option.some.injEq, reduceCtorEq] at hs ⊢ <;>
    (subst hs; exact h _ rfl)

theorem TreuEnd.zuAusgang {W G} {σ : World D} {o : EndAusgang V l Γ} (h : TreuEnd W G σ o) :
    TreuAusgang W G σ o.zuAusgang := by
  intro σ' hs; cases o <;> simp only [Ausgang.welt, EndAusgang.zuAusgang, Option.some.injEq, reduceCtorEq] at hs ⊢ <;>
    (subst hs; exact h _ rfl)

theorem TreuAusgang.vor {W G} {σ σ1 : World D} {o : Ausgang V l Γ}
    (h1 : Treu W G σ σ1) (h : TreuAusgang W G σ1 o) : TreuAusgang W G σ o :=
  fun σ' hs => h1.trans (h σ' hs)

theorem TreuEnd.vor {W G} {σ σ1 : World D} {o : EndAusgang V l Γ}
    (h1 : Treu W G σ σ1) (h : TreuEnd W G σ1 o) : TreuEnd W G σ o :=
  fun σ' hs => h1.trans (h σ' hs)

theorem TreuAusgang.gibt {W G} {σ : World D} (L : D.Lock) {o : Ausgang V l Γ}
    (h : TreuAusgang W G (σ.nimmt L) o) : TreuAusgang W G σ (o.mapWelt (·.gibt L)) := by
  intro σ' hs
  cases o <;> simp only [Ausgang.welt, Ausgang.mapWelt, Option.some.injEq, reduceCtorEq] at hs ⊢ <;>
    (subst hs; exact treu_nimmt_gibt _ _ L (h _ rfl))

/-! ## 4. The three loop combinators -/

section Schleifen
variable {W : D.Tab → Bool} {G : D.Glob → Bool}

theorem traverseLauf_treu (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, TreuAusgang W G σ (schritt σ ρ))
    (hi : ∀ σ ρ, Treu W G σ (inv σ ρ).1) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ),
      TreuAusgang W G σ (traverseLauf (l := l) schritt inv ks σ ρ) := by
  intro ks
  induction ks with
  | nil =>
      intro σ ρ σ' h
      simp only [traverseLauf] at h
      split at h
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h; exact hi σ ρ
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | cons k ks ih =>
      intro σ ρ σ' h
      simp only [traverseLauf] at h
      split at h
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · have hinv := hi σ ρ
        have hstep := hs (inv σ ρ).1 (.cons k ρ)
        split at h
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1.tail σ' h)
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1.tail σ' h)
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          split at h <;> simp only [Ausgang.welt, Option.some.injEq, reduceCtorEq] at h
          subst h; exact g1.trans (hi σ1 ρ1.tail)
        · rename_i σ1 v hs1; simp only [Ausgang.welt, Option.some.injEq] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 r hs1; simp only [Ausgang.welt, Option.some.injEq] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · simp only [Ausgang.welt, reduceCtorEq] at h
        · simp only [Ausgang.welt, reduceCtorEq] at h

theorem retryLauf_treu (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueberlauf : World D → Env D Γ → Ausgang V l Γ)
    (hs : ∀ σ ρ, TreuAusgang W G σ (schritt σ ρ))
    (hb : ∀ σ ρ, Treu W G σ (bis σ ρ).1)
    (hu : ∀ σ ρ, TreuAusgang W G σ (ueberlauf σ ρ)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      TreuAusgang W G σ (retryLauf schritt bis ueberlauf n σ ρ) := by
  intro n
  induction n with
  | zero =>
      intro σ ρ σ' h
      simp only [retryLauf] at h
      split at h
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h; exact hb σ ρ
      · exact (hb σ ρ).trans (hu _ ρ σ' h)
  | succ n ih =>
      intro σ ρ σ' h
      simp only [retryLauf] at h
      split at h
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h; exact hb σ ρ
      · have hinv := hb σ ρ
        have hstep := hs (bis σ ρ).1 ρ
        split at h
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1 σ' h)
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1 σ' h)
        · rename_i σ1 ρ1 hs1; simp only [Ausgang.welt, Option.some.injEq] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 v hs1; simp only [Ausgang.welt, Option.some.injEq] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 r hs1; simp only [Ausgang.welt, Option.some.injEq] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · simp only [Ausgang.welt, reduceCtorEq] at h
        · simp only [Ausgang.welt, reduceCtorEq] at h

theorem foreverLauf_treu (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, TreuAusgang W G σ (schritt σ ρ))
    (hi : ∀ σ ρ, Treu W G σ (inv σ ρ).1) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      TreuAusgang W G σ (foreverLauf (l := l) a schritt inv n σ ρ) := by
  intro n
  induction n with
  | zero => intro σ ρ σ' h; simp only [Ausgang.welt, foreverLauf, reduceCtorEq] at h
  | succ n ih =>
      intro σ ρ σ' h
      simp only [foreverLauf] at h
      split at h
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · have hinv := hi σ ρ
        have hstep := hs (inv σ ρ).1 ρ
        split at h
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1 σ' h)
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1 σ' h)
        · rename_i σ1 ρ1 hs1; simp only [Ausgang.welt, Option.some.injEq] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 v hs1; simp only [Ausgang.welt, Option.some.injEq] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 r hs1; simp only [Ausgang.welt, Option.some.injEq] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · simp only [Ausgang.welt, reduceCtorEq] at h
        · simp only [Ausgang.welt, reduceCtorEq] at h

end Schleifen

/-! ## 5. The two premises: the hardware and the handler -/

/-- **The hardware's half of the frame** (H1, the first two conjuncts of
    `GutO`): an axiom keeps the frame of its declared `effects` and leaves
    the held locks alone. The trace SHAPE of `GutO` is not needed here. -/
def TreuO (O : Orakel D) : Prop :=
  ∀ a σ ρ, Rahmen (D.aschreibt a) (D.agschreibt a) σ (O.wirkt a σ ρ).1 ∧
    (O.wirkt a σ ρ).1.haelt = σ.haelt

theorem gutO_treuO {O : Orakel D} (hO : GutO O) : TreuO O :=
  fun a σ ρ => ⟨(hO a σ ρ).1, (hO a σ ρ).2.1⟩

/-- **The handler's half**, WITHOUT the `HeldB` premise of `GutR`. -/
def TreuR (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ f σ ρ σ', (R f σ ρ).welt = some σ' → Treu (D.schreibt f) (D.gschreibt f) σ σ'

/-! ## 6. THE INDUCTION over the whole grammar -/

section Rumpf
variable (O : Orakel D)

theorem axiomAntwort_treu (hO : TreuO O) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    Treu (D.aschreibt a) (D.agschreibt a) σ (axiomAntwort O a σ ρ).1 := by
  simp only [axiomAntwort]
  exact ⟨(hO a (σ.fragt (.inl a)) ρ).1, (hO a (σ.fragt (.inl a)) ρ).2⟩

variable (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (hR : TreuR R) (hO : TreuO O)
include hR hO
set_option linter.unusedSectionVars false

end Rumpf
end Gabbro.Grammatik
