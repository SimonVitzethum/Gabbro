/-
  File:      Grammatik/RahmenTreu.lean
  Subject:   **THE FRAME, AT EVERY WORLD** -- `Rahmen` and the held locks,
             without the lock discipline's `HeldB` premise.

  WHY THIS FILE EXISTS. `Satz.lean` proves ONE theorem about a body run
  (`stmt_gutB`/`block_gutB`/`end_gutB`, `rufAt_gut`) and it bundles THREE
  facts under the name `Gut`:

    1. `Rahmen`  -- the run writes no carrier its contract does not name;
    2. `σ'.haelt = σ.haelt` -- every lock it took it gave back;
    3. every event it left is GOOD and the trace stays consistent.

  Fact 3 is what needs the lock discipline: an access event is good only if
  the locks its `Λ` names are HELD, and a `nimmt` event is good only if the
  lock ranks strictly above everything held. So the whole theorem carries
  `HeldB bo Λ σ.haelt` -- a premise about the ENTRY WORLD.

  Facts 1 and 2 do not need it, and this file says so by proving them alone,
  by the same induction with the premise deleted:

    * a write goes to a carrier the constructor's own `hw : V.schreibt t =
      true` names -- nothing about locks;
    * a read (`lese`) appends `zugriff` events, which `offen` ignores
      (`lese_haelt`);
    * `locks L { .. }` is `nimmt L`, the body, `gibt L`, and
      `offen (gibt L :: nimmt L h :: s) = (L :: offen s).erase L = offen s`
      -- `List.erase` takes the FIRST occurrence, so this holds even at a
      world that ALREADY holds `L`. (Such a world is not well-disciplined,
      and `Gut` rightly refuses it: the `nimmt` event is not good there. But
      the frame and the held set survive it.)

  WHAT IT BUYS. `RufRahmenTreu P (rufAt P O passes n)` -- the frame half of
  `RespektiertRahmen` for the model's own call handler, at EVERY world --
  which `rufAt_gut` gives only at worlds meeting
  `HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) σ.haelt`.
  Part 4 of the closing theorem quantifies over ANY Gabbro world, so it was
  carried as a named hypothesis of `rufAt_nurAbstieg` (RufLogik.lean) until
  this file. See `messung/muse/OPUS-BERICHT-RAHMEN.md`.

  THE ONE PREMISE THAT STAYS is the hardware's: an axiom answer keeps the
  frame of its `effects` and leaves the held locks alone (`TreuO`, the first
  two conjuncts of `GutO`). That is H1 and it is named, not hidden.
-/
import Grammatik.Satz

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
    (treu_merke _ _ (by intro e he; simp at he; subst he; simp [Ereignis.zugriffMit]; rfl))

theorem treu_schreibGlob {W G} (σ : World D) (g : D.Glob) (Λ : List (Res D))
    (v : Wert D (D.gtyp g)) (hg : G g = true) : Treu W G σ (σ.schreibGlob g Λ v) :=
  Treu.trans ⟨rahmen_storeGlob W G σ g v hg, rfl⟩
    (treu_merke _ _ (by intro e he; simp at he; subst he; simp [Ereignis.zugriffMit]; rfl))

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
  intro σ' hs; cases o <;> simp [Ausgang.schrumpf, Ausgang.welt] at hs ⊢ <;>
    (subst hs; exact h _ rfl)

theorem TreuAusgang.schrumpfArm {W G} {σ : World D} (c : Option (Int × Int))
    {o : Ausgang V l (ArmCtx Γ c)} (h : TreuAusgang W G σ o) :
    TreuAusgang W G σ (o.schrumpfArm c) := by
  cases c with
  | none => exact h
  | some p => obtain ⟨_, _⟩ := p; exact h.schrumpf

theorem TreuEnd.schrumpf {W G} {σ : World D} {o : EndAusgang V l (τ :: Γ)}
    (h : TreuEnd W G σ o) : TreuEnd W G σ o.schrumpf := by
  intro σ' hs; cases o <;> simp [EndAusgang.schrumpf, EndAusgang.welt] at hs ⊢ <;>
    (subst hs; exact h _ rfl)

theorem TreuEnd.zuAusgang {W G} {σ : World D} {o : EndAusgang V l Γ} (h : TreuEnd W G σ o) :
    TreuAusgang W G σ o.zuAusgang := by
  intro σ' hs; cases o <;> simp [EndAusgang.zuAusgang, Ausgang.welt] at hs ⊢ <;>
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
  cases o <;> simp [Ausgang.mapWelt, Ausgang.welt] at hs ⊢ <;>
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
      · simp [Ausgang.welt] at h
  | cons k ks ih =>
      intro σ ρ σ' h
      simp only [traverseLauf] at h
      split at h
      · simp [Ausgang.welt] at h
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
          split at h <;> simp [Ausgang.welt] at h
          subst h; exact g1.trans (hi σ1 ρ1.tail)
        · rename_i σ1 v hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 r hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · simp [Ausgang.welt] at h
        · simp [Ausgang.welt] at h

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
      · simp [Ausgang.welt] at h; subst h; exact hb σ ρ
      · have hinv := hb σ ρ
        have hstep := hs (bis σ ρ).1 ρ
        split at h
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1 σ' h)
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1 σ' h)
        · rename_i σ1 ρ1 hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 v hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 r hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · simp [Ausgang.welt] at h
        · simp [Ausgang.welt] at h

theorem foreverLauf_treu (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, TreuAusgang W G σ (schritt σ ρ))
    (hi : ∀ σ ρ, Treu W G σ (inv σ ρ).1) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      TreuAusgang W G σ (foreverLauf (l := l) a schritt inv n σ ρ) := by
  intro n
  induction n with
  | zero => intro σ ρ σ' h; simp [foreverLauf, Ausgang.welt] at h
  | succ n ih =>
      intro σ ρ σ' h
      simp only [foreverLauf] at h
      split at h
      · simp [Ausgang.welt] at h
      · have hinv := hi σ ρ
        have hstep := hs (inv σ ρ).1 ρ
        split at h
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1 σ' h)
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1 σ' h)
        · rename_i σ1 ρ1 hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 v hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 r hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · simp [Ausgang.welt] at h
        · simp [Ausgang.welt] at h

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
  exact ⟨(hO a σ ρ).1, (hO a σ ρ).2⟩

variable (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (hR : TreuR R) (hO : TreuO O)
include hR hO
set_option linter.unusedSectionVars false

mutual

/-- **The frame and the held locks of one statement**, at EVERY world. -/
theorem stmt_treu :
    ∀ (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ),
    TreuAusgang V.schreibt V.gschreibt σ (execStmt O passes R s σ ρ)
  | .assignSlot t f i e hw hL, σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _).trans
        (treu_schreibSlot _ t Λ _ f _ hw)
  | .assignDurch p t _ f i e hw hL, σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _).trans
        (treu_schreibSlot _ t Λ _ f _ hw)
  | .assignGlob g e hw hL, σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _).trans
        (treu_schreibGlob _ g Λ _ hw)
  | .schreibBytes t f hf n i _ _ e hw hL, σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _).trans
        (treu_schreibBytes _ t f hf Λ hw _ _)
  | .assignVar x e, σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact treu_lese σ Λ _
  | .uebergang t f hτ i von nach hn he hw hL, σ, ρ, σ', h => by
      simp only [execStmt] at h
      split at h
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        exact (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _).trans
          (treu_schreibSlot _ t Λ _ f _ hw)
      · simp [Ausgang.welt] at h
  | .ite c t e, σ, ρ, σ', h => by
      simp only [execStmt] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ c.orte
      split at h
      · exact (TreuAusgang.vor hl (block_treu t _ ρ)) σ' h
      · exact (TreuAusgang.vor hl (block_treu e _ ρ)) σ' h
  | .onOption o p a, σ, ρ, σ', h => by
      simp only [execStmt] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ o.orte
      split at h
      · exact (TreuAusgang.vor hl (block_treu p _ _)).schrumpf σ' h
      · exact (TreuAusgang.vor hl (block_treu a _ ρ)) σ' h
  | .onTag v arms, σ, ρ, σ', h => by
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ v.orte
      exact (TreuAusgang.vor hl (arms_treu arms _ _ ρ)) σ' h
  | .onGrund r arms, σ, ρ, σ', h => by
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ r.orte
      exact (TreuAusgang.vor hl (grund_treu arms _ _ ρ)) σ' h
  | .call f args hp hr, σ, ρ, σ', h => by
      simp only [execStmt] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      split at h
      · rename_i σ1 v hR1
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        exact hl.trans (Treu.weiter hp.hw hp.hg
          (hR f (σ.lese Λ args.orte) _ σ1 (by rw [hR1]; rfl)))
      · rename_i σ1 r _; exact keinGrund hr r
      · simp [Ausgang.welt] at h
      · simp [Ausgang.welt] at h
  | .callInd p args hp hr, σ, ρ, σ', h => by
      simp only [execStmt] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (p.orte ++ args.orte)
      generalize hpv : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pv at h
      obtain ⟨f, hf⟩ := pv
      simp only at h
      split at h
      · rename_i σ1 v hR1
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        subst hf
        exact hl.trans (Treu.weiter hp.hw hp.hg
          (hR f (σ.lese Λ (p.orte ++ args.orte)) _ σ1 (by rw [hR1]; rfl)))
      · rename_i σ1 r _; exact keinGrundSig hf hr r
      · simp [Ausgang.welt] at h
      · simp [Ausgang.welt] at h
  | .locks L hr body, σ, ρ, σ', h =>
      (TreuAusgang.gibt L (block_treu body (σ.nimmt L) ρ)) σ' h
  | .breaking _ body, σ, ρ, σ', h => block_treu body σ ρ σ' h
  | .traverse t inv body, σ, ρ, σ', h =>
      traverseLauf_treu _ _ (fun σ ρ => block_treu body σ ρ)
        (fun σ ρ => treu_lese σ Λ inv.orte) _ σ ρ σ' h
  | .retry n bis body ueberlauf, σ, ρ, σ', h =>
      retryLauf_treu _ _ _ (fun σ ρ => block_treu body σ ρ)
        (fun σ ρ => treu_lese σ Λ bis.orte)
        (fun σ ρ => block_treu ueberlauf σ ρ) n σ ρ σ' h
  | .forever a inv body, σ, ρ, σ', h =>
      foreverLauf_treu a _ _ (fun σ ρ => block_treu body σ ρ)
        (fun σ ρ => treu_lese σ Λ inv.orte) passes σ ρ σ' h
  | .axiomCall a args _ hw hg hd hgd, σ, ρ, σ', h => by
      simp only [execStmt] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      split at h
      · rename_i σ1 v ha
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        have := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
        rw [ha] at this
        exact hl.trans (Treu.weiter hw hg this)
      · simp [Ausgang.welt] at h
  | .regSchreib r _ e, σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact treu_lese σ Λ _
  | .transition .., σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .publish g e _ _ hw hL, σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _).trans
        (treu_schreibGlob _ g Λ _ hw)
  | .advances .., σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .retires .., σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .ret e _, σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact treu_lese σ Λ _
  | .retGrund .., σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .leave _, σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .next _, σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _

theorem block_treu :
    ∀ (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ),
    TreuAusgang V.schreibt V.gschreibt σ (execBlock O passes R b σ ρ)
  | .nil, σ, ρ, σ', h => by
      simp only [execBlock, Ausgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .cons s rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      split at h
      · rename_i σ1 ρ1 hs
        have g1 := stmt_treu s σ ρ σ1 (by rw [hs]; rfl)
        exact g1.trans (block_treu rest σ1 ρ1 σ' h)
      · subst_vars
        exact stmt_treu s σ ρ σ' h
  | .bind e rest, σ, ρ, σ', h => by
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
      exact (TreuAusgang.vor hl (block_treu rest _ _)).schrumpf σ' h
  | .bindCall f args he hp hr rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      split at h
      · rename_i σ1 v hR1
        have g1 := hl.trans (Treu.weiter hp.hw hp.hg
          (hR f (σ.lese Λ args.orte) _ σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((block_treu rest σ1 _).schrumpf σ' h)
      · rename_i σ1 r _; exact keinGrund hr r
      · simp [Ausgang.welt] at h
      · simp [Ausgang.welt] at h
  | .bindCallInd p args he hp hr rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (p.orte ++ args.orte)
      generalize hpv : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pv at h
      obtain ⟨f, hf⟩ := pv
      simp only at h
      split at h
      · rename_i σ1 v hR1
        have g2 := block_treu rest σ1 (.cons (ergWert (ergSig hf he) v) ρ)
        subst hf
        have g1 := hl.trans (Treu.weiter hp.hw hp.hg
          (hR f (σ.lese Λ (p.orte ++ args.orte)) _ σ1 (by rw [hR1]; rfl)))
        exact g1.trans (g2.schrumpf σ' h)
      · rename_i σ1 r _; exact keinGrundSig hf hr r
      · simp [Ausgang.welt] at h
      · simp [Ausgang.welt] at h
  | .bindCallElse f args he hp _ err rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      split at h
      · rename_i σ1 v hR1
        have g1 := hl.trans (Treu.weiter hp.hw hp.hg
          (hR f (σ.lese Λ args.orte) _ σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((block_treu rest σ1 _).schrumpf σ' h)
      · rename_i σ1 r hR1
        have g1 := hl.trans (Treu.weiter hp.hw hp.hg
          (hR f (σ.lese Λ args.orte) _ σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((end_treu err σ1 _).schrumpf.zuAusgang σ' h)
      · simp [Ausgang.welt] at h
      · simp [Ausgang.welt] at h
  | .bindAxiom a args he hw hg hd hgd rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      split at h
      · rename_i σ1 v ha
        have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
        rw [ha] at h1
        have g1 := hl.trans (Treu.weiter hw hg h1)
        exact g1.trans ((block_treu rest σ1 _).schrumpf σ' h)
      · simp [Ausgang.welt] at h
  | .regLies r _ rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      split at h
      · split at h
        · exact (block_treu rest σ _).schrumpf σ' h
        · simp [Ausgang.welt] at h
      · simp [Ausgang.welt] at h
  | .regLiesElse r _ zusage sonst rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      split at h
      · have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ zusage.orte
        split at h
        · exact (TreuAusgang.vor hl (block_treu rest _ _)).schrumpf σ' h
        · exact (TreuEnd.vor hl (end_treu sonst _ ρ)).zuAusgang σ' h
      · simp [Ausgang.welt] at h
  | .awaits g _ _ hL rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      split at h
      · have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ [.inr g]
        exact (TreuAusgang.vor hl (block_treu rest _ _)).schrumpf σ' h
      · simp [Ausgang.welt] at h
  | .exchange g neu hw hL rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (.inr g :: neu.orte)
      have g1 := hl.trans (treu_schreibGlob (W := V.schreibt) (G := V.gschreibt)
        (σ.lese Λ (.inr g :: neu.orte)) g Λ (eval (σ.lese Λ (.inr g :: neu.orte)) neu
          (σ.lese Λ (.inr g :: neu.orte)) (.cons ((σ.lese Λ (.inr g :: neu.orte)).globs g) ρ))
          hw)
      exact (TreuAusgang.vor g1 (block_treu rest _ _)).schrumpf σ' h
  | .narrow e lo' hi' sonst rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
      split at h
      · exact (TreuAusgang.vor hl (block_treu rest _ _)).schrumpf σ' h
      · exact (TreuEnd.vor hl (end_treu sonst _ ρ)).zuAusgang σ' h
  | .pruefung c sonst rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ c.orte
      split at h
      · exact (TreuAusgang.vor hl (block_treu rest _ ρ)) σ' h
      · exact (TreuEnd.vor hl (end_treu sonst _ ρ)).zuAusgang σ' h
  | .gleit op a b lo hi rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (a.orte ++ b.orte)
      split at h
      · exact (TreuAusgang.vor hl (block_treu rest _ _)).schrumpf σ' h
      · simp [Ausgang.welt] at h
  | .gleitLit q lo hi rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      split at h
      · exact (block_treu rest σ _).schrumpf σ' h
      · simp [Ausgang.welt] at h
  | .gleitVon e lo hi rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
      split at h
      · exact (TreuAusgang.vor hl (block_treu rest _ _)).schrumpf σ' h
      · simp [Ausgang.welt] at h
  | .gleitNarrow e lo hi sonst rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
      split at h
      · exact (TreuAusgang.vor hl (block_treu rest _ _)).schrumpf σ' h
      · exact (TreuEnd.vor hl (end_treu sonst _ ρ)).zuAusgang σ' h

theorem end_treu :
    ∀ (b : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ),
    TreuEnd V.schreibt V.gschreibt σ (execEnd O passes R b σ ρ)
  | .ret e _, σ, ρ, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h
      exact treu_lese σ Λ _
  | .retGrund .., σ, ρ, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .leave _, σ, ρ, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .next _, σ, ρ, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .cons s rest, σ, ρ, σ', h => by
      simp only [execEnd] at h
      have hs := stmt_treu s σ ρ
      split at h
      · rename_i σ1 ρ1 hs1
        have g1 := hs σ1 (by rw [hs1]; rfl)
        exact g1.trans (end_treu rest σ1 ρ1 σ' h)
      all_goals first
        | (rename_i hs1; simp only [EndAusgang.welt, Option.some.injEq] at h; subst h
           exact hs _ (by rw [hs1]; rfl))
        | (simp [EndAusgang.welt] at h)
  | .bind e rest, σ, ρ, σ', h => by
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
      exact (TreuEnd.vor hl (end_treu rest _ _)).schrumpf σ' h

theorem arms_treu :
    ∀ (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)) (σ : World D) (ρ : Env D Γ),
    TreuAusgang V.schreibt V.gschreibt σ (execArms O passes R arms v σ ρ)
  | .cons b _, ⟨⟨0, _⟩, _⟩, σ, _, σ', h => (block_treu b σ _).schrumpfArm _ σ' h
  | .cons _ rest, ⟨⟨_ + 1, _⟩, _⟩, σ, ρ, σ', h => arms_treu rest _ σ ρ σ' h

theorem grund_treu :
    ∀ (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n) (σ : World D) (ρ : Env D Γ),
    TreuAusgang V.schreibt V.gschreibt σ (execGrund O passes R arms r σ ρ)
  | .cons b _, ⟨0, _⟩, σ, ρ, σ', h => block_treu b σ ρ σ' h
  | .cons _ rest, ⟨_ + 1, _⟩, σ, ρ, σ', h => grund_treu rest _ σ ρ σ' h

end

end Rumpf

/-! ## 7. THE CALL, at every world -/

/-- **THE FRAME OF A CALL, AT EVERY WORLD.** `rufAt_gut` (Satz.lean) proves
    the same and more at worlds meeting `HeldB`; this proves the frame and
    the held locks at ALL of them, by the same induction on the depth. The
    only premise is the hardware's (H1). -/
theorem rufAt_treu (P : Programm D) (O : Orakel D) (passes : Nat) (hO : TreuO O) :
    ∀ fuel, TreuR (rufAt P O passes fuel) := by
  intro fuel
  induction fuel with
  | zero => intro f σ ρ σ' h; simp [rufAt, RufAusgang.welt] at h
  | succ n ih =>
      intro f σ ρ σ' h
      simp only [rufAt] at h
      have g0 : Treu (D.schreibt f) (D.gschreibt f) σ
          (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) := treu_lese _ _ _
      split at h
      · simp [RufAusgang.welt] at h
      · have hb := end_treu O passes (rufAt P O passes n) ih hO (P.rumpf f)
          (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ
        split at h
        · rename_i σ2 v hs
          have g2 : Treu (D.schreibt f) (D.gschreibt f) _ σ2 := hb σ2 (by rw [hs]; rfl)
          have g3 : Treu (D.schreibt f) (D.gschreibt f) σ2
              (σ2.lese (vertragVon D f).ende (P.ensures f).orte) :=
            treu_lese σ2 (vertragVon D f).ende (P.ensures f).orte
          split at h
          · simp [RufAusgang.welt] at h
          · have g4 : Treu (D.schreibt f) (D.gschreibt f) _
                ((D.invs.filter (schuldet f)).foldl
                  (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
                  (σ2.lese (vertragVon D f).ende (P.ensures f).orte)) :=
              treu_foldl_lese P (D.invs.filter (schuldet f)) _
            split at h
            · simp [RufAusgang.welt] at h
            · simp only [RufAusgang.welt, Option.some.injEq] at h; subst h
              exact ((g0.trans g2).trans g3).trans g4
        · rename_i σ2 r hs
          simp only [RufAusgang.welt, Option.some.injEq] at h; subst h
          exact g0.trans (hb _ (by rw [hs]; rfl))
        · rename_i hl _ _ _; exact absurd hl (by decide)
        · rename_i hl _ _ _; exact absurd hl (by decide)
        · simp [RufAusgang.welt] at h
        · simp [RufAusgang.welt] at h

#print axioms Gabbro.Grammatik.rufAt_treu

end Gabbro.Grammatik
