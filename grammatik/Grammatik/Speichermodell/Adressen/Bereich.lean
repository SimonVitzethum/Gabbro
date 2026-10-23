/-
  File:      Grammatik/Speichermodell/Adressen/Bereich.lean
  Subject:   NOTHING OUTSIDE THE DECLARED EXTENTS IS EVER WRITTEN (2026-10-22, review of gabbro_ziel, point 3).

  The memory of machine G is a function on EVERY index of a table (`Speicher.slots : ∀ t, Int → …`); the declared
  extent of table `t` is `0 ..< D.count t`. An index outside it has no address in a real memory (Layout.lean): a
  write there would land in another carrier. Here: no step of machine G or GX writes such a cell, provided foreign
  code does not (`ImBereichO`, a named assumption about the oracle: what an `axiom` body writes is the hardware's
  and the foreign code's, as everything else `wirkt` answers).

  * `AussenGleich s s'` -- `s` and `s'` agree on every cell outside the declared extents;
  * `execStmt_blatt_aussen` -- a leaf writes inside the extents: every index it writes has an index type
    (`assignSlot`, `assignThru`, `shift`), or lies in the checked byte range (`putBytes`), or comes from the oracle;
  * `rufSchrittG_aussen`, `rufSchrittGX_aussen` -- every step of machine G and GX;
  * `rufErreichbarGX_aussen` -- every reached machine agrees with its start outside the extents.
-/
import Grammatik.Speichermodell.Maschine.GXMaschine

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The extents -/

/-- Index `k` lies in the declared extent of table `t`. -/
def ImBereich (D : Deklaration) (t : D.Tab) (k : Int) : Prop := 0 ≤ k ∧ k < D.count t

/-- Two memories agree on every cell outside the declared extents. -/
def AussenGleich (s s' : Speicher D) : Prop :=
  ∀ t k (f : D.Feld t), ¬ ImBereich D t k → s'.slots t k f = s.slots t k f

/-- **Foreign code writes inside the declared extents** (a named assumption, inside the leg that uses it). -/
def ImBereichO (O : Orakel D) : Prop :=
  ∀ a σ ρ t k (f : D.Feld t), ¬ ImBereich D t k → ((O.wirkt a σ ρ).1).slots t k f = σ.slots t k f

theorem AussenGleich.refl (s : Speicher D) : AussenGleich s s := fun _ _ _ _ => rfl

theorem AussenGleich.trans {a b c : Speicher D} (h1 : AussenGleich a b) (h2 : AussenGleich b c) :
    AussenGleich a c := fun t k f h => (h2 t k f h).trans (h1 t k f h)

/-! ## 2. Writes -/

theorem storeSlot_aussen (σ : World D) (t : D.Tab) (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f))
    (hk : ImBereich D t k) : AussenGleich σ.speicher (σ.storeSlot t k f v).speicher := by
  intro t' k' f' h'
  show (σ.storeSlot t k f v).slots t' k' f' = σ.slots t' k' f'
  unfold World.storeSlot
  by_cases ht : t' = t
  · subst ht
    have hk' : k' ≠ k := fun e => h' (e ▸ hk)
    simp [hk']
  · simp [ht]

theorem schreibSlot_aussen (σ : World D) (t : D.Tab) (Λ : List (Res D)) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f)) (hk : ImBereich D t k) : AussenGleich σ.speicher (σ.schreibSlot t Λ k f v).speicher :=
  storeSlot_aussen σ t k f v hk

theorem schreibBytes_aussen (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) (Λ : List (Res D)) :
    ∀ (bs : List Byte) (σ : World D) (k : Int), 0 ≤ k → k + bs.length ≤ D.count t →
      AussenGleich σ.speicher (σ.schreibBytes t f hf Λ k bs).speicher
  | [], σ, _, _, _ => AussenGleich.refl _
  | b :: bs, σ, k, h0, h1 => by
      simp only [List.length_cons] at h1
      have h2 := schreibBytes_aussen t f hf Λ bs
        (σ.schreibSlot t Λ k f (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))) (k + 1)
        (by omega) (by omega)
      exact (schreibSlot_aussen σ t Λ k f _ ⟨h0, by omega⟩).trans h2

theorem lese_speicher (σ : World D) (Λ : List (Res D)) (orte : List (D.Tab ⊕ D.Glob)) :
    (σ.lese Λ orte).speicher = σ.speicher := rfl

theorem index_imBereich {t : D.Tab} (z : Wert D (.index (D.count t))) : ImBereich D t z.n :=
  ⟨z.lo_le, by have := z.le_hi; omega⟩

/-! ## 3. Leaves -/

/-- **A leaf writes inside the declared extents.** -/
theorem execStmt_blatt_aussen {O : Orakel D} (hI : ImBereichO O) (p : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (hleaf : s.istBlatt = true) (σ : World D) (ρ : Env D Γ)
    {σ' : World D} {ρ' : Env D Γ}
    (h : execStmt O p R s σ ρ = .ok σ' ρ') : AussenGleich σ.speicher σ'.speicher := by
  cases s with
  | assignSlot t f i e _ _ =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact schreibSlot_aussen (σ.lese Λ _) t Λ _ f _ (index_imBereich _)
  | assignThru pp t _ f i e _ _ =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact schreibSlot_aussen (σ.lese Λ _) t Λ _ f _ (index_imBereich _)
  | assignGlob g e _ _ =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact AussenGleich.refl _
  | putBytes t f hf n i hlo hhi e _ _ =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, -⟩ := h
      refine schreibBytes_aussen t f hf Λ _ _ _ ?_ ?_
      · exact Int.le_trans hlo (eval _ i _ ρ).lo_le
      · rw [zahlZuBytes_length]; have := (eval (σ.lese Λ (i.orte ++ e.orte)) i (σ.lese Λ (i.orte ++ e.orte)) ρ).le_hi
        omega
  | assignVar x e =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact AussenGleich.refl _
  | shift t f hτ i von nach hn _ _ _ =>
      simp only [execStmt] at h
      split at h
      · simp only [Ausgang.ok.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact schreibSlot_aussen (σ.lese Λ _) t Λ _ f _ (index_imBereich _)
      · cases h
  | axiomCall a args _ _ _ _ _ =>
      simp only [execStmt] at h
      split at h
      · rename_i σ'' v hax
        simp only [Ausgang.ok.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simp only [axiomAntwort] at hax
        have e1 := congrArg Prod.fst hax
        simp only at e1
        rw [← e1]
        exact fun t k f hk => hI a _ _ t k f hk
      · cases h
  | regWrite r _ e =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact AussenGleich.refl _
  | transition r _ m _ _ maske bits =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact AussenGleich.refl _
  | publish g e _ _ _ _ =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact AussenGleich.refl _
  | advances _ _ _ _ =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact AussenGleich.refl _
  | retires _ _ _ _ =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact AussenGleich.refl _
  | ret e _ => simp [execStmt] at h
  | retWhy r _ => simp [execStmt] at h
  | leave _ => simp [execStmt] at h
  | next _ => simp [execStmt] at h
  | _ => simp [Stmt.istBlatt] at hleaf

/-! ## 4. Every step -/

theorem axiomAntwort_aussen {O : Orakel D} (hI : ImBereichO O) {a : D.Ax} {σ σ₂ : World D}
    {ρ : Env D (D.aparams a)} {r : Option (ErgVal D (D.aerg a))} (hax : axiomAntwort O a σ ρ = (σ₂, r)) :
    AussenGleich σ.speicher σ₂.speicher := by
  have e := congrArg Prod.fst hax
  simp only [axiomAntwort] at e
  rw [← e]
  exact fun t k f hk => hI a σ ρ t k f hk

theorem axiomAntwortSonst_aussen {O : Orakel D} (hI : ImBereichO O) {a : D.Ax} {σ σ₂ : World D}
    {ρ : Env D (D.aparams a)} {r : Option (ErgVal D (D.aerg a) ⊕ Fin (D.agruende a))}
    (hax : axiomAntwortSonst O a σ ρ = (σ₂, r)) : AussenGleich σ.speicher σ₂.speicher := by
  have e := congrArg Prod.fst hax
  simp only [axiomAntwortSonst] at e
  rw [← e]
  exact fun t k f hk => hI a σ ρ t k f hk

theorem execStmt_leave_welt {O : Orakel D} {p : Nat} {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)} {hl hl' : true = true} {σ σ' : World D} {ρ ρ' : Env D Γ}
    (h : execStmt O p R ((.leave hl) : Stmt D V true Γ Λ Λ) σ ρ = Ausgang.leave hl' σ' ρ') : σ' = σ := by
  simp only [execStmt, Ausgang.leave.injEq] at h
  exact h.1.symm

theorem execStmt_next_welt {O : Orakel D} {p : Nat} {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)} {hl hl' : true = true} {σ σ' : World D} {ρ ρ' : Env D Γ}
    (h : execStmt O p R ((.next hl) : Stmt D V true Γ Λ Λ) σ ρ = Ausgang.next hl' σ' ρ') : σ' = σ := by
  simp only [execStmt, Ausgang.next.injEq] at h
  exact h.1.symm

/-- One case of `rufSchrittG_aussen`. -/
macro "aussen_fall" hI:term : tactic => `(tactic| first
  | exact AussenGleich.refl _
  | (subst_vars; exact AussenGleich.refl _)
  | exact execStmt_blatt_aussen $hI _ _ _ ‹_› _ _ ‹_›
  | (subst_vars; exact axiomAntwort_aussen $hI ‹_›)
  | (subst_vars; exact axiomAntwortSonst_aussen $hI ‹_›)
  | (subst_vars; have e := execStmt_leave_welt (by assumption); rw [e]; exact AussenGleich.refl _)
  | (subst_vars; have e := execStmt_next_welt (by assumption); rw [e]; exact AussenGleich.refl _)
  | (have e := execStmt_leave_welt (by assumption); rw [e]; exact AussenGleich.refl _)
  | (have e := execStmt_next_welt (by assumption); rw [e]; exact AussenGleich.refl _))

set_option maxHeartbeats 4000000 in
/-- **Every step of machine G writes inside the declared extents.** -/
theorem rufSchrittG_aussen {P : Programm D} {O : Orakel D} {p : Nat} (hI : ImBereichO O) {M M' : RufMaschineG D}
    {u : Faden} (h : RufSchrittG P O p M u M') : AussenGleich M.speicher M'.speicher := by
  cases h <;> aussen_fall hI

/-- **Every step of machine GX**: the presented memory differs from the actual one only at shared atomics, and
    they are globals. -/
theorem rufSchrittGX_aussen {P : Programm D} {O : Orakel D} {p : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    (hTg : ∀ t, ¬ Tg (.inl t)) (hI : ImBereichO O) {M M' : RufMaschineG D} {u : Faden}
    (h : RufSchrittGX P O p Tg M u M') : AussenGleich M.speicher M'.speicher := by
  obtain ⟨σ, M'', hs, hσ, h1, h2, -, -, -⟩ := h
  have hG := rufSchrittG_aussen hI hs
  intro t k f hk
  have eσ : σ.slots t = M.speicher.slots t := hσ (.inl t) (hTg t)
  by_cases hw : SchreibG (mitSpeicher M σ) M'' u (.inl t)
  · have e1 : M'.speicher.slots t = M''.speicher.slots t := h1 _ hw
    rw [e1, hG t k f hk]
    show σ.slots t k f = M.speicher.slots t k f
    rw [eσ]
  · have e2 : M'.speicher.slots t = M.speicher.slots t := h2 _ hw
    rw [e2]

/-- **Every machine GX reaches agrees with its start outside the declared extents.** -/
theorem rufErreichbarGX_aussen {P : Programm D} {O : Orakel D} {p : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    (hTg : ∀ t, ¬ Tg (.inl t)) (hI : ImBereichO O) {M0 M : RufMaschineG D}
    (h : RufErreichbarGX P O p Tg M0 M) : AussenGleich M0.speicher M.speicher := by
  induction h with
  | start => exact AussenGleich.refl _
  | schritt M M' u _ hs ih => exact ih.trans (rufSchrittGX_aussen hTg hI hs)

end Gabbro.Grammatik
