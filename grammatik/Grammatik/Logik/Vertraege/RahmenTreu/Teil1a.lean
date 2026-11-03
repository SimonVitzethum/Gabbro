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

/-- Release-aware frame for scoped returns: the frame plus a lock release. -/
def TreuRet (W : D.Tab → Bool) (G : D.Glob → Bool) (σ σ' : World D) : Prop :=
  Rahmen W G σ σ' ∧ ∃ Ls : List D.Lock, σ'.haelt = Ls.foldl (fun h L => h.erase L) σ.haelt

theorem TreuRet.refl (W G) (σ : World D) : TreuRet W G σ σ :=
  ⟨Rahmen.refl _ _ _, ⟨[], rfl⟩⟩

/-- `Treu` is `TreuRet` with no release. -/
theorem Treu.toRet {W G} {a b : World D} (h : Treu W G a b) : TreuRet W G a b :=
  ⟨h.1, ⟨[], by simpa using h.2⟩⟩

theorem Treu.transRet {W G} {a b c : World D} (h1 : Treu W G a b) (h2 : TreuRet W G b c) :
    TreuRet W G a c := by
  obtain ⟨Ls, hLs⟩ := h2.2
  exact ⟨h1.1.trans h2.1, ⟨Ls, by rw [hLs, h1.2]⟩⟩

/-- Release then no release is the same release (frame-only). -/
theorem TreuRet.transGut {W G} {a b c : World D} (h1 : TreuRet W G a b) (h2 : Treu W G b c) :
    TreuRet W G a c := by
  obtain ⟨Ls, hLs⟩ := h1.2
  exact ⟨h1.1.trans h2.1, ⟨Ls, by rw [h2.2, hLs]⟩⟩

/-- Single-erase commutes: erasing `M` then `L` is erasing `L` then `M`. -/
theorem erase_comm_single (L M : D.Lock) (h : List D.Lock) :
    (h.erase M).erase L = (h.erase L).erase M := by
  rw [List.erase_comm]

/-- Fold-erase commutes with one more erase. -/
theorem erase_fold_comm (L : D.Lock) (Ms : List D.Lock) (h : List D.Lock) :
    (Ms.foldl (fun h M => h.erase M) h).erase L =
      Ms.foldl (fun h M => h.erase M) (h.erase L) := by
  induction Ms generalizing h with
  | nil => rfl
  | cons M Ms ih =>
      simp only [List.foldl_cons]
      rw [ih]
      rw [List.erase_comm]

/-- Taking `L` then releasing `Ls` and `L` is releasing `Ls`. -/
theorem erase_nimmt_gibt' (L : D.Lock) (Ls : List D.Lock) (h : List D.Lock) :
    (Ls.foldl (fun h M => h.erase M) (L :: h)).erase L =
      Ls.foldl (fun h M => h.erase M) h := by
  induction Ls generalizing h with
  | nil => exact List.erase_cons_head L h
  | cons M Ms ih =>
      simp only [List.foldl_cons]
      by_cases heq : M = L
      · subst heq
        simp only [List.erase_cons_head]
        rw [erase_fold_comm]
      · rw [List.erase_cons_tail (by simpa [beq_iff_eq] using Ne.symm heq)]
        exact ih _

theorem Treu.refl (W G) (σ : World D) : Treu W G σ σ := ⟨Rahmen.refl _ _ _, rfl⟩

theorem Treu.trans {W G} {a b c : World D} (h1 : Treu W G a b) (h2 : Treu W G b c) :
    Treu W G a c := ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩

theorem Treu.weiter {W W' : D.Tab → Bool} {G G' : D.Glob → Bool} {a b : World D}
    (hW : ∀ t, W t = true → W' t = true) (hG : ∀ g, G g = true → G' g = true)
    (h : Treu W G a b) : Treu W' G' a b := ⟨h.1.weiter hW hG, h.2⟩

/-- A releasing frame widens like a plain one (frame-only). -/
theorem TreuRet.weiter {W W' : D.Tab → Bool} {G G' : D.Glob → Bool} {a b : World D}
    (hW : ∀ t, W t = true → W' t = true) (hG : ∀ g, G g = true → G' g = true)
    (h : TreuRet W G a b) : TreuRet W' G' a b := ⟨h.1.weiter hW hG, h.2⟩

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

/-- `locks L { … }` with a releasing body (no rank premise, like `treu_nimmt_gibt`). -/
theorem treu_nimmt_gibtRet {W G} (σ σ1 : World D) (L : D.Lock)
    (h : TreuRet W G (σ.nimmt L) σ1) : TreuRet W G σ (σ1.gibt L) := by
  obtain ⟨Ls, hLs⟩ := h.2
  refine ⟨?_, ?_⟩
  · exact (rahmen_gleich (W := W) (G := G) (σ := σ) (σ' := σ.nimmt L) rfl rfl).trans
      (h.1.trans (rahmen_gleich rfl rfl))
  · refine ⟨Ls, ?_⟩
    show (offen σ1.spur).erase L = Ls.foldl (fun h M => h.erase M) (offen σ.spur)
    have e1 : σ1.haelt = Ls.foldl (fun h M => h.erase M) (L :: σ.haelt) := hLs
    have e2 : σ1.haelt = Ls.foldl (fun h M => h.erase M) (offen (σ.nimmt L).spur) := by
      simp only [World.haelt, World.nimmt, offen] at e1 ⊢
      exact e1
    have e3 : (offen σ1.spur).erase L = Ls.foldl (fun h M => h.erase M) (offen σ.spur) := by
      have := e2
      simp only [World.haelt] at e1
      rw [e1]
      exact erase_nimmt_gibt' L Ls (offen σ.spur)
    exact e3

/-- Guard for `TreuRet`: `GutRet` is at least `TreuRet`. -/
theorem GutRet.treu {W G} {a b : World D} (h : GutRet W G a b) : TreuRet W G a b :=
  ⟨h.1, h.2.1⟩

/-- A read followed by releases is releasing with exactly those scopes (frame-only). -/
theorem treuRet_retScoped {W G} {σ σ1 : World D} (Ls : List D.Lock)
    (hl : Treu W G σ σ1) : TreuRet W G σ (Ls.foldl World.gibt σ1) := by
  refine ⟨hl.1.trans (rahmen_gibt_foldl σ1 Ls), ⟨Ls, ?_⟩⟩
  rw [haelt_gibt_foldl, hl.2]

/-- A release alone is releasing with exactly those scopes (frame-only). -/
theorem treuRet_retWhyScoped {W G} (σ : World D) (Ls : List D.Lock) :
    TreuRet W G σ (Ls.foldl World.gibt σ) := by
  refine ⟨rahmen_gibt_foldl σ Ls, ⟨Ls, ?_⟩⟩
  rw [haelt_gibt_foldl]

/-! ## 3. Outcomes -/

def TreuAusgang (W : D.Tab → Bool) (G : D.Glob → Bool) (σ : World D) (o : Ausgang V l Γ) : Prop :=
  ∀ σ', o.welt = some σ' →
    match o with
    | .zurueck _ _ | .why _ _ => TreuRet W G σ σ'
    | _ => Treu W G σ σ'

def TreuEnd (W : D.Tab → Bool) (G : D.Glob → Bool) (σ : World D) (o : EndAusgang V l Γ) : Prop :=
  ∀ σ', o.welt = some σ' →
    match o with
    | .zurueck _ _ | .why _ _ => TreuRet W G σ σ'
    | _ => Treu W G σ σ'

theorem TreuAusgang.schrumpf {W G} {σ : World D} {o : Ausgang V l (τ :: Γ)}
    (h : TreuAusgang W G σ o) : TreuAusgang W G σ o.schrumpf := by
  intro σ' hs; cases o <;> simp only [Ausgang.welt, Ausgang.schrumpf, Option.some.injEq, reduceCtorEq] at hs ⊢ <;>
    (subst hs; exact h _ rfl)

theorem TreuAusgang.schrumpfArm {W G} {σ : World D} (c : Option Ty)
    {o : Ausgang V l (ArmCtx Γ c)} (h : TreuAusgang W G σ o) :
    TreuAusgang W G σ (o.schrumpfArm c) := by
  cases c with
  | none => exact h
  | some _ => exact h.schrumpf

theorem TreuEnd.schrumpf {W G} {σ : World D} {o : EndAusgang V l (τ :: Γ)}
    (h : TreuEnd W G σ o) : TreuEnd W G σ o.schrumpf := by
  intro σ' hs; cases o <;> simp only [EndAusgang.welt, EndAusgang.schrumpf, Option.some.injEq, reduceCtorEq] at hs ⊢ <;>
    (subst hs; exact h _ rfl)

theorem TreuEnd.zuAusgang {W G} {σ : World D} {o : EndAusgang V l Γ} (h : TreuEnd W G σ o) :
    TreuAusgang W G σ o.zuAusgang := by
  intro σ' hs; cases o <;> simp only [Ausgang.welt, EndAusgang.zuAusgang, Option.some.injEq, reduceCtorEq] at hs ⊢ <;>
    (subst hs; exact h _ rfl)

theorem TreuAusgang.vor {W G} {σ σ1 : World D} {o : Ausgang V l Γ}
    (h1 : Treu W G σ σ1) (h : TreuAusgang W G σ1 o) : TreuAusgang W G σ o := by
  intro σ' hs
  cases o with
  | ok _ _ => exact h1.trans (h _ hs)
  | zurueck _ _ => exact h1.transRet (h _ hs)
  | why _ _ => exact h1.transRet (h _ hs)
  | leave _ _ _ => exact h1.trans (h _ hs)
  | next _ _ _ => exact h1.trans (h _ hs)
  | logik _ => cases hs
  | hardware _ => cases hs

theorem TreuEnd.vor {W G} {σ σ1 : World D} {o : EndAusgang V l Γ}
    (h1 : Treu W G σ σ1) (h : TreuEnd W G σ1 o) : TreuEnd W G σ o := by
  intro σ' hs
  cases o with
  | zurueck _ _ => exact h1.transRet (h _ hs)
  | why _ _ => exact h1.transRet (h _ hs)
  | leave _ _ _ => exact h1.trans (h _ hs)
  | next _ _ _ => exact h1.trans (h _ hs)
  | logik _ => cases hs
  | hardware _ => cases hs

theorem TreuAusgang.gibt {W G} {σ : World D} (L : D.Lock) {o : Ausgang V l Γ}
    (h : TreuAusgang W G (σ.nimmt L) o) : TreuAusgang W G σ (o.mapWelt (·.gibt L)) := by
  intro σ' hs
  cases o with
  | ok _ _ =>
      simp only [Ausgang.welt, Ausgang.mapWelt, Option.some.injEq] at hs ⊢
      subst hs; exact treu_nimmt_gibt _ _ L (h _ rfl)
  | zurueck _ _ =>
      simp only [Ausgang.welt, Ausgang.mapWelt, Option.some.injEq] at hs ⊢
      subst hs; exact treu_nimmt_gibtRet _ _ L (h _ rfl)
  | why _ _ =>
      simp only [Ausgang.welt, Ausgang.mapWelt, Option.some.injEq] at hs ⊢
      subst hs; exact treu_nimmt_gibtRet _ _ L (h _ rfl)
  | leave _ _ _ =>
      simp only [Ausgang.welt, Ausgang.mapWelt, Option.some.injEq] at hs ⊢
      subst hs; exact treu_nimmt_gibt _ _ L (h _ rfl)
  | next _ _ _ =>
      simp only [Ausgang.welt, Ausgang.mapWelt, Option.some.injEq] at hs ⊢
      subst hs; exact treu_nimmt_gibt _ _ L (h _ rfl)
  | logik _ => simp only [Ausgang.welt, Ausgang.mapWelt, reduceCtorEq] at hs
  | hardware _ => simp only [Ausgang.welt, Ausgang.mapWelt, reduceCtorEq] at hs
end Gabbro.Grammatik
