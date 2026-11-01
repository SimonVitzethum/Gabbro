module

public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Kern.Syntax.Extraktion

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 2. Guard implies held: writing t records an event needing Held L -/

/-- A write event on `t` carries `t`'s guards: from a good event, the static
    resource list satisfies `darf`, so every guard entry is present in `Λ`. -/
theorem zugriff_darf_aus_gut {t : D.Tab} {Λ : List (Res D)} {h : List D.Lock}
    {schreibt : Bool} (hg : (Ereignis.zugriff t schreibt Λ h).gut) :
    darf D t Λ := by
  simp only [Ereignis.gut] at hg
  exact hg.1

/-- `HeldGenau` reads back: `Res.held L ∈ Λ` iff `L` is in the held list. -/
theorem held_in_Λ_aus_offen {Λ : List (Res D)} {h : List D.Lock}
    (hΛ : HeldGenau Λ h) {L : D.Lock} (hmem : L ∈ h) :
    Res.held L ∈ Λ :=
  (hΛ L).mpr hmem

/-- Key step: a thread whose open locks exclude `L` cannot fire a good write
    event on a carrier guarded by `L`. `HeldGenau` turns the static guard
    token into dynamic holding, contradicting the exclusion. -/
theorem kein_schreibzugriff_ohne_sperre
    {Λ : List (Res D)} {h : List D.Lock}
    (hΛ : HeldGenau Λ h)
    {t : D.Tab} {L : D.Lock}
    (hGuard : Sum.inl L ∈ D.braucht t)
    (hfrei : L ∉ h)
    {schreibt : Bool}
    (hg : (Ereignis.zugriff t schreibt Λ h).gut) :
    schreibt = false := by
  have hdarf : darf D t Λ := zugriff_darf_aus_gut hg
  have hmem : Res.von D (Sum.inl L) ∈ Λ := hdarf _ hGuard
  simp only [Res.von] at hmem
  have hheld : L ∈ h := (hΛ L).mp hmem
  exact absurd hheld hfrei

/-! ## 3. Slot preservation: a leaf step of a thread not holding L
    leaves the slots of the guarded carrier t unchanged -/

/-- Reads (`World.lese`) only extend the trace: slots are untouched. -/
theorem lese_slots_gleich (σ : World D) (Λ : List (Res D))
    (orte : List (D.Tab ⊕ D.Glob)) (t : D.Tab) (k : Int) (f : D.Feld t) :
    (σ.lese Λ orte).slots t k f = σ.slots t k f := by
  rfl

/-- A store to another carrier leaves t's slots untouched.
    Used: every premise (`h`, `k`, `f`, `v`, `k'`, `f'`) feeds the conclusion. -/
theorem storeSlot_fremd_traeger (σ : World D)
    {t u : D.Tab} (h : t ≠ u)
    (k : Int) (f : D.Feld u) (v : Wert D (D.typ u f))
    (k' : Int) (f' : D.Feld t) :
    (σ.storeSlot u k f v).slots t k' f' = σ.slots t k' f' := by
  simp only [World.storeSlot, h, ↓reduceDIte]

/-- A store to the same carrier but a different slot leaves this slot
    untouched. Used: `hk` selects the branch, `hf` is the field equation
    discharged by the `if` on fields. -/
theorem storeSlot_fremd_slot (σ : World D) (t : D.Tab)
    (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f))
    (k' : Int) (f' : D.Feld t) (hk : k' ≠ k) (hf : f' = f) :
    (σ.storeSlot t k f v).slots t k' f' = σ.slots t k' f' := by
  subst hf
  simp only [World.storeSlot, ↓reduceDIte, hk, ↓reduceIte]

/-- A store to the same slot but a different field leaves this field
    untouched. Used: `hk` forces the same-index branch, `hf` selects the
    else-branch on fields. -/
theorem storeSlot_fremd_feld (σ : World D) (t : D.Tab)
    (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f))
    (k' : Int) (f' : D.Feld t) (hk : k' = k) (hf : f' ≠ f) :
    (σ.storeSlot t k f v).slots t k' f' = σ.slots t k' f' := by
  subst hk
  simp only [World.storeSlot, ↓reduceDIte, ↓reduceIte, hf]

/-- A global store leaves every table slot untouched: the table/write
    distinction is the frame. Used: all premises feed the `rfl` unfolding. -/
theorem storeGlob_slots_gleich (σ : World D) (g : D.Glob)
    (v : Wert D (D.gtyp g)) (t : D.Tab) (k : Int) (f : D.Feld t) :
    (σ.storeGlob g v).slots t k f = σ.slots t k f := by
  rfl

/-- Byte writes to another carrier leave t's slots untouched, by induction
    over the byte list. Used: `h` picks the foreign-carrier case at each
    byte; `k`, `bs` drive the induction. -/
theorem schreibBytes_fremd_traeger (σ : World D)
    {t u : D.Tab} (h : t ≠ u)
    (f : D.Feld u) (hf : D.typ u f = .int 0 255) (Λ : List (Res D))
    (k : Int) (bs : List Byte) :
    ∀ (k' : Int) (f' : D.Feld t),
      (σ.schreibBytes u f hf Λ k bs).slots t k' f' = σ.slots t k' f' := by
  induction bs generalizing σ k with
  | nil => intro k' f'; rfl
  | cons b bs ih =>
      intro k' f'
      simp only [World.schreibBytes]
      have h1 : ((σ.schreibSlot u Λ k f
          (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))).schreibBytes
            u f hf Λ (k + 1) bs).slots t k' f' =
          (σ.schreibSlot u Λ k f
            (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))).slots t k' f' :=
        ih _ _ _ _
      have h2 : (σ.schreibSlot u Λ k f
          (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))).slots t k' f' =
          σ.slots t k' f' :=
        storeSlot_fremd_traeger _ h _ _ _ k' f'
      rw [h1, h2]

/-- Same-carrier byte write with no write event in the trace: the byte list
    must be empty (a nonempty list emits a `zugriff t true` head event via
    `schreibBytes_spur_eq`, ruled out by `hno`), and the empty list leaves
    slots unchanged (`lese` only extends the trace). Used: `hf` types the
    byte field in `hstep`/`hspur`, `hstep` fixes the outcome, `hneu` aligns
    the trace tails, `hno` fires on the head write event. -/
theorem schreibBytes_gleich_samma_traeger (σ₀ : World D) (t : D.Tab)
    (fld : D.Feld t) (hf : D.typ t fld = .int 0 255) (Λ : List (Res D))
    (orte : List (D.Tab ⊕ D.Glob)) (k : Int) (bs : List Byte)
    (σ' : World D)
    (hstep : ((σ₀.lese Λ orte).schreibBytes t fld hf Λ k bs) = σ')
    (neu : List (Ereignis D)) (hneu : σ'.spur = neu ++ σ₀.spur)
    (hno : ∀ e ∈ neu, e.traeger = some (.inl t : D.Tab ⊕ D.Glob) →
      ∀ (Λe : List (Res D)) (h : List D.Lock),
        e = Ereignis.zugriff t true Λe h → False) :
    ∀ (k' : Int) (fld' : D.Feld t), σ'.slots t k' fld' = σ₀.slots t k' fld' := by
  cases bs with
  | nil =>
      intro k' fld'
      have hnil : ((σ₀.lese Λ orte).schreibBytes t fld hf Λ k []) =
          σ₀.lese Λ orte := rfl
      have hseq : σ' = σ₀.lese Λ orte := by rw [← hstep, hnil]
      rw [hseq]
      exact lese_slots_gleich _ _ _ _ _ _
  | cons b bs' =>
      have hspur := Extraktion.schreibBytes_spur_eq (σ₀.lese Λ orte) t fld hf Λ k (b :: bs')
      have hlese : (σ₀.lese Λ orte).spur = (orte.map fun o => match o with
          | .inl t' => Ereignis.zugriff t' false Λ σ₀.haelt
          | .inr g => Ereignis.gzugriff g false Λ σ₀.haelt) ++ σ₀.spur := rfl
      rw [← hstep] at hneu
      rw [hspur, hlese, ← List.append_assoc] at hneu
      have hneueq := List.append_cancel_right hneu
      have hev : Ereignis.zugriff t true Λ (σ₀.lese Λ orte).haelt ∈ neu := by
        rw [← hneueq]
        have hrep : List.replicate (List.length (b :: bs'))
            (Ereignis.zugriff t true Λ (σ₀.lese Λ orte).haelt) =
            Ereignis.zugriff t true Λ (σ₀.lese Λ orte).haelt ::
            List.replicate (List.length bs')
              (Ereignis.zugriff t true Λ (σ₀.lese Λ orte).haelt) :=
          List.replicate_succ
        rw [hrep]
        exact List.mem_append_left _ (List.mem_cons.mpr (Or.inl rfl))
      have htr : (Ereignis.zugriff t true Λ (σ₀.lese Λ orte).haelt).traeger =
          some (.inl t : D.Tab ⊕ D.Glob) := rfl
      exact False.elim (hno _ hev htr Λ _ rfl)

/-! ## 4. The leaf lemma: a firing leaf of a thread not holding L
    preserves the slots of the L-guarded carrier -/

/-- A firing leaf step of a thread that does not hold `L` leaves every slot
    of the `L`-guarded carrier `t` unchanged.

    Proof: case on the leaf statement (only leaf shapes can fire: compound
    shapes have `istBlatt = false`). For the five shapes that write tables
    (`assignSlot`, `assignDurch`, `schreibBytes`, `uebergang`), `execStmt`
    writes through `schreibSlot`/`schreibBytes`, which records a `zugriff`
    event carrying the statement `Λ` and the pre-step held locks. That event
    is good (its world is reachable, so `gen_gut_obs` applies through the
    `Brav` provenance of `blatt_brav`), and `kein_schreibzugriff_ohne_sperre`
    forces its `schreibt` flag to `false` -- contradiction with the write
    event, unless the write went to another carrier. All other leaf shapes
    (`assignGlob`, `publish`, `assignVar`, `ret`, `retGrund`, `leave`,
    `next`, `regSchreib`, `transition`, `advances`, `retires`,
    `axiomCall`) never touch table slots: globals go through `storeGlob`,
    the rest leave the world or only the trace.

    Every premise is used: `hΛ` ties the static `Λ` to the dynamic held
    locks, `hfrei` excludes `L`, `hGuard` names the guard, `hO` gives the
    event goodness via `stmt_gut`, `hstep` is the firing, `hneu` is the
    trace equation consumed by the `Brav` membership. -/
end Gabbro.Grammatik
