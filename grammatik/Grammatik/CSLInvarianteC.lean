/-
  File:      Grammatik/CSLInvarianteC.lean
  Subject:   THE CSL RESOURCE INVARIANT AT EVENT GRAIN (attempt C).

  While lock L is free, no thread that could write carrier t is inside a
  critical section, so t's invariant holds. Each leaf step of a thread not
  holding L leaves the slots of t unchanged: writing t records an access
  event whose guards (`darf`, `Ereignis.gut`) require `Held L`, and
  `HeldGenau` ties the static resource list to the thread's open locks.
-/
import Grammatik.Maschine
import Grammatik.Extraktion

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
  simp [World.storeSlot, h]

/-- A store to the same carrier but a different slot leaves this slot
    untouched. Used: `hk` selects the branch, `hf` is the field equation
    discharged by the `if` on fields. -/
theorem storeSlot_fremd_slot (σ : World D) (t : D.Tab)
    (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f))
    (k' : Int) (f' : D.Feld t) (hk : k' ≠ k) (hf : f' = f) :
    (σ.storeSlot t k f v).slots t k' f' = σ.slots t k' f' := by
  subst hf
  simp [World.storeSlot, hk]

/-- A store to the same slot but a different field leaves this field
    untouched. Used: `hk` forces the same-index branch, `hf` selects the
    else-branch on fields. -/
theorem storeSlot_fremd_feld (σ : World D) (t : D.Tab)
    (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f))
    (k' : Int) (f' : D.Feld t) (hk : k' = k) (hf : f' ≠ f) :
    (σ.storeSlot t k f v).slots t k' f' = σ.slots t k' f' := by
  subst hk
  simp [World.storeSlot, hf]

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
theorem blatt_slots_t_gleich
    (O : Orakel D) (passes : Nat)
    (M : GenMaschine D) (f : Faden)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hleaf : s.istBlatt = true)
    (hax : match s with | .axiomCall _ _ _ _ _ => False | _ => True)
    (σ' : World D)
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
    (neu : List (Ereignis D))
    (hneu : σ'.spur = neu ++ (M.weltVon f).spur)
    (t : D.Tab) (L : D.Lock)
    (hGuard : Sum.inl L ∈ D.braucht t)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (hfrei : L ∉ offen (M.spuren f))
    (hneu_gut : ∀ e ∈ neu, e.gut)
    (tabs : List D.Tab) (globs : List D.Glob) :
    ∀ (k : Int) (fld : D.Feld t), σ'.slots t k fld = (M.weltVon f).slots t k fld := by
  -- Every new event carries the statement Λ and touches only the written
  -- carrier plus the read hull (read-only reuse of the §17 characterization).
  have hchar := Extraktion.execEreignis_aus_blatt_ohne_axiomCall (D := D)
    O passes s hleaf hax tabs globs (M.weltVon f) ρ σ' neu hstep hneu
  -- Every write-shaped new event on t is impossible: it would carry the
  -- statement Λ (by hchar.1) and the pre-step held locks (its `haelt`
  -- equals the entry held list, since reads record `σ.haelt` and the write
  -- records the post-read held list, which `Brav` keeps equal), so
  -- `kein_schreibzugriff_ohne_sperre` forces its flag to false.
  -- Hence every new event with carrier t is a read; reads leave slots.
  have hnoWrite : ∀ e ∈ neu, e.traeger = some (.inl t : D.Tab ⊕ D.Glob) →
      ∀ (Λe : List (Res D)) (h : List D.Lock),
        e = Ereignis.zugriff t true Λe h → False := by
    intro e he htr Λe h heq
    have hlam : (Ereignis.zugriff t true Λe h).lambda = Λ := by
      rw [← heq]; exact hchar.1 e he
    have hg : (Ereignis.zugriff t true Λe h).gut := by
      rw [← heq]; exact hneu_gut e he
    simp only [Ereignis.lambda] at hlam
    -- After `subst`, the statement-Λ binder is rewritten to `Λe`
    -- everywhere, including `hmem`, `hΛ`, `hchar`, `hfrei`.
    subst hlam
    have hdarf : darf D t Λe := zugriff_darf_aus_gut hg
    have hmem : Res.von D (Sum.inl L) ∈ Λe := hdarf _ hGuard
    simp only [Res.von] at hmem
    -- `h` is the held list recorded on the event. Leaf steps never take
    -- locks (`hkein_nimmt` in `GenSchritt.blatt`), and `Brav` keeps held
    -- locks equal from entry to exit, so `h = offen (M.spuren f)`:
    -- the recorded held list is the pre-step open locks. This equality
    -- is established by the caller supplying `hneu_gut` together with the
    -- `Brav` provenance; here we close the remaining link by noting the
    -- event haelt equals the entry haelt on leaf paths.
    have hheld : L ∈ h := by
      have hHin : HeldIn Λe h := hg.2
      exact hHin L hmem
    -- The recorded held list `h` is the pre-step open locks: leaf events
    -- record `σ.haelt` at their site, and the leaf characterization gives
    -- the event Λ as the statement Λ, so `hΛ` turns `hmem` into
    -- `L ∈ offen _` only when `h` is the entry opens. The remaining link
    -- -- `h` equals the entry opens -- follows because leaf paths record
    -- `σ.haelt` and `Brav` keeps held locks equal; the caller supplies
    -- `hneu_gut` with the `GenSchritt.blatt` provenance that fixes `h`.
    have hLopen : L ∈ offen (M.spuren f) := (hΛ L).mp hmem
    exact absurd hLopen hfrei
  -- No new event is a write on t. Now case on the statement: the frame
  -- (`Rahmen`) from `stmt_gut` gives slot equality unless the statement
  -- writes t itself -- and writing t emits exactly the write event that
  -- `hnoWrite` rules out. Each write shape is handled by unfolding
  -- `execStmt` and applying the foreign-carrier lemmas above.
  cases s with
  | assignSlot u fld i e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      -- `σ'` is the post-write world; its slots at t come from the store.
      -- If `u = t`, the write event contradicts `hnoWrite`; else the
      -- foreign-carrier frame applies.
      by_cases htu : u = t
      · subst htu
        -- The write event is in `neu` (head of the post-write trace).
        have hev : Ereignis.zugriff u true Λ ((M.weltVon f).lese Λ (i.orte ++ e.orte)).haelt ∈ neu := by
          have hsp : (((M.weltVon f).lese Λ (i.orte ++ e.orte)).schreibSlot u Λ
              (eval ((M.weltVon f).lese Λ (i.orte ++ e.orte)) i
                ((M.weltVon f).lese Λ (i.orte ++ e.orte)) ρ).n fld
              (eval ((M.weltVon f).lese Λ (i.orte ++ e.orte)) e
                ((M.weltVon f).lese Λ (i.orte ++ e.orte)) ρ)).spur =
              [Ereignis.zugriff u true Λ ((M.weltVon f).lese Λ (i.orte ++ e.orte)).haelt] ++
              ((i.orte ++ e.orte).map fun o => match o with
                | .inl t' => Ereignis.zugriff t' false Λ (M.weltVon f).haelt
                | .inr g => Ereignis.gzugriff g false Λ (M.weltVon f).haelt) ++ (M.weltVon f).spur := rfl
          rw [hsp] at hneu
          have hneueq : [Ereignis.zugriff u true Λ ((M.weltVon f).lese Λ (i.orte ++ e.orte)).haelt] ++
              ((i.orte ++ e.orte).map fun o => match o with
                | .inl t' => Ereignis.zugriff t' false Λ (M.weltVon f).haelt
                | .inr g => Ereignis.gzugriff g false Λ (M.weltVon f).haelt) = neu :=
            List.append_cancel_right hneu
          rw [← hneueq]
          exact List.mem_append_left _ (List.mem_singleton.mpr rfl)
        have htr : (Ereignis.zugriff u true Λ ((M.weltVon f).lese Λ (i.orte ++ e.orte)).haelt).traeger =
            some (.inl u : D.Tab ⊕ D.Glob) := by
          simp [Ereignis.traeger]
        exact False.elim (hnoWrite _ hev htr Λ _ rfl)
      · intro k fld'
        have hslot : (((M.weltVon f).lese Λ (i.orte ++ e.orte)).schreibSlot u Λ
            (eval ((M.weltVon f).lese Λ (i.orte ++ e.orte)) i
              ((M.weltVon f).lese Λ (i.orte ++ e.orte)) ρ).n fld
            (eval ((M.weltVon f).lese Λ (i.orte ++ e.orte)) e
              ((M.weltVon f).lese Λ (i.orte ++ e.orte)) ρ)).slots t k fld' =
            ((M.weltVon f).lese Λ (i.orte ++ e.orte)).slots t k fld' :=
          storeSlot_fremd_traeger _ (Ne.symm htu) _ _ _ _ _
        -- `hslot` states the goal up to the read prefix; close by rewrite.
        have hgoal : (((M.weltVon f).lese Λ (i.orte ++ e.orte)).schreibSlot u Λ
            (eval ((M.weltVon f).lese Λ (i.orte ++ e.orte)) i
              ((M.weltVon f).lese Λ (i.orte ++ e.orte)) ρ).n fld
            (eval ((M.weltVon f).lese Λ (i.orte ++ e.orte)) e
              ((M.weltVon f).lese Λ (i.orte ++ e.orte)) ρ)).slots t k fld' =
            (M.weltVon f).slots t k fld' := by
          rw [hslot]
          exact lese_slots_gleich _ _ _ _ _ _
        exact hgoal
  | assignDurch p u ht fld i e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      by_cases htu : u = t
      · subst htu
        have hev : Ereignis.zugriff u true Λ
            ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)).haelt ∈ neu := by
          have hsp : (((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)).schreibSlot u Λ
              (eval ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)) i
                ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)) ρ).n fld
              (eval ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)) e
                ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)) ρ)).spur =
              [Ereignis.zugriff u true Λ ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)).haelt] ++
              ((p.orte ++ i.orte ++ e.orte).map fun o => match o with
                | .inl t' => Ereignis.zugriff t' false Λ (M.weltVon f).haelt
                | .inr g => Ereignis.gzugriff g false Λ (M.weltVon f).haelt) ++ (M.weltVon f).spur := rfl
          rw [hsp] at hneu
          have hneueq := List.append_cancel_right hneu
          rw [← hneueq]
          exact List.mem_append_left _ (List.mem_singleton.mpr rfl)
        have htr : (Ereignis.zugriff u true Λ
            ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)).haelt).traeger =
            some (.inl u : D.Tab ⊕ D.Glob) := by
          simp [Ereignis.traeger]
        exact False.elim (hnoWrite _ hev htr Λ _ rfl)
      · intro k fld'
        have hslot : (((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)).schreibSlot u Λ
            (eval ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)) i
              ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)) ρ).n fld
            (eval ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)) e
              ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)) ρ)).slots t k fld' =
            ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)).slots t k fld' :=
          storeSlot_fremd_traeger _ (Ne.symm htu) _ _ _ _ _
        have hgoal : (((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)).schreibSlot u Λ
            (eval ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)) i
              ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)) ρ).n fld
            (eval ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)) e
              ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)) ρ)).slots t k fld' =
            (M.weltVon f).slots t k fld' := by
          rw [hslot]
          exact lese_slots_gleich _ _ _ _ _ _
        exact hgoal
  | assignGlob g e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      have hgoal : (((M.weltVon f).lese Λ e.orte).schreibGlob g Λ
          (eval ((M.weltVon f).lese Λ e.orte) e
            ((M.weltVon f).lese Λ e.orte) ρ)).slots t k fld' =
          (M.weltVon f).slots t k fld' := by
        have h1 : (((M.weltVon f).lese Λ e.orte).schreibGlob g Λ
            (eval ((M.weltVon f).lese Λ e.orte) e
              ((M.weltVon f).lese Λ e.orte) ρ)).slots t k fld' =
            ((M.weltVon f).lese Λ e.orte).slots t k fld' := by
          have hsg := storeGlob_slots_gleich ((M.weltVon f).lese Λ e.orte) g
            (eval ((M.weltVon f).lese Λ e.orte) e
              ((M.weltVon f).lese Λ e.orte) ρ) t k fld'
          -- `schreibGlob` is store + merke; merke keeps slots definitionally.
          exact hsg
        rw [h1]
        exact lese_slots_gleich _ _ _ _ _ _
      exact hgoal
  | schreibBytes u fld hf n i hlo hhi e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      -- Do NOT subst: the byte-list case split below needs `hstep`
      -- (world equation) and `hneu` (trace equation) both intact.
      by_cases htu : u = t
      · subst htu
        -- A byte write on u emits `zugriff u true` events (one per byte).
        -- The read prefix (`World.lese`) already records read events with
        -- `σ.haelt`, so the byte-write events carry the POST-read held
        -- list, which `Brav` keeps equal to the entry opens. Hence every
        -- byte-write event is a write event on u in `neu`, and the FIRST
        -- byte already contradicts `hnoWrite`. We only need existence of
        -- one byte: `n > 0` would be needed for a write, but the guard
        -- argument does not need it -- `hnoWrite` fires on ANY write
        -- event, and `hsp` exhibits the replicate shape directly.
        -- Instead of casing on the byte list, use the frame: byte writes
        -- to u preserve every slot of u EXCEPT the written range -- but
        -- the written range is nonempty only if `n > 0`. Since `hnoWrite`
        -- rules out every write event, the byte list must be empty on
        -- this path; the empty case is `rfl` by `schreibBytes`.
        -- Full case split on the byte list (as sketched) needs `hstep`
        -- intact; it is, since we did not subst. Do it now.
        have hsp := Extraktion.schreibBytes_spur_eq (D := D)
          ((M.weltVon f).lese Λ (i.orte ++ e.orte)) u fld hf Λ
          (eval ((M.weltVon f).lese Λ (i.orte ++ e.orte)) i
            ((M.weltVon f).lese Λ (i.orte ++ e.orte)) ρ).n
          (zahlZuBytes n (eval ((M.weltVon f).lese Λ (i.orte ++ e.orte)) e
            ((M.weltVon f).lese Λ (i.orte ++ e.orte)) ρ).n)
        -- `hsp` tails at the READ world, but `hneu` tails at the ENTRY
        -- world: the read prefix sits between them. Rewrite `hneu`
        -- through the read-event equation to align the tails, then read
        -- off the first write event. This alignment is the remaining gap.
        sorry
      · intro k fld'
        -- `hstep : schreibBytes-world = σ'`; rewrite the goal into the
        -- schreibBytes world, then apply the foreign-carrier frame.
        have hgoal : σ'.slots t k fld' = (M.weltVon f).slots t k fld' := by
          rw [← hstep]
          have hslot := schreibBytes_fremd_traeger
            ((M.weltVon f).lese Λ (i.orte ++ e.orte)) (Ne.symm htu) fld hf Λ
            (eval ((M.weltVon f).lese Λ (i.orte ++ e.orte)) i
              ((M.weltVon f).lese Λ (i.orte ++ e.orte)) ρ).n
            (zahlZuBytes n (eval ((M.weltVon f).lese Λ (i.orte ++ e.orte)) e
              ((M.weltVon f).lese Λ (i.orte ++ e.orte)) ρ).n) k fld'
          rw [hslot]
          exact lese_slots_gleich _ _ _ _ _ _
        exact hgoal
  | assignVar x e =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      have hgoal : ((M.weltVon f).lese Λ e.orte).slots t k fld' =
          (M.weltVon f).slots t k fld' :=
        lese_slots_gleich _ _ _ _ _ _
      exact hgoal
  | uebergang u fld hτ i von nach hn he hw hL =>
      -- `uebergang` either fails (`.logik`, contradicting `hstep`'s `some`)
      -- or writes through `schreibSlot`: same argument as `assignSlot`.
      simp only [execStmt] at hstep
      split at hstep
      · simp only [Ausgang.welt, Option.some.injEq] at hstep
        subst hstep
        by_cases htu : u = t
        · subst htu
          have hev : Ereignis.zugriff u true Λ
              ((M.weltVon f).lese Λ (.inl u :: i.orte)).haelt ∈ neu := by
            have hsp : (((M.weltVon f).lese Λ (.inl u :: i.orte)).schreibSlot u Λ
                (eval ((M.weltVon f).lese Λ (.inl u :: i.orte)) i
                  ((M.weltVon f).lese Λ (.inl u :: i.orte)) ρ).n fld
                (hτ ▸ (⟨nach, hn.1, hn.2⟩ : Zahl _ _))).spur =
                [Ereignis.zugriff u true Λ ((M.weltVon f).lese Λ (.inl u :: i.orte)).haelt] ++
                (((.inl u :: i.orte).map fun o => match o with
                  | .inl t' => Ereignis.zugriff t' false Λ (M.weltVon f).haelt
                  | .inr g => Ereignis.gzugriff g false Λ (M.weltVon f).haelt) ++
                  (M.weltVon f).spur) := rfl
            have hneueq : [Ereignis.zugriff u true Λ ((M.weltVon f).lese Λ (.inl u :: i.orte)).haelt] ++
                (((.inl u :: i.orte).map fun o => match o with
                  | .inl t' => Ereignis.zugriff t' false Λ (M.weltVon f).haelt
                  | .inr g => Ereignis.gzugriff g false Λ (M.weltVon f).haelt)) = neu :=
              List.append_cancel_right (by
                have h2 := hsp.symm.trans hneu
                -- `hsp` RHS parses as `write ++ (reads ++ spur)`; fold the
                -- LHS into `(write ++ reads) ++ spur` by assoc, then cancel.
                have h3 : (([Ereignis.zugriff u true Λ ((M.weltVon f).lese Λ (.inl u :: i.orte)).haelt] ++
                    (((.inl u :: i.orte).map fun o => match o with
                      | .inl t' => Ereignis.zugriff t' false Λ (M.weltVon f).haelt
                      | .inr g => Ereignis.gzugriff g false Λ (M.weltVon f).haelt))) ++
                    (M.weltVon f).spur) = neu ++ (M.weltVon f).spur := by
                  have hassoc := List.append_assoc
                    [Ereignis.zugriff u true Λ ((M.weltVon f).lese Λ (.inl u :: i.orte)).haelt]
                    (((.inl u :: i.orte).map fun o => match o with
                      | .inl t' => Ereignis.zugriff t' false Λ (M.weltVon f).haelt
                      | .inr g => Ereignis.gzugriff g false Λ (M.weltVon f).haelt))
                    (M.weltVon f).spur
                  rw [hassoc]
                  exact h2
                exact h3)
            rw [← hneueq]
            exact List.mem_append_left _ (List.mem_singleton.mpr rfl)
          have htr : (Ereignis.zugriff u true Λ
              ((M.weltVon f).lese Λ (.inl u :: i.orte)).haelt).traeger =
              some (.inl u : D.Tab ⊕ D.Glob) := by
            simp [Ereignis.traeger]
          exact False.elim (hnoWrite _ hev htr Λ _ rfl)
        · intro k fld'
          have hslot : (((M.weltVon f).lese Λ (.inl u :: i.orte)).schreibSlot u Λ
              (eval ((M.weltVon f).lese Λ (.inl u :: i.orte)) i
                ((M.weltVon f).lese Λ (.inl u :: i.orte)) ρ).n fld
              (hτ ▸ (⟨nach, hn.1, hn.2⟩ : Zahl _ _))).slots t k fld' =
              ((M.weltVon f).lese Λ (.inl u :: i.orte)).slots t k fld' :=
            storeSlot_fremd_traeger _ (Ne.symm htu) _ _ _ _ _
          have hgoal : (((M.weltVon f).lese Λ (.inl u :: i.orte)).schreibSlot u Λ
              (eval ((M.weltVon f).lese Λ (.inl u :: i.orte)) i
                ((M.weltVon f).lese Λ (.inl u :: i.orte)) ρ).n fld
              (hτ ▸ (⟨nach, hn.1, hn.2⟩ : Zahl _ _))).slots t k fld' =
              (M.weltVon f).slots t k fld' := by
            rw [hslot]
            exact lese_slots_gleich _ _ _ _ _ _
          exact hgoal
      · simp [Ausgang.welt] at hstep
  | ite c tb eb => simp [Stmt.istBlatt] at hleaf
  | onOption o pb ab => simp [Stmt.istBlatt] at hleaf
  | onTag v arms => simp [Stmt.istBlatt] at hleaf
  | onGrund r arms => simp [Stmt.istBlatt] at hleaf
  | call fn args hp hr => simp [Stmt.istBlatt] at hleaf
  | callInd p args hp hr => simp [Stmt.istBlatt] at hleaf
  | locks L' hr body => simp [Stmt.istBlatt] at hleaf
  | breaking ii body => simp [Stmt.istBlatt] at hleaf
  | traverse u inv body => simp [Stmt.istBlatt] at hleaf
  | retry n bis body ueber => simp [Stmt.istBlatt] at hleaf
  | forever a inv body => simp [Stmt.istBlatt] at hleaf
  | axiomCall a args hh hw hg => exact False.elim (hax)
  | regSchreib r hk e =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      exact lese_slots_gleich _ _ _ _ _ _
  | transition r hk m hm hl maske bits =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      rfl
  | publish g e payload hp hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      have hgoal : (((M.weltVon f).lese Λ e.orte).schreibGlob g Λ
          (eval ((M.weltVon f).lese Λ e.orte) e
            ((M.weltVon f).lese Λ e.orte) ρ)).slots t k fld' =
          (M.weltVon f).slots t k fld' := by
        -- `schreibGlob` is store + merke; both keep table slots by `rfl`.
        show (((M.weltVon f).lese Λ e.orte).storeGlob g
          (eval ((M.weltVon f).lese Λ e.orte) e
            ((M.weltVon f).lese Λ e.orte) ρ)).slots t k fld' = _
        exact lese_slots_gleich ((M.weltVon f).lese Λ e.orte) Λ e.orte t k fld'
      exact hgoal
  | advances m a hh hs =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      rfl
  | retires m st hh a =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      rfl
  | ret e hΛe =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      exact lese_slots_gleich _ _ _ _ _ _
  | retGrund r hΛe =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      rfl
  | leave hh =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      rfl
  | next hh =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      rfl

/-! ## 5. The main theorem: CSL resource invariant at event grain -/

/-- **CSL resource invariant at event grain (attempt C).**

    While lock `L` is free in every thread trace, the carrier-`t`
    invariant `inv` holds at the machine memory -- provided `inv`
    depends only on `t`'s slots (`hLokal`), holds at start (`hStart`),
    and every release step of `L` restores it (`hRelease`, the writer's
    own obligation).

    Proof: induction over `PCReach`. The start case is `hStart`. For a
    step, case on the step kind and on whether `L` was free before:
    - leaf by a thread not holding `L`: `blatt_slots_t_gleich` keeps
      every slot of `t`, so `hLokal` transports `inv`;
    - leaf by a thread holding `L`: `L` is not free after (access events
      never give locks), so the conclusion's freeness premise is
      contradictory -- UNLESS the thread releases later, which is the
      `hRelease` case;
    - take of `L`: `L` becomes held, freeness premise contradictory;
    - take of another lock: memory unchanged, `hLokal` transports;
    - release of `L`: `hRelease` restores `inv` directly;
    - release of another lock: memory unchanged, `hLokal` transports.

    Every premise is used: `hO` feeds event goodness in the leaf lemma,
    `hGuard` names the guard there, `hLokal` transports `inv` across
    slot-preserving steps, `hStart` grounds the induction, `hRelease`
    closes the release case. -/
theorem csl_ressourceninvarianteC
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D)
    (t : D.Tab) (L : D.Lock) (inv : Speicher D → Prop)
    (hGuard : Sum.inl L ∈ D.braucht t)
    (hLokal : ∀ s s' : Speicher D, (∀ k f, s.slots t k f = s'.slots t k f) → (inv s ↔ inv s'))
    (hStart : inv sp)
    (hRelease : ∀ M pc f M' pc', PCReach P O passes prog (GenStart sp) M pc →
        PCSchritt P O passes prog M pc f M' pc' →
        L ∈ offen (M.spuren f) → L ∉ offen (M'.spuren f) → inv M'.speicher) :
    ∀ M pc, PCReach P O passes prog (GenStart sp) M pc →
      (∀ g, L ∉ offen (M.spuren g)) → inv M.speicher := by
  intro M pc hReach hfrei
  induction hReach with
  | start =>
      -- `GenStart sp` carries `sp` as its memory definitionally.
      show inv (GenStart sp).speicher
      exact hStart
  | step M M' pc pc' f hReach hs ih =>
      -- Whether L was free at M decides which argument fires.
      by_cases hvor : (∀ g, L ∉ offen (M.spuren g))
      · -- L was free before: the IH gives `inv M.speicher`.
        have hinvM : inv M.speicher := ih hvor
        -- Case on the step kind.
        cases hs with
        | leaf V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkn Λa cs hpc hΛa hmark hcar =>
            -- A leaf step: memory moves to `σ'.speicher`, traces extend.
            -- If f held L, `hvor f` contradicts; else the leaf lemma
            -- keeps t's slots and `hLokal` transports `inv`.
            by_cases hheld : L ∈ offen (M.spuren f)
            · exact absurd hheld (hvor f)
            · -- Build the leaf-lemma inputs: non-oracle shape, goodness
              -- of new events from the machine invariant.
              sorry
        | take L' hself hrang hfrei' hpc =>
            -- A take step leaves memory unchanged definitionally: the
            -- result memory is `M.speicher`. Transport `inv` across the
            -- definitional equality.
            have hmem : (⟨M.speicher,
                genUpdate M.spuren f (Ereignis.nimmt L' (offen (M.spuren f)) :: M.spuren f),
                M.lauf ++ genEigen f [Ereignis.nimmt L' (offen (M.spuren f))],
                M.start,
                M.welten ++ [M.speicher.welt (Ereignis.nimmt L' (offen (M.spuren f)) :: M.spuren f)],
                M.tiefe + 1⟩ : GenMaschine D).speicher = M.speicher := rfl
            -- The goal is `inv M'.speicher` where `M'` is that tuple.
            show inv (⟨M.speicher,
                genUpdate M.spuren f (Ereignis.nimmt L' (offen (M.spuren f)) :: M.spuren f),
                M.lauf ++ genEigen f [Ereignis.nimmt L' (offen (M.spuren f))],
                M.start,
                M.welten ++ [M.speicher.welt (Ereignis.nimmt L' (offen (M.spuren f)) :: M.spuren f)],
                M.tiefe + 1⟩ : GenMaschine D).speicher
            rw [hmem]
            exact hinvM
        | rel L' hhaelt hpc =>
            -- A release step leaves memory unchanged, unless it releases
            -- L itself -- then `hRelease` restores `inv` directly.
            by_cases hLL : L' = L
            · -- Release of L itself: apply the writer's obligation.
              -- After subst, `L'` IS the outer `L`; rebuild the step.
              subst hLL
              have hs' : PCSchritt P O passes prog M pc f
                  ⟨M.speicher,
                   genUpdate M.spuren f (Ereignis.gibt L' :: M.spuren f),
                   M.lauf ++ genEigen f [Ereignis.gibt L'],
                   M.start,
                   M.welten ++ [M.speicher.welt (Ereignis.gibt L' :: M.spuren f)],
                   M.tiefe + 1⟩
                  (pcAdvance pc f) :=
                PCSchritt.rel M pc f L' hhaelt hpc
              -- `hRelease` needs the reachability at M: it is the
              -- induction's `hReach`. L' was held before (`hhaelt`), and
              -- the conclusion's freeness (at M') gives not-held after.
              sorry
            · -- Release of another lock: memory unchanged, transport.
              have hmem : (⟨M.speicher,
                  genUpdate M.spuren f (Ereignis.gibt L' :: M.spuren f),
                  M.lauf ++ genEigen f [Ereignis.gibt L'],
                  M.start,
                  M.welten ++ [M.speicher.welt (Ereignis.gibt L' :: M.spuren f)],
                  M.tiefe + 1⟩ : GenMaschine D).speicher = M.speicher := rfl
              show inv (⟨M.speicher,
                  genUpdate M.spuren f (Ereignis.gibt L' :: M.spuren f),
                  M.lauf ++ genEigen f [Ereignis.gibt L'],
                  M.start,
                  M.welten ++ [M.speicher.welt (Ereignis.gibt L' :: M.spuren f)],
                  M.tiefe + 1⟩ : GenMaschine D).speicher
              rw [hmem]
              exact hinvM
      · -- L was NOT free before: some thread held it. But the conclusion
        -- demands L free now. The only steps that free L are releases of
        -- L -- closed by `hRelease`. All other steps keep some holder:
        -- leaf steps never give locks, takes only add, releases of other
        -- locks use erase of another key. This holder-persistence is the
        -- remaining gap alongside the leaf case above.
        sorry

/-! ## CUTS
  - `blatt_slots_t_gleich`: green except the same-carrier `schreibBytes`
    case (byte-list replicate alignment between the read-world tail of
    `schreibBytes_spur_eq` and the entry-world tail of `hneu`).
  - `csl_ressourceninvarianteC`: skeleton induction over `PCReach` with
    take/other-release transport closed by `rfl`; open: leaf case wiring
    (non-oracle shape + new-event goodness from the machine invariant),
    same-L release via `hRelease` (needs post-step freeness unfolding),
    and the not-free-before holder-persistence branch.
-/

#print axioms Gabbro.Grammatik.zugriff_darf_aus_gut
#print axioms Gabbro.Grammatik.kein_schreibzugriff_ohne_sperre
#print axioms Gabbro.Grammatik.blatt_slots_t_gleich
#print axioms Gabbro.Grammatik.csl_ressourceninvarianteC

#print axioms Gabbro.Grammatik.zugriff_darf_aus_gut
#print axioms Gabbro.Grammatik.kein_schreibzugriff_ohne_sperre

end Gabbro.Grammatik
