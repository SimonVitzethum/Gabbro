module

public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Kern.Syntax.Extraktion
public import Grammatik.Nebenlaeufigkeit.Sperren.RessourcenBlatt.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

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
    (hax : match s with | .axiomCall _ _ _ _ _ _ _ => False | _ => True)
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
    have hg : (Ereignis.zugriff t true Λe h).gut := by
      rw [← heq]; exact hneu_gut e he
    have hlam : (Ereignis.zugriff t true Λe h).lambda = Λ := by
      rcases hchar.1 e he with hl | hl
      · rw [← heq]; exact hl
      · -- a write with an empty `Λ` names no guard, but the guarded carrier needs one
        rw [heq] at hl
        simp only [Ereignis.lambda] at hl
        subst hl
        have hd : darf D t [] := zugriff_darf_aus_gut hg
        exact absurd (hd _ hGuard) List.not_mem_nil
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
          simp only [Ereignis.traeger]
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
  | assignThru p u ht fld i e hw hL =>
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
          simp only [Ereignis.traeger]
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
  | assignThruOwn p u ht fld i e m s ho he hg hm hw hL =>
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
          simp only [Ereignis.traeger]
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
  | assignSlotRef r u ht ho fld e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      by_cases htu : u = t
      · subst htu
        have hev : Ereignis.zugriff u true Λ
            ((M.weltVon f).lese Λ (r.orte ++ e.orte)).haelt ∈ neu := by
          have hsp : (((M.weltVon f).lese Λ (r.orte ++ e.orte)).schreibSlot u Λ
              ((eval ((M.weltVon f).lese Λ (r.orte ++ e.orte)) r
                ((M.weltVon f).lese Λ (r.orte ++ e.orte)) ρ).zelle : Int) fld
              (eval ((M.weltVon f).lese Λ (r.orte ++ e.orte)) e
                ((M.weltVon f).lese Λ (r.orte ++ e.orte)) ρ)).spur =
              [Ereignis.zugriff u true Λ ((M.weltVon f).lese Λ (r.orte ++ e.orte)).haelt] ++
              ((r.orte ++ e.orte).map fun o => match o with
                | .inl t' => Ereignis.zugriff t' false Λ (M.weltVon f).haelt
                | .inr g => Ereignis.gzugriff g false Λ (M.weltVon f).haelt) ++ (M.weltVon f).spur := rfl
          rw [hsp] at hneu
          have hneueq := List.append_cancel_right hneu
          rw [← hneueq]
          exact List.mem_append_left _ (List.mem_singleton.mpr rfl)
        have htr : (Ereignis.zugriff u true Λ
            ((M.weltVon f).lese Λ (r.orte ++ e.orte)).haelt).traeger =
            some (.inl u : D.Tab ⊕ D.Glob) := by
          simp only [Ereignis.traeger]
        exact False.elim (hnoWrite _ hev htr Λ _ rfl)
      · intro k fld'
        have hslot : (((M.weltVon f).lese Λ (r.orte ++ e.orte)).schreibSlot u Λ
            ((eval ((M.weltVon f).lese Λ (r.orte ++ e.orte)) r
              ((M.weltVon f).lese Λ (r.orte ++ e.orte)) ρ).zelle : Int) fld
            (eval ((M.weltVon f).lese Λ (r.orte ++ e.orte)) e
              ((M.weltVon f).lese Λ (r.orte ++ e.orte)) ρ)).slots t k fld' =
            ((M.weltVon f).lese Λ (r.orte ++ e.orte)).slots t k fld' :=
          storeSlot_fremd_traeger _ (Ne.symm htu) _ _ _ _ _
        have hgoal : (((M.weltVon f).lese Λ (r.orte ++ e.orte)).schreibSlot u Λ
            ((eval ((M.weltVon f).lese Λ (r.orte ++ e.orte)) r
              ((M.weltVon f).lese Λ (r.orte ++ e.orte)) ρ).zelle : Int) fld
            (eval ((M.weltVon f).lese Λ (r.orte ++ e.orte)) e
              ((M.weltVon f).lese Λ (r.orte ++ e.orte)) ρ)).slots t k fld' =
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
  | putBytes u fld hf n i hlo hhi e hw hL =>
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
        -- `hsp` tails at the READ world, but `hneu` tails at the ENTRY
        -- world: the read prefix must be aligned before the first write
        -- event can be read off into `neu`. Closed by
        -- `schreibBytes_gleich_samma_traeger`: the byte-list case split
        -- lives there (empty list keeps slots, nonempty head event fires
        -- `hnoWrite`).
        exact schreibBytes_gleich_samma_traeger (M.weltVon f) _ _ _ _
          _ _ _ _ hstep _ hneu hnoWrite
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
  | shift u fld hτ i von nach hn he hw hL =>
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
            simp only [Ereignis.traeger]
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
      · simp only [Ausgang.welt, reduceCtorEq] at hstep
  | ite c tb eb => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | onOption o pb ab => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | onTag v arms => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | onWhy r arms => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | call fn args hp hr => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | callInd p args hp hr => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | callIndElse p args he hp hr err => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | locks L' hr body => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | breaking ii body => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | consumeTraverse => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | axiomCallElse => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | traverse u inv body => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | retry n bis body ueber => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | forever a inv body => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | axiomCall a args hh hw hg _ _ => exact False.elim (hax)
  | regWrite r hk e =>
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
  | retScoped =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      exact lese_slots_gleich _ _ _ _ _ _
  | retWhyScoped =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      rfl
  | ret e hΛe =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      exact lese_slots_gleich _ _ _ _ _ _
  | retWhy r hΛe =>
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

/-! ## 5. The main theorem: CUT -- the target is false for `axiomCall`

    The fixed target `csl_ressourceninvarianteC` is recorded in
    `MUSE-REPORT-54.md`, not proved here. Finding: `Stmt.axiomCall`
    (Semantik.lean:617) answers with the oracle world `O.wirkt a σ ρ`,
    which may change `t`'s slots while recording NO access event (the
    trace may even be unchanged); `GutO` enforces only the declared
    frame, not the guard. The leaf branch of the `PCReach` induction
    owes `hax` (non-oracle shape) for the fired statement, underivable
    for `axiomCall` -- and slot preservation is genuinely false there.
    Per rule 12, a variant with an added no-oracle premise is future
    work; per rule 13 no `_zeuge` is owed for a cut theorem. -/
/- Target cut: fixed statement and model finding recorded in MUSE-REPORT-54.md. -/

end Gabbro.Grammatik
