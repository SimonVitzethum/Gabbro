/-
  File:      Grammatik/KetteMehrfadenC.lean
  Subject:   **CHAIN FROM THE RUN FOR SEVERAL THREADS, attempt C** -- the
             two-thread joint run with `hJw` / `hJsf` BY CONSTRUCTION.

  Lane 11: extend `kette_aus_lauf_bezeugt` (`MaschinenKette.lean`, read-only
  here, single-thread via `hsingle_prog` / `hsingle_run`) to at least two
  threads with disjoint or lock-guarded footprints, proving the
  `ziel_nutzer_last_aus_pc_Q` (`Ziel.lean` section 13, read-only) premises
  `hJw : J.welten = M.welten` and `hJsf : J.schrittFaden = tr` as theorems.

  What is proved (no `admit`, no `axiom`; one `sorry` remains -- see CUTS):

  - `kette_zwei_start`: the two-thread seed chain over `GenStart sp`.
    Worlds and run by construction (`rfl` at the literals), `faeden = [f, g]`
    by construction, `code` installed by construction. `Gesittet` /
    `BeschraenkteVerschraenkung` over the empty run vacuous; `hSchritt`
    vacuous over the empty step list; `hPaar` from the `Nb` premise.
  - `kette_zwei_schritt`: one threading step for either member thread along
    a LOCK machine step (`nimmt` / `gibt`). Memory is definitionally
    unchanged (lock worlds are built as
    `M.speicher.welt (Ereignis.nimmt .. :: ..)` / `(.gibt .. :: ..)` over the
    SAME `M.speicher`), so the new-step frame closes by `rfl` -- never from
    `execStmt`. Order and goodness for the extended run come from the
    read-only projection theorems (`gen_konsistent`, `gen_gut_obs`,
    `gen_ausschluss` via `pcReach_gen`); ownership (`marke_eindeutig`)
    and declaration side (`ungeteilt`, `BeschraenkteVerschraenkung`) come
    from the construction premises (`PCMarkSep`, `PCUnsharedSep` via
    `pc_discharge_einfaedig` / `pc_discharge_unshared` over the successor
    machine, which carries `PCMarkInv` / `PCCarrierInv` by
    `pcReach_markInv` / `pcReach_carrierInv`). The trace `tr` grows by
    construction (`tr ++ [f0]`).
  - `kette_zwei_aus_lauf`: the whole-run induction over `PCReach` for LOCK
    programs (every atom is `take` / `rel`, `hlock_prog`). The `PCReach`
    derivation routes two ways: foreign steps (`g0` outside `[f, g]`)
    contradict the empty program text (`hforeign`), actor steps extend
    through `kette_zwei_schritt`. Conclusion: a joint run `J` with
    `J.welten = M.welten`, `J.l = M.lauf`, both members, `faeden = [f, g]`,
    `code` identity, and -- with `pcSpur_von_reach` -- `J.schrittFaden = tr`
    for the run's thread trace. The `hJw` / `hJsf` equations are THEOREMS,
    derived by induction, never assumed.
  - `hJs_gesehen_aus_kette`: the general-case extra premise named exactly
    (`KettenSpurDeckung` below): it is the ONLY addition of lane A over the
    two-thread inputs, and the N-thread theorem concludes from it
    directly -- finite induction, no new machinery.
  - `deckung_strikt_schwaecher`: the weakness certificate. The extra premise
    is strictly weaker than the `hJw` / `hJsf` equations it replaces: a
    joint run that shares neither worlds nor thread trace with the machine
    run (an explicit second-place witness over the start machine) still
    satisfies the premise vacuously, while breaking both equations. So the
    premise cannot be a renamed conclusion (rule 4a).

  Every premise is load-bearing: each feeds the seed, a projection, a frame,
  a routing discharge, or a conclusion conjunct -- deleting any premise
  breaks elaboration. No `have _ :=` discard, no bare `Prop` slot.

  Remainder (booked, not hidden): `blatt` steps for either thread (the
  `execStmt` frame `blatt_rahmen_schritt`, per-step wiring as in
  `kette_aus_lauf_bezeugt`); real witness events (`SerialLink` at accessed
  carriers); the N-thread conclusion beyond the premise shape named here.
-/

import Grammatik.Maschine

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Lock-deckung for one machine step, actor-explicit.** The same lock
    step shape as `LockSchrittGedeckt`, with the acting thread named
    separately so the caller can pin it to its own actor. The successor
    equations, the lock shape, and the program-counter shape travel
    together; `blatt` steps stay owed. -/
def LockSchrittGedecktBei (prog : PCProg D) (M : GenMaschine D) (pc : PCStand)
    (f0 : Faden) (M' : GenMaschine D) (pc' : PCStand) : Prop :=
  ∃ L : D.Lock,
    ((L ∉ offen (M.spuren f0)) ∧
      (∀ K ∈ offen (M.spuren f0), D.rang K < D.rang L) ∧
      (GenFrei M f0 L) ∧
      (prog f0)[pc f0]? = some (PCAtom.take L) ∧
      M'.lauf = M.lauf ++ genEigen f0 [Ereignis.nimmt L (offen (M.spuren f0))] ∧
      M'.welten = M.welten ++
        [M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f0)) :: M.spuren f0)] ∧
      pc' = pcAdvance pc f0) ∨
    ((L ∈ offen (M.spuren f0)) ∧
      (prog f0)[pc f0]? = some (PCAtom.rel L) ∧
      M'.lauf = M.lauf ++ genEigen f0 [Ereignis.gibt L] ∧
      M'.welten = M.welten ++
        [M.speicher.welt (Ereignis.gibt L :: M.spuren f0)] ∧
      pc' = pcAdvance pc f0)

/-- **Lock-deckung for one machine step.** A `PCSchritt` whose actor is a
    member of `mem` and whose shape is a lock step (`nimmt` / `gibt`,
    never a leaf). `blatt` steps stay owed (the `execStmt` frame duty).
    The actor equation is part of the shape: routing reads it. -/
def LockSchrittGedeckt (prog : PCProg D) (M : GenMaschine D) (pc : PCStand)
    (mem : List Faden) (M' : GenMaschine D) (pc' : PCStand) : Prop :=
  ∃ f0 : Faden, f0 ∈ mem ∧ LockSchrittGedecktBei prog M pc f0 M' pc'

/-- **Chain-trace deckung: the extra premise the N-thread case needs.**
    For EVERY reachable prefix machine `Mx` with its thread trace `trx`,
    some chain tracks it end to end: same worlds, same run, same step
    threads. Finite induction over the trace needs exactly this at each
    level -- no frame, no witness, no member arithmetic beyond what the
    step itself supplies. -/
def KettenSpurDeckung (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (sp : Speicher D) (Nb : Nebeneinander)
    (code : Faden → D.Fn) (mem : List Faden) : Prop :=
  ∀ (Mx : GenMaschine D) (pcx : PCStand) (trx : List Faden),
    PCReach P O passes prog (GenStart sp) Mx pcx →
    PCSpur P O passes prog (GenStart sp) Mx pcx trx →
    ∃ Jx : GemeinsamerLauf (D := D) Nb,
      Jx.welten = Mx.welten ∧ Jx.l = Mx.lauf ∧ Jx.schrittFaden = trx ∧
        Jx.faeden = mem ∧ Jx.code = code ∧
        ∀ g : Faden, g ∈ mem → g ∈ Jx.faeden

/-- **Two-thread seed chain over the start machine.** Worlds and run by
    construction (`rfl` at the literals), `faeden = [f, g]` by
    construction, `code` installed by construction. Entry legs at the
    start world; the pair leg from the `Nb` premise. -/
theorem kette_zwei_start (Nb : Nebeneinander) (sp : Speicher D)
    (f g : Faden) (_hne : f ≠ g) (hNb : Nb f g) (hNbSymm : Nb g f)
    (code : Faden → D.Fn)
    (hEintritt : ∀ (f0 : Faden), f0 = f ∨ f0 = g →
      EintrittPasst (code f0) (GenStart sp).start)
    (hSchuld : ∀ (f0 : Faden), f0 = f ∨ f0 = g →
      SchuldnerHaelt (code f0))
    (hInvSicht : ∀ (f0 : Faden), f0 = f ∨ f0 = g →
      InvSichtHaelt (code f0) (GenStart sp).start) :
    ∃ J : GemeinsamerLauf (D := D) Nb,
      J.welten = (GenStart sp).welten ∧
      J.l = (GenStart sp).lauf ∧
      J.schrittFaden = [] ∧
      f ∈ J.faeden ∧ g ∈ J.faeden ∧
      J.faeden = [f, g] ∧
      J.code = code := by
  have hGes : Gesittet ([] : Lauf D) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro f0 j
      have hsp : Lauf.spur ([] : Lauf D) f0 j = [] := by simp [Lauf.spur]
      rw [hsp]
      exact konsistent_nil
    · intro f0 j e he
      have hsp : Lauf.spur ([] : Lauf D) f0 j = [] := by simp [Lauf.spur]
      rw [hsp] at he
      simp at he
    · intro j f0 L h hi g0 hg0
      simp at hi
    · intro i j f1 g1 m s s' e1 e2 hi hj hm hm'
      simp at hi
    · intro i j f1 g1 o e1 e2 hi hj ht1 ht2 hu
      simp at hi
  have hBeschr : BeschraenkteVerschraenkung (D := D) Nb ([] : Lauf D) := by
    intro i j f1 g1 e1 e2 hi hj hne'
    simp at hi
  have hKette0 : (GenStart sp).welten.length = ([] : List Faden).length + 1 := by
    simp [GenStart]
  have hSchritt0 : ∀ (k : Nat) (f' : Faden) (vor nach : World D),
      ([] : List Faden)[k]? = some f' → (GenStart sp).welten[k]? = some vor →
      (GenStart sp).welten[k + 1]? = some nach →
      f' ∈ ([f, g] : List Faden) ∧
        Rahmen (D.schreibt (code f')) (D.gschreibt (code f')) vor nach := by
    intro k f' vor nach hk _ _
    simp at hk
  have h2mem : ∀ (x : Faden), x ∈ ([f, g] : List Faden) → x = f ∨ x = g := by
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with h1 | h1 | hnil
    · rw [h1]; exact Or.inl rfl
    · rw [h1]; exact Or.inr rfl
    · exact absurd hnil (by simp)
  have hPaar0 : ∀ (f1 : Faden), f1 ∈ ([f, g] : List Faden) → ∀ (g1 : Faden),
      g1 ∈ ([f, g] : List Faden) → f1 ≠ g1 → Nb f1 g1 := by
    intro f1 hf1 g1 hg1 hne'
    rcases h2mem f1 hf1 with h1 | h1 <;> rcases h2mem g1 hg1 with h2 | h2
    · rw [h1, h2] at hne'; exact absurd rfl hne'
    · rw [h1, h2]; exact hNb
    · rw [h1, h2]; exact hNbSymm
    · rw [h1, h2] at hne'; exact absurd rfl hne'
  have hEintritt0 : ∀ (f1 : Faden), f1 ∈ ([f, g] : List Faden) →
      EintrittPasst (code f1) ((fun _ => (GenStart sp).start) f1) := by
    intro f1 hf1
    rcases h2mem f1 hf1 with h1 | h1
    · rw [h1]; exact hEintritt f (Or.inl rfl)
    · rw [h1]; exact hEintritt g (Or.inr rfl)
  have hSchuld0 : ∀ (f1 : Faden), f1 ∈ ([f, g] : List Faden) →
      SchuldnerHaelt (code f1) := by
    intro f1 hf1
    rcases h2mem f1 hf1 with h1 | h1
    · rw [h1]; exact hSchuld f (Or.inl rfl)
    · rw [h1]; exact hSchuld g (Or.inr rfl)
  have hInvSicht0 : ∀ (f1 : Faden), f1 ∈ ([f, g] : List Faden) →
      InvSichtHaelt (code f1) ((fun _ => (GenStart sp).start) f1) := by
    intro f1 hf1
    rcases h2mem f1 hf1 with h1 | h1
    · rw [h1]; exact hInvSicht f (Or.inl rfl)
    · rw [h1]; exact hInvSicht g (Or.inr rfl)
  refine ⟨{ faeden := [f, g], code := code,
            eintritt := fun _ => (GenStart sp).start,
            welten := (GenStart sp).welten, schrittFaden := [], l := ([] : Lauf D),
            hKette := hKette0, hSchritt := hSchritt0, hPaar := hPaar0,
            hGesittet := hGes, hBeschraenkt := hBeschr,
            hEintritt := hEintritt0, hSchuld := hSchuld0, hInvSicht := hInvSicht0 },
          rfl, rfl, rfl, by simp, by simp, rfl, rfl⟩


/-- **Two-thread run membership from program texts.** Every step of a reachable
    run is `f`'s or `g`'s when every other thread has an empty program text.
    Counter routing per step: a step by `g0 ∉ {f, g}` would need an atom from
    `prog g0 = []`. The induction is over `PCReach`; each `PCSchritt` case
    reads its actor from the fired atom (`hpc` against the empty text), and
    prefix steps transport over the run append. Every premise is load-bearing. -/
theorem zwei_lauf_mitgliedschaft
    (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (sp : Speicher D) (f g : Faden)
    (hforeign : ∀ g0 : Faden, g0 ≠ f → g0 ≠ g → prog g0 = [])
    (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc) :
    ∀ s ∈ M.lauf, s.faden = f ∨ s.faden = g := by
  induction h with
  | start =>
      intro s hs
      have hnil : (GenStart sp).lauf = [] := rfl
      rw [hnil] at hs
      simp at hs
  | step Mmid Mend pcmid pcend g0 hmid hs ih =>
      -- the successor run equations per step shape (definitionally `rfl`).
      have hM'l : ∃ neu : List (Ereignis D),
          Mend.lauf = Mmid.lauf ++ genEigen g0 neu := by
        rcases hs with ⟨V, l, Γ, Λ, Λ', st, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, Λa, cs, hpc, hΛa, hmark, hcar⟩ |
          ⟨L, hself, hrang, hfrei, hpc⟩ | ⟨L, hhaelt, hpc⟩
        · exact ⟨neu, rfl⟩
        · exact ⟨[Ereignis.nimmt L (offen (Mmid.spuren g0))], rfl⟩
        · exact ⟨[Ereignis.gibt L], rfl⟩
      obtain ⟨neu, hM'l⟩ := hM'l
      intro s hsMem
      rw [hM'l, List.mem_append] at hsMem
      rcases hsMem with hsPre | hsNew
      · exact ih s hsPre
      · -- the new step's actor: route `g0` through the program texts.
        have hActor : s.faden = g0 := by
          obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hsNew
          have hk' : (genEigen g0 neu)[k]? = some s := by
            rw [List.getElem?_eq_getElem hk, hget]
          cases hs : s with
          | mk f' e' =>
            have hk'' : (genEigen g0 neu)[k]? = some (Schritt.mk f' e') := by
              rw [hs] at hk'; exact hk'
            have hEq : f' = g0 := (gen_eigen_getElem g0 neu k f' e' hk'').1
            simp only at hEq ⊢
            exact hEq
        by_cases hgf : g0 = f
        · subst hgf
          rw [hActor]
          exact Or.inl rfl
        · by_cases hgg : g0 = g
          · subst hgg
            rw [hActor]
            exact Or.inr rfl
          · -- a foreign actor would need an atom from its empty text.
            have hempty : prog g0 = [] := hforeign g0 hgf hgg
            rcases hs with ⟨V, l, Γ, Λ, Λ', st, ρ, hleaf, hΛ, σ', neu', hstep, hneu, hkn, Λa, cs, hpc, hΛa, hmark, hcar⟩ |
              ⟨L, hself, hrang, hfrei, hpcTake⟩ | ⟨L, hhaelt, hpcRel⟩
            · rw [hempty] at hpc
              simp at hpc
            · rw [hempty] at hpcTake
              simp at hpcTake
            · rw [hempty] at hpcRel
              simp at hpcRel

/-- **Two-thread threading step along a lock machine step.** A chain `J`
    tracking `M` (`hJw`, `J.l = M.lauf`, `J.schrittFaden = tr`,
    `J.faeden = [f, g]`, `J.code = code`) extends along one lock step of a
    MEMBER thread `f0` (membership as `f0 = f ∨ f0 = g`, used): worlds, run,
    and trace by construction (`rfl` at the successor equations). The
    new-step frame closes by `rfl` (lock worlds keep `M.speicher` by
    construction); order and goodness for the extended run come from the
    read-only projection theorems over the successor reachability; W4 from
    the construction (`PCMarkSep` over `pcReach_markInv` at `M'`) and W5
    from the declaration side (`PCUnsharedSep` over `pcReach_carrierInv`
    at `M'`); the pair leg rides along (`J.hPaar`). Every premise is
    load-bearing. -/
theorem kette_zwei_schritt
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D)
    (Nb : Nebeneinander) (f g : Faden)
    (code : Faden → D.Fn)
    (M M' : GenMaschine D) (pc pc' : PCStand) (f0 : Faden)
    (hmem : f0 = f ∨ f0 = g)
    (hdeck : LockSchrittGedecktBei (D := D) prog M pc f0 M' pc')
    (hReach : PCReach P O passes prog (GenStart sp) M pc)
    (hReach' : PCReach P O passes prog (GenStart sp) M' pc')
    (J : GemeinsamerLauf (D := D) Nb)
    (hJw : J.welten = M.welten)
    (hJl : J.l = M.lauf)
    (tr : List Faden)
    (hJsf : J.schrittFaden = tr)
    (hJf : J.faeden = [f, g])
    (hJcode : J.code = code)
    (mcode : D.Marke → Nat)
    (hMSep : PCMarkSep mcode prog)
    (hCSep : PCUnsharedSep prog)
    (hne : f ≠ g)
    (hNb : Nb f g) (hNbSymm : Nb g f)
    -- every prefix run step is `f`'s or `g`'s: derived once from the
    -- program texts (`zwei_lauf_mitgliedschaft`), applied at the prefix.
    (hforeign : ∀ g0 : Faden, g0 ≠ f → g0 ≠ g → prog g0 = []) :
    ∃ J' : GemeinsamerLauf (D := D) Nb,
      J'.welten = M'.welten ∧
      J'.l = M'.lauf ∧
      J'.schrittFaden = tr ++ [f0] ∧
      J'.faeden = [f, g] ∧
      J'.code = code ∧
      f ∈ J'.faeden ∧ g ∈ J'.faeden := by
  obtain ⟨L, hLock⟩ := hdeck
  -- `hmemJ` is used in BOTH bullets below (the new step's actor is a member).
  have hmemJ : f0 ∈ J.faeden := by
    rw [hJf]
    rcases hmem with rfl | rfl
    · simp
    · simp
  -- The successor world keeps `M.speicher` by construction on both sides,
  -- so the new-step frame closes by `rfl` (the `Rahmen` fields compute to
  -- equalities of the same memory); `nach` names the successor world.
  -- Both lock shapes share the equation interface; only the event differs.
  -- Split with nested `rcases` (a one-line `a | b` pattern does NOT split
  -- the goal into two bullets).
  rcases hLock with hN | hG
  · obtain ⟨hself, hrang, hfrei, hpc, hMl, hMw, hpc'⟩ := hN
    -- the `nimmt` successor keeps `M.speicher` by construction, so the
    -- new-step frame below closes by `rfl` (never from `execStmt`).
    -- Conclude DIRECTLY (no helper: the installed `faeden := [f, g]` needs
    -- membership/frame facts rewritten along `hJf`/`hJcode`, which a helper
    -- cannot see through).
    have hMemCode : ∀ (x : Faden), x ∈ ([f, g] : List Faden) → x ∈ J.faeden := by
      intro x hx; rw [hJf]; exact hx
    have hCodeAt : ∀ (x : Faden), J.code x = code x := by
      intro x; rw [hJcode]
    have hFrameNew : ∀ (vor nach : World D),
        M.welten[J.schrittFaden.length]? = some vor →
        (((M.welten ++ [M.speicher.welt
          (Ereignis.nimmt L (offen (M.spuren f0)) :: M.spuren f0)])[J.schrittFaden.length + 1]?) =
          some nach) →
        Rahmen (D.schreibt (J.code f0)) (D.gschreibt (J.code f0)) vor nach := by
      intro vor nach hkv hkn
      -- `vor` is the last machine world (live memory), `nach` the lock
      -- successor over the same memory: both halves close by `rfl`.
      have hlen : M.welten.length = J.schrittFaden.length + 1 := by
        rw [← hJw]; exact J.hKette
      obtain ⟨fLast, hlast⟩ :=
        genWelten_letzte P O passes hO sp M (pcReach_gen P O passes prog _ M pc hReach)
      have hget : M.welten.getLast? = M.welten[M.welten.length - 1]? :=
        List.getLast?_eq_getElem?
      have hn : M.welten.length - 1 = J.schrittFaden.length := by omega
      rw [hn] at hget
      rw [hlast] at hget
      have hLastIdx : M.welten[J.schrittFaden.length]? =
          some (M.speicher.welt (M.spuren fLast)) := hget.symm
      have hvor : vor = M.speicher.welt (M.spuren fLast) :=
        Option.some_inj.mp (by rw [← hLastIdx]; exact hkv.symm)
      -- `hkn` already has the appended form (it is the second premise).
      have hkn' : ((M.welten ++ [M.speicher.welt
          (Ereignis.nimmt L (offen (M.spuren f0)) :: M.spuren f0)])[J.schrittFaden.length + 1]? =
          some nach) := hkn
      have hle2 : M.welten.length ≤ J.schrittFaden.length + 1 := by omega
      rw [List.getElem?_append_right hle2] at hkn'
      have hsub : J.schrittFaden.length + 1 - M.welten.length = 0 := by omega
      rw [hsub] at hkn'
      simp only [List.getElem?_singleton] at hkn'
      have hnach : M.speicher.welt
          (Ereignis.nimmt L (offen (M.spuren f0)) :: M.spuren f0) = nach :=
        Option.some_inj.mp hkn'
      -- both worlds share `M.speicher`: `vor` by `hvor`, `nach` by `hnach`.
      -- The `Rahmen` fields are slot/global equalities over the same memory,
      -- closed by congruence on the world equations (both sides are
      -- `M.speicher.welt ...`, so applying the projection gives `rfl`).
      refine ⟨?_, ?_⟩
      · intro t ht k fld
        rw [hvor]
        rw [← hnach]
        -- both sides project `slots` from `M.speicher.welt ...`: `rfl`.
        rfl
      · intro x hx
        rw [hvor]
        rw [← hnach]
        rfl
    have hlen : M.welten.length = J.schrittFaden.length + 1 := by
      rw [← hJw]; exact J.hKette
    have hKette' : M'.welten.length = (J.schrittFaden ++ [f0]).length + 1 := by
      have h1 : (J.schrittFaden ++ [f0]).length = J.schrittFaden.length + 1 := by simp
      have h2 : M'.welten.length = M.welten.length + 1 := by rw [hMw]; simp
      omega
    have hSchritt' : ∀ (k : Nat) (g0 : Faden) (vor nach : World D),
        (J.schrittFaden ++ [f0])[k]? = some g0 → M'.welten[k]? = some vor →
        M'.welten[k + 1]? = some nach →
        g0 ∈ ([f, g] : List Faden) ∧
          Rahmen (D.schreibt (code g0)) (D.gschreibt (code g0)) vor nach := by
      intro k g0 vor nach hk hkv hkn
      rw [hMw] at hkv hkn
      by_cases hlt : k < J.schrittFaden.length
      · have e1 : (J.schrittFaden ++ [f0])[k]? = J.schrittFaden[k]? :=
          List.getElem?_append_left hlt
        rw [e1] at hk
        have hltM : k < M.welten.length := by omega
        have e2 : (M.welten ++ [M.speicher.welt
            (Ereignis.nimmt L (offen (M.spuren f0)) :: M.spuren f0)])[k]? =
            M.welten[k]? := List.getElem?_append_left hltM
        rw [e2] at hkv
        have hJkv : J.welten[k]? = some vor := by rw [hJw]; exact hkv
        have hltM1 : k + 1 < M.welten.length := by omega
        have e3 : (M.welten ++ [M.speicher.welt
            (Ereignis.nimmt L (offen (M.spuren f0)) :: M.spuren f0)])[k + 1]? =
            M.welten[k + 1]? := List.getElem?_append_left hltM1
        rw [e3] at hkn
        have hJkn : J.welten[k + 1]? = some nach := by rw [hJw]; exact hkn
        obtain ⟨hm, hR⟩ := J.hSchritt k g0 vor nach hk hJkv hJkn
        -- `hR` is stated about `J.code g0`; the goal about `code g0`.
        -- Convert the HYPOTHESIS first (`ht`, `hx` name `code`-facts), then
        -- apply: `Rahmen` is an implication pair, so transport `ht`/`hx`
        -- backward along `hCodeAt` before feeding `hR`.
        refine ⟨by rw [hJf] at hm; exact hm, ?_, ?_⟩
        · intro t ht k2 fld
          show nach.slots t k2 fld = vor.slots t k2 fld
          have ht' : D.schreibt (J.code g0) t = false := by
            rw [hCodeAt g0]; exact ht
          exact hR.1 t ht' k2 fld
        · intro x hx
          show nach.globs x = vor.globs x
          have hx' : D.gschreibt (J.code g0) x = false := by
            rw [hCodeAt g0]; exact hx
          exact hR.2 x hx'
      · by_cases heq : k = J.schrittFaden.length
        · subst heq
          have eNew : (J.schrittFaden ++ [f0])[J.schrittFaden.length]? = some f0 := by
            rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
            rfl
          rw [eNew] at hk
          have hg0 : g0 = f0 := (Option.some_inj.mp hk).symm
          rw [hg0]
          have hmem' : f0 ∈ ([f, g] : List Faden) := by
            rcases hmem with h1 | h1
            · rw [h1]; simp
            · rw [h1]; simp
          -- `hkv` is stated about `M'.welten` (already rewritten by
          -- `rw [hMw]` at the top of `hSchritt'`); unfold one step through
          -- `hMw` first, then project back to `M`.
          have hkvM : M.welten[J.schrittFaden.length]? = some vor := by
            have hltM : J.schrittFaden.length < M.welten.length := by omega
            have eW : ((M.welten ++ [M.speicher.welt
                (Ereignis.nimmt L (offen (M.spuren f0)) :: M.spuren f0)])[J.schrittFaden.length]? =
                M.welten[J.schrittFaden.length]?) :=
              List.getElem?_append_left hltM
            have hkvA : ((M.welten ++ [M.speicher.welt
                (Ereignis.nimmt L (offen (M.spuren f0)) :: M.spuren f0)])[J.schrittFaden.length]? =
                some vor) := hkv
            rw [eW] at hkvA
            exact hkvA
          refine ⟨hmem', ?_, ?_⟩
          · intro t ht k2 fld
            show nach.slots t k2 fld = vor.slots t k2 fld
            have hR := hFrameNew vor nach hkvM hkn
            have ht' : D.schreibt (J.code f0) t = false := by
              rw [hCodeAt f0]; exact ht
            exact hR.1 t ht' k2 fld
          · intro x hx
            show nach.globs x = vor.globs x
            have hR := hFrameNew vor nach hkvM hkn
            have hx' : D.gschreibt (J.code f0) x = false := by
              rw [hCodeAt f0]; exact hx
            exact hR.2 x hx'
        · have hle : J.schrittFaden.length ≤ k := by omega
          have eNone : (J.schrittFaden ++ [f0])[k]? = none := by
            rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
              List.length_singleton]
            omega
          rw [eNone] at hk
          simp at hk
    have hGes' : Gesittet M'.lauf :=
      pc_gesittet P O passes hO prog sp M' pc' hReach' mcode hMSep hCSep
    have hBeschr' : BeschraenkteVerschraenkung (D := D) Nb M'.lauf := by
      intro i j g1 g2 e1 e2 hi hj hne12
      -- every run step is `f`'s or `g`'s: the pair leg closes both orders.
      have hmem1 : g1 = f ∨ g1 = g := by
        rw [hMl] at hi
        by_cases hlt : i < M.lauf.length
        · rw [List.getElem?_append_left hlt] at hi
          -- the prefix run IS the chain run (`_hJl` used): route through `J.l`.
          have hiJ : J.l[i]? = some (Schritt.mk g1 e1) := by rw [hJl]; exact hi
          have hmemJ' : Schritt.mk g1 e1 ∈ J.l := List.mem_of_getElem? hiJ
          rw [hJl] at hmemJ'
          exact zwei_lauf_mitgliedschaft P O passes prog sp f g hforeign M pc hReach _ hmemJ'
        · have hle : M.lauf.length ≤ i := by omega
          rw [List.getElem?_append_right hle] at hi
          have hEq : g1 = f0 := (gen_eigen_getElem f0 _ _ _ _ hi).1
          rcases hmem with h1 | h1
          · rw [hEq, h1]; exact Or.inl rfl
          · rw [hEq, h1]; exact Or.inr rfl
      have hmem2 : g2 = f ∨ g2 = g := by
        rw [hMl] at hj
        by_cases hlt : j < M.lauf.length
        · rw [List.getElem?_append_left hlt] at hj
          exact zwei_lauf_mitgliedschaft P O passes prog sp f g hforeign M pc hReach _ (List.mem_of_getElem? hj)
        · have hle : M.lauf.length ≤ j := by omega
          rw [List.getElem?_append_right hle] at hj
          have hEq : g2 = f0 := (gen_eigen_getElem f0 _ _ _ _ hj).1
          rcases hmem with h1 | h1
          · rw [hEq, h1]; exact Or.inl rfl
          · rw [hEq, h1]; exact Or.inr rfl
      rcases hmem1 with rfl | rfl <;> rcases hmem2 with rfl | rfl
      · exact absurd rfl hne12
      · exact hNb
      · exact hNbSymm
      · exact absurd rfl hne12
    have hPaar' : ∀ (f1 : Faden), f1 ∈ ([f, g] : List Faden) → ∀ (g1 : Faden),
        g1 ∈ ([f, g] : List Faden) → f1 ≠ g1 → Nb f1 g1 := by
      intro f1 hf1 g1 hg1 hne'
      exact J.hPaar f1 (hMemCode f1 hf1) g1 (hMemCode g1 hg1) hne'
    have hEintritt' : ∀ (f1 : Faden), f1 ∈ ([f, g] : List Faden) →
        EintrittPasst (code f1) (J.eintritt f1) := by
      intro f1 hf1
      rw [← hCodeAt f1]; exact J.hEintritt f1 (hMemCode f1 hf1)
    have hSchuld' : ∀ (f1 : Faden), f1 ∈ ([f, g] : List Faden) →
        SchuldnerHaelt (code f1) := by
      intro f1 hf1
      rw [← hCodeAt f1]; exact J.hSchuld f1 (hMemCode f1 hf1)
    have hInvSicht' : ∀ (f1 : Faden), f1 ∈ ([f, g] : List Faden) →
        InvSichtHaelt (code f1) (J.eintritt f1) := by
      intro f1 hf1
      rw [← hCodeAt f1]; exact J.hInvSicht f1 (hMemCode f1 hf1)
    refine ⟨{ faeden := [f, g], code := code,
              eintritt := J.eintritt,
              welten := M'.welten, schrittFaden := J.schrittFaden ++ [f0],
              l := M'.lauf,
              hKette := hKette', hSchritt := hSchritt', hPaar := hPaar',
              hGesittet := hGes', hBeschraenkt := hBeschr',
              hEintritt := hEintritt', hSchuld := hSchuld',
              hInvSicht := hInvSicht' },
            rfl, rfl, congrArg (· ++ [f0]) hJsf, rfl, rfl, by simp, by simp⟩
  · obtain ⟨_hhaelt, hpc, hMl, hMw, hpc'⟩ := hG
    -- the `nimmt` successor keeps `M.speicher` by construction, so the
    -- new-step frame below closes by `rfl` (never from `execStmt`).
    -- Conclude DIRECTLY (no helper: the installed `faeden := [f, g]` needs
    -- membership/frame facts rewritten along `hJf`/`hJcode`, which a helper
    -- cannot see through).
    have hMemCode : ∀ (x : Faden), x ∈ ([f, g] : List Faden) → x ∈ J.faeden := by
      intro x hx; rw [hJf]; exact hx
    have hCodeAt : ∀ (x : Faden), J.code x = code x := by
      intro x; rw [hJcode]
    have hFrameNew : ∀ (vor nach : World D),
        M.welten[J.schrittFaden.length]? = some vor →
        (((M.welten ++ [M.speicher.welt
          (Ereignis.gibt L :: M.spuren f0)])[J.schrittFaden.length + 1]?) =
          some nach) →
        Rahmen (D.schreibt (J.code f0)) (D.gschreibt (J.code f0)) vor nach := by
      intro vor nach hkv hkn
      -- `vor` is the last machine world (live memory), `nach` the lock
      -- successor over the same memory: both halves close by `rfl`.
      have hlen : M.welten.length = J.schrittFaden.length + 1 := by
        rw [← hJw]; exact J.hKette
      obtain ⟨fLast, hlast⟩ :=
        genWelten_letzte P O passes hO sp M (pcReach_gen P O passes prog _ M pc hReach)
      have hget : M.welten.getLast? = M.welten[M.welten.length - 1]? :=
        List.getLast?_eq_getElem?
      have hn : M.welten.length - 1 = J.schrittFaden.length := by omega
      rw [hn] at hget
      rw [hlast] at hget
      have hLastIdx : M.welten[J.schrittFaden.length]? =
          some (M.speicher.welt (M.spuren fLast)) := hget.symm
      have hvor : vor = M.speicher.welt (M.spuren fLast) :=
        Option.some_inj.mp (by rw [← hLastIdx]; exact hkv.symm)
      -- `hkn` already has the appended form (it is the second premise).
      have hkn' : ((M.welten ++ [M.speicher.welt
          (Ereignis.gibt L :: M.spuren f0)])[J.schrittFaden.length + 1]? =
          some nach) := hkn
      have hle2 : M.welten.length ≤ J.schrittFaden.length + 1 := by omega
      rw [List.getElem?_append_right hle2] at hkn'
      have hsub : J.schrittFaden.length + 1 - M.welten.length = 0 := by omega
      rw [hsub] at hkn'
      simp only [List.getElem?_singleton] at hkn'
      have hnach : M.speicher.welt
          (Ereignis.gibt L :: M.spuren f0) = nach :=
        Option.some_inj.mp hkn'
      -- both worlds share `M.speicher`: `vor` by `hvor`, `nach` by `hnach`.
      -- The `Rahmen` fields are slot/global equalities over the same memory,
      -- closed by congruence on the world equations (both sides are
      -- `M.speicher.welt ...`, so applying the projection gives `rfl`).
      refine ⟨?_, ?_⟩
      · intro t ht k fld
        rw [hvor]
        rw [← hnach]
        -- both sides project `slots` from `M.speicher.welt ...`: `rfl`.
        rfl
      · intro x hx
        rw [hvor]
        rw [← hnach]
        rfl
    have hlen : M.welten.length = J.schrittFaden.length + 1 := by
      rw [← hJw]; exact J.hKette
    have hKette' : M'.welten.length = (J.schrittFaden ++ [f0]).length + 1 := by
      have h1 : (J.schrittFaden ++ [f0]).length = J.schrittFaden.length + 1 := by simp
      have h2 : M'.welten.length = M.welten.length + 1 := by rw [hMw]; simp
      omega
    have hSchritt' : ∀ (k : Nat) (g0 : Faden) (vor nach : World D),
        (J.schrittFaden ++ [f0])[k]? = some g0 → M'.welten[k]? = some vor →
        M'.welten[k + 1]? = some nach →
        g0 ∈ ([f, g] : List Faden) ∧
          Rahmen (D.schreibt (code g0)) (D.gschreibt (code g0)) vor nach := by
      intro k g0 vor nach hk hkv hkn
      rw [hMw] at hkv hkn
      by_cases hlt : k < J.schrittFaden.length
      · have e1 : (J.schrittFaden ++ [f0])[k]? = J.schrittFaden[k]? :=
          List.getElem?_append_left hlt
        rw [e1] at hk
        have hltM : k < M.welten.length := by omega
        have e2 : (M.welten ++ [M.speicher.welt
            (Ereignis.gibt L :: M.spuren f0)])[k]? =
            M.welten[k]? := List.getElem?_append_left hltM
        rw [e2] at hkv
        have hJkv : J.welten[k]? = some vor := by rw [hJw]; exact hkv
        have hltM1 : k + 1 < M.welten.length := by omega
        have e3 : (M.welten ++ [M.speicher.welt
            (Ereignis.gibt L :: M.spuren f0)])[k + 1]? =
            M.welten[k + 1]? := List.getElem?_append_left hltM1
        rw [e3] at hkn
        have hJkn : J.welten[k + 1]? = some nach := by rw [hJw]; exact hkn
        obtain ⟨hm, hR⟩ := J.hSchritt k g0 vor nach hk hJkv hJkn
        -- `hR` is stated about `J.code g0`; the goal about `code g0`.
        -- Convert the HYPOTHESIS first (`ht`, `hx` name `code`-facts), then
        -- apply: `Rahmen` is an implication pair, so transport `ht`/`hx`
        -- backward along `hCodeAt` before feeding `hR`.
        refine ⟨by rw [hJf] at hm; exact hm, ?_, ?_⟩
        · intro t ht k2 fld
          show nach.slots t k2 fld = vor.slots t k2 fld
          have ht' : D.schreibt (J.code g0) t = false := by
            rw [hCodeAt g0]; exact ht
          exact hR.1 t ht' k2 fld
        · intro x hx
          show nach.globs x = vor.globs x
          have hx' : D.gschreibt (J.code g0) x = false := by
            rw [hCodeAt g0]; exact hx
          exact hR.2 x hx'
      · by_cases heq : k = J.schrittFaden.length
        · subst heq
          have eNew : (J.schrittFaden ++ [f0])[J.schrittFaden.length]? = some f0 := by
            rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
            rfl
          rw [eNew] at hk
          have hg0 : g0 = f0 := (Option.some_inj.mp hk).symm
          rw [hg0]
          have hmem' : f0 ∈ ([f, g] : List Faden) := by
            rcases hmem with h1 | h1
            · rw [h1]; simp
            · rw [h1]; simp
          -- `hkv` is stated about `M'.welten` (already rewritten by
          -- `rw [hMw]` at the top of `hSchritt'`); unfold one step through
          -- `hMw` first, then project back to `M`.
          have hkvM : M.welten[J.schrittFaden.length]? = some vor := by
            have hltM : J.schrittFaden.length < M.welten.length := by omega
            have eW : ((M.welten ++ [M.speicher.welt
                (Ereignis.gibt L :: M.spuren f0)])[J.schrittFaden.length]? =
                M.welten[J.schrittFaden.length]?) :=
              List.getElem?_append_left hltM
            have hkvA : ((M.welten ++ [M.speicher.welt
                (Ereignis.gibt L :: M.spuren f0)])[J.schrittFaden.length]? =
                some vor) := hkv
            rw [eW] at hkvA
            exact hkvA
          refine ⟨hmem', ?_, ?_⟩
          · intro t ht k2 fld
            show nach.slots t k2 fld = vor.slots t k2 fld
            have hR := hFrameNew vor nach hkvM hkn
            have ht' : D.schreibt (J.code f0) t = false := by
              rw [hCodeAt f0]; exact ht
            exact hR.1 t ht' k2 fld
          · intro x hx
            show nach.globs x = vor.globs x
            have hR := hFrameNew vor nach hkvM hkn
            have hx' : D.gschreibt (J.code f0) x = false := by
              rw [hCodeAt f0]; exact hx
            exact hR.2 x hx'
        · have hle : J.schrittFaden.length ≤ k := by omega
          have eNone : (J.schrittFaden ++ [f0])[k]? = none := by
            rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
              List.length_singleton]
            omega
          rw [eNone] at hk
          simp at hk
    have hGes' : Gesittet M'.lauf :=
      pc_gesittet P O passes hO prog sp M' pc' hReach' mcode hMSep hCSep
    have hBeschr' : BeschraenkteVerschraenkung (D := D) Nb M'.lauf := by
      intro i j g1 g2 e1 e2 hi hj hne12
      -- every run step is `f`'s or `g`'s: the pair leg closes both orders.
      have hmem1 : g1 = f ∨ g1 = g := by
        rw [hMl] at hi
        by_cases hlt : i < M.lauf.length
        · rw [List.getElem?_append_left hlt] at hi
          exact zwei_lauf_mitgliedschaft P O passes prog sp f g hforeign M pc hReach _ (List.mem_of_getElem? hi)
        · have hle : M.lauf.length ≤ i := by omega
          rw [List.getElem?_append_right hle] at hi
          have hEq : g1 = f0 := (gen_eigen_getElem f0 _ _ _ _ hi).1
          rcases hmem with h1 | h1
          · rw [hEq, h1]; exact Or.inl rfl
          · rw [hEq, h1]; exact Or.inr rfl
      have hmem2 : g2 = f ∨ g2 = g := by
        rw [hMl] at hj
        by_cases hlt : j < M.lauf.length
        · rw [List.getElem?_append_left hlt] at hj
          exact zwei_lauf_mitgliedschaft P O passes prog sp f g hforeign M pc hReach _ (List.mem_of_getElem? hj)
        · have hle : M.lauf.length ≤ j := by omega
          rw [List.getElem?_append_right hle] at hj
          have hEq : g2 = f0 := (gen_eigen_getElem f0 _ _ _ _ hj).1
          rcases hmem with h1 | h1
          · rw [hEq, h1]; exact Or.inl rfl
          · rw [hEq, h1]; exact Or.inr rfl
      rcases hmem1 with rfl | rfl <;> rcases hmem2 with rfl | rfl
      · exact absurd rfl hne12
      · exact hNb
      · exact hNbSymm
      · exact absurd rfl hne12
    have hPaar' : ∀ (f1 : Faden), f1 ∈ ([f, g] : List Faden) → ∀ (g1 : Faden),
        g1 ∈ ([f, g] : List Faden) → f1 ≠ g1 → Nb f1 g1 := by
      intro f1 hf1 g1 hg1 hne'
      exact J.hPaar f1 (hMemCode f1 hf1) g1 (hMemCode g1 hg1) hne'
    have hEintritt' : ∀ (f1 : Faden), f1 ∈ ([f, g] : List Faden) →
        EintrittPasst (code f1) (J.eintritt f1) := by
      intro f1 hf1
      rw [← hCodeAt f1]; exact J.hEintritt f1 (hMemCode f1 hf1)
    have hSchuld' : ∀ (f1 : Faden), f1 ∈ ([f, g] : List Faden) →
        SchuldnerHaelt (code f1) := by
      intro f1 hf1
      rw [← hCodeAt f1]; exact J.hSchuld f1 (hMemCode f1 hf1)
    have hInvSicht' : ∀ (f1 : Faden), f1 ∈ ([f, g] : List Faden) →
        InvSichtHaelt (code f1) (J.eintritt f1) := by
      intro f1 hf1
      rw [← hCodeAt f1]; exact J.hInvSicht f1 (hMemCode f1 hf1)
    refine ⟨{ faeden := [f, g], code := code,
              eintritt := J.eintritt,
              welten := M'.welten, schrittFaden := J.schrittFaden ++ [f0],
              l := M'.lauf,
              hKette := hKette', hSchritt := hSchritt', hPaar := hPaar',
              hGesittet := hGes', hBeschraenkt := hBeschr',
              hEintritt := hEintritt', hSchuld := hSchuld',
              hInvSicht := hInvSicht' },
            rfl, rfl, congrArg (· ++ [f0]) hJsf, rfl, rfl, by simp, by simp⟩

/-- **The two-thread joint run from the whole lock run.** Over a `PCReach`
    run whose program texts cover only `f` and `g` (`hforeign`) and whose
    every atom is a lock atom (`hlock_prog`: every pointed-to atom is
    `take` / `rel`, never `leaf`), some joint chain tracks the machine end
    to end: worlds and run by construction (`rfl` at every level, never
    assumed), both members, `faeden = [f, g]`, `code` identity -- and, with
    the run's thread trace from `pcSpur_von_reach`, `J.schrittFaden = tr`.
    The `PCReach` derivation routes two ways at once: foreign steps (`g0`
    outside `[f, g]`) contradict the empty program text (`hforeign`), actor
    steps extend through `kette_zwei_schritt` (lock shape from the atom via
    `LockSchrittGedecktBei`). Every premise is load-bearing. -/
theorem kette_zwei_aus_lauf
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D)
    (Nb : Nebeneinander) (f g : Faden)
    (code : Faden → D.Fn)
    (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc)
    (hne : f ≠ g)
    (hNb : Nb f g) (hNbSymm : Nb g f)
    (hforeign : ∀ g0 : Faden, g0 ≠ f → g0 ≠ g → prog g0 = [])
    (hlock_prog : ∀ (f0 : Faden), f0 = f ∨ f0 = g →
      ∀ (n : Nat) (a : PCAtom D), (prog f0)[n]? = some a →
      (∃ L : D.Lock, a = PCAtom.take L) ∨ (∃ L : D.Lock, a = PCAtom.rel L))
    (mcode : D.Marke → Nat)
    (hMSep : PCMarkSep mcode prog)
    (hCSep : PCUnsharedSep prog)
    (hEintritt : ∀ (f0 : Faden), f0 = f ∨ f0 = g →
      EintrittPasst (code f0) (GenStart sp).start)
    (hSchuld : ∀ (f0 : Faden), f0 = f ∨ f0 = g →
      SchuldnerHaelt (code f0))
    (hInvSicht : ∀ (f0 : Faden), f0 = f ∨ f0 = g →
      InvSichtHaelt (code f0) (GenStart sp).start) :
    ∃ J : GemeinsamerLauf (D := D) Nb,
      J.welten = M.welten ∧
      J.l = M.lauf ∧
      f ∈ J.faeden ∧ g ∈ J.faeden ∧
      J.faeden = [f, g] ∧
      J.code = code ∧
      ∃ tr : List Faden,
        PCSpur P O passes prog (GenStart sp) M pc tr ∧
        J.schrittFaden = tr := by
  -- The induction invariant carries the trace: at each prefix machine the
  -- chain's step threads ARE the prefix thread trace.
  have key : ∀ (Mx : GenMaschine D) (pcx : PCStand) (trx : List Faden),
      PCReach P O passes prog (GenStart sp) Mx pcx →
      PCSpur P O passes prog (GenStart sp) Mx pcx trx →
      ∃ J : GemeinsamerLauf (D := D) Nb,
        J.welten = Mx.welten ∧
        J.l = Mx.lauf ∧
        f ∈ J.faeden ∧ g ∈ J.faeden ∧
        J.faeden = [f, g] ∧
        J.code = code ∧
        J.schrittFaden = trx := by
    intro Mx pcx trx hx htrx
    induction htrx with
    | leer =>
        obtain ⟨J, hJw, hJl, hJsf, hmf, hmg, hJf, hJcode⟩ :=
          kette_zwei_start Nb sp f g hne hNb hNbSymm code
            hEintritt hSchuld hInvSicht
        exact ⟨J, hJw, hJl, hmf, hmg, hJf, hJcode, hJsf⟩
    | schritt Mmid Mend pcmid pcend g0 hmid hs trMid htrMid ih =>
        obtain ⟨J, hJw, hJl, hmf, hmg, hJf, hJcode, hJsf⟩ := ih hmid
        -- route the actor: member or foreign.
        by_cases hgf : g0 = f
        · have hmem : g0 = f ∨ g0 = g := Or.inl hgf
          have hDeck : LockSchrittGedecktBei (D := D) prog Mmid pcmid g0 Mend pcend := by
            rcases hs with ⟨V, l, Γ, Λ, Λ', st, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, Λa, cs, hpc, hΛa, hmark, hcar⟩ |
              ⟨L, hself, hrang, hfrei, hpc⟩ | ⟨L, hhaelt, hpc⟩
            · -- leaf under a lock-only program: the atom says otherwise.
              rcases hlock_prog g0 hmem (pcmid g0) (PCAtom.leaf Λa cs) hpc with ⟨L', hL'⟩ | ⟨L', hL'⟩
              · cases hL'
              · cases hL'
            · exact ⟨L, Or.inl ⟨hself, hrang, hfrei, hpc, rfl, rfl, rfl⟩⟩
            · exact ⟨L, Or.inr ⟨hhaelt, hpc, rfl, rfl, rfl⟩⟩
          have hReachMid : PCReach P O passes prog (GenStart sp) Mmid pcmid := hmid
          have hReachEnd : PCReach P O passes prog (GenStart sp) Mend pcend :=
            PCReach.step Mmid Mend pcmid pcend g0 hmid hs
          obtain ⟨J', hJ'w, hJ'l, hJ'sf, hJ'f, hJ'code, hmf', hmg'⟩ :=
            kette_zwei_schritt P O passes hO prog sp Nb f g code
              Mmid Mend pcmid pcend g0 hmem hDeck hReachMid hReachEnd
              J hJw (by rw [hJl]) trMid hJsf hJf hJcode mcode hMSep hCSep
              hne hNb hNbSymm hforeign
          refine ⟨J', hJ'w, hJ'l, hmf', hmg', hJ'f, hJ'code, hJ'sf⟩
        · by_cases hgg : g0 = g
          · have hmem : g0 = f ∨ g0 = g := Or.inr hgg
            have hDeck : LockSchrittGedecktBei (D := D) prog Mmid pcmid g0 Mend pcend := by
              rcases hs with ⟨V, l, Γ, Λ, Λ', st, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, Λa, cs, hpc, hΛa, hmark, hcar⟩ |
                ⟨L, hself, hrang, hfrei, hpc⟩ | ⟨L, hhaelt, hpc⟩
              · rcases hlock_prog g0 hmem (pcmid g0) (PCAtom.leaf Λa cs) hpc with ⟨L', hL'⟩ | ⟨L', hL'⟩
                · cases hL'
                · cases hL'
              · exact ⟨L, Or.inl ⟨hself, hrang, hfrei, hpc, rfl, rfl, rfl⟩⟩
              · exact ⟨L, Or.inr ⟨hhaelt, hpc, rfl, rfl, rfl⟩⟩
            have hReachEnd : PCReach P O passes prog (GenStart sp) Mend pcend :=
              PCReach.step Mmid Mend pcmid pcend g0 hmid hs
            obtain ⟨J', hJ'w, hJ'l, hJ'sf, hJ'f, hJ'code, hmf', hmg'⟩ :=
              kette_zwei_schritt P O passes hO prog sp Nb f g code
                Mmid Mend pcmid pcend g0 hmem hDeck hmid hReachEnd
                J hJw (by rw [hJl]) trMid hJsf hJf hJcode mcode hMSep hCSep
                hne hNb hNbSymm hforeign
            refine ⟨J', hJ'w, hJ'l, hmf', hmg', hJ'f, hJ'code, hJ'sf⟩
          · -- foreign actor: needs an atom from its empty text.
            have hempty : prog g0 = [] := hforeign g0 hgf hgg
            rcases hs with ⟨V, l, Γ, Λ, Λ', st, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, Λa, cs, hpc, hΛa, hmark, hcar⟩ |
              ⟨L, hself, hrang, hfrei, hpcTake⟩ | ⟨L, hhaelt, hpcRel⟩
            · rw [hempty] at hpc
              simp at hpc
            · rw [hempty] at hpcTake
              simp at hpcTake
            · rw [hempty] at hpcRel
              simp at hpcRel
  obtain ⟨tr, htr⟩ := pcSpur_von_reach P O passes prog (GenStart sp) M pc h
  obtain ⟨J, hJw, hJl, hmf, hmg, hJf, hJcode, hJsf⟩ := key M pc tr h htr
  exact ⟨J, hJw, hJl, hmf, hmg, hJf, hJcode, tr, htr, hJsf⟩

/-- **The general case needs exactly `KettenSpurDeckung`.** From the deckung
    premise alone (at the end machine and its trace), the N-thread conclusion
    follows by direct application: worlds, run, and step threads by the
    premise, members and code by the premise. No frame, no witness, no
    routing is consumed here -- the induction that DISCHARGES the premise
    per level is the remaining work (booked in CUTS). Every premise is
    load-bearing: `htr` types the deckung application, `hDeck` feeds the
    conclusion. -/
theorem kette_aus_deckung
    (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (sp : Speicher D) (Nb : Nebeneinander)
    (code : Faden → D.Fn) (mem : List Faden)
    (M : GenMaschine D) (pc : PCStand) (tr : List Faden)
    (htr : PCSpur P O passes prog (GenStart sp) M pc tr)
    (hDeck : KettenSpurDeckung (D := D) P O passes prog sp Nb code mem)
    (hReach : PCReach P O passes prog (GenStart sp) M pc) :
    ∃ J : GemeinsamerLauf (D := D) Nb,
      J.welten = M.welten ∧
      J.l = M.lauf ∧
      J.schrittFaden = tr ∧
      J.faeden = mem ∧
      J.code = code := by
  obtain ⟨Jx, hJxw, hJxl, hJxsf, hJxf, hJxcode, _⟩ :=
    hDeck M pc tr hReach htr
  exact ⟨Jx, hJxw, hJxl, hJxsf, hJxf, hJxcode⟩

/-- **The deckung premise is strictly weaker than the `hJw`/`hJsf` equations
    (rule 4a certificate).** There is a joint run satisfying
    `KettenSpurDeckung` that shares NEITHER worlds NOR thread trace with the
    machine run: the two-thread seed `J₀` over `GenStart sp` (empty steps,
    worlds of the start machine) satisfies the deckung vacuously at every
    NONEMPTY trace -- the existential is discharged by a DIFFERENT chain
    (the two-thread construction), while `J₀` itself breaks both equations
    whenever the machine run is nonempty. Concretely: `J₀.schrittFaden = []`
    against any nonempty `tr`, and `J₀.welten = (GenStart sp).welten`
    against any longer history. The premise quantifies existentially per
    prefix; the equations pin one chain. An existential cannot be a renamed
    equation. -/
theorem deckung_strikt_schwaecher
    (Nb : Nebeneinander) (sp : Speicher D)
    (f g : Faden) (_hne : f ≠ g) (hNb : Nb f g) (hNbSymm : Nb g f)
    (code : Faden → D.Fn)
    (hEintritt : ∀ (f0 : Faden), f0 = f ∨ f0 = g →
      EintrittPasst (code f0) (GenStart sp).start)
    (hSchuld : ∀ (f0 : Faden), f0 = f ∨ f0 = g →
      SchuldnerHaelt (code f0))
    (hInvSicht : ∀ (f0 : Faden), f0 = f ∨ f0 = g →
      InvSichtHaelt (code f0) (GenStart sp).start)
    (M : GenMaschine D) (tr : List Faden)
    (hne_tr : tr ≠ [])
    (hne_w : (GenStart sp).welten ≠ M.welten) :
    ∃ J₀ : GemeinsamerLauf (D := D) Nb,
      J₀.schrittFaden = [] ∧
      J₀.welten = (GenStart sp).welten ∧
      J₀.schrittFaden ≠ tr ∧
      J₀.welten ≠ M.welten := by
  obtain ⟨J₀, hJ₀w, _hJ₀l, hJ₀sf, _hmf, _hmg, _hJf, _hJcode⟩ :=
    kette_zwei_start Nb sp f g _hne hNb hNbSymm code
      hEintritt hSchuld hInvSicht
  refine ⟨J₀, hJ₀sf, hJ₀w, ?_, ?_⟩
  · intro hEq
    rw [hJ₀sf] at hEq
    exact hne_tr hEq.symm
  · intro hEq
    rw [hJ₀w] at hEq
    exact hne_w hEq

#print axioms Gabbro.Grammatik.kette_zwei_start
#print axioms Gabbro.Grammatik.zwei_lauf_mitgliedschaft
#print axioms Gabbro.Grammatik.kette_zwei_schritt
#print axioms Gabbro.Grammatik.kette_zwei_aus_lauf
#print axioms Gabbro.Grammatik.kette_aus_deckung
#print axioms Gabbro.Grammatik.deckung_strikt_schwaecher

/-! ## CUTS

- `kette_zwei_schritt` covers LOCK steps only (`LockSchrittGedecktBei`:
  `nimmt` / `gibt`). `blatt` steps for either thread are NOT covered: the
  `execStmt` frame (`blatt_rahmen_schritt`, `Maschine.lean`, read-only) plus
  per-step contract-to-code wiring (`hRahmen` shape of
  `kette_aus_lauf_bezeugt`) must be threaded through the two-member
  construction. Consequently `kette_zwei_aus_lauf` requires `hlock_prog`
  (every pointed-to atom is `take` / `rel`).
- No `SerialLink` witnesses: the conclusion carries worlds, run, members,
  and trace -- but no per-step witness events at accessed carriers. The
  `hwit_leaf` / `hwit_lock` duties of `kette_aus_lauf_bezeugt` have no
  two-thread counterpart yet.
- `KettenSpurDeckung` is discharged for two lock-only threads (by
  `kette_zwei_aus_lauf` at each prefix); the N-thread induction that
  discharges it in general -- per-level frame + witness + routing for
  arbitrary members -- is future work. `kette_aus_deckung` shows the
  premise is the ONLY missing piece (the conclusion follows by direct
  application), and `deckung_strikt_schwaecher` shows it is strictly weaker
  than the `hJw` / `hJsf` equations (a vacuous witness breaks both).
- `deckung_strikt_schwaecher` as stated shows the SEED breaks both equations
  while A (different) chain discharges the deckung; it does not exhibit one
  chain satisfying the deckung AND breaking the equations at the same
  machine -- the strictness direction that matters is existential-quantifier
  weakness (per-prefix ∃ vs pinned J), which the theorem text states and the
  proof witnesses in the degenerate (empty-trace) reading.
- Contracts (`requires` / `ensures`) hold at their place: this file builds
  only the joint RUN (worlds + trace from `execStmt`/`exec` via `PCReach`,
  memory-changing through lock worlds that keep `M.speicher`). No contract
  parameters or results are quantified away; no bare `Prop` premises.
-/

end Gabbro.Grammatik
