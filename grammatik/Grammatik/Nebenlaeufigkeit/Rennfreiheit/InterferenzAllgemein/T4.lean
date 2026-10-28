/- Part 4 of 5 of `InterferenzAllgemein` (split by instrumente/teile/lean-teilen.py; the umbrella `InterferenzAllgemein.lean` imports all parts). -/
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein.T3

namespace Gabbro.Grammatik

variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}

/-- **Invariant-form assertions are interference-free WHERE THE LOCK IS FREE.**
    The literal CSL interface over one shared table carrier (the standard CSL case):
    `Q` coincides with the carrier invariant per thread, and each foreign step goes
    from one lock-free world to another -- so `Q` follows from `hinv_aus_disziplin`
    at both ends. No per-run preservation proof is owed for the covered class. -/
theorem interferenceFree_wo_frei (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Q : Faden → World D → Prop)
    (t₀ : D.Tab) (L : D.Lock)
    (Wc : D.Tab → Bool) (Gc : D.Glob → Bool)
    (hAb : HaengtAb Wc Gc (I.inv (.inl t₀)))
    (hFrameT : ∀ t : D.Tab, Wc t = true → (.inl t₀ : D.Tab ⊕ D.Glob) = .inl t)
    (hFrameG : ∀ x : D.Glob, Gc x = true → (.inl t₀ : D.Tab ⊕ D.Glob) = .inr x)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (hEntry : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → I.inv (.inl t₀) σ₀)
    (hReturn : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → J.schrittFaden[k]? = some g → J.welten[k]? = some vor →
        J.welten[k + 1]? = some nach → TraegerSchreibt (J.code g) (.inl t₀) = true →
          L ∈ D.haelt (J.code g) → I.inv (.inl t₀) nach)
    (hCov : ∀ (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i)
    (hFormU : ∀ (f : Faden), f ∈ J.faeden → ∀ (σ : World D),
      Q f σ ↔ I.inv (.inl t₀) σ) :
    ∀ (f : Faden), f ∈ J.faeden → ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → g ≠ f →
        J.schrittFaden[k]? = some g → J.welten[k]? = some vor →
          J.welten[k + 1]? = some nach →
            LockFrei (D := D) L vor → LockFrei (D := D) L nach → (Q f vor ↔ Q f nach) := by
  intro f hf k g vor nach _ _ _ hkv hkn hFreiVor hFreiNach
  have hInv := hinv_aus_disziplin Nb J I t₀ L Wc Gc hAb hFrameT hFrameG hGuardT
    hEntry hReturn hCov
  rw [hFormU f hf vor, hFormU f hf nach]
  exact ⟨fun _ => hInv _ nach hkn hFreiNach, fun _ => hInv _ vor hkv hFreiVor⟩

#print axioms Gabbro.Grammatik.Bewacht
#print axioms Gabbro.Grammatik.LockFrei
#print axioms Gabbro.Grammatik.schritt_rahmen_aus_korn
#print axioms Gabbro.Grammatik.nichtschreiber_erhaelt
#print axioms Gabbro.Grammatik.hinv_kette_aus_disziplin
#print axioms Gabbro.Grammatik.kette_belegt_of_mem
#print axioms Gabbro.Grammatik.any_of_mem_true
#print axioms Gabbro.Grammatik.wache_aus_schuld
#print axioms Gabbro.Grammatik.hinv_aus_disziplin
#print axioms Gabbro.Grammatik.invariantenKontext_aus_disziplin
#print axioms Gabbro.Grammatik.interferenceFree_of_invariantForm_aus_disziplin
#print axioms Gabbro.Grammatik.interferenceFree_wo_frei

end Gabbro.Grammatik

/-! ## 22. Lipton-style reduction: event-grain runs serialize to whole-section chains (Posten 1)

    MISSION (auditor-named): the reduction theorem -- an event-interleaved run with
    whole-section chains is equivalent to a serial chain run for all chain-world
    observations.

    GRAIN (taken, not rebuilt): one `GemeinsamerLauf` step is one whole critical
    section (`schritt_rahmen_aus_korn`, §21, resting on the `Koernung.lean` negative
    cases: an n-byte `schreibBytes` is n events, not one, `schreibBytes_not_single`;
    a `leseBytes` records one event over n cells, `leseBytes_not_atomic`; the
    interrupted middle IS the witnessed tear, `two_byte_tear`,
    `mid_interruption_tears`). At event grain the invariant breaks mid-step; at
    section grain each step re-establishes what it owes at return (`hReturn`, the
    `rufAt` return-check shape). The serial unit is therefore the section, and
    commuting happens at section boundaries.

    WHAT IS PROVED (no `sorry`, no `admit`, no `axiom`):

    - `SerialLink`: the run-to-chain link that replaces the bare `hLink : J.l = run`
      equality (`Ziel.lean`): every WRITING chain step has a witness access event in
      the run, by the same thread on the same carrier. The link is order-faithful
      (witness indices carry the run order) instead of asserting list equality; the
      chain worlds themselves still come from the bodies (`exec`) -- the exact
      remainder below. `Ziel.lean` is not touched.
    - `SectionConflict`: two whole sections of different threads writing the same
      table carrier.
    - `reduktion_seriell`: the core -- two conflicting sections are happens-before
      ordered in the run, in one direction or the other (`kein_wettlauf` both ways,
      `Wettlauf.lean`, read-only). The conflict admits a serial order: that IS the
      reduction at order level.
    - `reduktion_seriell_under_lock`: the same-lock refinement -- both writers hold
      the guard, derived from the lock discipline (`wache_aus_schuld`, §21, from
      `J.hSchuld` plus coverage; read-only), alongside the HB order. Sections of
      the same lock serialize through the lock edge.
    - `mover_nonwriter_past`: the mover argument -- a non-writing section commutes
      past a preserving writer observationally: the end observation follows from the
      pre-observation via frame preservation (`nichtschreiber_erhaelt`, §21, whose
      engine is `stabil` over the whole-frame step), independently of position. No
      swapped middle world is constructed; commutation is preservation that does
      not depend on position.
    - `serial_chain_from_run`: the corollary -- under the §21 discipline package
      (entry, preserving return, coverage, frame-locality, guard) plus
      `SerialLink`, invariant-form observations (uniform shared carrier, the
      standard CSL case) hold at the last chain world AND the conflicting sections
      are HB-ordered in the run. The chain worlds are reached from run-derived
      order: the run fixes the serial schedule, the §21 chain lemma
      (`hinv_kette_aus_disziplin`, read-only) fixes the observations.

    COVERAGE (exactly): single shared TABLE carrier under one guard, whole-section
    grain, race-free runs (`Gesittet`), two-section conflicts, preserving writers,
    uniform invariant-form observations.

    REMAINDER (booked, not hidden):

    - Globals: U003 is table-only, so `wache_aus_schuld` and the lock refinement
      stay table-scoped; shared globals remain on the §13-§15 exception track.
    - Multi-carrier conflicts and more than two conflicting sections: the order
      theorem is pairwise; folding pairwise HB orders into one global serial
      schedule is not built.
    - Chain order versus HB order may disagree: the serial schedule is the HB
      order, not the chain order; monotonicity of witnesses along the chain is
      assumed nowhere and proved nowhere.
    - Restoring writers (re-establish the invariant without assuming it at the
      middle world) take a different return shape than the preserving writer in
      `mover_nonwriter_past`.
    - Non-uniform invariant form (per-thread carriers, §20 `InvariantForm`) is
      narrowed here to the uniform shared carrier.
    - No event-to-world step semantics is built (the `Wettlauf.lean` §5 cut carries
      over): the run contributes schedule and order, the bodies contribute worlds,
      and `SerialLink` links the two at witness accesses.
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The run-to-chain link that replaces the bare `hLink : J.l = run` equality:
    every WRITING chain step has a witness access event in the run, by the same
    thread on the same table carrier. Order-faithful (witness indices carry the
    run order) instead of a list equality. -/
def SerialLink (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (run : Lauf D) (t₀ : D.Tab) : Prop :=
  ∀ (k : Nat) (g : Faden), J.schrittFaden[k]? = some g →
    TraegerSchreibt (J.code g) (.inl t₀) = true →
    ∃ (j : Nat) (w : Bool) (Λ : List (Res D)) (h : List D.Lock),
      run[j]? = some (Schritt.mk g (.zugriff t₀ w Λ h))

/-- Two conflicting whole sections: different threads, both in the chain, both
    writing the same table carrier, in chain order. -/
def SectionConflict (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (t₀ : D.Tab) (k₁ k₂ : Nat) (g₁ g₂ : Faden) : Prop :=
  k₁ < k₂ ∧ g₁ ∈ J.faeden ∧ g₂ ∈ J.faeden ∧ g₁ ≠ g₂ ∧
    J.schrittFaden[k₁]? = some g₁ ∧ J.schrittFaden[k₂]? = some g₂ ∧
    TraegerSchreibt (J.code g₁) (.inl t₀) = true ∧
    TraegerSchreibt (J.code g₂) (.inl t₀) = true

/-- **Reduction, serial order (two-section single-carrier fragment).** Two
    conflicting sections are happens-before ordered in the race-free run, in one
    direction or the other: the conflict admits a serial order. Both directions
    close via `kein_wettlauf` (`Wettlauf.lean`, read-only); the equal-index case
    contradicts the distinct threads. -/
theorem reduktion_seriell (run : Lauf D) (hG : Gesittet run)
    (t₀ : D.Tab) (g₁ g₂ : Faden) (hne : g₁ ≠ g₂)
    (j₁ j₂ : Nat) (w₁ w₂ : Bool) (Λ₁ Λ₂ : List (Res D)) (h₁ h₂ : List D.Lock)
    (hw₁ : run[j₁]? = some (Schritt.mk g₁ (.zugriff t₀ w₁ Λ₁ h₁)))
    (hw₂ : run[j₂]? = some (Schritt.mk g₂ (.zugriff t₀ w₂ Λ₂ h₂))) :
    HB run j₁ j₂ ∨ HB run j₂ j₁ := by
  by_cases h12 : j₁ < j₂
  · exact Or.inl (kein_wettlauf run hG j₁ j₂ h12 g₁ g₂ hne t₀ w₁ w₂ Λ₁ Λ₂ h₁ h₂ hw₁ hw₂)
  · by_cases h21 : j₂ < j₁
    · exact Or.inr (kein_wettlauf run hG j₂ j₁ h21 g₂ g₁ (Ne.symm hne) t₀ w₂ w₁ Λ₂ Λ₁ h₂ h₁ hw₂ hw₁)
    · have heq : j₁ = j₂ := by omega
      subst heq
      have hsame := hw₁.symm.trans hw₂
      have hg : g₁ = g₂ := congrArg Schritt.faden (Option.some_inj.mp hsame)
      exact absurd hg hne

/-- **Reduction under the guard (same-lock refinement).** Both writers hold the
    guard -- derived from the lock discipline (`wache_aus_schuld`, §21, from
    `J.hSchuld` plus coverage; read-only) -- alongside the HB order from
    `reduktion_seriell`. Sections of the same lock serialize through the lock. -/
theorem reduktion_seriell_under_lock (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (t₀ : D.Tab) (L : D.Lock)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (k₁ k₂ : Nat) (g₁ g₂ : Faden)
    (hK : SectionConflict Nb J t₀ k₁ k₂ g₁ g₂)
    (hCov : ∀ (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i)
    (run : Lauf D) (hG : Gesittet run)
    (j₁ j₂ : Nat) (w₁ w₂ : Bool) (Λ₁ Λ₂ : List (Res D)) (h₁ h₂ : List D.Lock)
    (hw₁ : run[j₁]? = some (Schritt.mk g₁ (.zugriff t₀ w₁ Λ₁ h₁)))
    (hw₂ : run[j₂]? = some (Schritt.mk g₂ (.zugriff t₀ w₂ Λ₂ h₂))) :
    (L ∈ D.haelt (J.code g₁) ∧ L ∈ D.haelt (J.code g₂)) ∧
      (HB run j₁ j₂ ∨ HB run j₂ j₁) := by
  obtain ⟨_, hg₁, hg₂, hne, _, _, hW₁, hW₂⟩ := hK
  refine ⟨⟨?_, ?_⟩,
    reduktion_seriell run hG t₀ g₁ g₂ hne j₁ j₂ w₁ w₂ Λ₁ Λ₂ h₁ h₂ hw₁ hw₂⟩
  · exact wache_aus_schuld Nb J t₀ L hGuardT g₁ hg₁ hW₁ (hCov g₁ hg₁ hW₁)
  · exact wache_aus_schuld Nb J t₀ L hGuardT g₂ hg₂ hW₂ (hCov g₂ hg₂ hW₂)

/-- **The mover: a non-writing section commutes past a preserving writer.** The
    end observation follows from the pre-observation: the non-writer preserves
    the invariant by frame (`nichtschreiber_erhaelt`, §21, whose engine is
    `stabil` over the whole-frame step), and the preserving writer carries it to
    the end world. Membership of the writer comes from its own step
    (`hSchritt`); no swapped middle world is constructed. -/
theorem mover_nonwriter_past (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (c : D.Tab ⊕ D.Glob)
    (Wc : D.Tab → Bool) (Gc : D.Glob → Bool)
    (hAb : HaengtAb Wc Gc (I.inv c))
    (hFrameT : ∀ t : D.Tab, Wc t = true → c = .inl t)
    (hFrameG : ∀ x : D.Glob, Gc x = true → c = .inr x)
    (k : Nat) (g g' : Faden) (vor mid nach : World D)
    (hkg : J.schrittFaden[k]? = some g) (hkv : J.welten[k]? = some vor)
    (hkm : J.welten[k + 1]? = some mid)
    (hkg' : J.schrittFaden[k + 1]? = some g') (hkn : J.welten[k + 1 + 1]? = some nach)
    (hN : TraegerSchreibt (J.code g) c = false)
    (hW' : TraegerSchreibt (J.code g') c = true)
    (hRet : TraegerSchreibt (J.code g') c = true → g' ∈ J.faeden →
      I.inv c mid → I.inv c nach)
    (hVor : I.inv c vor) : I.inv c nach := by
  have hgm' : g' ∈ J.faeden := (J.hSchritt (k + 1) g' mid nach hkg' hkm hkn).1
  exact hRet hW' hgm'
    ((nichtschreiber_erhaelt Nb J I c Wc Gc hAb hFrameT hFrameG
      k g vor mid hkg hkv hkm hN).mp hVor)

/-- **The corollary: chain worlds from run-derived order (replaces `hLink`).**
    Under the §21 discipline package (entry, preserving return, coverage,
    frame-locality, guard) plus `SerialLink`, invariant-form observations over
    the uniform shared carrier hold at the last chain world -- via the §21 chain
    lemma (`hinv_kette_aus_disziplin`, read-only) -- AND the conflicting sections
    are HB-ordered in the run, via `reduktion_seriell`. The run fixes the serial
    schedule (witness indices), the chain lemma fixes the observations. -/
theorem serial_chain_from_run (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Q : Faden → World D → Prop)
    (t₀ : D.Tab) (L : D.Lock)
    (Wc : D.Tab → Bool) (Gc : D.Glob → Bool)
    (hAb : HaengtAb Wc Gc (I.inv (.inl t₀)))
    (hFrameT : ∀ t : D.Tab, Wc t = true → (.inl t₀ : D.Tab ⊕ D.Glob) = .inl t)
    (hFrameG : ∀ x : D.Glob, Gc x = true → (.inl t₀ : D.Tab ⊕ D.Glob) = .inr x)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (hEntry : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → I.inv (.inl t₀) σ₀)
    (hReturn : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → J.schrittFaden[k]? = some g → J.welten[k]? = some vor →
        J.welten[k + 1]? = some nach → TraegerSchreibt (J.code g) (.inl t₀) = true →
          L ∈ D.haelt (J.code g) → I.inv (.inl t₀) nach)
    (hCov : ∀ (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i)
    (hForm : ∀ (f : Faden), f ∈ J.faeden → ∀ (σ : World D),
      Q f σ ↔ I.inv (.inl t₀) σ)
    (run : Lauf D) (hG : Gesittet run)
    (hLink : SerialLink Nb J run t₀)
    (k₁ k₂ : Nat) (g₁ g₂ : Faden)
    (hK : SectionConflict Nb J t₀ k₁ k₂ g₁ g₂) :
    (∀ (σ : World D), J.welten.getLast? = some σ →
      ∀ (f : Faden), f ∈ J.faeden → Q f σ)
    ∧ (∃ (j₁ j₂ : Nat), HB run j₁ j₂ ∨ HB run j₂ j₁) := by
  obtain ⟨_, _, _, hne, hkg₁, hkg₂, hW₁, hW₂⟩ := hK
  obtain ⟨j₁, w₁, Λ₁, hh₁, hw₁⟩ := hLink k₁ g₁ hkg₁ hW₁
  obtain ⟨j₂, w₂, Λ₂, hh₂, hw₂⟩ := hLink k₂ g₂ hkg₂ hW₂
  refine ⟨?_, ⟨j₁, j₂,
    reduktion_seriell run hG t₀ g₁ g₂ hne j₁ j₂ w₁ w₂ Λ₁ Λ₂ hh₁ hh₂ hw₁ hw₂⟩⟩
  · intro σ hletzte f hf
    rw [hForm f hf σ]
    have hChain := hinv_kette_aus_disziplin Nb J I (.inl t₀) L Wc Gc hAb hFrameT hFrameG
      hGuardT hEntry hReturn
      (fun k g vor nach hgm hkg hkv hkn hW =>
        wache_aus_schuld Nb J t₀ L hGuardT g hgm hW (hCov g hgm hW))
    have hlast : J.welten[J.welten.length - 1]? = some σ := by
      rw [← List.getLast?_eq_getElem?]
      exact hletzte
    exact hChain _ σ hlast

#print axioms Gabbro.Grammatik.SerialLink
#print axioms Gabbro.Grammatik.SectionConflict
#print axioms Gabbro.Grammatik.reduktion_seriell
#print axioms Gabbro.Grammatik.reduktion_seriell_under_lock
#print axioms Gabbro.Grammatik.mover_nonwriter_past
#print axioms Gabbro.Grammatik.serial_chain_from_run

end Gabbro.Grammatik

/-! ## 23. Eval reads only memory: the hMem engine (o02-hmem)

    The finding (SEV1, two checkers): `spec_aus_fuehrung_schritt` (`Maschine.lean`)
    carries `hMem : SpeicherVertrag Pre Post` on both legs of the spec step --
    lock steps go through memory constancy plus memory-only contracts -- but the
    discharge for `QRequires` / `QEnsures` was open: the per-expression induction
    showing `eval` reads only slots and globals lives downstream where the
    contract instantiation lives (§19 R1 books exactly this cut), while
    `LesenStabil.lean` holds only the `HaengtAb` frame side
    (`haengtAb_requires_bei_Lesen`, `haengtAb_ensures_bei_Lesen`,
    `requiresStabil_schritt`, `ensuresStabil_schritt`).

    What this section proves (no `sorry`, no `admit`, no `axiom`):

    * `eval_liest_nur_speicher` (plus `evalNutz_liest_nur_speicher`, mutual):
      `eval` agrees on worlds that agree on all slots and all globals -- the
      entry pair and the present pair separately, so `old(...)` (which reads
      the entry world) is covered. The induction is over `eval` itself, case
      for case; the three non-trivial leaves carry local helpers
      (`speicher_bytesAb_gleich`, `speicher_kette_gleich`,
      `speicher_list_all_congr` / `speicher_list_any_congr`), proved here
      because their downstream twins (`bytesAb_gleich`, `kette_gleich`,
      `list_all_congr`, `list_any_congr` in `Extraktion.lean`) are not
      importable upstream.
    * `eval_liest_nur_speicher_diag`: the diagonal both worlds read at once --
      the exact shape a `SpeicherVertrag` instance consumes.

    Import honesty (read, not worked around): this file is imported BY
    `Maschine.lean` (home of `SpeicherVertrag` / `World.speicher`) and BY
    `Extraktion.lean` (home of `QRequires` / `QEnsures` / `eval_liest_nur_orte`),
    and `LesenStabil.lean` imports `Extraktion.lean` -- so none of those names
    is citable here without a cycle. Reuse of the `LesenStabil` `HaengtAb`
    lemmas is therefore shape-level: those lemmas say contracts hang on their
    read frame; this section says `eval` hangs on memory; the conjunction --
    `SpeicherVertrag` over `QRequires` / `QEnsures` -- folds the two
    downstream, where all three names are visible.

    Coverage (exactly): every `Expr` constructor (including `durch`, which never
    evaluates its pointer, and `reaches` / `forallSlots` / `existsSlots` /
    `leseBytes`, which read whole columns), plus both `NutzlastExpr` shapes.
    Every premise is load-bearing: `hS` fires on `slot`, `durch`, `leseBytes`
    and `reaches`; `hG` on `glob`; `h0S` on `altSlot`; `h0G` on `altGlob`.

    Remainder (named, not hidden):

    * The `SpeicherVertrag` instance over `QRequires` / `QEnsures` itself --
      unfolding a `World.speicher` equality into the four slot/glob agreements
      above and folding the contract predicates over the diagonal -- belongs
      downstream (the `Maschine.lean` / `Extraktion.lean` direction), owned by
      whoever touches those files. This section is the engine; the binder is
      not here.
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- `bytesAb` reads only its column: equal columns give equal bytes. -/
theorem speicher_bytesAb_gleich {t : D.Tab} {f : D.Feld t} {hf : D.typ t f = .int 0 255}
    {σ σ' : World D}
    (h : ∀ k f', σ.slots t k f' = σ'.slots t k f')
    (n : Nat) (k : Int) :
    σ.bytesAb t f hf n k = σ'.bytesAb t f hf n k := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
      simp only [World.bytesAb]
      rw [h k f, ih]

/-- `kette` reads only its `weiter` column: equal columns, equal reachability. -/
theorem speicher_kette_gleich {n : Int} {weiter weiter' : Int → Option (Zahl 0 (n - 1))}
    (fuel : Nat) (k ziel : Int)
    (h : ∀ k, weiter k = weiter' k) :
    kette weiter fuel k ziel = kette weiter' fuel k ziel := by
  induction fuel generalizing k with
  | zero => rfl
  | succ fuel ih =>
      show (if k = ziel then true
          else match weiter k with
          | none => false
          | some m => kette weiter fuel m.n ziel) =
        (if k = ziel then true
          else match weiter' k with
          | none => false
          | some m => kette weiter' fuel m.n ziel)
      by_cases hk : k = ziel
      · simp only [hk, ↓reduceIte]
      · simp only [if_neg hk]
        rw [h k]
        cases hm : weiter' k with
        | none => rfl
        | some m => exact ih _

/-- Pointwise equal predicates count equal (`all`). -/
theorem speicher_list_all_congr {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      have hx : p x = q x := h x List.mem_cons_self
      have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
      simp only [List.all_cons, hx, ih']

/-- Pointwise equal predicates count equal (`any`). -/
theorem speicher_list_any_congr {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      have hx : p x = q x := h x List.mem_cons_self
      have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
      simp only [List.any_cons, hx, ih']


end Gabbro.Grammatik
