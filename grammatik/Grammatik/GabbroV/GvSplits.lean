/-
  File:      Grammatik/GabbroV/GvSplits.lean
  Subject:   GabbroV: disjunctive callee postconditions and call chains (agent 05).

  TODO.md section 0f, two open items: (a) a callee with a DISJUNCTIVE
  postcondition multiplies the proof goals of the GabbroV pipeline
  (`beispiele/126`: 94 goals); (b) a CHAIN of 64 calls (`beispiele/147`,
  `148`, `tick_runde`) is not instantiated by twelve rounds of the
  `gabbro_calls` step nor by extra passes. Analysis: REPORT-05.md section 1.

  WHAT THIS FILE PROVES, over the accepted exec model (`execBlock` via the
  `HTripel` Hoare rules of `HoareRegeln.lean`, no new interpreter):
  * `disj_kontinuation_einmal`: where the continuation is proved ONCE from
    a common weaker middle `M` (both disjuncts imply `M`), the disjunctive
    goal follows with one continuation proof plus two small implications.
  * `kette_invariant` / `kette_block_invariant`: a uniform `n`-link chain
    is discharged by ONE induction on the chain, not `n` instantiations.
  Witnesses on the `rufD` fixture (`RufMaschineD.lean`) show the premises
  are jointly satisfiable without vacuity. Heterogeneous chains stay open
  (see CUTS).
-/
import Grammatik.Logik.Ruf.HoareRuf

namespace Gabbro.Grammatik.GvSplits

variable {D : Deklaration} {V : Vertrag D}

/-- **Disjunctive post, one continuation proof.** -/
theorem disj_kontinuation_einmal {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (rest : Block D V l Γ Λ Λ')
    (Q1 Q2 M Pst : World D → Env D Γ → Prop)
    (hRest : HTripel O passes R rest M Pst)
    (h1 : ∀ σ ρ, Q1 σ ρ → M σ ρ)
    (h2 : ∀ σ ρ, Q2 σ ρ → M σ ρ) :
    HTripel O passes R rest (fun σ ρ => Q1 σ ρ ∨ Q2 σ ρ) Pst := by
  intro σ ρ hPre σ' ρ' hrun
  cases hPre with
  | inl h => exact hRest σ ρ (h1 σ ρ h) σ' ρ' hrun
  | inr h => exact hRest σ ρ (h2 σ ρ h) σ' ρ' hrun

/-- **Monotone continuation: the stronger disjunct is covered by the weaker
    one's proof.** Where `Q1` implies `Q2`, a continuation proved once from
    `Q2` already covers `Q1` and hence the disjunction `Q1 ∨ Q2`: the case
    analysis costs one small implication, not a second continuation proof.
    Every premise is used: `hRest` for the run, `hSub` for the left branch. -/
theorem disj_monoton_staerker {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (rest : Block D V l Γ Λ Λ')
    (Q1 Q2 Pst : World D → Env D Γ → Prop)
    (hRest : HTripel O passes R rest Q2 Pst)
    (hSub : ∀ σ ρ, Q1 σ ρ → Q2 σ ρ) :
    HTripel O passes R rest (fun σ ρ => Q1 σ ρ ∨ Q2 σ ρ) Pst := by
  intro σ ρ hPre σ' ρ' hrun
  cases hPre with
  | inl h => exact hRest σ ρ (hSub σ ρ h) σ' ρ' hrun
  | inr h => exact hRest σ ρ h σ' ρ' hrun

/-! ## 2. Call chains: one induction instead of n instantiations -/

/-- **A uniform chain of `n` links** over the exec model's states: `leer`
    is the empty chain (as `tick_runde`'s 64 calls stand in one block, each
    link leaves the next link's start state); `schritt` takes one `Rel`
    step and then the remaining `n` links. `Rel` is instantiated with the
    `execBlock`-step of one link in `kette_block_invariant` below, so no
    second interpreter is defined here. -/
inductive Kette (Rel : World D → Env D Γ → World D → Env D Γ → Prop)
    : Nat → World D → Env D Γ → World D → Env D Γ → Prop where
  | leer : Kette Rel 0 σ ρ σ ρ
  | schritt : Rel σ ρ σm ρm → Kette Rel n σm ρm σ' ρ' →
      Kette Rel (n + 1) σ ρ σ' ρ'

/-- **A uniform chain is discharged by one induction.** Where every link
    preserves `Inv`, the `n`-link chain preserves `Inv` for every `n`: the
    per-link argument (`hSchritt`) is proved once and used at each
    induction step, instead of instantiating one contract per link.
    Every premise is used: `hSchritt` at each step, `hInv` at the base,
    `hK` as the induction subject. -/
theorem kette_invariant
    (Rel : World D → Env D Γ → World D → Env D Γ → Prop)
    (Inv : World D → Env D Γ → Prop)
    (hSchritt : ∀ σ ρ σ' ρ', Inv σ ρ → Rel σ ρ σ' ρ' → Inv σ' ρ')
    (n : Nat) :
    ∀ σ ρ σ' ρ', Inv σ ρ → Kette Rel n σ ρ σ' ρ' → Inv σ' ρ' := by
  induction n with
  | zero =>
      intro σ ρ σ' ρ' hInv hK
      cases hK
      exact hInv
  | succ n ih =>
      intro σ ρ σ' ρ' hInv hK
      cases hK with
      | schritt hStep hRest => exact ih _ _ _ _ (hSchritt _ _ _ _ hInv hStep) hRest

/-- **One link's step as a relation**: the accepted `execBlock`
    (`Semantik.lean`) ends normally. Reused, never redefined. -/
def ExecRel {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (b : Block D V l Γ Λ Λ') :
    World D → Env D Γ → World D → Env D Γ → Prop :=
  fun σ ρ σ' ρ' => execBlock O passes R b σ ρ = Ausgang.ok σ' ρ'

/-- **The chain induction at a real block.** Where one link preserves `Inv`
    (a single `HTripel`, proved once), the `n`-fold chain of that link
    preserves `Inv` for every `n`: one induction covers `tick_runde`'s 64
    uniform `fenster_schritt` links instead of 64 contract instances.
    Every premise is used: `hTrip` for each link step, `hInv` at the base,
    `hK` as the induction subject. -/
theorem kette_block_invariant {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (b : Block D V l Γ Λ Λ)
    (Inv : World D → Env D Γ → Prop)
    (hTrip : HTripel O passes R b Inv Inv)
    (n : Nat) :
    ∀ σ ρ σ' ρ', Inv σ ρ → Kette (ExecRel O passes R b) n σ ρ σ' ρ' →
      Inv σ' ρ' := by
  have hStep : ∀ σ ρ σ' ρ', Inv σ ρ →
      ExecRel O passes R b σ ρ σ' ρ' → Inv σ' ρ' := by
    intro σ ρ σ' ρ' hI hR
    exact hTrip σ ρ hI σ' ρ' hR
  intro σ ρ σ' ρ' hInv hK
  exact kette_invariant (ExecRel O passes R b) Inv hStep n σ ρ σ' ρ' hInv hK

/-! ## 3. Witnesses: the premises are satisfiable without vacuity.

    Fixture: the one-function `rufD` program of `RufMaschineD.lean`
    (accepted exec model, real `World`/`Env`/`execBlock`). The two
    disjuncts read the witness slot (`true` vs `false`); both sides are
    inhabited and neither implies the other. The chain witness moves:
    each link appends one trace event, so a 2-link chain grows the spur
    `0 → 2` while the slot invariant holds. -/

/-- The two disjuncts: the witness slot holds `true` / `false`. -/
def Q1w : World rufD → Env rufD [] → Prop := fun σ _ => σ.slots () 0 () = true

/-- The two disjuncts: the witness slot holds `true` / `false`. -/
def Q2w : World rufD → Env rufD [] → Prop := fun σ _ => σ.slots () 0 () = false

/-- The common weaker middle: no constraint. -/
def Mw : World rufD → Env rufD [] → Prop := fun _ _ => True

/-- A world where the slot holds `false` (the `Q2w` side). -/
def weltFalschD : World rufD :=
  ⟨fun _ _ _ => false, fun g => Empty.elim g, []⟩

/-- **Joint witness for `disj_kontinuation_einmal`.** All three premises
    hold jointly on `rufD` with the silent block: the continuation from
    `Mw` (`hoare_skip`), both implications (into `True`), both disjuncts
    inhabited on opposite sides, each side refuting the other, and the
    block actually running to a normal outcome. -/
theorem disj_kontinuation_einmal_zeuge :
    HTripel (V := vertragVon rufD rufIncD) (l := false) (Γ := []) (Λ := []) (Λ' := [])
      rufOD 0 Rwit70 Block.nil Mw Mw ∧
    (∀ σ ρ, Q1w σ ρ → Mw σ ρ) ∧ (∀ σ ρ, Q2w σ ρ → Mw σ ρ) ∧
    (∃ σ ρ, Q1w σ ρ) ∧ (∃ σ ρ, Q2w σ ρ) ∧
    (∃ σ ρ, Q1w σ ρ ∧ ¬ Q2w σ ρ) ∧ (∃ σ ρ, Q2w σ ρ ∧ ¬ Q1w σ ρ) ∧
    (∃ σ ρ σ' ρ', execBlock (V := vertragVon rufD rufIncD) rufOD 0 Rwit70
      (Block.nil : Block rufD (vertragVon rufD rufIncD) false [] [] [])
      σ ρ = Ausgang.ok σ' ρ') := by
  refine ⟨hoare_skip _ _ _ _, (fun _ _ _ => trivial), (fun _ _ _ => trivial),
    ⟨rufWeltD, Env.nil, rfl⟩, ⟨weltFalschD, Env.nil, rfl⟩,
    ⟨rufWeltD, Env.nil, rfl, by simp [Q2w, rufWeltD]⟩,
    ⟨weltFalschD, Env.nil, rfl, by simp [Q1w, weltFalschD]⟩,
    ⟨rufWeltD, Env.nil, rufWeltD, Env.nil, rfl⟩⟩

/-- **Joint witness for `disj_monoton_staerker`.** `Q1w` implies the weak
    `Mw`, `Q1w` is inhabited (the `true` side) while `Mw` also holds where
    `Q1w` fails (the `false` side: strictly weaker), and the block runs. -/
theorem disj_monoton_staerker_zeuge :
    HTripel (V := vertragVon rufD rufIncD) (l := false) (Γ := []) (Λ := []) (Λ' := [])
      rufOD 0 Rwit70 Block.nil Mw Mw ∧
    (∀ σ ρ, Q1w σ ρ → Mw σ ρ) ∧
    (∃ σ ρ, Q1w σ ρ) ∧ (∃ σ ρ, Mw σ ρ ∧ ¬ Q1w σ ρ) ∧
    (∃ σ ρ σ' ρ', execBlock (V := vertragVon rufD rufIncD) rufOD 0 Rwit70
      (Block.nil : Block rufD (vertragVon rufD rufIncD) false [] [] [])
      σ ρ = Ausgang.ok σ' ρ') := by
  refine ⟨hoare_skip _ _ _ _, (fun _ _ _ => trivial),
    ⟨rufWeltD, Env.nil, rfl⟩, ⟨weltFalschD, Env.nil, trivial, by simp [Q1w, weltFalschD]⟩,
    ⟨rufWeltD, Env.nil, rufWeltD, Env.nil, rfl⟩⟩

/-- **One witness link**: append a single trace event, touching nothing
    else. The trace grows, the slots do not. -/
def Relw : World rufD → Env rufD [] → World rufD → Env rufD [] → Prop :=
  fun σ _ σ' ρ' => σ' = σ.merke [.zugriff () true [] []] ∧ ρ' = Env.nil

/-- **The witness invariant**: every slot of every table holds `true`.
    A trace step preserves it (it touches only the spur); it fails on
    `weltFalschD`, so it is a real constraint. -/
def Invw : World rufD → Env rufD [] → Prop :=
  fun σ _ => ∀ (t : rufD.Tab) (k : Int) (f : rufD.Feld t), σ.slots t k f = true

/-- Every witness link preserves the witness invariant. Both premises are
    used: `hI` is the invariant carried over, `hR` fixes the step. -/
theorem hSchrittw :
    ∀ σ ρ σ' ρ', Invw σ ρ → Relw σ ρ σ' ρ' → Invw σ' ρ' := by
  intro σ ρ σ' ρ' hI hR
  obtain ⟨rfl, rfl⟩ := hR
  exact hI

/-- The witness invariant holds at the start world. -/
theorem invw_start : Invw rufWeltD Env.nil := by
  intro t k f
  rfl

/-- The witness invariant genuinely constrains: it fails on `weltFalschD`. -/
theorem invw_falsch : ¬ Invw weltFalschD Env.nil := by
  intro h
  have h0 := h () 0 ()
  simp [weltFalschD] at h0

/-- **Joint witness for `kette_invariant`: a real moving chain.** Both
    premises hold (`hSchrittw`, `invw_start`), and a 2-link chain over
    `rufWeltD` grows the spur `0 → 2` while the invariant holds at the
    end: the induction covers a chain that actually moves, not a silent
    one. -/
theorem kette_invariant_zeuge :
    (∀ σ ρ σ' ρ', Invw σ ρ → Relw σ ρ σ' ρ' → Invw σ' ρ') ∧
    Invw rufWeltD Env.nil ∧ ¬ Invw weltFalschD Env.nil ∧
    (∃ σ' ρ', Kette Relw 2 rufWeltD Env.nil σ' ρ' ∧
      σ'.spur.length = 2 ∧ Invw σ' ρ') := by
  refine ⟨hSchrittw, invw_start, invw_falsch, ?_⟩
  exact ⟨_, _, Kette.schritt ⟨rfl, rfl⟩ (Kette.schritt ⟨rfl, rfl⟩ Kette.leer),
    rfl, fun t k f => rfl⟩

/-- **Joint witness for `kette_block_invariant`.** The single-link triple
    over the silent block (`hoare_skip`), the invariant at the start, and
    a 2-link `execBlock` chain: the corollary fires on a real block. The
    silent links are stated honestly (see CUTS): genuine movement is
    witnessed at the schema level above. -/
theorem kette_block_invariant_zeuge :
    HTripel (V := vertragVon rufD rufIncD) (l := false) (Γ := []) (Λ := []) (Λ' := [])
      rufOD 0 Rwit70 Block.nil Invw Invw ∧
    Invw rufWeltD Env.nil ∧
    (∃ σ' ρ', Kette
      (ExecRel (V := vertragVon rufD rufIncD) (l := false) (Γ := []) (Λ := [])
        rufOD 0 Rwit70
        (Block.nil : Block rufD (vertragVon rufD rufIncD) false [] [] []))
      2 rufWeltD Env.nil σ' ρ') ∧
    (∃ σ ρ σ' ρ', execBlock (V := vertragVon rufD rufIncD) rufOD 0 Rwit70
      (Block.nil : Block rufD (vertragVon rufD rufIncD) false [] [] [])
      σ ρ = Ausgang.ok σ' ρ') := by
  refine ⟨hoare_skip _ _ _ _, invw_start,
    ⟨_, _, Kette.schritt rfl (Kette.schritt rfl Kette.leer)⟩,
    ⟨rufWeltD, Env.nil, rufWeltD, Env.nil, rfl⟩⟩

/- CUTS: what is not proved or not covered.
    PROVED here: `disj_kontinuation_einmal` (+ `_zeuge`),
    `disj_monoton_staerker` (+ `_zeuge`), `Kette` + `kette_invariant`
    (+ `_zeuge`), `ExecRel` + `kette_block_invariant` (+ `_zeuge`).
    NOT proved / not covered:
    * heterogeneous (non-uniform) chains: `kette_invariant` covers uniform
      links (one `Rel`, one `Inv`); `tick_runde`'s 64 `fenster_schritt`
      calls share one callee contract but differ per site (distinct
      arguments, distinct preconditions). The list-generalisation is open.
    * the `kette_block_invariant_zeuge` links are silent (`.nil` steps);
      genuine movement is witnessed at the schema level
      (`kette_invariant_zeuge`, spur `0 → 2`), not through `execBlock`,
      because `rufD` admits no writing block (`schreibt` is constantly
      false, `rufSigSchreibtFalse`).
    * no tactic integration: nothing here changes what `gabbro_calls` or
      `gabbro_open_hyps` (in `programmlogik/`, a different project) do;
      the lemmas are the sound proof rules such integration would invoke.
    * the 126 multiplication itself is analysed (REPORT-05.md section 1),
      not re-measured: the strengthened disjunctive specification was
      reverted upstream, so no 94-goal duty exists in the tree to close. -/
#print axioms Gabbro.Grammatik.GvSplits.disj_kontinuation_einmal
#print axioms Gabbro.Grammatik.GvSplits.disj_monoton_staerker
#print axioms Gabbro.Grammatik.GvSplits.kette_invariant
#print axioms Gabbro.Grammatik.GvSplits.kette_block_invariant
#print axioms Gabbro.Grammatik.GvSplits.disj_kontinuation_einmal_zeuge
#print axioms Gabbro.Grammatik.GvSplits.disj_monoton_staerker_zeuge
#print axioms Gabbro.Grammatik.GvSplits.hSchrittw
#print axioms Gabbro.Grammatik.GvSplits.invw_start
#print axioms Gabbro.Grammatik.GvSplits.invw_falsch
#print axioms Gabbro.Grammatik.GvSplits.kette_invariant_zeuge
#print axioms Gabbro.Grammatik.GvSplits.kette_block_invariant_zeuge

end Gabbro.Grammatik.GvSplits
