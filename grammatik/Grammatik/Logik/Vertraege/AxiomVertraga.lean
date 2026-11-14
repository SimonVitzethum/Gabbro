/-
  File:      Grammatik/AxiomVertrag.lean
  Subject:   AXIOM-CALLING BODIES WITH A RESULT-DEPENDENT CONTRACT -- the
             finding about `KoerperGutV`, and the strengthening that closes
             it: per-axiom declared ensures.

  `KoerperGutV P passes f` asks for the body triple of `f` against EVERY
  oracle that respects the declared axiom frames (`RahmenO`). A frame says
  WHICH carriers an axiom may write, not WHAT it writes nor what it answers.
  Here, on the smallest body that calls an axiom and returns its answer --

      axiom inc() -> 0 .. 3  writes tab            (frame: `tab`)
      fn zaehle() -> 0 .. 3  requires Held(L)  writes tab
        { if true { let r = inc(); return r }; return 0 }

  -- the finding (`koerperGutV_nur_rahmen`): whatever `ensures E` the user
  writes, `KoerperGutV` holds only if `E` holds for EVERY result `v` and
  EVERY written value `w` of the slot (the post world `σ[tab[0] := w]`). So
  `E` cannot relate the result to the written slot: `result == tab[0]`
  ("inc returns the new value") fails (`inc_ensures_nicht_V`), for the
  frame-respecting oracle that writes `1` and answers `2`.

  The strengthening (`KoerperGutA`): an axiom DECLARES an ensures `Q` over
  its result and its post world (as a syscall declares `Qu`), the machine's
  oracle meets it (`AxVertragO Q O`, a hardware premise like `GutO`), and the
  user obligation quantifies over the frame-respecting oracles that meet
  the declared ensures. With `Q inc σ' v := (v == σ'.tab[0])`, the contract
  `result == tab[0]` is provable (`inc_koerperGutA`). The goal theorem over
  the strengthened obligation is `ziel_ort_voll_ax` (`ZielOrtAx.lean`); it
  needs `Q` to read only the axiom's declared carriers of the post world
  (`AxEnsLokal`), the class the replay can transfer.
-/
module
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollZeuge
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Declared axiom ensures, and the strengthened obligation -/

/-- A per-axiom declared ensures: a decision over the axiom's answer world
    and its (range-checked) result. -/
abbrev AxEns (D : Deklaration) := ∀ a : D.Ax, World D → ErgVal D (D.aerg a) → Bool

/-- The oracle meets the declared ensures: whenever an axiom's raw answer
    fits its declared result type, the declared ensures holds of the
    answer world and the result (the hardware premise of the declaration,
    as `GutO` is the one of the frame). -/
def AxVertragO (Q : AxEns D) (O : Orakel D) : Prop :=
  ∀ (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) (v : ErgVal D (D.aerg a)),
    einpassenErg O.zeiger (D.aerg a) (O.wirkt a σ ρ).2 = some v → Q a (O.wirkt a σ ρ).1 v = true

/-- A per-gate argument precondition: the declared `requires`, over the
    world at the call and the passed arguments. -/
abbrev AxPre (D : Deklaration) := ∀ a : D.Ax, World D → Env D (D.aparams a) → Bool

/-- **The conditional oracle class (C08 R3b).** Machine G asks an oracle about
    item `a` only in a QUESTION world `σ0.fragt (.inl a)` (the question event is
    recorded first, `World.fragt`). The class asks the declared ensures exactly
    there: at every question world whose precondition holds, a fitting raw answer
    meets `Q`. Worlds without the question are never asked and carry no duty. -/
def AxVertragOP {D : Deklaration} (Pre : AxPre D) (Q : AxEns D) (O : Orakel D) : Prop :=
  ∀ (a : D.Ax) (σ0 : World D) (ρ : Env D (D.aparams a)) (v : ErgVal D (D.aerg a)),
    Pre a (σ0.fragt (.inl a)) ρ = true →
    einpassenErg O.zeiger (D.aerg a) (O.wirkt a (σ0.fragt (.inl a)) ρ).2 = some v →
      Q a (O.wirkt a (σ0.fragt (.inl a)) ρ).1 v = true

/-- The precondition-restricted premise over EVERY world, question or not: the
    form of the gate split of fix lane F5 (`FremdRuf/T2`). It is strictly stronger
    than `AxVertragOP` (`CallSiteQuestionBlocker.old_class_too_strong`). -/
def AxVertragOPAlle {D : Deklaration} (Pre : AxPre D) (Q : AxEns D) (O : Orakel D) : Prop :=
  ∀ (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) (v : ErgVal D (D.aerg a)),
    Pre a σ ρ = true →
    einpassenErg O.zeiger (D.aerg a) (O.wirkt a σ ρ).2 = some v → Q a (O.wirkt a σ ρ).1 v = true

/-- The every-world form contains the question-world class. -/
theorem axVertragOP_of_alle {D : Deklaration} {Pre : AxPre D} {Q : AxEns D} {O : Orakel D}
    (h : AxVertragOPAlle Pre Q O) : AxVertragOP Pre Q O :=
  fun a σ0 ρ v hp hfit => h a (σ0.fragt (.inl a)) ρ v hp hfit

/-- (1) Every oracle meeting the full premise is in the class, for every precondition. -/
theorem axVertragOP_of_O {D : Deklaration} (Pre : AxPre D) {Q : AxEns D} {O : Orakel D}
    (h : AxVertragO Q O) : AxVertragOP Pre Q O :=
  fun a σ0 ρ v _ hfit => h a (σ0.fragt (.inl a)) ρ v hfit

/-- The oracle class of body duties: software summaries require the interface
    pre at the queried world; hardware and unresolved items remain unconditional.
    This lives below the replay and foreign-call layers to avoid import cycles. -/
def PreQ (P : Programm D) : AxPre D := fun a σ ρ =>
  if D.axHerkunft a = some AxOrigin.software then
    wahr? (eval σ (P.axVertrag a).pre σ ρ)
  else true

theorem preQ_hw (P : Programm D) {a : D.Ax}
    (h : D.axHerkunft a ≠ some AxOrigin.software)
    (σ : World D) (ρ : Env D (D.aparams a)) : PreQ P a σ ρ = true := by
  unfold PreQ
  rw [if_neg h]

theorem preQ_sw (P : Programm D) {a : D.Ax}
    (h : D.axHerkunft a = some AxOrigin.software)
    (σ : World D) (ρ : Env D (D.aparams a)) :
    PreQ P a σ ρ = wahr? (eval σ (P.axVertrag a).pre σ ρ) := by
  unfold PreQ
  rw [if_pos h]

/-- Without software items the conditional class is the unconditional summary at
    every question world. -/
theorem axVertragOP_preQ_ohne {P : Programm D} {Q : AxEns D} {O : Orakel D}
    (h : ∀ a : D.Ax, D.axHerkunft a ≠ some AxOrigin.software) :
    AxVertragOP (PreQ P) Q O ↔
      ∀ (a : D.Ax) (σ0 : World D) (ρ : Env D (D.aparams a)) (v : ErgVal D (D.aerg a)),
        einpassenErg O.zeiger (D.aerg a) (O.wirkt a (σ0.fragt (.inl a)) ρ).2 = some v →
          Q a (O.wirkt a (σ0.fragt (.inl a)) ρ).1 v = true := by
  constructor
  · intro hQ a σ0 ρ v hv
    exact hQ a σ0 ρ v (preQ_hw P (h a) _ ρ) hv
  · intro hQ a σ0 ρ v _ hv
    exact hQ a σ0 ρ v hv

/-- The declared ensures reads only the axiom's declared write carriers of
    the answer world (and the result). -/
def AxEnsLokal (Q : AxEns D) : Prop :=
  ∀ (a : D.Ax) (σ σ' : World D) (v : ErgVal D (D.aerg a)),
    (∀ t, D.aschreibt a t = true → σ.slots t = σ'.slots t) →
    (∀ g, D.agschreibt a g = true → σ.globs g = σ'.globs g) → Q a σ v = Q a σ' v

/-- **The strengthened user obligation.** The body triple and the caller
    duty of `KoerperGut`, for every oracle that respects the declared axiom
    frames AND meets the declared axiom ensures where `PreQ P` holds. The
    software pre restricts reliance; this enlarges the quantified oracle class. -/
def KoerperGutA (P : Programm D) (passes : Nat) (Q : AxEns D) (f : D.Fn) : Prop :=
  ∀ O' : Orakel D, RahmenO O' → AxVertragOP (PreQ P) Q O' → KoerperGut P O' passes f

/-- The strengthened obligation is weaker than `KoerperGutV`: fewer oracles. -/
theorem koerperGutA_of_V {P : Programm D} {passes : Nat} (Q : AxEns D) {f : D.Fn}
    (h : KoerperGutV P passes f) : KoerperGutA P passes Q f :=
  fun O' hr _ => h O' hr

/-- Every recorded axiom answer meets the declared ensures. -/
def VertragA (z : Int → Option D.Fn) (Q : AxEns D) (HA : List (AxEintrag D)) : Prop :=
  ∀ (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) (x : World D × Int),
    (⟨a, σ, ρ, x⟩ : AxEintrag D) ∈ HA →
      ∀ v : ErgVal D (D.aerg a), einpassenErg z (D.aerg a) x.2 = some v →
        ∀ w : World D, w.slots = x.1.slots → w.globs = x.1.globs → Q a w v = true

theorem vertragA_nil (z : Int → Option D.Fn) (Q : AxEns D) : VertragA z Q ([] : List (AxEintrag D)) :=
  fun _ _ _ _ h => absurd h List.not_mem_nil

/-- The oracle of a record meets the declared ensures when the machine's
    oracle does and every recorded answer does. -/
theorem orakelAus_vertrag {Q : AxEns D} {O : Orakel D} (hQ : AxVertragO Q O)
    {HA : List (AxEintrag D)} (hv : VertragA O.zeiger Q HA) : AxVertragO Q (orakelAus O HA) := by
  intro a σ ρ v hfit
  by_cases h : AxFrage HA a σ.ohneLese ρ
  · obtain ⟨hs, hg, h2⟩ := orakelAus_frage_speicher O HA h
    have hfit' : einpassenErg O.zeiger (D.aerg a) (Classical.choose h).2.2 = some v := by
      rw [← h2]
      exact hfit
    exact hv a _ ρ _ (Classical.choose_spec h).1 v hfit' _ hs hg
  · rw [orakelAus_wirkt_sonst O HA h] at hfit ⊢
    exact hQ a σ ρ v hfit

/-- (3) Conditional summaries survive replay: recorded answers satisfy the summary;
    every other question retains the actual oracle's conditional contract at the
    same question world. No non-decoding fallback word or extra realizability
    premise is required. -/
theorem orakelAus_vertragOP {Pre : AxPre D} {Q : AxEns D} {O : Orakel D}
    (hQ : AxVertragOP Pre Q O) {HA : List (AxEintrag D)}
    (hv : VertragA O.zeiger Q HA) : AxVertragOP Pre Q (orakelAus O HA) := by
  intro a σ0 ρ v hp hfit
  by_cases h : AxFrage HA a (σ0.fragt (.inl a)).ohneLese ρ
  · obtain ⟨hs, hg, h2⟩ := orakelAus_frage_speicher O HA h
    have hfit' : einpassenErg O.zeiger (D.aerg a) (Classical.choose h).2.2 = some v := by
      rw [← h2]
      exact hfit
    exact hv a _ ρ _ (Classical.choose_spec h).1 v hfit' _ hs hg
  · rw [orakelAus_wirkt_sonst O HA h] at hfit ⊢
    exact hQ a σ0 ρ v hp hfit

/-- The recorded answer world agrees with the machine's answer world on the
    axiom's declared carriers, so a local declared ensures transfers. -/
theorem axWelt_vertrag {Q : AxEns D} (hlok : AxEnsLokal Q) (e0 : Ereignis D) (a : D.Ax)
    (κ σ₂ : World D) (v : ErgVal D (D.aerg a)) (h : Q a σ₂ v = true) :
    ∀ w : World D, w.slots = (axWelt e0 a κ σ₂).slots → w.globs = (axWelt e0 a κ σ₂).globs →
      Q a w v = true := by
  intro w hws hwg
  rw [hlok a w σ₂ v (fun t ht => by
      rw [hws]
      show (if D.aschreibt a t = true then σ₂.slots t else κ.slots t) = σ₂.slots t
      rw [if_pos ht])
    (fun g hg => by
      rw [hwg]
      show (if D.agschreibt a g = true then σ₂.globs g else κ.globs g) = σ₂.globs g
      rw [if_pos hg])]
  exact h


end Gabbro.Grammatik
