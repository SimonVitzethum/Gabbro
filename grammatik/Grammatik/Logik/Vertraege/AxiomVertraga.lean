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

/-- The declared ensures reads only the axiom's declared write carriers of
    the answer world (and the result). -/
def AxEnsLokal (Q : AxEns D) : Prop :=
  ∀ (a : D.Ax) (σ σ' : World D) (v : ErgVal D (D.aerg a)),
    (∀ t, D.aschreibt a t = true → σ.slots t = σ'.slots t) →
    (∀ g, D.agschreibt a g = true → σ.globs g = σ'.globs g) → Q a σ v = Q a σ' v

/-- **The strengthened user obligation.** The body triple and the caller
    duty of `KoerperGut`, for every oracle that respects the declared axiom
    frames AND meets the declared axiom ensures. -/
def KoerperGutA (P : Programm D) (passes : Nat) (Q : AxEns D) (f : D.Fn) : Prop :=
  ∀ O' : Orakel D, RahmenO O' → AxVertragO Q O' → KoerperGut P O' passes f

/-- The strengthened obligation is weaker than `KoerperGutV`: fewer oracles. -/
theorem koerperGutA_of_V {P : Programm D} {passes : Nat} (Q : AxEns D) {f : D.Fn}
    (h : KoerperGutV P passes f) : KoerperGutA P passes Q f :=
  fun O' hr _ => h O' hr

/-- Every recorded axiom answer meets the declared ensures. -/
def VertragA (z : Int → Option D.Fn) (Q : AxEns D) (HA : List (AxEintrag D)) : Prop :=
  ∀ (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) (x : World D × Int),
    (⟨a, σ, ρ, x⟩ : AxEintrag D) ∈ HA →
      ∀ v : ErgVal D (D.aerg a), einpassenErg z (D.aerg a) x.2 = some v → Q a x.1 v = true

theorem vertragA_nil (z : Int → Option D.Fn) (Q : AxEns D) : VertragA z Q ([] : List (AxEintrag D)) :=
  fun _ _ _ _ h => absurd h List.not_mem_nil

/-- The oracle of a record meets the declared ensures when the machine's
    oracle does and every recorded answer does. -/
theorem orakelAus_vertrag {Q : AxEns D} {O : Orakel D} (hQ : AxVertragO Q O)
    {HA : List (AxEintrag D)} (hv : VertragA O.zeiger Q HA) : AxVertragO Q (orakelAus O HA) := by
  intro a σ ρ v
  simp only [orakelAus]
  split
  · rename_i hex
    exact hv a σ ρ _ (Classical.choose_spec hex) v
  · exact hQ a σ ρ v

/-- The recorded answer world agrees with the machine's answer world on the
    axiom's declared carriers, so a local declared ensures transfers. -/
theorem axWelt_vertrag {Q : AxEns D} (hlok : AxEnsLokal Q) (e0 : Ereignis D) (a : D.Ax)
    (κ σ₂ : World D) (v : ErgVal D (D.aerg a)) (h : Q a σ₂ v = true) :
    Q a (axWelt e0 a κ σ₂) v = true := by
  rw [hlok a (axWelt e0 a κ σ₂) σ₂ v (fun t ht => by
      show (if D.aschreibt a t = true then σ₂.slots t else κ.slots t) = σ₂.slots t
      rw [if_pos ht])
    (fun g hg => by
      show (if D.agschreibt a g = true then σ₂.globs g else κ.globs g) = σ₂.globs g
      rw [if_pos hg])]
  exact h


end Gabbro.Grammatik
