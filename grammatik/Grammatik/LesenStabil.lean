/-
  File:     Grammatik/LesenStabil.lean
  Subject:  **The stable form for READS** -- read-only shared data (config
              tables and the like): a read through a held guard, or off a
              never-written carrier, is stable across foreign steps; contract
              reads (`requires` / `ensures` / invariant) plug in through the
              computed `Extraktion` read hulls as the read-only reference.

  What it gives:

    `RequiresLiestIn` / `EnsuresLiestIn` / `InvarianteLiestIn` -- the contract
      reads as frame inclusions: every `orte` member of the contract lies in
      the read frame `(W, G)`. The read-only reference, next to the computed
      hulls (`liestDirekt` family, `liestVertrag…`, `liestVertragMitInv…`).
    `requiresLiestIn_aus_Huelle` / `ensuresLiestIn_aus_Huelle` /
      `invarianteLiestIn_aus_Huelle` -- the hull covers the contract: frame
      coverage of `liestVertragTab/Glob` (resp. `…MitInvTab/Glob`) discharges
      the inclusion, via the `…_deckt_requires / …_deckt_ensures /
      …_deckt_invariante` bridges of `Extraktion.lean` §15.
    `SchreibtNie` / `NieGeschrieben` -- the never-written carrier: no thread
      (resp. one foreign thread) writes inside the read frame.
    `FremdOhneWache` -- the guard miss: the foreign thread lacks the guard of
      a carrier (negated `WaechterGehalten`).
    `schreibtNicht_ohne_Wache` -- the touch rule, contrapositive: under the
      `TraegerInv` discipline, a guard miss is a write miss.
    `schreibtNie_aus_Wache` -- guard misses over the whole read frame lift to
      `SchreibtNie`.
    `disjunkt_aus_schreibtNie` -- a write miss over the read frame is the
      `Disjunkt` side `stabil` consumes.
    `LesenStabilSchritt` / `lesenStabil_schritt_gilt` -- the stable form for
      one foreign step, as a `Prop` shape plus its proof.
    `LesenStabilKette` / `lesenStabil_kette_gilt` / `lesenStabil_amEnde` --
      the fold over the `GemeinsamerLauf` chain (`kette_erhaelt`), down to its
      last world (`getLast?` as in `allgemeinStabil`).
    `haengtAb_requires_bei_Lesen` / `haengtAb_ensures_bei_Lesen` /
      `haengtAb_invariante_bei_Lesen` -- contracts hang on any covering read
      frame (the `haengtAb_requires / …_ensures / …_invariante` premises with
      `(W, G)` in place of the signature frame, via `haengtAb_weitet`).
    `requiresStabil_schritt` / `ensuresStabil_schritt` /
      `invarianteStabil_schritt` -- contract reads survive one foreign step
      that never writes their frame.
    `requiresStabil_kette` / `ensuresStabil_kette` / `invarianteStabil_kette`
      -- the same over the whole chain.
    `lesenUnterWache_schritt` -- the guarded read in one step: guard misses
      over the frame plus a frame step preserve any frame-local `Q`.

  Cuts, booked not hidden:

    (L1) No lock exclusion across threads. The guarded side proves only the
      contrapositive (guard miss implies write miss); that the foreign thread
      actually misses the guard while the reader holds it is a premise
      (`FremdOhneWache`), never derived. The model has no mutual-exclusion
      theorem over `haelt` lists, and this file does not invent one.
    (L2) Body reads stay out. `liestDirekt` / `liestTab` / `liestGlob` are
      referenced only as the hull family the contract bridges belong to; no
      `HaengtAb` is derived from the body hull for abstract `Q`. What has no
      computed footprint is assumed (`HaengtAb` premise), not derived.
    (L3) One world only. Like G7/R1a, every `Q` here speaks about a single
      world; `old(…)` two-world contract readings are out of scope.
    (L4) No call-transitive hull. `NieGeschrieben` ranges over declared write
      frames (`D.schreibt` / `D.gschreibt`), not over transitive call hulls;
      indirect foreign targets (S7) stay refused elsewhere, not covered here.
    (L5) No machine-ordering exceptions. `atomic` globals (A10) and
      `publishes` / `awaits` pairs (G4) get no side clause: a written carrier
      fails the `SchreibtNie` premise loudly instead of passing silently.

  Core only: no `mathlib`, no extra axioms -- only `def` and `theorem` over
  the genuine types (`GemeinsamerLauf`, `TraegerInv`, `Programm`).
-/

import Grammatik.InterferenzAllgemein
import Grammatik.Extraktion

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Contract reads as frame inclusions (the read-only reference) -/

/-- What `requires` reads lies in `(W, G)`: every `orte` member on either side
    is covered by the read frame. The premise shape of `haengtAb_requires`,
    with the signature frame replaced by the read frame. -/
def RequiresLiestIn (P : Programm D) (f : D.Fn)
    (W : D.Tab → Bool) (G : D.Glob → Bool) : Prop :=
  (∀ t : D.Tab, (.inl t : D.Tab ⊕ D.Glob) ∈ (P.requires f).orte → W t = true) ∧
  (∀ g : D.Glob, (.inr g : D.Tab ⊕ D.Glob) ∈ (P.requires f).orte → G g = true)

/-- What `ensures` reads lies in `(W, G)`. -/
def EnsuresLiestIn (P : Programm D) (f : D.Fn)
    (W : D.Tab → Bool) (G : D.Glob → Bool) : Prop :=
  (∀ t : D.Tab, (.inl t : D.Tab ⊕ D.Glob) ∈ (P.ensures f).orte → W t = true) ∧
  (∀ g : D.Glob, (.inr g : D.Tab ⊕ D.Glob) ∈ (P.ensures f).orte → G g = true)

/-- What the invariant `i` reads lies in `(W, G)`. -/
def InvarianteLiestIn (P : Programm D) (i : D.Inv)
    (W : D.Tab → Bool) (G : D.Glob → Bool) : Prop :=
  (∀ t : D.Tab, (.inl t : D.Tab ⊕ D.Glob) ∈ (P.invariante i).orte → W t = true) ∧
  (∀ g : D.Glob, (.inr g : D.Tab ⊕ D.Glob) ∈ (P.invariante i).orte → G g = true)

/-- Hull coverage discharges the `requires` inclusion: what the contract hull
    `liestVertragTab/Glob` covers, the contract reads. The bridges are
    `liestVertragTab_deckt_requires` / `liestVertragGlob_deckt_requires`
    (`Extraktion.lean` §15) -- the `liestDirekt` family as read-only
    reference (L2). -/
theorem requiresLiestIn_aus_Huelle (P : Programm D) (f : D.Fn)
    (W : D.Tab → Bool) (G : D.Glob → Bool)
    (hT : ∀ t ∈ Extraktion.liestVertragTab P f, W t = true)
    (hG : ∀ g ∈ Extraktion.liestVertragGlob P f, G g = true) :
    RequiresLiestIn P f W G := by
  constructor
  · intro t ht
    exact hT t (Extraktion.liestVertragTab_deckt_requires P f t ht)
  · intro g hg
    exact hG g (Extraktion.liestVertragGlob_deckt_requires P f g hg)

/-- Hull coverage discharges the `ensures` inclusion. -/
theorem ensuresLiestIn_aus_Huelle (P : Programm D) (f : D.Fn)
    (W : D.Tab → Bool) (G : D.Glob → Bool)
    (hT : ∀ t ∈ Extraktion.liestVertragTab P f, W t = true)
    (hG : ∀ g ∈ Extraktion.liestVertragGlob P f, G g = true) :
    EnsuresLiestIn P f W G := by
  constructor
  · intro t ht
    exact hT t (Extraktion.liestVertragTab_deckt_ensures P f t ht)
  · intro g hg
    exact hG g (Extraktion.liestVertragGlob_deckt_ensures P f g hg)

/-- Hull coverage with owed invariants discharges the invariant inclusion
    (`…MitInvTab/Glob_deckt_invariante`). -/
theorem invarianteLiestIn_aus_Huelle (P : Programm D) (f : D.Fn)
    (invs : List D.Inv) (i : D.Inv) (hi : i ∈ invs)
    (hs : schuldet f i = true)
    (W : D.Tab → Bool) (G : D.Glob → Bool)
    (hT : ∀ t ∈ Extraktion.liestVertragMitInvTab P f invs, W t = true)
    (hG : ∀ g ∈ Extraktion.liestVertragMitInvGlob P f invs, G g = true) :
    InvarianteLiestIn P i W G := by
  constructor
  · intro t ht
    exact hT t (Extraktion.liestVertragMitInvTab_deckt_invariante P f invs i hi hs t ht)
  · intro g hg
    exact hG g (Extraktion.liestVertragMitInvGlob_deckt_invariante P f invs i hi hs g hg)

/-! ## 2. Never-written carriers and guard misses -/

/-- One foreign thread never writes inside the read frame. -/
def SchreibtNie (g : D.Fn) (W : D.Tab → Bool) (G : D.Glob → Bool) : Prop :=
  (∀ t : D.Tab, W t = true → D.schreibt g t = false) ∧
  (∀ x : D.Glob, G x = true → D.gschreibt g x = false)

/-- No thread of the joint run writes inside the read frame: the
    never-written carrier (config-table shape), over all `J.faeden`. -/
def NieGeschrieben (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (W : D.Tab → Bool) (G : D.Glob → Bool) : Prop :=
  ∀ f : Faden, f ∈ J.faeden → SchreibtNie (J.code f) W G

/-- The guard miss: the foreign thread lacks the guard of carrier `c`
    (negated `WaechterGehalten`). Whether the reader's held guard excludes
    the foreign thread is NOT derived here (L1) -- it arrives as this
    premise. -/
def FremdOhneWache (g : D.Fn) (c : D.Tab ⊕ D.Glob) : Prop :=
  ¬ WaechterGehalten g c

/-- The touch rule, contrapositive: under the carrier discipline, a guard
    miss is a write miss. Pure logic over `I.disziplin` -- no run premise. -/
theorem schreibtNicht_ohne_Wache (I : TraegerInv (D := D)) (g : D.Fn)
    (c : D.Tab ⊕ D.Glob) (h : FremdOhneWache (D := D) g c) :
    TraegerSchreibt g c = false := by
  cases heq : TraegerSchreibt g c with
  | true => exact absurd (I.disziplin g c heq) h
  | false => rfl

/-- Guard misses over the whole read frame lift to `SchreibtNie`: the held
    guard, read through, keeps the foreign write off. -/
theorem schreibtNie_aus_Wache (I : TraegerInv (D := D)) (g : D.Fn)
    (W : D.Tab → Bool) (G : D.Glob → Bool)
    (hT : ∀ t : D.Tab, W t = true → FremdOhneWache (D := D) g (.inl t))
    (hG : ∀ x : D.Glob, G x = true → FremdOhneWache (D := D) g (.inr x)) :
    SchreibtNie g W G := by
  constructor
  · intro t ht
    have h := schreibtNicht_ohne_Wache I g (.inl t) (hT t ht)
    exact h
  · intro x hx
    have h := schreibtNicht_ohne_Wache I g (.inr x) (hG x hx)
    exact h

/-- A write miss over the read frame is the `Disjunkt` side `stabil`
    consumes. -/
theorem disjunkt_aus_schreibtNie (g : D.Fn)
    (W : D.Tab → Bool) (G : D.Glob → Bool)
    (h : SchreibtNie (D := D) g W G) :
    Disjunkt W G (D.schreibt g) (D.gschreibt g) := by
  constructor
  · intro t ht
    exact h.1 t ht
  · intro x hx
    exact h.2 x hx

/-! ## 3. The stable form for one foreign step -/

/-- **The stable form for READS in one foreign step**: what hangs only on
    the read frame survives a frame step of a thread that never writes it. -/
def LesenStabilSchritt (W : D.Tab → Bool) (G : D.Glob → Bool)
    (Q : World D → Prop) (fremd : D.Fn) : Prop :=
  HaengtAb W G Q → SchreibtNie fremd W G →
    ∀ σ σ' : World D,
      Rahmen (D.schreibt fremd) (D.gschreibt fremd) σ σ' → (Q σ ↔ Q σ')

/-- **The form holds.** Frame plus write miss give `Disjunkt`, and `stabil`
    closes. -/
theorem lesenStabil_schritt_gilt (W : D.Tab → Bool) (G : D.Glob → Bool)
    (Q : World D → Prop) (fremd : D.Fn) :
    LesenStabilSchritt W G Q fremd := by
  intro hQ hN σ σ' hR
  exact stabil hQ hR (disjunkt_aus_schreibtNie fremd W G hN)

/-- **The guarded read in one step.** Guard misses over the frame plus a
    frame step preserve any frame-local `Q` -- via `schreibtNie_aus_Wache`
    and `stabil`. -/
theorem lesenUnterWache_schritt (I : TraegerInv (D := D))
    (W : D.Tab → Bool) (G : D.Glob → Bool) (Q : World D → Prop)
    (hQ : HaengtAb W G Q) (g : D.Fn)
    {vor nach : World D}
    (hR : Rahmen (D.schreibt g) (D.gschreibt g) vor nach)
    (hT : ∀ t : D.Tab, W t = true → FremdOhneWache (D := D) g (.inl t))
    (hG : ∀ x : D.Glob, G x = true → FremdOhneWache (D := D) g (.inr x)) :
    Q vor ↔ Q nach :=
  stabil hQ hR
    (disjunkt_aus_schreibtNie g W G (schreibtNie_aus_Wache I g W G hT hG))

/-! ## 4. Contracts hang on any covering read frame -/

/-- `requires` hangs on any read frame its reads lie in (the
    `haengtAb_requires` premises at `(W, G)` instead of the signature
    frame). -/
theorem haengtAb_requires_bei_Lesen (P : Programm D) (f : D.Fn)
    (W : D.Tab → Bool) (G : D.Glob → Bool)
    (hT : ∀ t : D.Tab, (.inl t : D.Tab ⊕ D.Glob) ∈ (P.requires f).orte → W t = true)
    (hG : ∀ g : D.Glob, (.inr g : D.Tab ⊕ D.Glob) ∈ (P.requires f).orte → G g = true) :
    HaengtAb W G (Extraktion.QRequires P f) :=
  Extraktion.haengtAb_weitet
    (fun t ht => hT t ((Extraktion.vertragW_mem _ t).mp ht))
    (fun g hg => hG g ((Extraktion.vertragG_mem _ g).mp hg))
    (Extraktion.haengtAb_expr (P.requires f))

/-- `ensures` hangs on any read frame its reads lie in. -/
theorem haengtAb_ensures_bei_Lesen (P : Programm D) (f : D.Fn)
    (W : D.Tab → Bool) (G : D.Glob → Bool)
    (hT : ∀ t : D.Tab, (.inl t : D.Tab ⊕ D.Glob) ∈ (P.ensures f).orte → W t = true)
    (hG : ∀ g : D.Glob, (.inr g : D.Tab ⊕ D.Glob) ∈ (P.ensures f).orte → G g = true) :
    HaengtAb W G (Extraktion.QEnsures P f) :=
  Extraktion.haengtAb_weitet
    (fun t ht => hT t ((Extraktion.vertragW_mem _ t).mp ht))
    (fun g hg => hG g ((Extraktion.vertragG_mem _ g).mp hg))
    (Extraktion.haengtAb_ensures_shape P f)

/-- An invariant hangs on any read frame its reads lie in. -/
theorem haengtAb_invariante_bei_Lesen (P : Programm D) (i : D.Inv)
    (W : D.Tab → Bool) (G : D.Glob → Bool)
    (hT : ∀ t : D.Tab, (.inl t : D.Tab ⊕ D.Glob) ∈ (P.invariante i).orte → W t = true)
    (hG : ∀ g : D.Glob, (.inr g : D.Tab ⊕ D.Glob) ∈ (P.invariante i).orte → G g = true) :
    HaengtAb W G (Extraktion.QInvariante P i) :=
  Extraktion.haengtAb_weitet
    (fun t ht => hT t ((Extraktion.vertragW_mem _ t).mp ht))
    (fun g hg => hG g ((Extraktion.vertragG_mem _ g).mp hg))
    (Extraktion.haengtAb_invariante_shape P i)

/-! ## 5. Contract reads survive foreign steps that never write their frame -/

/-- A `requires` read survives one foreign step that never writes its frame. -/
theorem requiresStabil_schritt (P : Programm D) (f fremd : D.Fn)
    (W : D.Tab → Bool) (G : D.Glob → Bool)
    (hR0 : RequiresLiestIn P f W G)
    (hN : SchreibtNie (D := D) fremd W G)
    {vor nach : World D}
    (hR : Rahmen (D.schreibt fremd) (D.gschreibt fremd) vor nach) :
    Extraktion.QRequires P f vor ↔ Extraktion.QRequires P f nach :=
  stabil (haengtAb_requires_bei_Lesen P f W G hR0.1 hR0.2) hR
    (disjunkt_aus_schreibtNie fremd W G hN)

/-- An `ensures` read survives one foreign step that never writes its frame. -/
theorem ensuresStabil_schritt (P : Programm D) (f fremd : D.Fn)
    (W : D.Tab → Bool) (G : D.Glob → Bool)
    (hR0 : EnsuresLiestIn P f W G)
    (hN : SchreibtNie (D := D) fremd W G)
    {vor nach : World D}
    (hR : Rahmen (D.schreibt fremd) (D.gschreibt fremd) vor nach) :
    Extraktion.QEnsures P f vor ↔ Extraktion.QEnsures P f nach :=
  stabil (haengtAb_ensures_bei_Lesen P f W G hR0.1 hR0.2) hR
    (disjunkt_aus_schreibtNie fremd W G hN)

/-- An invariant read survives one foreign step that never writes its frame. -/
theorem invarianteStabil_schritt (P : Programm D) (i : D.Inv) (fremd : D.Fn)
    (W : D.Tab → Bool) (G : D.Glob → Bool)
    (hR0 : InvarianteLiestIn P i W G)
    (hN : SchreibtNie (D := D) fremd W G)
    {vor nach : World D}
    (hR : Rahmen (D.schreibt fremd) (D.gschreibt fremd) vor nach) :
    Extraktion.QInvariante P i vor ↔ Extraktion.QInvariante P i nach :=
  stabil (haengtAb_invariante_bei_Lesen P i W G hR0.1 hR0.2) hR
    (disjunkt_aus_schreibtNie fremd W G hN)

/-! ## 6. The fold over the chain: never-written reads reach the last world -/

/-- **The stable form for READS over the chain**: frame-local and
    never-written at every thread, valid at the head -- valid everywhere. -/
def LesenStabilKette (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (W : D.Tab → Bool) (G : D.Glob → Bool) (Q : World D → Prop) : Prop :=
  HaengtAb W G Q → NieGeschrieben Nb J W G →
    (∀ σ₀ : World D, J.welten[0]? = some σ₀ → Q σ₀) →
      ∀ (k : Nat) (σ : World D), J.welten[k]? = some σ → Q σ

/-- **The fold holds.** Every link stays in its thread's frame (`hSchritt`),
    and the write miss at that thread is the `Disjunkt` side -- so
    `kette_erhaelt` carries `Q` down the chain. -/
theorem lesenStabil_kette_gilt (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (W : D.Tab → Bool) (G : D.Glob → Bool) (Q : World D → Prop)
    (hQ : HaengtAb W G Q) (hN : NieGeschrieben Nb J W G)
    (hInit : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → Q σ₀) :
    ∀ (k : Nat) (σ : World D), J.welten[k]? = some σ → Q σ := by
  refine kette_erhaelt J.welten J.schrittFaden J.hKette Q hInit ?_
  intro k g vor nach hkg hkv hkn
  obtain ⟨hgm, hR⟩ := J.hSchritt k g vor nach hkg hkv hkn
  exact stabil hQ hR (disjunkt_aus_schreibtNie (J.code g) W G (hN g hgm))

/-- **The chain form holds as stated.** -/
theorem lesenStabilKette_gilt (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (W : D.Tab → Bool) (G : D.Glob → Bool) (Q : World D → Prop) :
    LesenStabilKette Nb J W G Q := by
  intro hQ hN hInit k σ hσ
  exact lesenStabil_kette_gilt Nb J W G Q hQ hN hInit k σ hσ

/-- **At the last world** (`getLast?` as in `allgemeinStabil`). -/
theorem lesenStabil_amEnde (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (W : D.Tab → Bool) (G : D.Glob → Bool) (Q : World D → Prop)
    (hQ : HaengtAb W G Q) (hN : NieGeschrieben Nb J W G)
    (hInit : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → Q σ₀)
    (σ : World D) (hletzte : J.welten.getLast? = some σ) : Q σ := by
  have hall := lesenStabil_kette_gilt Nb J W G Q hQ hN hInit
  have hlast : J.welten[J.welten.length - 1]? = some σ := by
    rw [← List.getLast?_eq_getElem?]
    exact hletzte
  exact hall _ σ hlast

/-- A `requires` read valid at the head reaches every chain world. -/
theorem requiresStabil_kette (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb) (P : Programm D) (f : D.Fn)
    (W : D.Tab → Bool) (G : D.Glob → Bool)
    (hR0 : RequiresLiestIn P f W G) (hN : NieGeschrieben Nb J W G)
    (hInit : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → Extraktion.QRequires P f σ₀) :
    ∀ (k : Nat) (σ : World D), J.welten[k]? = some σ → Extraktion.QRequires P f σ :=
  lesenStabil_kette_gilt Nb J W G _ (haengtAb_requires_bei_Lesen P f W G hR0.1 hR0.2) hN hInit

/-- An `ensures` read valid at the head reaches every chain world. -/
theorem ensuresStabil_kette (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb) (P : Programm D) (f : D.Fn)
    (W : D.Tab → Bool) (G : D.Glob → Bool)
    (hR0 : EnsuresLiestIn P f W G) (hN : NieGeschrieben Nb J W G)
    (hInit : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → Extraktion.QEnsures P f σ₀) :
    ∀ (k : Nat) (σ : World D), J.welten[k]? = some σ → Extraktion.QEnsures P f σ :=
  lesenStabil_kette_gilt Nb J W G _ (haengtAb_ensures_bei_Lesen P f W G hR0.1 hR0.2) hN hInit

/-- An invariant read valid at the head reaches every chain world. -/
theorem invarianteStabil_kette (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb) (P : Programm D) (i : D.Inv)
    (W : D.Tab → Bool) (G : D.Glob → Bool)
    (hR0 : InvarianteLiestIn P i W G) (hN : NieGeschrieben Nb J W G)
    (hInit : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → Extraktion.QInvariante P i σ₀) :
    ∀ (k : Nat) (σ : World D), J.welten[k]? = some σ → Extraktion.QInvariante P i σ :=
  lesenStabil_kette_gilt Nb J W G _ (haengtAb_invariante_bei_Lesen P i W G hR0.1 hR0.2) hN hInit

#print axioms Gabbro.Grammatik.schreibtNicht_ohne_Wache
#print axioms Gabbro.Grammatik.schreibtNie_aus_Wache
#print axioms Gabbro.Grammatik.disjunkt_aus_schreibtNie
#print axioms Gabbro.Grammatik.lesenStabil_schritt_gilt
#print axioms Gabbro.Grammatik.lesenUnterWache_schritt
#print axioms Gabbro.Grammatik.haengtAb_requires_bei_Lesen
#print axioms Gabbro.Grammatik.haengtAb_ensures_bei_Lesen
#print axioms Gabbro.Grammatik.haengtAb_invariante_bei_Lesen
#print axioms Gabbro.Grammatik.requiresStabil_schritt
#print axioms Gabbro.Grammatik.ensuresStabil_schritt
#print axioms Gabbro.Grammatik.invarianteStabil_schritt
#print axioms Gabbro.Grammatik.lesenStabil_kette_gilt
#print axioms Gabbro.Grammatik.lesenStabilKette_gilt
#print axioms Gabbro.Grammatik.lesenStabil_amEnde
#print axioms Gabbro.Grammatik.requiresStabil_kette
#print axioms Gabbro.Grammatik.ensuresStabil_kette
#print axioms Gabbro.Grammatik.invarianteStabil_kette
#print axioms Gabbro.Grammatik.requiresLiestIn_aus_Huelle
#print axioms Gabbro.Grammatik.ensuresLiestIn_aus_Huelle
#print axioms Gabbro.Grammatik.invarianteLiestIn_aus_Huelle

end Gabbro.Grammatik
