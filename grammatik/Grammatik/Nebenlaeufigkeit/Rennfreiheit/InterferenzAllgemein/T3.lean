/- Part 3 of 5 of `InterferenzAllgemein` (split by instrumente/teile/lean-teilen.py; the umbrella `InterferenzAllgemein.lean` imports all parts). -/
module
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein.T2
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}
variable {D : Deklaration}

/-- Stability from specifications (N threads): sequential contract triples
    plus interference freedom over the conjunction give stable contract
    assertions at the last world, via the proved `owickiGries_stabil`. The
    sequential triples supply `hInit`/`hEigen` (folded above); the
    interference check supplies `hFremd` through its preserved side. -/
theorem stabil_from_spec (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Pre Post : D.Fn → World D → Prop)
    (hInv : InvariantenKontext Nb J I)
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f))
        (SpecQ Pre Post Nb J f))
    (hSpec : ∀ (f : Faden), f ∈ J.faeden → SpecTriple Pre Post Nb J f)
    (hFree : InterferenceFree Nb J (SpecQ Pre Post Nb J)) :
    ∀ (σ : World D), J.welten.getLast? = some σ →
      ∀ (f : Faden), f ∈ J.faeden → SpecQ Pre Post Nb J f σ := by
  refine owickiGries_stabil Nb J I _ hInv hDeck hAb ?_ hFree
  intro f hf
  exact seqTriple_from_spec Nb J Pre Post f (hSpec f hf)

#print axioms Gabbro.Grammatik.seqTriple_from_spec
#print axioms Gabbro.Grammatik.stabil_from_spec

end Gabbro.Grammatik

/-! ## 20. CSL discharge: invariant-form assertions need no per-run check (x02)

    The auditor's finding: `ziel_seqLogic_aus_spec` (Ziel.lean §6, bound to
    `stabil_from_spec`, §19 above) books `hFree : InterferenceFree` as user
    OWN-LOGIC -- and `InterferenceFree` (§18, `:891`) is verbatim the
    Owicki-Gries condition (every foreign step preserves every assertion), so
    concurrent code over shared carriers forces the user into a per-run
    non-interference proof.

    The full derivation -- `InterferenceFree` for ARBITRARY `Q` from
    `TraegerInv` + `HaengtAb` -- does NOT close, and the reason is one line:
    `HaengtAb` says `Q` reads only its frame, but a foreign step writing
    INSIDE that frame may still break `Q`. Frame-locality is not preservation.
    So the CSL restriction is taken: assertions over lock-shared carriers are
    allowed ONLY in invariant (resource-invariant) form -- and invariant-form
    assertions are interference-free BY CONSTRUCTION, on the same engine that
    carries `allgemeinStabil_invariant` (§11): the context holds the invariant
    at every chain world (`invErhalt_aus_Kontext`), so each foreign step goes
    from one invariant world to another and `Q`, being the invariant, follows.

    What this section proves (no `sorry`, no `axiom`):

    * `InvariantForm` -- the covered fragment, named: per thread, `Q f`
      coincides with some carrier invariant `I.inv c` (the carrier may differ
      per thread; shared carriers are the point, disjoint ones already travel
      through the `stabil` side of `hFremd`).
    * `interferenceFree_of_invariantForm` -- the discharge: form plus context
      yields `InterferenceFree`. This is the theorem that removes the per-run
      proof for the covered class.
    * `owickiGries_stabil_invariantForm` -- the Owicki-Gries corollary with
      `hFree` replaced by `hForm` (same conclusion as `owickiGries_stabil`).
    * `stabil_from_spec_invariantForm` -- the contract-level corollary with
      `hFree` replaced by `hForm` over `SpecQ` (same conclusion as
      `stabil_from_spec`, §19).

    User-obligation delta, stated exactly (BEFORE = §19 R3, AFTER = this section):

    * BEFORE: the user owes `hFree` -- for every thread `f` and every foreign
      step, `Q f` survives the step. A per-run preservation proof, OWN-LOGIC.
    * AFTER (covered class -- `Q` in invariant form): `hFree` is DERIVED. The
      user owes instead (U1) `hForm` -- exhibit, per thread, the carrier `c`
      with `Q f σ ↔ I.inv c σ` for all `σ`: a static shape check, no per-step
      reasoning; and (U2) `hInv` (`InvariantenKontext`) -- UNCHANGED, it was
      already a premise of `stabil_from_spec`. `hSpec` and `hAb` are likewise
      unchanged.
    * NOT covered: assertions over shared carriers that are NOT in invariant
      form. There `hFree` remains OWN-LOGIC, exactly as §19 R3 books it. This
      section narrows R3 for the invariant fragment; it does not delete it.

    Remainder (not here, named so no wave re-measures it):

    * The Ziel-level binder -- a `ziel_seqLogic_aus_spec` variant consuming
      `stabil_from_spec_invariantForm` (with `hForm` instead of `hFree`) --
      belongs to the proof architect: `Ziel.lean` is owned by another wave and
      is not touched here (§19 R5 carries over).
    * `hInv` itself (establishing the context per run: entry plus discipline)
      is carried as before, not discharged; `hDeck` is carried, not consumed
      (G5 carries over).
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- An assertion in invariant (resource-invariant) form: for every thread, `Q f`
    coincides, at every world, with the invariant of some carrier. This is the
    CSL fragment -- assertions over lock-shared carriers are allowed only in
    this form; the carrier may differ per thread. -/
def InvariantForm (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Q : Faden → World D → Prop) : Prop :=
  ∀ (f : Faden), f ∈ J.faeden → ∃ c : D.Tab ⊕ D.Glob, ∀ (σ : World D), Q f σ ↔ I.inv c σ

/-- **Interference freedom by construction.** An invariant-form assertion
    survives every foreign step: both worlds of the step are chain worlds, the
    context holds the invariant at each (`invErhalt_aus_Kontext`, the engine
    behind `allgemeinStabil_invariant`), and `Q` IS the invariant -- so there
    is nothing per-run left to prove. -/
theorem interferenceFree_of_invariantForm (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Q : Faden → World D → Prop)
    (hForm : InvariantForm Nb J I Q)
    (hInv : InvariantenKontext Nb J I) :
    InterferenceFree Nb J Q := by
  intro f hf k g vor nach _ _ hkg hkv hkn
  obtain ⟨c, hc⟩ := hForm f hf
  rw [hc vor, hc nach]
  exact invErhalt_aus_Kontext Nb J I hInv c vor nach
    (List.mem_of_getElem? hkv) (List.mem_of_getElem? hkn)

/-- Owicki-Gries stability for the invariant fragment: sequential triples plus
    the FORM check give stable assertions at the last world -- `hFree` is
    derived above, not assumed. Same conclusion as `owickiGries_stabil`. -/
theorem owickiGries_stabil_invariantForm (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Q : Faden → World D → Prop)
    (hInv : InvariantenKontext Nb J I)
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f)) (Q f))
    (hSeq : ∀ (f : Faden), f ∈ J.faeden → SeqTriple Nb J Q f)
    (hForm : InvariantForm Nb J I Q) :
    ∀ (σ : World D), J.welten.getLast? = some σ → ∀ (f : Faden), f ∈ J.faeden → Q f σ :=
  owickiGries_stabil Nb J I Q hInv hDeck hAb hSeq
    (interferenceFree_of_invariantForm Nb J I Q hForm hInv)

/-- Stability from specifications for the invariant fragment: sequential
    contract triples plus the FORM check over the conjunction give stable
    contract assertions at the last world. Same conclusion as
    `stabil_from_spec` (§19), with `hFree` derived instead of owed. -/
theorem stabil_from_spec_invariantForm (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Pre Post : D.Fn → World D → Prop)
    (hInv : InvariantenKontext Nb J I)
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f))
        (SpecQ Pre Post Nb J f))
    (hSpec : ∀ (f : Faden), f ∈ J.faeden → SpecTriple Pre Post Nb J f)
    (hForm : InvariantForm Nb J I (SpecQ Pre Post Nb J)) :
    ∀ (σ : World D), J.welten.getLast? = some σ →
      ∀ (f : Faden), f ∈ J.faeden → SpecQ Pre Post Nb J f σ := by
  refine stabil_from_spec Nb J I Pre Post hInv hDeck hAb hSpec ?_
  exact interferenceFree_of_invariantForm Nb J I _ hForm hInv

#print axioms Gabbro.Grammatik.interferenceFree_of_invariantForm
#print axioms Gabbro.Grammatik.owickiGries_stabil_invariantForm
#print axioms Gabbro.Grammatik.stabil_from_spec_invariantForm

end Gabbro.Grammatik

/-! ## 21. CSL-exact discipline: the invariant from entry plus return (Posten 1)

    The auditor's finding against §20: `interferenceFree_of_invariantForm` derives
    interference freedom from `InvariantenKontext` (`∀ c σ, σ ∈ J.welten → I.inv c σ` --
    the invariant at EVERY world), but that context is discharged nowhere and is
    STRONGER than CSL: real code breaks the invariant mid-critical-section at
    instruction granularity, so the theorem fits no real code unless a chain step is
    a whole critical section -- and no file fixed what a `GemeinsamerLauf` step is.

    This section fixes the grain FIRST, then proves the context FROM DISCIPLINE.

    GRAIN (stated and used): one `GemeinsamerLauf` step is ONE WHOLE CRITICAL SECTION --
    one sequential body execution, indivisible at chain level. The step stays inside the
    writer's whole frame (`hSchritt`, discharged per body by `exec_rahmen`, `Satz.lean`:1323,
    named at `rahmen_aus_exec`, `Interferenz.lean`:148). It is NOT one machine event:
    `Koernung.lean` proves an n-byte `schreibBytes` leaves exactly n events
    (`schreibBytes_event_count`:158) and is NOT one event for 2 <= n
    (`schreibBytes_not_single`:173); a `leseBytes` records ONE event while folding over
    n cells (`leseBytes_not_atomic`:195); and the interrupted middle IS the witnessed
    tear (`two_byte_tear`:208, `mid_interruption_tears`:617). So at event grain the
    invariant DOES break mid-step, and a context claimed at every event-world would fit
    no real code -- exactly the auditor's charge. The chain therefore resolves bodies,
    not events (the same reason `Wettlauf.lean` §5, honest passage, builds no general
    interleaving semantics for `eval`): the invariant is claimed only at chain worlds,
    which are section boundaries, and each step re-establishes what it owes at return
    (`rufAt`, `Semantik.lean`:778-780: a normal return carries every owed invariant).
    `schritt_rahmen_aus_korn` is the grain as a theorem, CONSUMED below: the non-writer
    preservation (`nichtschreiber_erhaelt`) runs `stabil` over exactly that whole-frame
    step.

    DISCIPLINE (proved, not assumed): `hinv_aus_disziplin` derives the invariant from
    (E) entry -- it holds at the chain head (caller/sequential side, same shape as `hInit`);
    (R) return -- every WRITING step re-establishes it at its end world, conditioned on
    holding the guard (the `rufAt` return-check shape under `schuldet`, `Semantik.lean`:374);
    (W) THE single lock-holding premise, bounded -- writing steps hold the guard, as a
    STATIC declared-holds fact (`D.haelt` shape, exactly like `SchuldnerHaelt`, §3:162,
    which already travels per thread in `GemeinsamerLauf.hSchritt`'s sibling `hSchuld`,
    §3:200, proved per body by `schuldnerHaelt_gilt`, §7:283, from U003
    `invarianten_gehalten`, `Syntax.lean`:181, via `inv_schreiber_sperren`,
    `Interferenz.lean`:159); plus the standard frame-locality of the invariant
    (`HaengtAb` over its carrier singleton, with the carrier-frame link) and the static
    guard link (`Bewacht`). The conclusion is CSL-exact: `LockFrei L σ → I.inv c σ`
    (lock free implies invariant), NOT at every world. `hinv_kette_aus_disziplin` is the
    unconditional chain lemma underneath (forward induction over `k`, reusing §9
    `lt_of_belegt`/`kette_welt_belegt`); `hinv_aus_disziplin` is its CSL-exact weakening.

    What exists and is CITED, not rebuilt: `SchuldnerHaelt` (§3:162), `schuldet`
    (`Semantik.lean`:374), U003 (`Syntax.lean`:181), `schuldnerHaelt_gilt` (§7:283),
    `inv_schreiber_sperren` (`Interferenz.lean`:159), `heldIn_invarianten`
    (`Satz.lean`:1249), `eintrittHeldIn_aus_Passt` (§7:290, entry declared-holds goes
    dynamic at entry). `wache_aus_schuld` DISCHARGES the watch premise for TABLE carriers
    from `J.hSchuld` plus invariant coverage (every written table sits in some owed
    invariant's carrier list -- the CSL coverage side condition, per thread, no run
    reasoning); the guard fact `Sum.inl L ∈ D.braucht t` is consumed there.

    Scope, honestly narrowed: `wache_aus_schuld` discharges the watch of TABLE carriers (U003 now also covers
    the global carriers of an invariant, `D.traeger : Inv → List (Tab ⊕ Glob)`; the global discharge is not done here), so the
    derived watch (`wache_aus_schuld`) and the named `hinv_aus_disziplin` are TABLE-scoped.
    Shared globals stay on the §13-§15 exception track (`AtomarAusgenommen` via A10
    machine ordering, `PaarungAusgenommen` via publishes/awaits); the general per-carrier
    lemma (`hinv_kette_aus_disziplin`, `invariantenKontext_aus_disziplin`) keeps the watch
    as its single named premise, which for globals is checker-side. Per-site dynamic
    holding (that the checker proves held sets at every write site) stands nowhere --
    the G3 remainder (`messung/NEBENLAEUFIGKEIT-ENTWURF.md` §6 point 1); the static
    declared-holds side is what U003 delivers, and the interior of a step (take at
    entry, release at return) is the body's own critical-section discipline, booked as
    checker remainder beside `hReturn`.

    Re-derivation (§20 untouched): `invariantenKontext_aus_disziplin` folds the lemma to
    the full `InvariantenKontext` (per carrier, via `kette_belegt_of_mem`);
    `interferenceFree_of_invariantForm_aus_disziplin` feeds that derived context into
    `interferenceFree_of_invariantForm` (§20:1128) -- the §20 chain now runs on a derived
    premise. `interferenceFree_wo_frei` is the literal CSL interface: invariant-form
    assertions (uniform shared carrier, the standard CSL case) are interference-free
    WHERE THE LOCK IS FREE, both step worlds free.
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The guard lock of a carrier: the lock in the carrier's watch list (`D.braucht`
    for tables, `D.gbraucht` for globals -- the static side of the touch rule
    `TraegerInv.disziplin`). -/
def Bewacht (c : D.Tab ⊕ D.Glob) (L : D.Lock) : Prop :=
  match c with
  | .inl t => Sum.inl L ∈ D.braucht t
  | .inr x => Sum.inl L ∈ D.gbraucht x

/-- CSL lock-freedom at a world: the guard is not held (`World.haelt`,
    `Semantik.lean`: `offen` of the trace; `nimmt` takes, `gibt` releases). -/
def LockFrei (L : D.Lock) (σ : World D) : Prop :=
  L ∉ σ.haelt

/-- **The grain, as a theorem.** Every chain step is a whole-frame step of its writer:
    one sequential body execution (`hSchritt`, per body `exec_rahmen`), indivisible at
    chain level -- NOT one machine event (cf. `Koernung.lean`: an n-byte transfer is n
    events, `schreibBytes_not_single`). Consumed by `nichtschreiber_erhaelt`. -/
theorem schritt_rahmen_aus_korn (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (k : Nat) (g : Faden) (vor nach : World D)
    (hkg : J.schrittFaden[k]? = some g) (hkv : J.welten[k]? = some vor)
    (hkn : J.welten[k + 1]? = some nach) :
    Rahmen (D.schreibt (J.code g)) (D.gschreibt (J.code g)) vor nach :=
  (J.hSchritt k g vor nach hkg hkv hkn).2

end Gabbro.Grammatik
