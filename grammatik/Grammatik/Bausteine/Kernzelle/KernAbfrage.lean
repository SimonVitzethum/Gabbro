module

public import Grammatik.Bausteine.Kernzelle.Belegung
public import Grammatik.Kern.Syntax.Marken.Teil1

@[expose] public section



namespace Gabbro.Grammatik.Kernzelle

open Gabbro.Grammatik

/-! ## 1. The foreign shape of the core query

    The running core is not an expression of the language: asking for it is a
    foreign call through the C08 path (`Block.bindAxiom` and its optional and
    top-level variants, with the caller's duty as `RufPasst` over the canonical
    `D.asignatur`). The query answers exactly a `Fin N`-equivalent bounded
    value: no parameters, one answer in `0 .. N - 1`, no reason channel, and
    no memory writes. A Rust thread number, a modulo reduction or a constant
    `0` is not evidence; only this shape, with the provenance below, is. -/

/-- **The core-query shape**: the foreign item answers the running core for
    an `N`-cell accumulator. The positive count keeps `N = 0` refused
    (no `Fin 0` core exists); the range is the `Fin N` bound. -/
def KernAbfrageGestalt (D : Deklaration) (q : D.Ax) (N : Nat) : Prop :=
  1 ≤ N ∧ D.aparams q = [] ∧ D.aerg q = some (Ty.int 0 ((N : Int) - 1)) ∧
    D.agruende q = 0 ∧ (∀ t, D.aschreibt q t = false) ∧
    (∀ g, D.agschreibt q g = false)

/-- The shape, decided over the member lists. -/
def kernAbfrageGestaltB (D : Deklaration) (q : D.Ax) (N : Nat)
    (tabs : List D.Tab) (globs : List D.Glob) : Bool :=
  decide (1 ≤ N) && decide (D.aparams q = []) &&
  decide (D.aerg q = some (Ty.int 0 ((N : Int) - 1))) &&
  decide (D.agruende q = 0) &&
  tabs.all (fun t => decide (D.aschreibt q t = false)) &&
  globs.all (fun g => decide (D.agschreibt q g = false))

/-- The Bool decides the shape. -/
theorem kernAbfrageGestaltB_iff {D : Deklaration} {q : D.Ax} {N : Nat}
    {tabs : List D.Tab} {globs : List D.Glob}
    (hT : ∀ t : D.Tab, t ∈ tabs) (hG : ∀ g : D.Glob, g ∈ globs) :
    kernAbfrageGestaltB D q N tabs globs = true ↔ KernAbfrageGestalt D q N := by
  unfold kernAbfrageGestaltB KernAbfrageGestalt
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hN, hP, hE, hR, hW, hGs⟩
    refine ⟨hN, hP, hE, hR, fun t => ?_, fun g => ?_⟩
    · have h1 := (List.all_eq_true.mp hW) t (hT t)
      simp only [decide_eq_true_eq] at h1
      exact h1
    · have h1 := (List.all_eq_true.mp hGs) g (hG g)
      simp only [decide_eq_true_eq] at h1
      exact h1
  · rintro ⟨hN, hP, hE, hR, hW, hGs⟩
    refine ⟨hN, hP, hE, hR, ?_, ?_⟩
    · exact List.all_eq_true.mpr fun t ht => by
        simp only [decide_eq_true_eq]
        exact hW t
    · exact List.all_eq_true.mpr fun g hg => by
        simp only [decide_eq_true_eq]
        exact hGs g

/-! ## 2. The provenance: hardware under a named assumption

    Scheduling and pinning are software user logic; no OS or thread-library
    behaviour enters here. The query is a hardware-origin foreign item
    (`AxOrigin.hardware`) witnessed by the declaration's named assumption
    (`D.axBeleg`): that, together with the named `AxVertragO` ensures on the
    answer, is the ONE hardware premise of the core query. A software-origin
    or unresolved item is refused, never inferred from a keyword. -/

/-- **The core-query provenance**: hardware origin with a named witness.
    The witness carries no content here; what the hardware promises is the
    named `AxVertragO` ensures, and the identity below. -/
def KernAbfrageHerkunft (D : Deklaration) (q : D.Ax) : Prop :=
  D.axHerkunft q = some .hardware ∧ ∃ w, D.axBeleg q = some w

/-- The provenance, decided. -/
def kernAbfrageHerkunftB (D : Deklaration) (q : D.Ax) : Bool :=
  decide (D.axHerkunft q = some .hardware) && (D.axBeleg q).isSome

/-- The Bool decides the provenance. -/
theorem kernAbfrageHerkunftB_iff {D : Deklaration} {q : D.Ax} :
    kernAbfrageHerkunftB D q = true ↔ KernAbfrageHerkunft D q := by
  unfold kernAbfrageHerkunftB KernAbfrageHerkunft
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    match hq : D.axBeleg q with
    | none => simp only [hq, Option.isSome_none] at h2
    | some w => exact ⟨w, hq⟩
  · rintro ⟨h1, w, hw⟩
    refine ⟨h1, ?_⟩
    rw [hw]

/-! ## 3. The identity

    The machine's oracle sees no thread (`O.wirkt a σ ρ`), so the identity of
    the answer with the executing core is a run-level fact, not a clause of
    `Q`: at the query step of thread `u` under the declared core assignment
    `kern` (the same assignment the userspace scheduler and binding use), the
    decoded answer is `kern u`. Migration after the query does not reselect
    the destination: the sampled value is bound once per source update. What
    a pinned scope guarantees when the owner requires the core at the store
    rather than at query time is user logic, proved with the scheduler. -/

/-- **The core identity**: the query answer is the running core under the
    declared assignment. -/
def KernAbfrageTreue (kern : Faden → Nat) (u : Faden) (v : Int) : Prop :=
  v = (kern u : Int)

/-- The identity with the scheduler's core bound gives the query range: the
    answer lies in `0 .. N - 1`, the `Fin N` bound of the shape. The scheduler
    duty (`kern u < N` for every running thread) is user logic. -/
theorem treueImBereich {kern : Faden → Nat} {u : Faden} {v : Int} {N : Nat}
    (h : KernAbfrageTreue kern u v) (hk : kern u < N) :
    0 ≤ v ∧ v ≤ (N : Int) - 1 := by
  unfold KernAbfrageTreue at h
  omega

/-- Two answers at the same thread agree: sampling twice without migration
    cannot select two different destinations. -/
theorem treueEindeutig {kern : Faden → Nat} {u : Faden} {v₁ v₂ : Int}
    (h1 : KernAbfrageTreue kern u v₁) (h2 : KernAbfrageTreue kern u v₂) :
    v₁ = v₂ :=
  h1.trans h2.symm

#print axioms Gabbro.Grammatik.Kernzelle.kernAbfrageGestaltB_iff
#print axioms Gabbro.Grammatik.Kernzelle.kernAbfrageHerkunftB_iff
#print axioms Gabbro.Grammatik.Kernzelle.treueImBereich
#print axioms Gabbro.Grammatik.Kernzelle.treueEindeutig

end Gabbro.Grammatik.Kernzelle
