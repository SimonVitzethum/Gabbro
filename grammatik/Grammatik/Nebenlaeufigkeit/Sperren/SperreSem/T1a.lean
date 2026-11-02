/-
  File:      Grammatik/SperreSem.lean
  Subject:   LOCK INVARIANTS -- the sequential semantics a user proves a body
             against when shared state is protected by `locks L { … }` blocks
             (verdict item 2, `messung/URTEIL-OPUS-2026-09-13.md`).

  The shape is that of concurrent separation logic / Owicki-Gries resource
  invariants. A lock `L` protects a list of carriers `S.orte L` (each guarded
  by `L`) and carries an invariant `S.inv L` over them. In the SEQUENTIAL
  semantics of this file (`execStmtH`):
  * ACQUIRE: `locks L { body }` first lets the environment move (`U L`, an
    arbitrary `Umwelt` in the class `HavocOk S`): the protected carriers of
    `L` may take any values at which `S.inv L` holds, everything else and the
    trace stay. The body is then run from there.
  * RELEASE: when the body ends (normally, or by `leave`/`next`), `S.inv L`
    must hold; otherwise the run ends in `logik schleife` -- the invariant of
    the lock is checked at its boundary like a loop invariant.
  The user obligation stays a per-function SEQUENTIAL triple: it quantifies
  over the environment moves as it quantifies over call handlers and
  oracles (`KoerperGutS`, `SperreBeweis.lean`), and "no `logik` outcome"
  (the `KeineLogik` clause of `ziel_ort_ganz`) now also says "every release
  re-establishes the invariant".

  With the empty family (`SperrInv.leer`: no protected carriers, invariant
  `true`) every environment move is the identity and the semantics IS
  `execStmt` (`execStmtH_leer`), so today's theorem is the special case.

  This file: the family and its well-formedness (`SperrInvOk`), the class of
  environment moves (`HavocOk`), the semantics and its frame semantics
  (`weiterH`/`semH`) with the residue step lemmas, one per rule of G (copies
  of `ZielOrtVollSem.lean` §5 and `ZielOrtGeraetSem.lean` §6 for the new
  semantics, plus the acquire and release lemmas).
-/
module
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Lock invariants and environment moves -/

/-- **A family of lock invariants.** `orte L`: the carriers the lock `L`
    protects for its invariant (each guarded by `L`, `SperrInvOk`);
    `inv L`: the invariant, over memory. -/
structure SperrInv (D : Deklaration) where
  orte : D.Lock → List (D.Tab ⊕ D.Glob)
  inv : D.Lock → Speicher D → Bool

/-- Well-formedness of a family: every protected carrier is guarded by its
    lock, and the invariant reads only the protected carriers. The first
    half is decidable per declaration; the second holds by construction for
    an invariant written as an expression over those carriers. -/
def SperrInvOk (S : SperrInv D) : Prop :=
  (∀ L c, c ∈ S.orte L → Bewacht c L) ∧
  (∀ L (s s' : Speicher D), (∀ c ∈ S.orte L, TraegerGleich s s' c) → S.inv L s = S.inv L s')

/-- The empty family: no protected carriers, invariant `true`. -/
def SperrInv.leer (D : Deklaration) : SperrInv D := ⟨fun _ => [], fun _ _ => true⟩

theorem sperrInvOk_leer : SperrInvOk (SperrInv.leer D) :=
  ⟨fun _ _ h => absurd h List.not_mem_nil, fun _ _ _ _ => rfl⟩

/-- An environment move at an acquire: the world the body of `locks L`
    starts in, as a function of the world at the acquire. -/
abbrev Umwelt (D : Deklaration) := D.Lock → World D → World D

/-- **The class of environment moves.** At an acquire of `L` the other
    threads may have changed exactly the carriers `L` protects, leaving
    `S.inv L` true (they released `L` with it); the trace is the thread's
    own. -/
def HavocOk (S : SperrInv D) (U : Umwelt D) : Prop :=
  ∀ L σ, (U L σ).spur = σ.spur ∧
    (∀ c, c ∉ S.orte L → TraegerGleich (U L σ).speicher σ.speicher c) ∧
    S.inv L (U L σ).speicher = true

/-- Membership of a carrier in a carrier list, as a Boolean. -/
def istIn (l : List (D.Tab ⊕ D.Glob)) (c : D.Tab ⊕ D.Glob) : Bool :=
  l.any fun c' => decide (c' = c)

theorem istIn_iff {l : List (D.Tab ⊕ D.Glob)} {c : D.Tab ⊕ D.Glob} : istIn l c = true ↔ c ∈ l := by
  unfold istIn
  constructor
  · intro h
    obtain ⟨c', hc', he⟩ := List.any_eq_true.mp h
    rw [← of_decide_eq_true he]
    exact hc'
  · intro h
    exact List.any_eq_true.mpr ⟨c, h, decide_eq_true rfl⟩

/-- A world with the protected carriers of `L` taken from `s` and everything
    else (the trace included) from `σ`. -/
def mischU (S : SperrInv D) (L : D.Lock) (σ : World D) (s : Speicher D) : World D :=
  ⟨fun t => if istIn (S.orte L) (.inl t) = true then s.slots t else σ.slots t,
   fun g => if istIn (S.orte L) (.inr g) = true then s.globs g else σ.globs g, σ.spur⟩

theorem mischU_spur (S : SperrInv D) (L : D.Lock) (σ : World D) (s : Speicher D) :
    (mischU S L σ s).spur = σ.spur := by rfl

theorem mischU_aussen (S : SperrInv D) (L : D.Lock) (σ : World D) (s : Speicher D)
    (c : D.Tab ⊕ D.Glob) (hc : c ∉ S.orte L) :
    TraegerGleich (mischU S L σ s).speicher σ.speicher c := by
  cases c with
  | inl t => exact if_neg (fun h => hc (istIn_iff.mp h))
  | inr g => exact if_neg (fun h => hc (istIn_iff.mp h))

theorem mischU_innen (S : SperrInv D) (L : D.Lock) (σ : World D) (s : Speicher D)
    (c : D.Tab ⊕ D.Glob) (hc : c ∈ S.orte L) :
    TraegerGleich (mischU S L σ s).speicher s c := by
  cases c with
  | inl t => exact if_pos (istIn_iff.mpr hc)
  | inr g => exact if_pos (istIn_iff.mpr hc)

theorem mischU_inv {S : SperrInv D} (hS : SperrInvOk S) (L : D.Lock) (σ : World D)
    (s : Speicher D) : S.inv L (mischU S L σ s).speicher = S.inv L s :=
  hS.2 L _ _ fun c hc => mischU_innen S L σ s c hc

/-- The moves `mischU` with an invariant-satisfying source are in the class. -/
theorem havocOk_misch {S : SperrInv D} (hS : SperrInvOk S) (quelle : D.Lock → World D → Speicher D)
    (hq : ∀ L σ, S.inv L (quelle L σ) = true) :
    HavocOk S (fun L σ => mischU S L σ (quelle L σ)) :=
  fun L σ => ⟨rfl, mischU_aussen S L σ _, (mischU_inv hS L σ _).trans (hq L σ)⟩

/-- The same with only the locality half of `SperrInvOk` (the guard half is
    not used): a satisfiable, local family has a move in the class. -/
theorem havocOk_misch_lokal {S : SperrInv D}
    (hS : ∀ L (s s' : Speicher D), (∀ c ∈ S.orte L, TraegerGleich s s' c) →
      S.inv L s = S.inv L s')
    (quelle : D.Lock → World D → Speicher D) (hq : ∀ L σ, S.inv L (quelle L σ) = true) :
    HavocOk S (fun L σ => mischU S L σ (quelle L σ)) :=
  fun L σ => ⟨rfl, mischU_aussen S L σ _,
    (hS L _ _ fun c hc => mischU_innen S L σ _ c hc).trans (hq L σ)⟩

/-- Two worlds that agree on every carrier and on the trace are equal. -/
theorem world_ext {σ σ' : World D} (h : ∀ c, TraegerGleich σ.speicher σ'.speicher c)
    (hs : σ.spur = σ'.spur) : σ = σ' := by
  cases σ with
  | mk sl gl sp =>
    cases σ' with
    | mk sl' gl' sp' =>
      have e1 : sl = sl' := funext fun t => h (.inl t)
      have e2 : gl = gl' := funext fun g => h (.inr g)
      simp only at hs
      subst e1 e2 hs
      rfl

/-- Over the empty family every move in the class is the identity. -/
theorem havocOk_leer {U : Umwelt D} (h : HavocOk (SperrInv.leer D) U) : ∀ L σ, U L σ = σ :=
  fun L σ => world_ext (fun c => (h L σ).2.1 c (fun hc => absurd hc List.not_mem_nil)) (h L σ).1

/-! ## 2. The semantics with acquire moves and release checks -/

section Frei

variable {V : Vertrag D}

/-- **The release of `L`**: a normal end, a `leave` or a `next` of the body
    checks the invariant of `L` and releases the lock; a failed check is
    `logik schleife`. (A `return` or a reason cannot leave a `locks` body --
    `ret` is untypable there --; they only release.) -/
def freiH (S : SperrInv D) (L : D.Lock) {l : Bool} {Γ : Ctx} : Ausgang V l Γ → Ausgang V l Γ
  | .ok σ ρ => if S.inv L σ.speicher = true then .ok (σ.gibt L) ρ else .logik .schleife
  | .leave h σ ρ => if S.inv L σ.speicher = true then .leave h (σ.gibt L) ρ else .logik .schleife
  | .next h σ ρ => if S.inv L σ.speicher = true then .next h (σ.gibt L) ρ else .logik .schleife
  | .zurueck σ v => .zurueck (σ.gibt L) v
  | .why σ r => .why (σ.gibt L) r
  | .logik e => .logik e
  | .hardware e => .hardware e

/-- Under the invariant `true` the release is the plain release. -/
theorem freiH_leer (L : D.Lock) {l : Bool} {Γ : Ctx} (o : Ausgang V l Γ) :
    freiH (SperrInv.leer D) L o = o.mapWelt (·.gibt L) := by
  cases o <;> rfl

end Frei

end Gabbro.Grammatik
