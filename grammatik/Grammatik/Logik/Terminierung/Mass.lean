/-
  File:      Grammatik/Logik/Terminierung/Mass.lean
  Subject:   T2 -- THE RECURSION MEASURE IN THE MODEL (2026-10-22).

  The language's `decreases` becomes a measure in the model: per function a LEXICOGRAPHIC tuple of natural-number
  expressions over its parameters (`Mass`), so that measures like Ackermann's `(m, n)` are expressible. It is a
  parameter beside the program, like the order specification of the leg `folge`: the exporter fills it from the
  `decreases` clauses, and a function without one has the empty tuple.

  * `Mass.wert` -- the tuple's value at a world and the arguments; `lexLt` -- the strict lexicographic order;
    `lexLt_wf` -- it is well-founded on tuples of one length (`T4` uses it).
  * `massTor` -- the call handler that checks the measure at every call into the caller's own cycle: a call of `g`
    whose measure does not fall below the caller's entry value answers `logik (abstieg g)`, the outcome machine G's
    big-step semantics already uses for a recursion whose depth runs out. It is `torRuf`'s shape (the `requires`
    gate), so the replay that carries `requires` to every logged entry carries the measure the same way.
  * `MassPflicht` -- the user's duty: the body, run against every frame-respecting handler behind `massTor`, never
    ends in `abstieg`. The checker only checks THAT every recursion cycle that is not a tail-call cycle carries a
    measure (`Klasse.lean`); that the measure falls is the user's logic, as `ensures` is.
-/
import Grammatik.Logik.Terminierung.Klasse
import Grammatik.Speichermodell.Atomar.AtomarRec

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Measures and their order -/

/-- **A measure**: per function a lexicographic tuple of natural-number expressions over its parameters. -/
def Mass (D : Deklaration) : Type :=
  ∀ f : D.Fn, List (Σ hi : Int, {e : Expr D (D.params f) (Signatur.anfang D (D.signatur f)) (.int 0 hi) // e.orte = []})

/-- No function carries a measure. -/
def Mass.leer : Mass D := fun _ => []

/-- `f` carries a measure. -/
def Mass.hat (m : Mass D) (f : D.Fn) : Bool := !(m f).isEmpty

/-- The measure's value at the world `σ` and the arguments `ρ`. -/
def Mass.wert (m : Mass D) (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) : List Nat :=
  (m f).map fun e => ((eval σ e.2.1 σ ρ : Zahl 0 e.1)).n.toNat

/-- **A measure reads only the parameters**: its value is the same in every world. -/
theorem Mass.wert_welt (m : Mass D) (f : D.Fn) (σ σ' : World D) (ρ : Env D (D.params f)) :
    m.wert f σ ρ = m.wert f σ' ρ := by
  unfold Mass.wert
  congr 1
  funext e
  rw [eval_gleichAuf (S := []) e.2.1 (fun o ho => by rw [e.2.2] at ho; exact absurd ho List.not_mem_nil)
    ⟨fun t ht => absurd ht List.not_mem_nil, fun g hg => absurd hg List.not_mem_nil⟩ ρ]

/-- The strict lexicographic order. -/
def lexLt : List Nat → List Nat → Bool
  | a :: as, b :: bs => a < b || (a == b && lexLt as bs)
  | _, _ => false

theorem lexLt_laenge : ∀ {a b : List Nat}, lexLt a b = true → a ≠ [] ∧ b ≠ []
  | _ :: _, _ :: _, _ => ⟨List.cons_ne_nil _ _, List.cons_ne_nil _ _⟩
  | [], _, h => by simp only [lexLt, Bool.false_eq_true] at h
  | _ :: _, [], h => by simp only [lexLt, Bool.false_eq_true] at h

/-- The order restricted to tuples of length `n`. -/
def lexLtN (n : Nat) (a b : List Nat) : Prop := a.length = n ∧ b.length = n ∧ lexLt a b = true

/-- **The lexicographic order is well-founded on tuples of one length.** -/
theorem lexLt_wf : ∀ n, WellFounded (lexLtN n)
  | 0 => ⟨fun a => ⟨a, fun b ⟨_, hb, h⟩ => by
      have := (lexLt_laenge h).2; exact absurd (List.eq_nil_of_length_eq_zero hb) this⟩⟩
  | n + 1 => by
      have ih := lexLt_wf n
      -- a tuple `a :: as` is reached by induction on `a`, then on `as`
      refine ⟨fun x => ?_⟩
      suffices H : ∀ (a : Nat) (as : List Nat), as.length = n → Acc (lexLtN (n + 1)) (a :: as) by
        refine ⟨_, fun y ⟨hy, hx, _⟩ => ?_⟩
        cases y with
        | nil => simp only [List.length_nil, Nat.right_eq_add, Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false] at hy
        | cons b bs => exact H b bs (by simpa using hy)
      intro a
      induction a using Nat.strongRecOn with
      | _ a iha =>
      intro as has
      induction (ih.apply as) with
      | intro as _ ihas =>
      refine ⟨_, fun y ⟨hy, _, hlt⟩ => ?_⟩
      cases y with
      | nil => simp only [List.length_nil, Nat.right_eq_add, Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false] at hy
      | cons b bs =>
          simp only [lexLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hlt
          have hbs : bs.length = n := by simpa using hy
          rcases hlt with hlt | ⟨rfl, hlt⟩
          · exact iha b hlt bs hbs
          · exact ihas bs ⟨hbs, by simpa using has, hlt⟩ hbs

/-! ## 2. The measure gate and the user's duty -/

/-- `g` lies on a cycle with `f` (both reach each other), over the member list `fs`. -/
def zyklusMit [DecidableEq D.Fn] (P : Programm D) (fs : List D.Fn) (f g : D.Fn) : Bool :=
  reachB P fs f g && reachB P fs g f

/-- **The cycle relation of the measure gate**: `g` lies on a cycle with `f`, and `f` calls back into its cycle. A
    function on no cycle has none (`zyklusMit` alone is reflexive). -/
def zykS [DecidableEq D.Fn] (P : Programm D) (fs : List D.Fn) (f g : D.Fn) : Bool :=
  zyklusMit P fs f g && fs.any fun h => ruftB P f h && reachB P fs h f

section Pflicht

variable (P : Programm D)

/-- **The measure gate**: a call of `g` with `Z g` whose measure does not fall below `w` answers
    `logik (abstieg g)`; every other call is `R`'s. -/
def massTor (m : Mass D) (Z : D.Fn → Bool) (w : List Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) :
    ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f :=
  fun g σ ρ => if Z g && !(lexLt (m.wert g σ ρ) w) then .logik (.abstieg g) else R g σ ρ

/-- The handler never answers `abstieg` itself. -/
def OhneAbstieg (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ g σ ρ h, R g σ ρ ≠ .logik (.abstieg h)

/-- **The user's duty for the measure of `f`**: run against every frame-respecting handler that never answers
    `abstieg` or `vorbedingung` itself, behind the measure gate for `f`'s cycle `zyk f`, from every entry where `requires f` holds,
    the body never ends in `abstieg g` for a `g` of the cycle -- every call back into the cycle has a smaller
    measure than `f`'s entry. Vacuous where `zyk f` names nothing. -/
def MassPflicht (passes : Nat) (Q : AxEns D) (S : SperrInv D) (T : D.Tab ⊕ D.Glob → Prop) (m : Mass D)
    (zyk : D.Fn → D.Fn → Bool) (f : D.Fn) : Prop :=
  ∀ O' : Orakel D, RahmenO O' → RegLokal O' → AxVertragO Q O' →
    ∀ U : Umwelt D, HavocOk S U → ∀ A : AUmwelt D, HavocA T A →
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
      RespektiertRahmen P R → OhneAbstieg R → OhneVorbedingung R →
      ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ →
        ∀ g : D.Fn, zyk f g = true → execEndHA (V := vertragVon D f) S O' U A passes
          (massTor m (zyk f) (m.wert f σ ρ) R) (P.rumpf f) σ ρ ≠ EndAusgang.logik (Logik.abstieg g)

/-- Without a cycle to check, the duty is empty. -/
theorem massPflicht_aus (passes : Nat) (Q : AxEns D) (S : SperrInv D) (T : D.Tab ⊕ D.Glob → Prop) (m : Mass D)
    (f : D.Fn) : MassPflicht P passes Q S T m (fun _ _ => false) f :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g h => by cases h

/-- **A function on no cycle owes nothing**: its measure duty for `zykS` is empty. -/
theorem massPflicht_ohne_zyklus [DecidableEq D.Fn] (fs : List D.Fn) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (T : D.Tab ⊕ D.Glob → Prop) (m : Mass D) (f : D.Fn)
    (h : ∀ g, zykS P fs f g = false) : MassPflicht P passes Q S T m (zykS P fs) f :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g hg => absurd hg (by rw [h g]; decide)

end Pflicht

/-! ## 3. The record handler with a neutral default -/

/-- The handler of a record that answers `logik schleife` for every unrecorded call (never `abstieg`). -/
noncomputable def rufAusM (H : List (EintragV D)) :
    ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g :=
  fun g σ ρ =>
    haveI := Classical.propDecidable (∃ a : RufAusgang g, (⟨g, σ, ρ, a⟩ : EintragV D) ∈ H)
    if h : ∃ a : RufAusgang g, (⟨g, σ, ρ, a⟩ : EintragV D) ∈ H then Classical.choose h
    else .logik .schleife

theorem rufAusM_passt {H : List (EintragV D)} (hf : FunkV H) : PasstV (rufAusM H) H := by
  intro g σ ρ a hmem
  have hex : ∃ a : RufAusgang g, (⟨g, σ, ρ, a⟩ : EintragV D) ∈ H := ⟨a, hmem⟩
  simp only [rufAusM, dif_pos hex]
  exact hf g σ ρ _ a (Classical.choose_spec hex) hmem

theorem rufAusM_mem {H : List (EintragV D)} {g : D.Fn} {σ : World D} {ρ : Env D (D.params g)}
    {a : RufAusgang g} (h : rufAusM H g σ ρ = a) (hne : ∀ e, a ≠ .logik e) :
    (⟨g, σ, ρ, a⟩ : EintragV D) ∈ H := by
  unfold rufAusM at h
  split at h
  · rename_i hex
    rw [← h]
    exact Classical.choose_spec hex
  · exact absurd h.symm (hne _)

theorem rufAusM_rahmen {P : Programm D} {H : List (EintragV D)} (hv : VertraegeOkR P H) :
    RespektiertRahmen P (rufAusM H) :=
  ⟨fun g σ ρ _ σ' v h => (hv.1 g σ ρ _ (rufAusM_mem h (fun e he => by cases he))).2.1 σ' v rfl,
   fun g σ ρ σ' v h => hv.2 g σ ρ _ (rufAusM_mem h (fun e he => by cases he)) σ' v rfl⟩

theorem rufAusM_ohneAbstieg {P : Programm D} {H : List (EintragV D)} (hv : VertraegeOkR P H) :
    OhneAbstieg (rufAusM H) := by
  intro g σ ρ k h
  unfold rufAusM at h
  split at h
  · rename_i hex
    exact (hv.1 g σ ρ _ (Classical.choose_spec hex)).2.2 _ h
  · cases h

theorem rufAusM_ohneVorbedingung {P : Programm D} {H : List (EintragV D)} (hv : VertraegeOkR P H) :
    OhneVorbedingung (rufAusM H) := by
  intro g σ ρ k h g' hk
  unfold rufAusM at h
  split at h
  · rename_i hex
    exact (hv.1 g σ ρ _ (Classical.choose_spec hex)).2.2 _ h
  · cases h
    cases hk

section Tor

/-- The gate keeps a handler's agreement with a record whose cycle calls all fall. -/
theorem massTor_passtV {m : Mass D} {Z : D.Fn → Bool} {w : List Nat}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f} {H : List (EintragV D)}
    (hp : PasstV R H)
    (hm : ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)) (a : RufAusgang g),
      (⟨g, σ, ρ, a⟩ : EintragV D) ∈ H → Z g = true → lexLt (m.wert g σ ρ) w = true) :
    PasstV (massTor m Z w R) H := by
  intro g σ ρ a hmem
  unfold massTor
  by_cases hz : Z g = true
  · simp only [hz, hm g σ ρ a hmem hz, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    exact hp g σ ρ a hmem
  · simp only [Bool.not_eq_true] at hz
    simp only [hz, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    exact hp g σ ρ a hmem

end Tor

end Gabbro.Grammatik
