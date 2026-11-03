module

public import Grammatik.Kern.Semantik.Semantik.T2.Teil2

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
variable {V : Vertrag D}
variable (P : Programm D) (O : Orakel D)
variable (passes : Nat)

/-! ## 6. Der Ruf -- `requires`, der Rumpf, `ensures`, die Invarianten; und die Tiefe -/

/-- Die Bedeutung eines Rufs auf Tiefe `fuel`: die Vorbedingung, der Rumpf, die
    Nachbedingung, die geschuldeten Invarianten. Ist die Tiefe erschoepft, ist das Mass
    nicht gefallen -- `abstieg`, eine Logikstelle. -/
def rufAt : Nat → ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f
  | 0, f, _, _ => .logik (.abstieg f)
  | n + 1, f, σ, ρ =>
      let σ := σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte
      if wahr? (eval σ (P.requires f) σ ρ) = false then .logik (.vorbedingung f) else
      match execEnd (V := vertragVon D f) O passes (rufAt n) (P.rumpf f) σ ρ with
      | EndAusgang.zurueck σ' v =>
          let σ' := σ'.lese (vertragVon D f).ende (P.ensures f).orte
          if wahr? (eval σ (P.ensures f) σ' (ergEnv (D.erg f) v ρ)) = false then .logik (.nachbedingung f)
          else
            let σ' := (D.invs.filter (schuldet f)).foldl (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte) σ'
            match D.invs.find? (fun i => schuldet f i && !wahr? (eval σ' (P.invariante i) σ' .nil)) with
            | Option.some i => .logik (.invariante i)
            | Option.none => .ok σ' v
      | .why σ' r => .why σ' r
      | .leave h _ _ => absurd h (by decide)
      | .next h _ _ => absurd h (by decide)
      | .logik e => .logik e
      | .hardware e => .hardware e

/-- **Die Bedeutung eines Rumpfs** in einem Programm, auf Rekursionstiefe `fuel`. -/
def exec (fuel : Nat) (V : Vertrag D) (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) :
    Ausgang V l Γ :=
  execBlock O passes (rufAt P O passes fuel) b σ ρ

/-! ## 7. User partition and async device step -- shapes beside the run, no discharge -/

/-! ### 7.1 The two sides of one boundary, over the flat key space -/

/-- The two sides of one boundary: kernel memory and user memory. The world stays
    one flat mapping (`slots`/`globs`/`spur` above); the partition is a side per key,
    not a second world -- so every existing theorem reads the same `World`. -/
inductive Seite where
  | kern
  | user
  deriving DecidableEq, Repr

/-- A side assignment over the flat key space: each table slot has one side. -/
def SeitenWahl (D : Deklaration) : Type :=
  D.Tab → Int → Seite

/-- The user side, as a boolean test. -/
def istUserSeite : Seite → Bool
  | .user => true
  | .kern => false

/-- The kernel side, as a boolean test. -/
def istKernSeite : Seite → Bool
  | .kern => true
  | .user => false

/-- A world key on the user side: the assignment says `user`. -/
def benutzerSchluessel (w : SeitenWahl D) (t : D.Tab) (k : Int) : Prop :=
  w t k = .user

/-- A world key on the kernel side: the assignment says `kern`. -/
def kernSchluessel (w : SeitenWahl D) (t : D.Tab) (k : Int) : Prop :=
  w t k = .kern

/-- The partition covers and separates: every key is on exactly one side. -/
theorem seite_zerlegt (w : SeitenWahl D) (t : D.Tab) (k : Int) :
    (benutzerSchluessel w t k ∨ kernSchluessel w t k) ∧
    ¬ (benutzerSchluessel w t k ∧ kernSchluessel w t k) := by
  constructor
  · cases h : w t k <;> simp_all [benutzerSchluessel, kernSchluessel]
  · cases h : w t k <;> simp_all [benutzerSchluessel, kernSchluessel]

/-- The flat mapping is preserved across the partition: a store to one carrier
    leaves every slot of another carrier untouched -- the frame the partition
    checks against, still stated on `World.slots`. -/
theorem seite_rahmen_fremd (σ : World D) {t t' : D.Tab} (h : t' ≠ t)
    (k k' : Int) (f : D.Feld t) (v : Wert D (D.typ t f)) (f' : D.Feld t') :
    (σ.storeSlot t k f v).slots t' k' f' = σ.slots t' k' f' := by
  simp only [World.storeSlot, h, ↓reduceDIte]

/-! ### 7.2 The async device write beside `Orakel.wirkt` -/

/-- An async device write to carrier `t`, world to world -- beside `Orakel.wirkt`,
    which acts AT a call site (`D.Ax` plus its `Env`). This shape takes neither:
    no axiom, no call site, no argument environment. What it may change is the
    DMA-visible buffer carrier `t` alone: every other carrier, every global, and
    the trace stay -- the frame half. What the write OBSERVES (content) is not
    stated here: events carry no values, so no run fact implies it. -/
structure GeraetSchreibt (t : D.Tab) (σ σ' : World D) : Prop where
  sichtbar : D.geteilt t = true
  rahmen : ∀ t' : D.Tab, t' ≠ t → ∀ k' : Int, ∀ f' : D.Feld t', σ'.slots t' k' f' = σ.slots t' k' f'
  globale : ∀ g : D.Glob, σ'.globs g = σ.globs g
  spur : σ'.spur = σ.spur

/-- The window around an async device write: handoff before, take-back after --
    the `vor`/`nach` premise shape of `GeraetWache` (Geraet.lean), stated over
    worlds instead of run indices. At the handoff the guard is released (not held
    in `σ`); at the take-back it is held again (held in `σ'`). The CPU-side
    ordering against these endpoints stays driver duty, as `haussen` there. -/
structure GeraetFensterWelt (W : D.Lock) (t : D.Tab) (σ σ' : World D) : Prop where
  schritt : GeraetSchreibt t σ σ'
  vor : W ∉ σ.haelt
  nach : W ∈ σ'.haelt

/-- A windowed device write leaves every foreign carrier untouched. -/
theorem asyncFenster_rahmen {W : D.Lock} {t : D.Tab} {σ σ' : World D}
    (w : GeraetFensterWelt W t σ σ') {t' : D.Tab} (h : t' ≠ t)
    (k' : Int) (f' : D.Feld t') :
    σ'.slots t' k' f' = σ.slots t' k' f' :=
  w.schritt.rahmen t' h k' f'

/-- A windowed device write leaves the trace untouched -- locks held stay held. -/
theorem asyncFenster_spur {W : D.Lock} {t : D.Tab} {σ σ' : World D}
    (w : GeraetFensterWelt W t σ σ') :
    σ'.spur = σ.spur :=
  w.schritt.spur

/-! ### Cuts (booked, not hidden)

    (S1) The partition is a shape over the flat key space; no `Stmt`/`Block`
         transition discharges it -- a range check inside `exec` stays future work.
    (S2) The async step is a shape beside `Orakel.wirkt`; there is no interleaving
         with `exec` runs here and no content invariant -- order without content
         leaves the content half open, content without order the race half open.
-/


end Gabbro.Grammatik
