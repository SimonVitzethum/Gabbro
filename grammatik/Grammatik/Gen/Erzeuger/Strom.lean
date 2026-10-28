/-
  File:      Grammatik/Gen/Erzeuger/Strom.lean
  Subject:   ONE PROGRAM AFTER THE OTHER: the sized streams `Sz` of `Gestuft.lean` as folds that hand each item to the
             consumer as it is built, so no list of all programs of a size is ever held. `Strom.faltet S A` says the
             fold `S` walks exactly the list `A k`, in its order; it is proved for every combinator, so the
             completeness theorems over `Sz` (`hautT_vollst`, ...) hold for the streams unchanged.
-/
import Grammatik.Gen.Erzeuger.Programm

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik

/-- A sized stream as a fold: result type `β`, size `k`, start value `b`, step `s`. -/
def Strom (α : Type) : Type 1 := (β : Type) → Nat → β → (β → α → β) → β

namespace Strom

variable {α γ : Type}

/-- `S` walks exactly the items of `A`, in the order of `A`. -/
def faltet (S : Strom α) (A : Sz α) : Prop := ∀ (β : Type) (k : Nat) (b : β) (s : β → α → β), S β k b s = (A k).foldl s b

/-- A list of a fixed size, walked from the front: the stream of tables and choices. -/
def ausSz (A : Sz α) : Strom α := fun _ k b s => (A k).foldl s b

theorem faltet_ausSz (A : Sz α) : faltet (ausSz A) A := fun _ _ _ _ => rfl

/-- **Sum of sizes**, as `Sz.bind`: the size `i` of the first item, then the rest on `k - i`. -/
def bind (S : Strom α) (F : α → Strom γ) : Strom γ := fun β k b s =>
  (List.range (k + 1)).foldl (fun b i => S β i b fun b a => F a β (k - i) b s) b

/-- The image under `f`. -/
def map (f : α → γ) (S : Strom α) : Strom γ := fun β k b s => S β k b fun b a => s b (f a)

theorem foldl_flatMap {δ β : Type} (xs : List δ) (g : δ → List α) (s : β → α → β) (b : β) :
    (xs.flatMap g).foldl s b = xs.foldl (fun b x => (g x).foldl s b) b := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, List.foldl_append, ih, List.foldl_cons]

theorem faltet_bind {S : Strom α} {A : Sz α} {F : α → Strom γ} {B : α → Sz γ} (hS : faltet S A)
    (hF : ∀ a, faltet (F a) (B a)) : faltet (bind S F) (Sz.bind A B) := by
  intro β k b s
  simp only [bind, Sz.bind, foldl_flatMap]
  congr 1
  funext b i
  have : (fun b a => F a β (k - i) b s) = (fun b a => (B a (k - i)).foldl s b) := by
    funext b a; exact hF a β _ _ _
  rw [this]
  exact hS β i b _

theorem faltet_map {S : Strom α} {A : Sz α} (f : α → γ) (hS : faltet S A) : faltet (map f S) (Sz.map f A) := by
  intro β k b s
  simp only [map, Sz.map, List.foldl_map]
  exact hS β _ _ _

end Strom

variable {D : Deklaration} [Aufz D] [Zahlen]

/-- `piS` as a stream: one family of values at a time. -/
def piF {ι : Type} [DecidableEq ι] {X : ι → Type} (L : ∀ i, Sz (X i)) :
    (alle : List ι) → Strom (∀ i, i ∈ alle → X i)
  | [] => Strom.ausSz (Sz.pure (fun _ h => absurd h List.not_mem_nil))
  | a :: as => Strom.bind (Strom.ausSz (L a)) fun x => Strom.map (fun f => fun i h =>
      if h' : i = a then h' ▸ x else f i ((List.mem_cons.1 h).resolve_left h')) (piF L as)

theorem faltet_piF {ι : Type} [DecidableEq ι] {X : ι → Type} (L : ∀ i, Sz (X i)) :
    ∀ alle : List ι, Strom.faltet (piF L alle) (piS L alle)
  | [] => Strom.faltet_ausSz _
  | _ :: as => Strom.faltet_bind (Strom.faltet_ausSz _) fun _ => Strom.faltet_map _ (faltet_piF L as)

/-- **The skeletons of exact size `k`, one at a time**: the stream of `hautT`. -/
def hautF (tbls : List (Σ f : D.Fn, List (List (Rumpf D f)))) : Strom (Haut D) :=
  Strom.bind (piF (rumpfS tbls) Aufz.fn) fun rs =>
    Strom.bind (piF (fun _ => Sz.wahl [false, true]) Aufz.fn) fun us =>
      Strom.ausSz (Sz.pure ⟨fun f => rs f (Aufz.fn_mem f), fun f => us f (Aufz.fn_mem f)⟩)

/-- The stream walks exactly the skeletons of `hautT`, so `hautT_vollst` is a statement about it. -/
theorem faltet_hautF (tbls : List (Σ f : D.Fn, List (List (Rumpf D f)))) : Strom.faltet (hautF tbls) (hautT tbls) :=
  Strom.faltet_bind (faltet_piF _ _) fun _ =>
    Strom.faltet_bind (faltet_piF _ _) fun _ => Strom.faltet_ausSz _

end Gabbro.Grammatik.Gen
