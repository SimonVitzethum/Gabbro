/-
  File:      Grammatik/Logik/Terminierung/Rekursion.lean
  Subject:   T4 -- MEASURED RECURSION TERMINATES (2026-10-22): on every infinite run of machine GX, every thread
             takes only finitely many steps, for a program whose calls go down a rank or along a cycle whose
             measure falls.

  A cost table cannot bound measured recursion: Ackermann's `(1, 0)` calls `(0, k)` for every `k`, so no number
  bounds the steps below `(1, 0)`. The bound is a WELL-FOUNDED RANK instead, read off a thread's stack:

  * every frame weighs `((rk f, measure of f at its entry), potRest of its residue)` (`gew`) -- the residue's
    potential with every call priced `0`, so it falls at every own step of the frame (`schrittArt`);
  * the stack, read from the bottom, is ordered lexicographically with a proper prefix below its extensions
    (`slt`); on stacks whose weights fall from bottom to top (`KetteW`) that order is well-founded
    (`acc_slt`);
  * an own step lowers the rank: a head step lowers the head's potential, a call lowers the caller's (the callee
    sits above it), a return drops the head and leaves the caller at most where it was; another thread's step
    leaves the rank alone;
  * the weights fall up the stack because every call goes to a lower rank or along a cycle (`tor`, checked on the
    bodies by `rufeE`), and along a cycle the replay of the goal proof carries the measure's fall to the frame
    (`WarteSA`, fed by `MassPflicht`).

  `endlich_aus_wf`: a sequence that falls in a well-founded order at marked indices and stays put elsewhere is
  marked only finitely often. `rekursion_endlich` is the theorem; `rekursion_endlich_aus` takes the premises of
  the goal's replay (`zielInvSA_erreichbarGX`) in place of the replay itself.

  The budget `passes` makes every `forever` finite in the model; T5 separates the programs whose termination does
  not lean on it.
-/
module
public import Grammatik.Zielsatz.Atomar.AtomarInvarianten
public import Grammatik.Logik.Fortschritt.KostenG
public import Grammatik.Logik.Terminierung.Mass
public import Grammatik.Logik.Terminierung.LaufGX
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Weights and their order -/

/-- A frame's weight: (rank, measure) of its function and entry, and the potential of its residue. -/
abbrev Gewicht : Type := (Nat × List Nat) × Nat

/-- **The order on weights**: by rank; at one rank by the measure (tuples of one length); at one measure by the
    potential. -/
def wlt (a b : Gewicht) : Prop :=
  a.1.1 < b.1.1 ∨ (a.1.1 = b.1.1 ∧ (lexLtN b.1.2.length a.1.2 b.1.2 ∨ (a.1.2 = b.1.2 ∧ a.2 < b.2)))

theorem acc_wlt : ∀ a : Gewicht, Acc wlt a := by
  suffices H : ∀ (r : Nat) (n : Nat) (w : List Nat), Acc (lexLtN n) w → w.length = n →
      ∀ p, Acc wlt ((r, w), p) by
    intro a
    exact H a.1.1 a.1.2.length a.1.2 ((lexLt_wf _).apply _) rfl a.2
  intro r
  induction r using Nat.strongRecOn with
  | _ r ihr =>
  intro n w hw
  induction hw with
  | intro w _ ihw =>
  intro hl p
  induction p using Nat.strongRecOn with
  | _ p ihp =>
  refine ⟨_, fun b hb => ?_⟩
  obtain ⟨⟨rb, wb⟩, pb⟩ := b
  rcases hb with h | ⟨h1, h | ⟨h2, h3⟩⟩
  · exact ihr rb h _ wb ((lexLt_wf _).apply _) rfl pb
  · dsimp only at h1 h
    subst h1
    rw [hl] at h
    exact ihw wb h h.1 pb
  · dsimp only at h1 h2 h3
    subst h1; subst h2
    exact ihp pb h3

/-! ## 2. Stacks and their order -/

/-- The weights of a stack, read from the bottom, fall from each one to the next. -/
def KetteW : List Gewicht → Prop
  | x :: y :: r => wlt y x ∧ KetteW (y :: r)
  | _ => True

/-- **The order on stacks** (read from the bottom): lexicographic, a proper prefix below its extensions. -/
def slt : List Gewicht → List Gewicht → Prop
  | [], _ :: _ => True
  | x :: xs, y :: ys => wlt x y ∨ (x = y ∧ slt xs ys)
  | _, [] => False

/-- The order restricted to falling stacks. -/
def sltK (a b : List Gewicht) : Prop := KetteW a ∧ slt a b

theorem ketteW_tail {x : Gewicht} : ∀ {t : List Gewicht}, KetteW (x :: t) → KetteW t
  | [], _ => trivial
  | _ :: _, h => h.2

/-- **The stack order is well-founded on falling stacks.** -/
theorem acc_sltK : ∀ b : List Gewicht, KetteW b → Acc sltK b := by
  have nil : Acc sltK [] := ⟨_, fun a ⟨_, h⟩ => by cases a <;> simp only [slt] at h⟩
  intro b hb
  cases b with
  | nil => exact nil
  | cons x t =>
  revert t
  induction (acc_wlt x) with
  | intro x _ ihx =>
  -- every falling tail below `x` is accessible
  have hacc : ∀ t, KetteW (x :: t) → Acc sltK t := by
    intro t ht
    cases t with
    | nil => exact nil
    | cons y t' => exact ihx y ht.1 t' ht.2
  intro t ht
  induction (hacc t ht) with
  | intro t _ iht =>
  refine ⟨_, fun a ⟨ha, hlt⟩ => ?_⟩
  cases a with
  | nil => exact nil
  | cons y as =>
    rcases hlt with h | ⟨rfl, h⟩
    · exact ihx y h as ha
    · exact iht as ⟨ketteW_tail ha, h⟩ ha

theorem ketteW_snoc : ∀ (xs : List Gewicht) (a b : Gewicht), KetteW (xs ++ [a]) → wlt b a →
    KetteW (xs ++ [a, b])
  | [], _, _, _, h => ⟨h, trivial⟩
  | [x], a, b, h, hb => ⟨h.1, hb, trivial⟩
  | x :: y :: r, a, b, h, hb => ⟨h.1, ketteW_snoc (y :: r) a b h.2 hb⟩

/-- A top-first stack whose weights fall upward. -/
def KetteT : List Gewicht → Prop
  | x :: y :: r => wlt x y ∧ KetteT (y :: r)
  | _ => True

theorem ketteT_reverse : ∀ l : List Gewicht, KetteT l → KetteW l.reverse
  | [], _ => trivial
  | [_], _ => trivial
  | x :: y :: r, h => by
      have ih := ketteT_reverse (y :: r) h.2
      simp only [List.reverse_cons] at ih ⊢
      rw [List.append_assoc]
      exact ketteW_snoc _ y x ih h.1

theorem slt_praefix : ∀ (p : List Gewicht) {a b : List Gewicht}, slt a b → slt (p ++ a) (p ++ b)
  | [], _, _, h => h
  | x :: p, _, _, h => Or.inr ⟨rfl, slt_praefix p h⟩

/-! ## 3. A sequence that falls at marked indices -/

theorem ex_min {p : Nat → Prop} : ∀ d, p d → ∃ d, p d ∧ ∀ e, e < d → ¬ p e := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
  intro hd
  by_cases h : ∃ e, e < d ∧ p e
  · obtain ⟨e, he, hpe⟩ := h
    exact ih e he hpe
  · exact ⟨d, hd, fun e he hpe => h ⟨e, he, hpe⟩⟩

/-- **Marked only finitely often**: a sequence that falls in a well-founded order at every marked index and stays
    put at every other is marked only finitely often. -/
theorem endlich_aus_wf {α : Type} (Rel : α → α → Prop) (x : Nat → α) (own : Nat → Prop)
    (hacc : ∀ j, Acc Rel (x j)) (hdown : ∀ j, own j → Rel (x (j + 1)) (x j))
    (hsame : ∀ j, ¬ own j → x (j + 1) = x j) : ∃ N, ∀ j, N ≤ j → ¬ own j := by
  suffices H : ∀ a, Acc Rel a → ∀ j, x j = a → ∃ N, ∀ j', N ≤ j' → ¬ own j' from
    H _ (hacc 0) 0 rfl
  intro a ha
  induction ha with
  | intro a _ ih =>
  intro j hj
  by_cases h : ∃ d, own (j + d)
  · obtain ⟨d0, hd0⟩ := h
    obtain ⟨d, hd, hmin⟩ := ex_min (p := fun d => own (j + d)) d0 hd0
    have hconst : ∀ e, e ≤ d → x (j + e) = a := by
      intro e
      induction e with
      | zero => intro _; exact hj
      | succ e ihe =>
        intro he
        rw [← Nat.add_assoc, hsame _ (hmin e (by omega))]
        exact ihe (by omega)
    have hr := hdown _ hd
    rw [hconst d (Nat.le_refl d)] at hr
    exact ih _ hr (j + d + 1) rfl
  · refine ⟨j, fun j' hj' hown => h ⟨j' - j, ?_⟩⟩
    rw [Nat.add_sub_cancel' hj']
    exact hown

/-! ## 4. The rank of a thread -/

section Rang

variable (P : Programm D) (pa : Nat) (m : Mass D) (zyk : D.Fn → D.Fn → Bool) (rk : D.Fn → Nat) (fs : List D.Fn)

/-- **The call gate**: from `f`, a call goes to a lower rank, or along `f`'s cycle at the same rank. -/
def tor (f g : D.Fn) : Bool := decide (rk g < rk f) || (rk g == rk f && zyk f g)

/-- **The gate of an indirect call** through signature `n`: every function of signature `n` passes `tor`. -/
def torS (f : D.Fn) (n : Nat) : Bool := fs.all fun g => !(D.passt g n) || tor zyk rk f g

theorem torS_tor (hvoll : ∀ g, g ∈ fs) {f : D.Fn} {n : Nat} {g : D.Fn} (h : torS zyk rk fs f n = true)
    (hp : D.passt g n = true) : tor zyk rk f g = true := by
  have := List.all_eq_true.mp h g (hvoll g)
  simpa [hp] using this

/-- A frame's weight. -/
def gew (r : RufRahmenG D) : Gewicht :=
  ((rk (RufSchluesselG r).1, m.wert (RufSchluesselG r).1 (RufSchluesselG r).2.2 (RufSchluesselG r).2.1),
    potRest (fun _ => 0) pa r.rest.2.2.2.2)

/-- **The rank of a thread**: the weights of its stack, read from the bottom. -/
def rangF (z : RufFadenG D) : List Gewicht := ((z.kopf :: z.stapel).map (gew pa m rk)).reverse

/-- The static facts of a stack, top first: every frame's residue calls through its gate, and every frame was
    called through the gate of the frame below it. -/
def Glieder : RufRahmenG D → List (RufRahmenG D) → Prop
  | r, [] => rufeR (tor zyk rk r.f) (torS zyk rk fs r.f) true r.rest.2.2.2.2 = true
  | r, b :: rest => rufeR (tor zyk rk r.f) (torS zyk rk fs r.f) true r.rest.2.2.2.2 = true ∧ tor zyk rk b.f r.f = true ∧ Glieder b rest

theorem glieder_kopf {r : RufRahmenG D} {st : List (RufRahmenG D)} (h : Glieder zyk rk fs r st) :
    rufeR (tor zyk rk r.f) (torS zyk rk fs r.f) true r.rest.2.2.2.2 = true := by
  cases st with
  | nil => exact h
  | cons _ _ => exact h.1

theorem glieder_ersetze {r r' : RufRahmenG D} {st : List (RufRahmenG D)} (h : Glieder zyk rk fs r st)
    (hf : r'.f = r.f) (hok : rufeR (tor zyk rk r.f) (torS zyk rk fs r.f) true r'.rest.2.2.2.2 = true) : Glieder zyk rk fs r' st := by
  have ht : tor zyk rk r'.f = tor zyk rk r.f := by rw [hf]
  have hts : torS zyk rk fs r'.f = torS zyk rk fs r.f := by rw [hf]
  cases st with
  | nil => show rufeR (tor zyk rk r'.f) (torS zyk rk fs r'.f) true r'.rest.2.2.2.2 = true; rw [ht, hts]; exact hok
  | cons b rest => exact ⟨by rw [ht, hts]; exact hok, hf ▸ h.2.1, h.2.2⟩

/-- Along the stack, every call into the caller's cycle has a smaller measure than the caller's entry (the
    replay's fact, `WarteSA`). -/
def MassFaellt : (Σ f : D.Fn, Env D (D.params f) × World D) → List (RufRahmenG D) → Prop
  | _, [] => True
  | G, F :: rest =>
      (∃ κ : World D, zyk F.f G.1 = true → lexLt (m.wert G.1 κ G.2.1) (m.wert F.f F.s0 F.rho) = true) ∧
      MassFaellt (RufSchluesselG F) rest

/-- **The weights fall up the stack**: the gate's links, with the measure's fall along a cycle. -/
theorem kette_aus (hL : ∀ f g, zyk f g = true → (m f).length = (m g).length) :
    ∀ (r : RufRahmenG D) (st : List (RufRahmenG D)), Glieder zyk rk fs r st →
      MassFaellt m zyk (RufSchluesselG r) st → KetteT ((r :: st).map (gew pa m rk))
  | r, [], _, _ => trivial
  | r, b :: rest, h, hm => by
      refine ⟨?_, kette_aus hL b rest h.2.2 hm.2⟩
      have ht := h.2.1
      unfold tor at ht
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at ht
      rcases ht with hlt | ⟨heq, hz⟩
      · exact Or.inl hlt
      · refine Or.inr ⟨heq, Or.inl ?_⟩
        obtain ⟨κ, hκ⟩ := hm.1
        have hlex : lexLt (m.wert r.f κ r.rho) (m.wert b.f b.s0 b.rho) = true := hκ hz
        rw [Mass.wert_welt m _ κ r.s0] at hlex
        refine ⟨?_, rfl, hlex⟩
        show (m.wert r.f r.s0 r.rho).length = (m.wert b.f b.s0 b.rho).length
        simp only [Mass.wert, List.length_map]
        exact (hL _ _ hz).symm

end Rang

end Gabbro.Grammatik
