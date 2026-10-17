import Grammatik.Llvm.Model.Facts
import Grammatik.Speichermodell.Maschine.Sicht

/-
  File:      Grammatik/Llvm/Model/Weak.lean
  Subject:   TRACK L, PHASE L0 -- THE LINK from the IR's atomics to the weak-memory interface
             that machine W / GX already use. No new memory model.

  * `Order.toOrdnung` -- the IR's six orders onto the model's two (`Speichermodell.Ordnung`):
    `unordered` and `monotonic` are `entspannt` (relaxed); `acquire`, `release`, `acq_rel` and
    `seq_cst` are `freigabe`. That is the over-approximation the model states for `seq`
    (Sicht.lean, `Ordnung`): `seq_cst` is read as release/acquire, which is weaker, so safe.
  * `Sees.weak` -- the instance of the interface `Sees` for the weak memory: an atomic load may
    return the value of ANY message of its location at or above the reader's view (`Lesbar`,
    the very predicate `LSchritt` and `RufSchrittW` use), the location being the pair (block,
    byte offset) the access names.
  * `sees_sc_weak` -- the SC reading is one of the weak readings: whenever the newest message
    of a location carries the memory's value and is at or above the view, `Sees.sc ⊆ Sees.weak`.
    (The direction the DRF theorem needs; the other is the weakness.)

  What stays for L3 (concurrency): the machine-level simulation, that is, that an IR run with
  `Sees.weak` and the per-access view updates simulates a `RufSchrittW` step. L0 fixes the shape.
-/

namespace Gabbro.Llvm

open Gabbro.Grammatik.Speichermodell

/-- The memory orders of the IR onto the weak-memory model's orders. -/
def Order.toOrdnung : Order → Ordnung
  | .unord => .entspannt
  | .mono => .entspannt
  | .acq => .freigabe
  | .rel => .freigabe
  | .acrel => .freigabe
  | .seqc => .freigabe

theorem toOrdnung_entspannt (o : Order) : o.toOrdnung = .entspannt ↔ (o = .unord ∨ o = .mono) := by
  cases o <;> simp [Order.toOrdnung]

theorem toOrdnung_freigabe (o : Order) :
    o.toOrdnung = .freigabe ↔ (o = .acq ∨ o = .rel ∨ o = .acrel ∨ o = .seqc) := by
  cases o <;> simp [Order.toOrdnung]

/-- A location of the weak memory: block and byte offset. -/
abbrev Loc := Nat × Int

/-- **The weak memory as an interface instance**: an atomic load returns the value of some
    message of its location that the reader's view `v` admits. -/
def Sees.weak (hist : Loc → List (Nachricht Loc Val)) (v : Sicht Loc) : Sees :=
  fun _ b o _ _ x => ∃ n, Lesbar hist v (b, o) n ∧ n.wert = x

/-- **The SC reading is a weak reading.** If the newest message of every location holds the value
    memory holds there and sits at or above the reader's view, every SC atomic load is allowed
    by the weak interface. -/
theorem sees_sc_weak (hist : Loc → List (Nachricht Loc Val)) (v : Sicht Loc)
    (hcoh : ∀ (m : Mem) b o t x, m.load b o t = some x →
      ∃ n ∈ hist (b, o), n.wert = x ∧ v (b, o) ≤ n.ts) :
    ∀ m b o t ord x, Sees.sc m b o t ord x → Sees.weak hist v m b o t ord x := by
  intro m b o t ord x h
  obtain ⟨n, hn, hw, hv⟩ := hcoh m b o t x h
  exact ⟨n, ⟨hn, hv⟩, hw⟩

/-- A step relation for a weaker interface is weaker: every step under `S` is a step under `S'`
    when `S ⊆ S'`. (So every SC run is a weak run: the IR over-approximates sequential
    consistency exactly as machine W over-approximates G, `w_aus_g`.) -/
theorem step_mono {M : Modl} {S S' : Sees}
    (h : ∀ m b o t ord x, S m b o t ord x → S' m b o t ord x) {c c' : Cfg}
    (hs : Step M S c c') : Step M S' c c' := by
  obtain ⟨O, hl, hst⟩ := hs
  refine ⟨O, ?_, hst⟩
  cases c with
  | fin m v => trivial
  | run m f ks =>
      unfold Oracle.legal at hl ⊢
      cases hn : Cfg.nextI M (.run m f ks) with
      | none => simp only [hn]
      | some i =>
          simp only [hn] at hl ⊢
          cases i with
          | aload d t p ord al =>
              intro b o x hp hx
              exact h _ _ _ _ _ _ (hl b o x hp hx)
          | _ => exact hl

theorem reach_mono {M : Modl} {S S' : Sees}
    (h : ∀ m b o t ord x, S m b o t ord x → S' m b o t ord x) {c c' : Cfg}
    (hs : Reach M S c c') : Reach M S' c c' := by
  induction hs with
  | refl => exact .refl _
  | step x y z hs _ ih => exact .step x y z (step_mono h hs) ih

end Gabbro.Llvm
