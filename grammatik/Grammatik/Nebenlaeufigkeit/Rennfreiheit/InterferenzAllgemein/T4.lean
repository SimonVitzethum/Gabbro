/- Part 4 of 5 of `InterferenzAllgemein` (split by instrumente/teile/lean-teilen.py; the umbrella `InterferenzAllgemein.lean` imports all parts). -/
module
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein.T4Basis
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein.T3
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein.T3a
@[expose] public section

/-! ## 23. Eval reads only memory: the hMem engine (o02-hmem)

    The finding (SEV1, two checkers): `spec_aus_fuehrung_schritt` (`Maschine.lean`)
    carries `hMem : SpeicherVertrag Pre Post` on both legs of the spec step --
    lock steps go through memory constancy plus memory-only contracts -- but the
    discharge for `QRequires` / `QEnsures` was open: the per-expression induction
    showing `eval` reads only slots and globals lives downstream where the
    contract instantiation lives (§19 R1 books exactly this cut), while
    `LesenStabil.lean` holds only the `HaengtAb` frame side
    (`haengtAb_requires_bei_Lesen`, `haengtAb_ensures_bei_Lesen`,
    `requiresStabil_schritt`, `ensuresStabil_schritt`).

    What this section proves (no `sorry`, no `admit`, no `axiom`):

    * `eval_liest_nur_speicher` (plus `evalNutz_liest_nur_speicher`, mutual):
      `eval` agrees on worlds that agree on all slots and all globals -- the
      entry pair and the present pair separately, so `old(...)` (which reads
      the entry world) is covered. The induction is over `eval` itself, case
      for case; the three non-trivial leaves carry local helpers
      (`speicher_bytesAb_gleich`, `speicher_kette_gleich`,
      `speicher_list_all_congr` / `speicher_list_any_congr`), proved here
      because their downstream twins (`bytesAb_gleich`, `kette_gleich`,
      `list_all_congr`, `list_any_congr` in `Extraktion.lean`) are not
      importable upstream.
    * `eval_liest_nur_speicher_diag`: the diagonal both worlds read at once --
      the exact shape a `SpeicherVertrag` instance consumes.

    Import honesty (read, not worked around): this file is imported BY
    `Maschine.lean` (home of `SpeicherVertrag` / `World.speicher`) and BY
    `Extraktion.lean` (home of `QRequires` / `QEnsures` / `eval_liest_nur_orte`),
    and `LesenStabil.lean` imports `Extraktion.lean` -- so none of those names
    is citable here without a cycle. Reuse of the `LesenStabil` `HaengtAb`
    lemmas is therefore shape-level: those lemmas say contracts hang on their
    read frame; this section says `eval` hangs on memory; the conjunction --
    `SpeicherVertrag` over `QRequires` / `QEnsures` -- folds the two
    downstream, where all three names are visible.

    Coverage (exactly): every `Expr` constructor (including `durch`, which never
    evaluates its pointer, and `reaches` / `forallSlots` / `existsSlots` /
    `leseBytes`, which read whole columns), plus both `NutzlastExpr` shapes.
    Every premise is load-bearing: `hS` fires on `slot`, `durch`, `leseBytes`
    and `reaches`; `hG` on `glob`; `h0S` on `altSlot`; `h0G` on `altGlob`.

    Remainder (named, not hidden):

    * The `SpeicherVertrag` instance over `QRequires` / `QEnsures` itself --
      unfolding a `World.speicher` equality into the four slot/glob agreements
      above and folding the contract predicates over the diagonal -- belongs
      downstream (the `Maschine.lean` / `Extraktion.lean` direction), owned by
      whoever touches those files. This section is the engine; the binder is
      not here.
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- `bytesAb` reads only its column: equal columns give equal bytes. -/
theorem speicher_bytesAb_gleich {t : D.Tab} {f : D.Feld t} {hf : D.typ t f = .int 0 255}
    {σ σ' : World D}
    (h : ∀ k f', σ.slots t k f' = σ'.slots t k f')
    (n : Nat) (k : Int) :
    σ.bytesAb t f hf n k = σ'.bytesAb t f hf n k := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
      simp only [World.bytesAb]
      rw [h k f, ih]

/-- `kette` reads only its `weiter` column: equal columns, equal reachability. -/
theorem speicher_kette_gleich {n : Int} {weiter weiter' : Int → Option (Zahl 0 (n - 1))}
    (fuel : Nat) (k ziel : Int)
    (h : ∀ k, weiter k = weiter' k) :
    kette weiter fuel k ziel = kette weiter' fuel k ziel := by
  induction fuel generalizing k with
  | zero => rfl
  | succ fuel ih =>
      show (if k = ziel then true
          else match weiter k with
          | none => false
          | some m => kette weiter fuel m.n ziel) =
        (if k = ziel then true
          else match weiter' k with
          | none => false
          | some m => kette weiter' fuel m.n ziel)
      by_cases hk : k = ziel
      · simp only [hk, ↓reduceIte]
      · simp only [if_neg hk]
        rw [h k]
        cases hm : weiter' k with
        | none => rfl
        | some m => exact ih _

/-- Pointwise equal predicates count equal (`all`). -/
theorem speicher_list_all_congr {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      have hx : p x = q x := h x List.mem_cons_self
      have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
      simp only [List.all_cons, hx, ih']

/-- Pointwise equal predicates count equal (`any`). -/
theorem speicher_list_any_congr {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      have hx : p x = q x := h x List.mem_cons_self
      have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
      simp only [List.any_cons, hx, ih']


end Gabbro.Grammatik
