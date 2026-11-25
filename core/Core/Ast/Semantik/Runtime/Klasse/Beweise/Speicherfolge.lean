/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Beweise/Speicherfolge.lean
  Subject:   THE MEMORY LEG OF THE CLASS SAFETY DUTY (MK-03, PERFECT-MODEL §3.6). The pinned statement
             `KlassenSpeicherbeinAussage` is proved for the three classes that record a memory event
             (`lesen`, `schreiben`, `rmw`). The index lemma identifies the access inside a one-label
             `Speicherfolge`; the guard supplies `Zustand.befugt`, which books the access at that index.
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Pflichten
public import Core.Ast.Semantik.Runtime.Klasse.Sicherheit

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog
open Gabbro.Core.Speicher (Etikett Modus)
open Gabbro.Core.Sicherheit (Speicherzugriff)

open Classical in
/-- **The access of a one-label `Speicherfolge` sits at `zugriffsereignis`.** Unfolding
    `Speicherfolge.cons` once for the single label `l` appends one lazily materialised initial write
    (`Initialisierung`, split on `HatQuelle g l.ort`) immediately before the access `(f, l)`:
    `es = init ++ [(f, l)]`. The exact form of `init` follows from the definition: in the `ohne` case
    `init = []` and, since `l.art ≠ .aussen`, `HatQuelle g l.ort`; in the `erste` case
    `init = [(.initial l.ort, ⟨.schreiben, l.ort, l.modus, anfang l.ort, anfang l.ort⟩)]` and
    `¬ HatQuelle g l.ort`. Hence `init.length = if HatQuelle g l.ort then 0 else 1` and the access is
    at index `init.length` of `es`, i.e. at absolute event index `g.ev.length + init.length`; this equals
    `g.ev.length + (if HatQuelle g l.ort then 0 else 1)`, the value of `Zustand.zugriffsereignis` at
    the pre-state graph `g` for `z = l.ort`. -/
theorem speicherfolge_zugriffsindex {anfang : Zelle → Int} {f : SpeicherAkteur Zelle}
    {g g' : SpeicherGraph Zelle Int} {l : Etikett Zelle Int}
    {es : List (SpeicherAkteur Zelle × Etikett Zelle Int)}
    (h : Speicherfolge anfang f g [l] es g') (hneq : l.art ≠ .aussen) :
    ∃ init : List (SpeicherAkteur Zelle × Etikett Zelle Int),
      es = init ++ [(f, l)] ∧
        (init = [] ∧ HatQuelle g l.ort ∨
          init = [(.initial l.ort, ⟨.schreiben, l.ort, l.modus, anfang l.ort, anfang l.ort⟩)] ∧
            ¬ HatQuelle g l.ort) ∧
      init.length = (if HatQuelle g l.ort then 0 else 1) ∧
      es[init.length]? = some (f, l) := by
  cases h with
  | cons vor hs nach =>
    cases nach with
    | nil =>
      cases vor with
      | ohne hh =>
        have hq : HatQuelle g l.ort := by
          rcases hh with hout | hq
          · exact False.elim (hneq hout)
          · exact hq
        refine ⟨[], ?_, ?_, ?_, ?_⟩
        · simp only [List.nil_append]
        · exact Or.inl ⟨rfl, hq⟩
        · simp only [List.length_nil, hq, ite_true]
        · simp only [List.nil_append, List.length_nil, List.getElem?_cons_zero]
      | erste mem neu hsinit =>
        refine ⟨[(.initial l.ort, ⟨.schreiben, l.ort, l.modus, anfang l.ort, anfang l.ort⟩)], ?_, ?_, ?_, ?_⟩
        · simp only [List.singleton_append]
        · exact Or.inr ⟨rfl, neu⟩
        · simp only [List.length_singleton, neu, ite_false]
        · simp only [List.singleton_append, List.length_singleton, List.getElem?_cons_succ,
            List.getElem?_cons_zero]

end Gabbro.Core.Ast.Semantik
