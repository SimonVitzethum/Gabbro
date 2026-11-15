module

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

public import Grammatik.Zielsatz.Kern.Akzeptiert.CheckProof
public import Grammatik.Zielsatz.Kern.Spec
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiOrte
public import Grammatik.Logik.Vertraege.EinpassenVoll
public import Grammatik.Zielsatz.Kern.Akzeptiert.Teil1
public import Grammatik.Zielsatz.Kern.Akzeptiert.Teil3
public import Grammatik.Zielsatz.Kern.Akzeptiert.Bibliothek
public import Grammatik.Kern.Syntax.Satz.T4.Teil3
public import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung.T4

@[expose] public section

namespace Gabbro.Grammatik
open Zielsatz
variable {D : Deklaration}
section Akzeptiert
variable [DecidableEq D.Fn]
variable [DecidableEq D.Ax]
section Komponenten
variable {P : Programm D} {S : SperrInv D} {fs : List D.Fn} {ls : List D.Lock}
  {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn}

theorem poolSicherWB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    {w : D.Fn} : poolSicherWB P fs cs w = true ↔ PoolSicherW P fs w := by
  unfold poolSicherWB PoolSicherW PoolSicher
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq, and_assoc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun f hf c hc => ?_⟩
    have h4 := (List.all_eq_true.mp h3) f (hvoll f)
    rw [hf] at h4
    simp only [Bool.not_true, Bool.false_or] at h4
    have h5 := (List.all_eq_true.mp h4) c (hcs c)
    rw [hc] at h5
    simp only [Bool.not_true, Bool.false_or] at h5
    cases hl : waechterVon c with
    | nil =>
        have he : (([] : List D.Lock).isEmpty) = true := rfl
        rw [hl, he] at h5
        simp only [Bool.not_true, Bool.false_or] at h5
        cases c with
        | inl _ => simp only [atomarB, Bool.false_eq_true] at h5
        | inr g => exact Or.inr ⟨g, rfl, h5⟩
    | cons L _ => exact Or.inl ⟨L, waechterVon_mem.mp (hl.symm ▸ List.mem_cons_self)⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, List.all_eq_true.mpr fun f _ => ?_⟩
    cases hf : reachB P fs w f with
    | false => rfl
    | true =>
        refine List.all_eq_true.mpr fun c _ => ?_
        cases hc : TraegerSchreibt f c with
        | false => rfl
        | true =>
            rcases h3 f hf c hc with ⟨L, hL⟩ | ⟨g, rfl, hg⟩
            · have he : (waechterVon c).isEmpty = false := by
                have hmem : L ∈ waechterVon c := waechterVon_mem.mpr hL
                cases hl : waechterVon c with
                | nil => rw [hl] at hmem; cases hmem
                | cons _ _ => rfl
              rw [he]
              rfl
            · have hag : atomarB (.inr g) = true := hg
              simp only [Bool.not_true, hag, Bool.or_true]

/-- **The start component decides its field** (`AkzeptiertSpec.einzeln`, fix lane F10). -/
theorem einzelnPoolB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) :
    einzelnPoolB P fs cs ws = true ↔ EinzelnPool P fs ws := by
  unfold einzelnPoolB EinzelnPool
  rw [List.all_eq_true]
  constructor
  · intro h w hm
    have hw : w ∈ ws := hm.subset List.mem_cons_self
    have h1 := h w hw
    rw [Bool.or_eq_true, mehrfachB_iff.mpr hm] at h1
    rcases h1 with h1 | h1
    · cases h1
    · exact (poolSicherWB_iff hvoll hcs).mp h1
  · intro h w _
    rw [Bool.or_eq_true]
    cases hm : mehrfachB ws w
    · exact Or.inl rfl
    · exact Or.inr ((poolSicherWB_iff hvoll hcs).mpr (h w (mehrfachB_iff.mp hm)))

/-- **The handler component decides its field** (`AkzeptiertSpec.masken`, Opus agent H). -/
theorem maskenB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) : maskenB P fs = true ↔ MaskenDisziplin P fs := by
  unfold maskenB maskenDisziplinB MaskenDisziplin
  constructor
  · intro h w hw f hf
    have h1 := List.all_eq_true.mp h w (hvoll w)
    rw [hw] at h1
    simp only [Bool.not_true, Bool.false_or] at h1
    have h2 := List.all_eq_true.mp h1 f (hvoll f)
    rw [hf] at h2
    simpa using h2
  · intro h
    refine List.all_eq_true.mpr fun w _ => ?_
    cases hw : P.unterbricht w
    · rfl
    · refine List.all_eq_true.mpr fun f _ => ?_
      cases hf : reachB P fs w f
      · rfl
      · simpa using h w hw f hf

/-- **No handler, no condition**: on a program that declares no function entered by hardware the
    handler component is `true` -- the Bool is the conjunction of before. -/
theorem maskenB_ohne (h : ∀ f, P.unterbricht f = false) : maskenB P fs = true :=
  List.all_eq_true.mpr fun w _ => by rw [h w]; rfl

/-- **The member carriers, split into tables and statics.** Every table of a
    complete carrier list is in the table projection, and likewise for statics. -/
theorem tabsOf_voll {cs : List (D.Tab ⊕ D.Glob)} (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    (t : D.Tab) : t ∈ tabsOf cs :=
  List.mem_filterMap.mpr ⟨.inl t, hcs _, rfl⟩

theorem globsOf_voll {cs : List (D.Tab ⊕ D.Glob)} (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    (g : D.Glob) : g ∈ globsOf cs :=
  List.mem_filterMap.mpr ⟨.inr g, hcs _, rfl⟩

end Komponenten
end Akzeptiert
end Gabbro.Grammatik
