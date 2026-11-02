module

public import Grammatik.Logik.Ruf.Schnittstellen.Vertrag
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtSem.Teil1

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {S : Signatur D.Tab D.Glob D.Lock D.Marke}

namespace CallContract

/-- Both contract footprints, including protected read-only carriers. Neither
    footprint is restricted to the signature's write effects. -/
def orte (C : CallContract D S) : List (D.Tab ⊕ D.Glob) :=
  C.pre.orte ++ C.post.orte

/-- Entry predicates depend only on their own footprint, with fixed arguments. -/
theorem pre_congr (C : CallContract D S) {s0 s0' : World D}
    (h : GleichAuf C.pre.orte s0 s0') (ρ : Env D S.params) :
    C.preHolds s0 ρ ↔ C.preHolds s0' ρ := by
  unfold preHolds
  rw [eval_gleichAuf C.pre (fun _ hc => hc) h ρ]

/-- Replay of the normal post keeps the entry and current agreements separate.
    In particular, agreement only in the current world cannot rewrite `old`. -/
theorem post_congr (C : CallContract D S) {s0 s0' s1 s1' : World D}
    (h0 : GleichAuf C.post.orte s0 s0') (h1 : GleichAuf C.post.orte s1 s1')
    (ρ : Env D S.params) (v : ErgVal D S.erg) :
    C.postHolds s0 s1 ρ v ↔ C.postHolds s0' s1' ρ v := by
  have he := Extraktion.eval_liest_orte C.post s0 s0' s1 s1'
    (ergEnv S.erg v ρ)
    (fun t ht k f => congrFun (congrFun (h1.1 t ht) k) f)
    (fun g hg => h1.2 g hg)
    (fun t ht k f => congrFun (congrFun (h0.1 t ht) k) f)
    (fun g hg => h0.2 g hg)
  unfold postHolds
  rw [he]

/-- A contract is free of carriers admitted as shared atomics. This component
    is syntax-derived; it proves no implication between arbitrary predicates. -/
def atomicFreeB (C : CallContract D S) (shared : D.Tab ⊕ D.Glob → Bool) : Bool :=
  C.orte.all fun c => !(shared c)

theorem atomicFreeB_ok (C : CallContract D S) (shared : D.Tab ⊕ D.Glob → Bool)
    (h : C.atomicFreeB shared = true) :
    ∀ c ∈ C.orte, shared c = false := by
  intro c hc
  have hf := List.all_eq_true.mp h c hc
  simpa only [Bool.not_eq_true'] using hf

/-- Each half of an accepted contract excludes shared atomic reads. -/
theorem atomicFreeB_halves (C : CallContract D S) (shared : D.Tab ⊕ D.Glob → Bool)
    (h : C.atomicFreeB shared = true) :
    (∀ c ∈ C.pre.orte, shared c = false) ∧
    (∀ c ∈ C.post.orte, shared c = false) :=
  ⟨fun c hc => C.atomicFreeB_ok shared h c (List.mem_append_left _ hc),
    fun c hc => C.atomicFreeB_ok shared h c (List.mem_append_right _ hc)⟩

end CallContract

end Gabbro.Grammatik
