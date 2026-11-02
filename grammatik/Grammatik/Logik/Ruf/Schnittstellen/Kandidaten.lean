module

public import Grammatik.Logik.Ruf.Schnittstellen.Vertrag

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- All admitted pairs in a finite source-derived function/signature inventory.
    This table is an untrusted candidate: generation establishes membership,
    never O43. It includes every matching pair, without consulting executions. -/
def ptrKandidaten (D : Deklaration) (fs : List D.Fn) (ns : List Nat) : List (D.Fn × Nat) :=
  fs.flatMap fun f => (ns.filter (D.passt f)).map fun n => (f, n)

theorem ptrKandidaten_mem {fs : List D.Fn} {ns : List Nat} {f : D.Fn} {n : Nat} :
    (f, n) ∈ ptrKandidaten D fs ns ↔ f ∈ fs ∧ n ∈ ns ∧ D.passt f n = true := by
  simp only [ptrKandidaten, List.mem_flatMap, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨g, hg, k, ⟨hk, hp⟩, he⟩
    have he' : g = f ∧ k = n := by simpa only [Prod.mk.injEq] using he
    rcases he' with ⟨rfl, rfl⟩
    exact ⟨hg, hk, hp⟩
  · rintro ⟨hf, hn, hp⟩
    exact ⟨f, hf, n, ⟨hn, hp⟩, rfl⟩

/-- Completeness is explicit: every function and every signature number to
    which any target is admitted occurs. Out-of-range admitted pairs cannot
    escape the logical duty by being omitted from the candidate inventory. -/
theorem ptrKandidaten_voll (fs : List D.Fn) (ns : List Nat)
    (hfs : ∀ f : D.Fn, f ∈ fs)
    (hns : ∀ (f : D.Fn) (n : Nat), D.passt f n = true → n ∈ ns)
    {f : D.Fn} {n : Nat} (hf : D.passt f n = true) :
    (f, n) ∈ ptrKandidaten D fs ns :=
  ptrKandidaten_mem.mpr ⟨hfs f, hns f n hf, hf⟩

/-- The finite proof table owes exactly the universally quantified O43 duty.
    A successful structural filter is never substituted for `hproof`. This
    theorem works for abstract declarations as well as finite source units. -/
theorem ptrVerfeinert_iff_kandidaten (P : Programm D) (fs : List D.Fn) (ns : List Nat)
    (hfs : ∀ f : D.Fn, f ∈ fs)
    (hns : ∀ (f : D.Fn) (n : Nat), D.passt f n = true → n ∈ ns) :
    PtrVerfeinert P ↔
      ∀ (f : D.Fn) (n : Nat), (f, n) ∈ ptrKandidaten D fs ns →
        ∀ hf : D.passt f n = true, PtrZielVerfeinert P f n hf := by
  constructor
  · intro h f n _ hf
    exact h f n hf
  · intro h f n hf
    exact h f n (ptrKandidaten_voll fs ns hfs hns hf) hf

end Gabbro.Grammatik
