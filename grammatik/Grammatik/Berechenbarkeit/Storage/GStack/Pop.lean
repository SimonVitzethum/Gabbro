import Grammatik.Berechenbarkeit.Storage.GStack.Link

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.GStack

open ArenaKette

variable {D : Deklaration} {A : FreiForm D}

section Execution

variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- The same executed pop prefix serves every continuation. Keeping the bound
index available is necessary for reading its payload and freeing its cell. -/
theorem linkPop_prefix (L : LinkFeld A) (G : LinkKopf A)
    (hwG : V.gschreibt G.g = true) (hLG : gdarf D G.g Λ) (hLT : darf D A.tab Λ)
    (failure : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) (hne : G.st σ < D.count A.tab) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      (∀ {Λ'} (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ'),
        execBlock O passes R (Block.linkPop L G hwG hLG hLT failure rest) σ ρ =
          (execBlock O passes R rest σ' (.cons k ρ)).schrumpf) ∧
      k.n = G.st σ ∧ σ'.slots = σ.slots := by
  have hk : 0 ≤ G.st σ ∧ G.st σ ≤ D.count A.tab - 1 :=
    ⟨(Wert.umTyp G.hg (σ.globs G.g)).lo_le, by omega⟩
  refine ⟨?s, ⟨G.st σ, hk.1, hk.2⟩, ?execution, rfl, ?slots⟩
  case execution =>
    intro Λ' rest
    simp only [Block.linkPop, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte, World.globs_lese]
    rw [dite_eq_left (by exact hk)]
    rfl
  case slots => rfl

theorem linkPop_values (L : LinkFeld A) (G : LinkKopf A)
    (hwG : V.gschreibt G.g = true) (hLG : gdarf D G.g Λ) (hLT : darf D A.tab Λ)
    (failure : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (value : Wert D (D.typ A.tab A.feld)) (values : List (Wert D (D.typ A.tab A.feld)))
    (hr : Represents L G σ (value :: values)) (hf : A.FreiOk σ) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      (∀ {Λ'} (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ'),
        execBlock O passes R (Block.linkPop L G hwG hLG hLT failure rest) σ ρ =
          (execBlock O passes R rest σ' (.cons k ρ)).schrumpf) ∧
      k.n = G.st σ ∧ σ'.slots A.tab k.n A.feld = value ∧ Represents L G σ' values ∧
      A.FreiOk σ' ∧ A.Lebt σ' k.n ∧ ¬ Auf (D.count A.tab) (L.wert σ') (G.st σ') k.n ∧
      (∀ i, A.Lebt σ' i ↔ A.Lebt σ i) := by
  have hne := hr.nonempty
  obtain ⟨σ', k, hexec, hkn, hslots⟩ := linkPop_prefix O passes R L G hwG hLG hLT failure σ ρ hne
  obtain ⟨σm, km, hm, _, _, hhead, hlinks, hfree, hnext, hcount⟩ :=
    linkPop_ausfuehren O passes R L G hwG hLG hLT failure (.nil) σ ρ hne
  have hworld : σm = σ' := by
    have he := hexec (.nil)
    rw [hm] at he
    change (Ausgang.ok σm ρ : Ausgang V l Γ) = .ok σ' ρ at he
    cases he; rfl
  subst σm
  have hsame := A.lebt_gleich hfree hnext hcount
  obtain ⟨indices, hc, hnd, hlive, hvalues⟩ := hr
  generalize hroot : G.st σ = root at hc
  cases hc with
  | nil => simp at hvalues
  | cons i h0 hi tail ht =>
    have hv := List.cons.inj (by simpa only [List.map_cons] using hvalues)
    have htail : KetteF (D.count A.tab) (L.wert σ') (G.st σ') tail := by
      rw [hhead, hroot]
      exact ht.uebertragen (fun j _ => hlinks j)
    have hn := List.nodup_cons.mp hnd
    have hrep : Represents L G σ' values := by
      refine ⟨tail, htail, hn.2, ?_, ?_⟩
      · intro j hj
        exact (hsame j).mpr (hlive j (List.mem_cons_of_mem _ hj))
      · simpa only [hslots] using hv.2
    have hnmem : ¬ Auf (D.count A.tab) (L.wert σ') (G.st σ') k.n := by
      rintro ⟨js, hjs, hmem⟩
      have he := KetteF.eindeutig hjs htail
      subst js
      rw [hkn, hroot] at hmem
      exact hn.1 hmem
    refine ⟨σ', k, hexec, by simpa only [hroot] using hkn, ?_, hrep, A.freiOk_gleich hfree hnext hcount hf,
      ?_, hnmem, hsame⟩
    · rw [hslots, hkn, hroot]
      exact hv.1
    · apply (hsame _).mpr
      rw [hkn, hroot]
      exact hlive _ (List.mem_cons_self ..)

end Execution

end Gabbro.Grammatik.Berechenbarkeit.Storage.GStack
