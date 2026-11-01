module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtStart
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtEinfaden
public import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-- **A head-local step**: a new head of the same function, held locks `o'`
    each named by the new head or old and carried, or ranking at least
    every floor of the stack. -/
theorem rangKette_kopf {o o' : List D.Lock} {F F' : RufRahmenG D} (hf : F'.f = F.f) :
    ∀ {S : List (RufRahmenG D)}, RangKette o (fun _ => False) F S →
    (∀ K ∈ o', Res.held K ∈ F'.rest.2.2.1 ∨
      (K ∈ o ∧ (Res.held K ∈ F.rest.2.2.1 → Res.held K ∈ F'.rest.2.2.1))) →
    (∀ K ∈ o', K ∈ o ∨ ∀ G ∈ F :: S, UeberB (bodenF G.f) K) →
    RangKette o' (fun _ => False) F' S
  | [], h, hK, _ => fun K hk => by
      rcases hK K hk with h1 | ⟨h1, h2⟩
      · exact Or.inl h1
      · rcases h K h1 with h3 | h3
        · exact Or.inl (h2 h3)
        · exact h3.elim
  | c :: rest, h, hK, hU => by
      obtain ⟨h1, h2, h3, h4⟩ := h
      have eb : bodenF F'.f = bodenF F.f := congrArg bodenF hf
      have eh : D.haelt F'.f = D.haelt F.f := congrArg D.haelt hf
      refine ⟨fun K hk => ?_, ?_, ?_, ?_⟩
      · rcases hK K hk with h5 | ⟨h5, h6⟩
        · exact Or.inl h5
        · rcases h1 K h5 with h7 | h7 | h7
          · exact Or.inl (h6 h7)
          · exact Or.inr (Or.inl (by rw [eb]; exact h7))
          · exact h7.elim
      · rw [eh]; exact h2
      · rw [eb]; exact h3
      · rw [eb]
        exact rangKette_tail h4 fun K hk => by
          rcases hU K hk with h5 | h5
          · exact Or.inl h5
          · exact Or.inr ⟨h5 F List.mem_cons_self, fun G hG => h5 G (List.mem_cons_of_mem _ hG)⟩


end Gabbro.Grammatik
