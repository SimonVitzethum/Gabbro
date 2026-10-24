import Grammatik.Berechenbarkeit.Storage.GStack.Values

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.GStack

open ArenaKette

variable {D : Deklaration} {A : FreiForm D}

section Execution

variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

theorem linkPush_prefix (L : LinkFeld A) (G : LinkKopf A)
    (x : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt G.g = true) (hLG : gdarf D G.g Λ) (σ : World D) (ρ : Env D Γ) :
    ∃ σ', (∀ {Λ'} (rest : Block D V l Γ Λ Λ'),
      execBlock O passes R (Block.linkPush L G x hwT hLT hwG hLG rest) σ ρ =
        execBlock O passes R rest σ' ρ) ∧
      ∀ i, σ'.slots A.tab i A.feld = σ.slots A.tab i A.feld := by
  refine ⟨?world, ?execution, ?payload⟩
  case execution => intro Λ' rest; rfl
  case payload =>
    intro i
    simp [eval, World.slots_schreibSlot_ne _ _ _ _ _ _ _ _ (Ne.symm L.h1)]

/-- Link an actually allocated cell in front of an existing G stack. The
conclusion specifies its value sequence, not only shape and liveness. -/
theorem linkPush_values (L : LinkFeld A) (G : LinkKopf A)
    (x : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt G.g = true) (hLG : gdarf D G.g Λ) (σ : World D) (ρ : Env D Γ)
    (values : List (Wert D (D.typ A.tab A.feld))) (hr : Represents L G σ values)
    (hf : A.FreiOk σ) (hi : A.Lebt σ (ρ.get x).n)
    (hnot : ¬ Auf (D.count A.tab) (L.wert σ) (G.st σ) (ρ.get x).n) :
    ∃ σ', (∀ {Λ'} (rest : Block D V l Γ Λ Λ'),
      execBlock O passes R (Block.linkPush L G x hwT hLT hwG hLG rest) σ ρ =
        execBlock O passes R rest σ' ρ) ∧
      Represents L G σ' (σ.slots A.tab (ρ.get x).n A.feld :: values) ∧ A.FreiOk σ' ∧
      G.st σ' = (ρ.get x).n ∧ (∀ i, A.Lebt σ' i ↔ A.Lebt σ i) := by
  obtain ⟨σ', he, _, hhead, hlink, hother, hfree, hnext, hcount⟩ :=
    linkPush_ausfuehren O passes R (l := l) L G x hwT hLT hwG hLG (.nil) σ ρ
  obtain ⟨σp, hexec, hbytes⟩ := linkPush_prefix O passes R (l := l) L G x hwT hLT hwG hLG σ ρ
  have hworld : σp = σ' := by
    have hp := hexec (.nil)
    rw [he] at hp
    change (Ausgang.ok σ' ρ : Ausgang V l Γ) = .ok σp ρ at hp
    cases hp; rfl
  subst σp
  obtain ⟨indices, hc, hnd, hlive, hvalues⟩ := hr
  have hnotmem : (ρ.get x).n ∉ indices := fun hm => hnot ⟨indices, hc, hm⟩
  have hold : KetteF (D.count A.tab) (L.wert σ') (G.st σ) indices :=
    hc.uebertragen (fun i hm => hother i (fun h => hnotmem (h ▸ hm)))
  have hsame := A.lebt_gleich hfree hnext hcount
  have hslot : (ρ.get x).n < D.count A.tab := by
    have := hi.2.1
    have := A.stand_le σ
    omega
  refine ⟨σ', hexec, ?_, A.freiOk_gleich hfree hnext hcount hf, hhead, hsame⟩
  refine ⟨(ρ.get x).n :: indices, ?_, List.nodup_cons.mpr ⟨hnotmem, hnd⟩, ?_, ?_⟩
  · rw [hhead]
    exact KetteF.cons _ hi.1 hslot indices (hlink ▸ hold)
  · intro i hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact (hsame _).mpr hi
    · exact (hsame _).mpr (hlive _ hm)
  · simp only [List.map_cons, hbytes]
    rw [hvalues]

/-- Linking changes no allocation grant: only the data-structure links move. -/
theorem linkPush_grants {σ σ' : World D}
    {rights : ArenaOwnership.State} (ha : rights.agrees A σ)
    (hl : ∀ i, A.Lebt σ' i ↔ A.Lebt σ i) : rights.agrees A σ' :=
  ⟨ha.1, fun i => (hl i).trans (ha.2 i)⟩

end Execution

end Gabbro.Grammatik.Berechenbarkeit.Storage.GStack
