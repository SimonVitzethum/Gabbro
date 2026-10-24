import Grammatik.Berechenbarkeit.Storage.GStack.Pop

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.GStack

open ArenaKette

variable {D : Deklaration} {A : FreiForm D}

namespace Block

/-- The head payload is bound before releasing its storage. The continuation
receives both the saved value and the now-dead index; ownership checking must
reject use of that index as an allocation reference after this point. -/
def popAndRelease {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (L : LinkFeld A) (G : LinkKopf A)
    (hwH : V.gschreibt G.g = true) (hLH : gdarf D G.g Λ)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwF : V.gschreibt A.kopf = true) (hLF : gdarf D A.kopf Λ)
    (empty : Endblock D V l Γ Λ)
    (rest : Gabbro.Grammatik.Block D V l (D.typ A.tab A.feld :: Ty.index (D.count A.tab) :: Γ) Λ Λ') :
    Gabbro.Grammatik.Block D V l Γ Λ Λ' :=
  .linkPop L G hwH hLH hLT empty
    (.bind (.slot A.tab A.feld (.var .here) hLT)
      (.freiVar A (.there .here) hwT hLT hwF hLF rest))

end Block

section Execution

variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

theorem free_prefix (A : FreiForm D) (x : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwF : V.gschreibt A.kopf = true) (hLF : gdarf D A.kopf Λ) (σ : World D) (ρ : Env D Γ) :
    ∃ σ', (∀ {Λ'} (rest : Gabbro.Grammatik.Block D V l Γ Λ Λ'),
      execBlock O passes R (Gabbro.Grammatik.Block.freiVar A x hwT hLT hwF hLF rest) σ ρ =
        execBlock O passes R rest σ' ρ) ∧
      ∀ i, σ'.slots A.tab i A.feld = σ.slots A.tab i A.feld := by
  refine ⟨?world, ?execution, ?payload⟩
  case execution => intro Λ' rest; rfl
  case payload =>
    intro i
    simp [eval, World.slots_schreibSlot_ne _ _ _ _ _ _ _ _ (Ne.symm A.hf)]

theorem free_values (A : FreiForm D) (L : LinkFeld A) (G : LinkKopf A)
    (x : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwF : V.gschreibt A.kopf = true) (hLF : gdarf D A.kopf Λ) (σ : World D) (ρ : Env D Γ)
    (values : List (Wert D (D.typ A.tab A.feld))) (hr : Represents L G σ values)
    (hf : A.FreiOk σ) (hi : A.Lebt σ (ρ.get x).n)
    (hnot : ¬ Auf (D.count A.tab) (L.wert σ) (G.st σ) (ρ.get x).n) :
    ∃ σ', (∀ {Λ'} (rest : Gabbro.Grammatik.Block D V l Γ Λ Λ'),
      execBlock O passes R (Gabbro.Grammatik.Block.freiVar A x hwT hLT hwF hLF rest) σ ρ =
        execBlock O passes R rest σ' ρ) ∧
      Represents L G σ' values ∧ A.FreiOk σ' ∧ ¬ A.Lebt σ' (ρ.get x).n ∧
      (∀ i, A.Lebt σ' i ↔ A.Lebt σ i ∧ i ≠ (ρ.get x).n) := by
  obtain ⟨σ', hexec, hbytes⟩ := free_prefix O passes R (l := l) A x hwT hLT hwF hLF σ ρ
  obtain ⟨σm, hm, hhead, hnew, hother, hcount, hframe⟩ :=
    freiVar_ausfuehren O passes R (l := l) A x hwT hLT hwF hLF (.nil) σ ρ
  have hworld : σm = σ' := by
    have he := hexec (.nil)
    rw [hm] at he
    change (Ausgang.ok σm ρ : Ausgang V l Γ) = .ok σ' ρ at he
    cases he; rfl
  subst σm
  have hfree := A.lebt_frei (ρ.get x).n hi hf hhead hnew hother hcount
  have hrep : Represents L G σ' values := hr.frame (G.st_fremd hframe) (L.wert_fremd hframe)
    (fun i hm => hfree.2.1 i (hr.list_ok.lebt_auf hm) (fun he => hnot (he ▸ hm)))
    (fun i _ => hbytes i)
  exact ⟨σ', hexec, hrep, hfree.1, hfree.2.2,
    fun i => A.release_live_iff (ρ.get x).n hi hf hhead hnew hother hcount i⟩

theorem popAndRelease_values (L : LinkFeld A) (G : LinkKopf A)
    (hwH : V.gschreibt G.g = true) (hLH : gdarf D G.g Λ)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwF : V.gschreibt A.kopf = true) (hLF : gdarf D A.kopf Λ)
    (empty : Endblock D V l Γ Λ)
    {Λ'} (rest : Gabbro.Grammatik.Block D V l (D.typ A.tab A.feld :: Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (value : Wert D (D.typ A.tab A.feld)) (values : List (Wert D (D.typ A.tab A.feld)))
    (hr : Represents L G σ (value :: values)) (hf : A.FreiOk σ) :
    ∃ σ' k,
      execBlock O passes R (Block.popAndRelease L G hwH hLH hwT hLT hwF hLF empty rest) σ ρ =
        ((execBlock O passes R rest σ' (.cons value (.cons k ρ))).schrumpf).schrumpf ∧
      k.n = G.st σ ∧ Represents L G σ' values ∧ A.FreiOk σ' ∧ ¬ A.Lebt σ' k.n ∧
      (∀ i, A.Lebt σ' i ↔ A.Lebt σ i ∧ i ≠ k.n) := by
  obtain ⟨σ1, k, hpop, hkn, hvalue, hrep, hfree, hlive, hnot, hpopLive⟩ :=
    linkPop_values O passes R L G hwH hLH hLT empty σ ρ value values hr hf
  let σ2 := σ1.lese Λ [Sum.inl A.tab]
  have hlive2 : A.Lebt σ2 k.n := (A.lebt_gleich (σ := σ1) (σ' := σ2) rfl (fun _ => rfl) rfl k.n).mpr hlive
  have hnot2 : ¬ Auf (D.count A.tab) (L.wert σ2) (G.st σ2) k.n := by
    have hn : L.wert σ2 = L.wert σ1 := funext (fun _ => rfl)
    rw [hn, show G.st σ2 = G.st σ1 from rfl]
    exact hnot
  obtain ⟨σ3, hrelease, hrep3, hfree3, hdead, hreleaseLive⟩ :=
    free_values O passes R (l := l) A L G (.there .here) hwT hLT hwF hLF σ2 (.cons value (.cons k ρ))
      values (hrep.reads _ _) (A.freiOk_gleich (σ := σ1) (σ' := σ2) rfl (fun _ => rfl) rfl hfree)
      (by simpa only [Env.get_cons_there, Env.get_cons_here] using hlive2)
      (by simpa only [Env.get_cons_there, Env.get_cons_here] using hnot2)
  refine ⟨σ3, k, ?_, hkn, hrep3, hfree3, hdead, ?_⟩
  · unfold Block.popAndRelease
    rw [hpop]
    have heval : eval σ2 (Expr.slot A.tab A.feld (Expr.var .here) hLT) σ2 (.cons k ρ) = value := hvalue
    change ((execBlock O passes R
      (Gabbro.Grammatik.Block.freiVar A (.there .here) hwT hLT hwF hLF rest)
      σ2 (.cons (eval σ2 (Expr.slot A.tab A.feld (Expr.var .here) hLT) σ2 (.cons k ρ)) (.cons k ρ))).schrumpf).schrumpf = _
    rw [heval, hrelease]
  · intro i
    exact (hreleaseLive i).trans (and_congr
      ((A.lebt_gleich (σ := σ1) (σ' := σ2) rfl (fun _ => rfl) rfl i).trans (hpopLive i)) Iff.rfl)

end Execution

end Gabbro.Grammatik.Berechenbarkeit.Storage.GStack
