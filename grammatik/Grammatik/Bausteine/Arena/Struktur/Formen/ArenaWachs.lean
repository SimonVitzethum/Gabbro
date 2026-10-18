/-
  File:      Grammatik/ArenaWachs.lean
  Subject:   `grow` COMPOSES WITH THE LINK MOVES (PLAN-DYNAMISCH.md section 8a.1, step (2)).

  `grow A by n` (`Block.dynGrowB`) writes ONLY the committed word `komm` (`dynGrow_commit`). The structure invariants
  read the used counter, the free list and the link fields, never `komm`; with `LinkKopf` excluding `komm`
  (`ArenaListe.lean`, field `h3`) and `FreiForm` holding `kopf ≠ komm` (`hk2`), a commit leaves every one of them
  where it was. So the invariants of the free list, the list and the tree survive a `grow`, and every continuation
  starts from the same facts: the moves of `ArenaListe`/`ArenaBaumWelt`/`ArenaLinkForm` compose with `grow`.

    * `nachGrow_gleich`  -- the frame: head, free links, counter, link field, link head, all as before.
    * `grow_liste`, `grow_baum` -- the executed `grow` keeps `FreiOk`, every liveness, `ListOk` resp. `BaumOk`, and
      continues in the commit world with the new committed word bound (`dynGrow_commit`'s equation).
-/
import Grammatik.Bausteine.Arena.Struktur.ArenaBaumWelt

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

variable {D : Deklaration}

/-- **A commit moves the committed word and nothing the structures read:** every global other than `komm` is as
    before, and so is every slot. -/
theorem nachGrow_rahmen (A : DynForm D) (n : Int) (Λ : List (Res D)) (σ : World D)
    (h0 : 0 ≤ A.komSt σ + n) (h : A.komSt σ + n ≤ D.count A.tab) :
    (∀ g, g ≠ A.komm → (nachGrow A n Λ σ h0 h).globs g = σ.globs g) ∧
    (nachGrow A n Λ σ h0 h).slots = σ.slots :=
  ⟨fun g hg => World.globs_schreibGlob_ne σ g A.komm Λ _ hg, rfl⟩

/-- A commit leaves the allocator's three views, the link field and the link head alone. -/
theorem nachGrow_gleich (A : FreiForm D) (L : LinkFeld A) (G : LinkKopf A) (n : Int) (Λ : List (Res D))
    (σ : World D) (h0 : 0 ≤ A.komSt σ + n) (h : A.komSt σ + n ≤ D.count A.tab) :
    A.kopfSt (nachGrow A.toDynForm n Λ σ h0 h) = A.kopfSt σ ∧
    (∀ j, A.naechst (nachGrow A.toDynForm n Λ σ h0 h) j = A.naechst σ j) ∧
    A.stand (nachGrow A.toDynForm n Λ σ h0 h) = A.stand σ ∧
    (∀ j, L.wert (nachGrow A.toDynForm n Λ σ h0 h) j = L.wert σ j) ∧
    G.st (nachGrow A.toDynForm n Λ σ h0 h) = G.st σ := by
  obtain ⟨hg, hs⟩ := nachGrow_rahmen A.toDynForm n Λ σ h0 h
  refine ⟨?_, fun j => ?_, ?_, fun j => ?_, ?_⟩
  · exact congrArg (fun w => (Wert.umTyp A.hkopf w).n) (hg A.kopf A.hk2)
  · simp only [FreiForm.naechst, hs]
  · exact congrArg (fun w => (Wert.umTyp A.hz w).n) (hg A.zaehl (Ne.symm A.hzwei))
  · simp only [LinkFeld.wert, hs]
  · exact congrArg (fun w => (Wert.umTyp G.hg w).n) (hg G.g G.h3)

section Bedeutung
variable (O : Orakel D) (passes : Nat)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (A : FreiForm D) (L : LinkFeld A) (G : LinkKopf A)

/-- **`grow` past the ceiling takes its `else`:** nothing moves but the recorded read. -/
theorem dynGrow_voll (A : DynForm D) (n : Int) (hwK : V.gschreibt A.komm = true) (hLK : gdarf D A.komm Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.int 0 (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hn : ¬ (0 ≤ A.komSt σ + n ∧ A.komSt σ + n ≤ D.count A.tab)) :
    execBlock (V := V) O passes R (Block.dynGrowB A n hwK hLK voll rest) σ ρ
      = (execEnd O passes R voll (σ.lese Λ [Sum.inr A.komm]) ρ).zuAusgang := by
  have hb : ¬ ((0 : Int) ≤ (Wert.umTyp A.hk (σ.globs A.komm)).n + n ∧
      (Wert.umTyp A.hk (σ.globs A.komm)).n + n ≤ D.count A.tab) := hn
  simp only [Block.dynGrowB, Block.dynSumme, execBlock, eval_umTyp, orte_umTyp, eval,
    Expr.orte, World.globs_lese, Zahl.add, List.append_nil]
  rw [dif_neg hb]

/-- **The executed `grow` keeps the free list, every liveness and the list.** The guard that fits (`h0`, `h`) is what
    `narrow` decides; the continuation runs in the commit world with the new committed word bound. -/
theorem grow_liste (n : Int) (hwK : V.gschreibt A.komm = true) (hLK : gdarf D A.komm Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.int 0 (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (h0 : 0 ≤ A.komSt σ + n) (h : A.komSt σ + n ≤ D.count A.tab)
    (hok : A.FreiOk σ) (hl : ListOk A L G σ) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R (Block.dynGrowB A.toDynForm n hwK hLK voll rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons ⟨A.komSt σ + n, h0, h⟩ ρ)).schrumpf ∧
      A.FreiOk σ' ∧ (∀ j, A.Lebt σ' j ↔ A.Lebt σ j) ∧ ListOk A L G σ' ∧ A.komSt σ' = A.komSt σ + n := by
  obtain ⟨he, hkomm, -, -⟩ := dynGrow_commit O passes R A.toDynForm n hwK hLK voll rest σ ρ h0 h
  obtain ⟨hk, hn, hs, hL, hG⟩ := nachGrow_gleich A L G n Λ σ h0 h
  refine ⟨_, he, A.freiOk_gleich hk hn hs hok, A.lebt_gleich hk hn hs, ?_, hkomm⟩
  unfold ListOk at *
  rw [funext hL, hG]
  exact hl.rahmen (fun j hj => (A.lebt_gleich hk hn hs j).mpr (hl.lebt_auf hj)) (fun _ _ => rfl)

/-- **The executed `grow` keeps the free list, every liveness and the tree.** -/
theorem grow_baum (Lf Rf : LinkFeld A) (n : Int) (hwK : V.gschreibt A.komm = true) (hLK : gdarf D A.komm Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.int 0 (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (h0 : 0 ≤ A.komSt σ + n) (h : A.komSt σ + n ≤ D.count A.tab)
    (hok : A.FreiOk σ) (hb : BaumOk A Lf Rf G σ) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R (Block.dynGrowB A.toDynForm n hwK hLK voll rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons ⟨A.komSt σ + n, h0, h⟩ ρ)).schrumpf ∧
      A.FreiOk σ' ∧ (∀ j, A.Lebt σ' j ↔ A.Lebt σ j) ∧ BaumOk A Lf Rf G σ' ∧ A.komSt σ' = A.komSt σ + n := by
  obtain ⟨he, hkomm, -, -⟩ := dynGrow_commit O passes R A.toDynForm n hwK hLK voll rest σ ρ h0 h
  obtain ⟨hk, hn, hs, hL, hG⟩ := nachGrow_gleich A Lf G n Λ σ h0 h
  obtain ⟨-, -, -, hR, -⟩ := nachGrow_gleich A Rf G n Λ σ h0 h
  refine ⟨_, he, A.freiOk_gleich hk hn hs hok, A.lebt_gleich hk hn hs, ?_, hkomm⟩
  unfold BaumOk at *
  rw [funext hL, funext hR, hG]
  exact hb.rahmen' (fun j hj => (A.lebt_gleich hk hn hs j).mpr (hb.lebt_in hj)) (fun _ _ => ⟨rfl, rfl⟩)

end Bedeutung

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.nachGrow_gleich
#print axioms Gabbro.Grammatik.grow_liste
#print axioms Gabbro.Grammatik.grow_baum
