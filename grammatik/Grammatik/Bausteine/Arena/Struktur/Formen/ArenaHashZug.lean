/-
  File:      Grammatik/ArenaHashZug.lean
  Subject:   THE HASH-CHAIN INVARIANT ON EXECUTED BLOCKS (PLAN-DYNAMISCH.md section 8a.1, third pass): `hash_push`,
             `hash_pop` and `hash_unlink` (`ArenaHash.lean`) take the store facts as hypotheses; here they are discharged by
             the executed forms of `ArenaHashForm.lean` (and `Block.linkUnlink` for the unlink inside one chain), for every
             continuation, with the bucket heads read out of the TABLE FIELD.

    `hash_push_zug`   -- a live slot on NO bucket becomes the head of bucket `b`;
    `hash_pop_zug`    -- the head of bucket `b` is taken off: the binder holds it, live and on no bucket afterwards;
    `hash_unlink_zug` -- the successor of a member of bucket `b0` is cut out; no bucket head moves.
-/
import Grammatik.Bausteine.Arena.Struktur.Formen.ArenaHashForm

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

variable {D : Deklaration}

section Bedeutung
variable (O : Orakel D) (passes : Nat)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {A : FreiForm D} (L : LinkFeld A) (H : BucketKopf A)

/-- **Executed `hashPush` keeps the hash table.** `x` names a live slot that is on NO bucket (the checker's `N586`: a pushed
    slot is owned). Valid for every continuation. -/
theorem hash_push_zug (b : Var Γ (Ty.index (D.count H.bt))) (x : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (hwB : V.schreibt H.bt = true)
    (hLB : darf D H.bt Λ) (rest : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) (hok : A.FreiOk σ)
    (hh : HashOk L H σ) (hi : A.Lebt σ (ρ.get x).n)
    (hnot : ∀ b', 0 ≤ b' → b' < D.count H.bt → ¬ Auf (D.count A.tab) (L.wert σ) (H.wert σ b') (ρ.get x).n) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R (Block.hashPush L H b x hwT hLT hwB hLB rest) σ ρ
          = execBlock (V := V) O passes R rest σ' ρ ∧
      LinkRahmen A [L.f] [] σ σ' ∧ HashOk L H σ' ∧ A.FreiOk σ' ∧ (∀ j, A.Lebt σ' j ↔ A.Lebt σ j) ∧
      H.wert σ' (ρ.get b).n = (ρ.get x).n ∧ L.wert σ' (ρ.get x).n = H.wert σ (ρ.get b).n := by
  obtain ⟨σ', he, hrm, hh1, hl1, hhd, ho, hk, hn, hs⟩ :=
    hashPush_ausfuehren O passes R L H b x hwT hLT hwB hLB rest σ ρ
  have hb0 : 0 ≤ (ρ.get b).n ∧ (ρ.get b).n < D.count H.bt :=
    ⟨(ρ.get b).lo_le, by have := (ρ.get b).le_hi; omega⟩
  have hc : (ρ.get x).n < D.count A.tab := by have := hi.2.1; have := A.stand_le σ; omega
  have hmono : ∀ j, A.Lebt σ j → A.Lebt σ' j := fun j h => (A.lebt_gleich hk hn hs j).mpr h
  exact ⟨σ', he, hrm,
    hash_push hh hb0 hi.1 hc (hmono _ hi) hmono hnot hhd hh1 hl1 ho,
    A.freiOk_gleich hk hn hs hok, A.lebt_gleich hk hn hs, hh1, hl1⟩

/-- **Executed `hashPop` keeps the hash table.** The bucket is non-empty; the binder holds its head, which is live and on NO
    bucket afterwards, so it may be released. Valid for every continuation. -/
theorem hash_pop_zug (b : Var Γ (Ty.index (D.count H.bt)))
    (hLT : darf D A.tab Λ) (hwB : V.schreibt H.bt = true) (hLB : darf D H.bt Λ) (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (σ : World D) (ρ : Env D Γ) (hok : A.FreiOk σ)
    (hh : HashOk L H σ) (hne : H.wert σ (ρ.get b).n < D.count A.tab) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock (V := V) O passes R (Block.hashPop L H b hLT hwB hLB voll rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons k ρ)).schrumpf ∧
      k.n = H.wert σ (ρ.get b).n ∧ HashOk L H σ' ∧ A.FreiOk σ' ∧ (∀ j, A.Lebt σ' j ↔ A.Lebt σ j) ∧
      A.Lebt σ' k.n ∧
      (∀ b', 0 ≤ b' → b' < D.count H.bt → ¬ Auf (D.count A.tab) (L.wert σ') (H.wert σ' b') k.n) := by
  obtain ⟨σ', k, he, hkn, hh1, hhd, ho, hk, hn, hs⟩ :=
    hashPop_ausfuehren O passes R L H b hLT hwB hLB voll rest σ ρ hne
  have hb0 : 0 ≤ (ρ.get b).n ∧ (ρ.get b).n < D.count H.bt :=
    ⟨(ρ.get b).lo_le, by have := (ρ.get b).le_hi; omega⟩
  have hmono : ∀ j, A.Lebt σ j → A.Lebt σ' j := fun j h => (A.lebt_gleich hk hn hs j).mpr h
  have hLnx : L.wert σ' = L.wert σ := funext ho
  have hhash := hash_pop (Live' := A.Lebt σ') hh hb0 hne hmono hhd hh1 ho
  -- the head of bucket `b` was on the chain, hence live
  have hc1 := hh.1
  have hc2 := hh.2
  have hchain := hc1 _ hb0.1 hb0.2
  have hlebtk : A.Lebt σ k.n := by
    rw [hkn]
    exact hchain.lebt_auf (auf_kopf hne (by obtain ⟨Ls, hk0, -, -⟩ := hchain; exact ⟨Ls, hk0⟩))
  refine ⟨σ', k, he, hkn, hhash, A.freiOk_gleich hk hn hs hok, A.lebt_gleich hk hn hs,
    (A.lebt_gleich hk hn hs _).mpr hlebtk, fun b' hb0' hb1' => ?_⟩
  by_cases hbb : b' = (ρ.get b).n
  · subst hbb
    rw [hLnx, hh1, hkn]
    exact (pop_ok (hc1 _ hb0.1 hb0.2) hne hmono rfl (fun _ => rfl)).2
  · rw [hLnx, hhd b' hbb, hkn]
    exact hc2 _ b' hb0.1 hb0.2 hb0' hb1' (Ne.symm hbb) _
      (auf_kopf hne (by obtain ⟨Ls, hk0, -, -⟩ := hchain; exact ⟨Ls, hk0⟩))

/-- **Executed `linkUnlink` inside bucket `b0` keeps the hash table.** `p` is a member of bucket `b0` and has a successor `i`;
    the binder holds `i`, which is live and on NO bucket afterwards, so it may be released. No bucket head moves. -/
theorem hash_unlink_zug (b0 : Int) (hb0 : 0 ≤ b0 ∧ b0 < D.count H.bt) (p : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (σ : World D) (ρ : Env D Γ) (hok : A.FreiOk σ)
    (hh : HashOk L H σ) (hp : Auf (D.count A.tab) (L.wert σ) (H.wert σ b0) (ρ.get p).n)
    (hi : L.wert σ (ρ.get p).n < D.count A.tab) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock (V := V) O passes R (Block.linkUnlink L p hwT hLT voll rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons k ρ)).schrumpf ∧
      k.n = L.wert σ (ρ.get p).n ∧ HashOk L H σ' ∧ A.FreiOk σ' ∧ (∀ j, A.Lebt σ' j ↔ A.Lebt σ j) ∧
      A.Lebt σ' k.n ∧
      (∀ b', 0 ≤ b' → b' < D.count H.bt → ¬ Auf (D.count A.tab) (L.wert σ') (H.wert σ' b') k.n) := by
  obtain ⟨σ', k, he, hkn, hnp, ho, hhd, hk, hn, hs⟩ :=
    hashUnlink_ausfuehren O passes R L H p hwT hLT voll rest σ ρ hi
  have hmono : ∀ j, A.Lebt σ j → A.Lebt σ' j := fun j h => (A.lebt_gleich hk hn hs j).mpr h
  have hHd : H.wert σ' = H.wert σ := funext hhd
  have hc1 := hh.1
  have hc2 := hh.2
  have hchain0 := hc1 _ hb0.1 hb0.2
  have hhash : HashOk L H σ' := by
    unfold HashOk
    rw [hHd]
    exact hash_unlink (Live' := A.Lebt σ') hh hb0 hp rfl hi hmono hnp ho
  have hik : Auf (D.count A.tab) (L.wert σ) (H.wert σ b0) (L.wert σ (ρ.get p).n) := auf_nach hp hi
  have hlebtk : A.Lebt σ k.n := by
    rw [hkn]; exact hchain0.lebt_auf hik
  refine ⟨σ', k, he, hkn, hhash, A.freiOk_gleich hk hn hs hok, A.lebt_gleich hk hn hs,
    (A.lebt_gleich hk hn hs _).mpr hlebtk, fun b' hb0' hb1' => ?_⟩
  rw [hHd, hkn]
  by_cases hbb : b' = b0
  · subst hbb
    exact (unlink_ok hchain0 hp rfl hi hmono hnp ho).2
  · intro hq
    have hsub : ∀ j, Auf (D.count A.tab) (L.wert σ') (H.wert σ b') j → Auf (D.count A.tab) (L.wert σ) (H.wert σ b') j := by
      have hchain' := hc1 _ hb0' hb1'
      have hex : ∃ Ls, KetteF (D.count A.tab) (L.wert σ) (H.wert σ b') Ls := by
        obtain ⟨Ls, hk0, -, -⟩ := hchain'; exact ⟨Ls, hk0⟩
      exact fun j hj => (auf_ho hex (fun j' hj' => ho j' (fun e =>
        hc2 _ b' hb0.1 hb0.2 hb0' hb1' (Ne.symm hbb) _ hp (e ▸ hj'))) j).mp hj
    exact hc2 _ b' hb0.1 hb0.2 hb0' hb1' (Ne.symm hbb) _ hik (hsub _ hq)

end Bedeutung

end Gabbro.Grammatik
