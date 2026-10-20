/-
  File:      Grammatik/ArenaSibZug.lean
  Subject:   SIBLING CONSISTENCY AND `revoke` ON EXECUTED BLOCKS (PLAN-DYNAMIC.md section 8a.1, third pass): the abstract
             theorems of `ArenaSibling.lean` and `ArenaBaumUnter.lean` take the store facts as hypotheses; here the executed
             blocks of `ArenaSibForm.lean` / `ArenaBaumForm.lean` / `ArenaBaumFormG.lean` discharge them.

    `sib_haengenErst_zug`, `sib_haengenBruder_zug`   -- a leaf in as first child / next sibling with its parent store keeps
                                                        `BaumOk` and `SibOk`;
    `sib_abschneiden_links_zug`, `_rechts_zug`        -- a leaf cut off keeps `BaumOk` and `SibOk` (the parent field untouched);
    `baum_unterbaum_aus_links_zug`, `_rechts_zug`     -- `revoke`: a whole SUBTREE cut off at a child place of a member:
                                                        `BaumOk` and `SibOk` hold on the remaining tree, no slot of the cut
                                                        subtree is a member any more, and every one of them is live (so each can
                                                        be released afterwards: `baum_frei`).
-/
import Grammatik.Bausteine.Arena.Struktur.Formen.ArenaSibForm

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

variable {D : Deklaration}

section Bedeutung
variable (O : Orakel D) (passes : Nat)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {A : FreiForm D} (G : LinkKopf A)

/-- **Executed `blattEinErst` keeps the tree and the sibling demand.** `p` is a member with an empty left place, `i` is live and
    not in the tree; afterwards `i` is a member whose parent is `p`. Valid for every continuation. -/
theorem sib_haengenErst_zug (Lf Rf Par : LinkFeld A) (hd : Lf.f ≠ Rf.f) (hPl : Lf.f ≠ Par.f) (hPr : Rf.f ≠ Par.f)
    (p i : Var Γ (Ty.index (D.count A.tab))) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (rest : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) (hok : A.FreiOk σ) (hb : BaumOk A Lf Rf G σ)
    (hs : SibOk Lf Rf Par G σ)
    (hp : InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) (ρ.get p).n)
    (hpl : Lf.wert σ (ρ.get p).n = D.count A.tab) (hi : A.Lebt σ (ρ.get i).n)
    (hnot : ¬ InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) (ρ.get i).n) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R (Block.blattEinErst Lf Rf Par p i hwT hLT rest) σ ρ
          = execBlock (V := V) O passes R rest σ' ρ ∧
      BaumOk A Lf Rf G σ' ∧ SibOk Lf Rf Par G σ' ∧ A.FreiOk σ' ∧ (∀ j, A.Lebt σ' j ↔ A.Lebt σ j) ∧
      InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') (ρ.get i).n ∧
      Par.wert σ' (ρ.get i).n = (ρ.get p).n := by
  have hpi : (ρ.get p).n ≠ (ρ.get i).n := fun e => hnot (e ▸ hp)
  obtain ⟨σ', he, hlp, hli, hri, hol, hor, hg, hpp, hpo, hk, hn, hss⟩ :=
    blattEinErst_ausfuehren O passes R G Lf Rf Par hd hPl hPr p i hwT hLT rest σ ρ hpi
  obtain ⟨h1, h2⟩ := baum_einfuegen_links A Lf Rf G hb _ _ hp hpl hi hnot hk hn hss hg hlp hli hri hol hor
  have hc : (ρ.get i).n < D.count A.tab := by have := hi.2.1; have := A.stand_le σ; omega
  have hsib := sib_einfuegen_links hs hb hp hpl hi.1 hc hnot hlp hli hri hol hor hpp hpo
  exact ⟨σ', he, h1, by unfold SibOk; rw [hg]; exact hsib, A.freiOk_gleich hk hn hss hok,
    A.lebt_gleich hk hn hss, h2, hpp⟩

/-- **Executed `blattEinBruder` keeps the tree and the sibling demand.** `p` is a member with an empty RIGHT place; afterwards
    `i` is a member whose parent is the parent of `p`. -/
theorem sib_haengenBruder_zug (Lf Rf Par : LinkFeld A) (hd : Rf.f ≠ Lf.f) (hPl : Lf.f ≠ Par.f) (hPr : Rf.f ≠ Par.f)
    (p i : Var Γ (Ty.index (D.count A.tab))) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (rest : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) (hok : A.FreiOk σ) (hb : BaumOk A Lf Rf G σ)
    (hs : SibOk Lf Rf Par G σ)
    (hp : InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) (ρ.get p).n)
    (hpr : Rf.wert σ (ρ.get p).n = D.count A.tab) (hi : A.Lebt σ (ρ.get i).n)
    (hnot : ¬ InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) (ρ.get i).n) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R (Block.blattEinBruder Lf Rf Par p i hwT hLT rest) σ ρ
          = execBlock (V := V) O passes R rest σ' ρ ∧
      BaumOk A Lf Rf G σ' ∧ SibOk Lf Rf Par G σ' ∧ A.FreiOk σ' ∧ (∀ j, A.Lebt σ' j ↔ A.Lebt σ j) ∧
      InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') (ρ.get i).n ∧
      Par.wert σ' (ρ.get i).n = Par.wert σ (ρ.get p).n := by
  have hpi : (ρ.get p).n ≠ (ρ.get i).n := fun e => hnot (e ▸ hp)
  obtain ⟨σ', he, hrp, hri, hli, hor, hol, hg, hpp, hpo, hk, hn, hss⟩ :=
    blattEinBruder_ausfuehren O passes R G Lf Rf Par hd hPl hPr p i hwT hLT rest σ ρ hpi
  obtain ⟨h1, h2⟩ := baum_einfuegen_rechts A Lf Rf G hb _ _ hp hpr hi hnot hk hn hss hg hrp hri hli hor hol
  have hc : (ρ.get i).n < D.count A.tab := by have := hi.2.1; have := A.stand_le σ; omega
  have hsib := sib_einfuegen_rechts hs hb hp hpr hi.1 hc hnot hrp hri hli hor hol hpp hpo
  exact ⟨σ', he, h1, by unfold SibOk; rw [hg]; exact hsib, A.freiOk_gleich hk hn hss hok,
    A.lebt_gleich hk hn hss, h2, hpp⟩

/-- **Executed `abschneiden` at the left keeps the sibling demand** (the leaf's parent field is left as it is: the leaf is
    out of the tree). -/
theorem sib_abschneiden_links_zug (Lf Rf Par : LinkFeld A) (hd : Rf.f ≠ Lf.f) (hPl : Lf.f ≠ Par.f)
    (p : Var Γ (Ty.index (D.count A.tab))) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (voll2 : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (σ : World D) (ρ : Env D Γ) (hok : A.FreiOk σ)
    (hb : BaumOk A Lf Rf G σ) (hs : SibOk Lf Rf Par G σ)
    (hp : InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) (ρ.get p).n)
    (hi : Lf.wert σ (ρ.get p).n < D.count A.tab)
    (hll : Lf.wert σ (Lf.wert σ (ρ.get p).n) = D.count A.tab)
    (hrl : Rf.wert σ (Lf.wert σ (ρ.get p).n) = D.count A.tab) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock (V := V) O passes R (Block.abschneiden Lf Rf Lf p hwT hLT voll voll2 rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons k ρ)).schrumpf ∧
      BaumOk A Lf Rf G σ' ∧ SibOk Lf Rf Par G σ' := by
  obtain ⟨σ', k, he, hrm, hkn, hlp, hol, hoth, hg, hk, hn, hs'⟩ :=
    abschneiden_ausfuehren O passes R G Lf Rf Lf p hwT hLT voll voll2 rest σ ρ hi hll hrl
  obtain ⟨σ'', k', he', hrm', hkn', hb', -, -, -, -, -, -⟩ :=
    baum_abschneiden_links_zug O passes R G Lf Rf hd p hwT hLT voll voll2 rest σ ρ hok hb hp hi hll hrl
  have hP : Par.wert σ' = Par.wert σ := funext (hoth Par (fun e => hPl e.symm))
  have hr : Rf.wert σ' = Rf.wert σ := funext fun j => hoth Rf hd j
  have hsib := sib_blatt_aus_links hs hb hp rfl (hkn ▸ k.lo_le) hi hll hrl hlp hol
  refine ⟨σ', k, he, ?_, ?_⟩
  · have := baum_blatt_aus_links A Lf Rf G hb _ _ hp rfl hi (hkn ▸ k.lo_le) hll hrl hk hn hs' hg hlp hol
      (fun j => hoth Rf hd j)
    exact this.1
  · unfold SibOk
    rw [hr, hP, hg]
    exact hsib

/-- **Executed `abschneiden` at the right keeps the sibling demand** (the mirror). -/
theorem sib_abschneiden_rechts_zug (Lf Rf Par : LinkFeld A) (hd : Lf.f ≠ Rf.f) (hPr : Rf.f ≠ Par.f)
    (p : Var Γ (Ty.index (D.count A.tab))) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (voll2 : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (σ : World D) (ρ : Env D Γ) (hok : A.FreiOk σ)
    (hb : BaumOk A Lf Rf G σ) (hs : SibOk Lf Rf Par G σ)
    (hp : InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) (ρ.get p).n)
    (hi : Rf.wert σ (ρ.get p).n < D.count A.tab)
    (hll : Lf.wert σ (Rf.wert σ (ρ.get p).n) = D.count A.tab)
    (hrl : Rf.wert σ (Rf.wert σ (ρ.get p).n) = D.count A.tab) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock (V := V) O passes R (Block.abschneiden Lf Rf Rf p hwT hLT voll voll2 rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons k ρ)).schrumpf ∧
      BaumOk A Lf Rf G σ' ∧ SibOk Lf Rf Par G σ' := by
  obtain ⟨σ', k, he, hrm, hkn, hrp, hor, hoth, hg, hk, hn, hs'⟩ :=
    abschneiden_ausfuehren O passes R G Lf Rf Rf p hwT hLT voll voll2 rest σ ρ hi hll hrl
  have hP : Par.wert σ' = Par.wert σ := funext (hoth Par (fun e => hPr e.symm))
  have hl : Lf.wert σ' = Lf.wert σ := funext fun j => hoth Lf hd j
  have hsib := sib_blatt_aus_rechts hs hb hp rfl (hkn ▸ k.lo_le) hi hll hrl hrp hor
  refine ⟨σ', k, he, ?_, ?_⟩
  · have := baum_blatt_aus_rechts A Lf Rf G hb _ _ hp rfl hi (hkn ▸ k.lo_le) hll hrl hk hn hs' hg hrp hor
      (fun j => hoth Lf hd j)
    exact this.1
  · unfold SibOk
    rw [hl, hP, hg]
    exact hsib

/-! ## `revoke`: a whole subtree off -/

/-- **Executed `blattAus` WITHOUT the leaf hypotheses (`revoke` at the left place).** `p` is a member with a left child `i`
    (the root of a subtree). Afterwards the tree that remains is well formed and sibling-consistent, its members are old
    members outside the subtree, no slot of the cut subtree is a member, and every slot of the cut subtree is still live
    (an orphan: it can be released). Valid for every continuation. -/
theorem baum_unterbaum_aus_links_zug (Lf Rf Par : LinkFeld A) (hd : Rf.f ≠ Lf.f) (hPl : Lf.f ≠ Par.f)
    (p : Var Γ (Ty.index (D.count A.tab))) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hok : A.FreiOk σ) (hb : BaumOk A Lf Rf G σ) (hs : SibOk Lf Rf Par G σ)
    (hp : InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) (ρ.get p).n)
    (hi : Lf.wert σ (ρ.get p).n < D.count A.tab) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock (V := V) O passes R (Block.blattAus Lf p hwT hLT voll rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons k ρ)).schrumpf ∧
      k.n = Lf.wert σ (ρ.get p).n ∧ BaumOk A Lf Rf G σ' ∧ SibOk Lf Rf Par G σ' ∧ A.FreiOk σ' ∧
      (∀ j, A.Lebt σ' j ↔ A.Lebt σ j) ∧
      (∀ j, InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') j →
        InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) j ∧
        ¬ InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) k.n j) ∧
      (∀ j, InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) k.n j →
        ¬ InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') j ∧ A.Lebt σ' j) := by
  obtain ⟨σ', k, he, hrm, hkn, hlp, hol, hoth, hg, hk, hn, hs'⟩ :=
    blattAus_ausfuehren O passes R G Lf p hwT hLT voll rest σ ρ hi
  have hP : Par.wert σ' = Par.wert σ := funext (hoth Par (fun e => hPl e.symm))
  have hr : Rf.wert σ' = Rf.wert σ := funext fun j => hoth Rf hd j
  have hmono : ∀ j, A.Lebt σ j → A.Lebt σ' j := fun j h => (A.lebt_gleich hk hn hs' j).mpr h
  obtain ⟨hb', hmem, hout, -, hsub⟩ := unterbaum_aus_ok (Live' := A.Lebt σ') hb hp rfl hmono hlp hol
  have hsib := sib_unterbaum_aus_links hs hb hp rfl hlp hol
  have hk' : InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) (Lf.wert σ (ρ.get p).n) := hp.links hi
  refine ⟨σ', k, he, hkn, ?_, ?_, A.freiOk_gleich hk hn hs' hok, A.lebt_gleich hk hn hs', ?_, ?_⟩
  · unfold BaumOk; rw [hr, hg]; exact hb'
  · unfold SibOk; rw [hr, hP, hg]; exact hsib
  · intro j hj
    rw [hr, hg] at hj
    rw [hkn]
    exact hmem j hj
  · intro j hj
    rw [hkn] at hj
    refine ⟨?_, hmono j (BaumOkF.lebt_in hb (hsub j hj))⟩
    rw [hr, hg]
    exact hout j hj

/-- **`revoke` at the right place** (the mirror): the next sibling of `p`, with everything below it, is cut off. -/
theorem baum_unterbaum_aus_rechts_zug (Lf Rf Par : LinkFeld A) (hd : Lf.f ≠ Rf.f) (hPr : Rf.f ≠ Par.f)
    (p : Var Γ (Ty.index (D.count A.tab))) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hok : A.FreiOk σ) (hb : BaumOk A Lf Rf G σ) (hs : SibOk Lf Rf Par G σ)
    (hp : InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) (ρ.get p).n)
    (hi : Rf.wert σ (ρ.get p).n < D.count A.tab) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock (V := V) O passes R (Block.blattAus Rf p hwT hLT voll rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons k ρ)).schrumpf ∧
      k.n = Rf.wert σ (ρ.get p).n ∧ BaumOk A Lf Rf G σ' ∧ SibOk Lf Rf Par G σ' ∧ A.FreiOk σ' ∧
      (∀ j, A.Lebt σ' j ↔ A.Lebt σ j) ∧
      (∀ j, InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') j →
        InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) j ∧
        ¬ InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) k.n j) ∧
      (∀ j, InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) k.n j →
        ¬ InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') j ∧ A.Lebt σ' j) := by
  obtain ⟨σ', k, he, hrm, hkn, hrp, hor, hoth, hg, hk, hn, hs'⟩ :=
    blattAus_ausfuehren O passes R G Rf p hwT hLT voll rest σ ρ hi
  have hP : Par.wert σ' = Par.wert σ := funext (hoth Par (fun e => hPr e.symm))
  have hl : Lf.wert σ' = Lf.wert σ := funext fun j => hoth Lf hd j
  have hmono : ∀ j, A.Lebt σ j → A.Lebt σ' j := fun j h => (A.lebt_gleich hk hn hs' j).mpr h
  obtain ⟨hb', hmem, hout, -, hsub⟩ := unterbaum_aus_rechts_ok (Live' := A.Lebt σ') hb hp rfl hmono hrp hor
  have hsib := sib_unterbaum_aus_rechts hs hb hp rfl hrp hor
  refine ⟨σ', k, he, hkn, ?_, ?_, A.freiOk_gleich hk hn hs' hok, A.lebt_gleich hk hn hs', ?_, ?_⟩
  · unfold BaumOk; rw [hl, hg]; exact hb'
  · unfold SibOk; rw [hl, hP, hg]; exact hsib
  · intro j hj
    rw [hl, hg] at hj
    rw [hkn]
    obtain ⟨a, b, -⟩ := hmem j hj
    exact ⟨a, fun e => b e.spiegel⟩
  · intro j hj
    rw [hkn] at hj
    have hj' := hj.spiegel
    refine ⟨?_, hmono j (BaumOkF.lebt_in hb (hsub j hj'))⟩
    rw [hl, hg]
    exact hout j hj'

end Bedeutung

end Gabbro.Grammatik
