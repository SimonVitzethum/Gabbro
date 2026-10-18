/-
  File:      Grammatik/ArenaSibForm.lean
  Subject:   THE PARENT STORE OF THE CAPABILITY TREE AND `revoke`, ON EXECUTED BLOCKS (PLAN-DYNAMISCH.md section 8a.1, third
             pass). The capability tree is a first-child / next-sibling tree: the left link is the first child, the right
             link is the next sibling, and a third field `par` names the parent (`ArenaSibling.lean`: `SibF`). A leaf in is
             then TWO things: the two child stores of `blattEin` and the parent store.

    `Block.blattEinErst Lf Rf Par p i rest`   =  `blattEin Lf Rf p i  (par[i] = p;  rest)`       -- first child of `p`
    `Block.blattEinBruder Lf Rf Par p i rest` =  `blattEin Rf Lf p i  (par[i] = par[p];  rest)`  -- next sibling of `p`

  The theorems keep BOTH invariants on the executed block: `BaumOk` and `SibOk A Lf Rf Par Wz σ`
  (`SibF count (Lf.wert σ) (Rf.wert σ) (Par.wert σ) (Wz.st σ)`). A cut that takes a whole subtree off (`revoke`) is the
  existing `Block.blattAus` WITHOUT the leaf hypotheses (`baum_unterbaum_aus_*_zug`): the remaining tree is well formed and
  sibling-consistent, and no slot of the cut subtree is a member any more, so each can be released (`baum_frei`).
-/
import Grammatik.Bausteine.Arena.Struktur.Formen.ArenaBaumFormZug
import Grammatik.Bausteine.Arena.Struktur.ArenaBaumUnter

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

variable {D : Deklaration}

/-- **Sibling consistency on a world:** the first child of every member has that member as its parent, and the next sibling
    of every member has the parent of that member. -/
def SibOk {A : FreiForm D} (Lf Rf Par : LinkFeld A) (Wz : LinkKopf A) (σ : World D) : Prop :=
  SibF (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (Par.wert σ) (Wz.st σ)

namespace Block
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable {A : FreiForm D}

/-- **`blattEin Lf Rf p i (par[i] = p; rest)`** -- hang `i` as the FIRST CHILD of `p`, its parent is `p`. -/
def blattEinErst (Lf Rf Par : LinkFeld A) (p i : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (rest : Block D V l Γ Λ Λ') : Block D V l Γ Λ Λ' :=
  blattEin Lf Rf p i hwT hLT
    (.cons (.assignSlot A.tab Par.f (Expr.var i) (linkIdxAlsFeld Par p) hwT hLT) rest)

/-- **`blattEin Rf Lf p i (par[i] = par[p]; rest)`** -- hang `i` as the NEXT SIBLING of `p`, its parent is the parent of `p`. -/
def blattEinBruder (Lf Rf Par : LinkFeld A) (p i : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (rest : Block D V l Γ Λ Λ') : Block D V l Γ Λ Λ' :=
  blattEin Rf Lf p i hwT hLT
    (.cons (.assignSlot A.tab Par.f (Expr.var i) (Expr.slot A.tab Par.f (Expr.var p) hLT) hwT hLT) rest)

end Block

section Bedeutung
variable (O : Orakel D) (passes : Nat)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {A : FreiForm D} (G : LinkKopf A)

/-- **A store into the parent field leaves:** the parent of `i` is the stored number, every other parent stays, no other link
    field and no link head moves, the allocator's views stay. `hv` says what the stored value is (it does not depend on the
    recorded reads). Valid for every continuation. -/
theorem parStore_ausfuehren (Par : LinkFeld A) (i : Var Γ (Ty.index (D.count A.tab)))
    (e : Expr D Γ Λ (D.typ A.tab Par.f)) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (rest : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) (v : Int)
    (hv : ∀ w : World D, w.slots = σ.slots → (Wert.umTyp Par.hf (eval w e w ρ)).n = v) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R (.cons (.assignSlot A.tab Par.f (Expr.var i) e hwT hLT) rest) σ ρ
          = execBlock (V := V) O passes R rest σ' ρ ∧
      (∀ C : LinkFeld A, C.f ≠ Par.f → C.wert σ' = C.wert σ) ∧ (∀ H : LinkKopf A, H.st σ' = H.st σ) ∧
      Par.wert σ' (ρ.get i).n = v ∧ (∀ j, j ≠ (ρ.get i).n → Par.wert σ' j = Par.wert σ j) ∧
      A.kopfSt σ' = A.kopfSt σ ∧ (∀ j, A.naechst σ' j = A.naechst σ j) ∧ A.stand σ' = A.stand σ := by
  refine ⟨_, rfl, fun C hC => funext fun j => ?_, fun H => rfl, ?_, fun j hj => ?_, rfl,
    fun j => A.naechst_schreibSlot_ne _ _ _ _ _ Par.h2 j, rfl⟩
  · simp [LinkFeld.wert, World.slots_schreibSlot_ne _ _ _ _ _ _ _ _ hC]
  · exact (Par.wert_schreibSlot_selbst _ _ _ _).trans (hv _ rfl)
  · exact Par.wert_schreibSlot_anderer _ _ _ _ _ hj

/-- **`blattEinErst` leaves:** the store facts of the leaf in at the left place, and the parent of `i` is `p`; every other
    parent stays. Valid for every continuation. -/
theorem blattEinErst_ausfuehren (Lf Rf Par : LinkFeld A) (hd : Lf.f ≠ Rf.f) (hPl : Lf.f ≠ Par.f)
    (hPr : Rf.f ≠ Par.f) (p i : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (rest : Block D V l Γ Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hpi : (ρ.get p).n ≠ (ρ.get i).n) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R (Block.blattEinErst Lf Rf Par p i hwT hLT rest) σ ρ
          = execBlock (V := V) O passes R rest σ' ρ ∧
      Lf.wert σ' (ρ.get p).n = (ρ.get i).n ∧ Lf.wert σ' (ρ.get i).n = D.count A.tab ∧
      Rf.wert σ' (ρ.get i).n = D.count A.tab ∧
      (∀ j, j ≠ (ρ.get p).n → j ≠ (ρ.get i).n → Lf.wert σ' j = Lf.wert σ j) ∧
      (∀ j, j ≠ (ρ.get i).n → Rf.wert σ' j = Rf.wert σ j) ∧ G.st σ' = G.st σ ∧
      Par.wert σ' (ρ.get i).n = (ρ.get p).n ∧ (∀ j, j ≠ (ρ.get i).n → Par.wert σ' j = Par.wert σ j) ∧
      A.kopfSt σ' = A.kopfSt σ ∧ (∀ j, A.naechst σ' j = A.naechst σ j) ∧ A.stand σ' = A.stand σ := by
  obtain ⟨σ1, he1, hrm1, hlp, hli, hri, hol, hor, hg, hk, hn, hs⟩ :=
    blattEin_ausfuehren O passes R G Lf Rf hd p i hwT hLT
      (.cons (.assignSlot A.tab Par.f (Expr.var i) (Block.linkIdxAlsFeld Par p) hwT hLT) rest) σ ρ hpi
  obtain ⟨σ2, he2, hC, hH, hpi2, hpo, hk2, hn2, hs2⟩ :=
    parStore_ausfuehren O passes R Par i (Block.linkIdxAlsFeld Par p) hwT hLT rest σ1 ρ (ρ.get p).n
      (fun w _ => by simp only [Block.linkIdxAlsFeld, eval_umTyp, eval]; exact umTyp_rund_n Par.hf _)
  have hP1 : Par.wert σ1 = Par.wert σ := hrm1.feld Par (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun e => hPl e.symm, fun e => hPr e.symm⟩)
  have hLf : Lf.wert σ2 = Lf.wert σ1 := hC Lf hPl
  have hRf : Rf.wert σ2 = Rf.wert σ1 := hC Rf hPr
  refine ⟨σ2, he1.trans he2, ?_, ?_, ?_, fun j hj1 hj2 => ?_, fun j hj => ?_, ?_, hpi2, fun j hj => ?_,
    hk2.trans hk, fun j => (hn2 j).trans (hn j), hs2.trans hs⟩
  · rw [hLf]; exact hlp
  · rw [hLf]; exact hli
  · rw [hRf]; exact hri
  · rw [hLf]; exact hol j hj1 hj2
  · rw [hRf]; exact hor j hj
  · exact (hH G).trans hg
  · rw [hpo j hj, hP1]

/-- **`blattEinBruder` leaves:** the store facts of the leaf in at the right place, and the parent of `i` is the parent of `p`;
    every other parent stays. Valid for every continuation. -/
theorem blattEinBruder_ausfuehren (Lf Rf Par : LinkFeld A) (hd : Rf.f ≠ Lf.f) (hPl : Lf.f ≠ Par.f)
    (hPr : Rf.f ≠ Par.f) (p i : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (rest : Block D V l Γ Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hpi : (ρ.get p).n ≠ (ρ.get i).n) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R (Block.blattEinBruder Lf Rf Par p i hwT hLT rest) σ ρ
          = execBlock (V := V) O passes R rest σ' ρ ∧
      Rf.wert σ' (ρ.get p).n = (ρ.get i).n ∧ Rf.wert σ' (ρ.get i).n = D.count A.tab ∧
      Lf.wert σ' (ρ.get i).n = D.count A.tab ∧
      (∀ j, j ≠ (ρ.get p).n → j ≠ (ρ.get i).n → Rf.wert σ' j = Rf.wert σ j) ∧
      (∀ j, j ≠ (ρ.get i).n → Lf.wert σ' j = Lf.wert σ j) ∧ G.st σ' = G.st σ ∧
      Par.wert σ' (ρ.get i).n = Par.wert σ (ρ.get p).n ∧ (∀ j, j ≠ (ρ.get i).n → Par.wert σ' j = Par.wert σ j) ∧
      A.kopfSt σ' = A.kopfSt σ ∧ (∀ j, A.naechst σ' j = A.naechst σ j) ∧ A.stand σ' = A.stand σ := by
  obtain ⟨σ1, he1, hrm1, hrp, hri, hli, hor, hol, hg, hk, hn, hs⟩ :=
    blattEin_ausfuehren O passes R G Rf Lf hd p i hwT hLT
      (.cons (.assignSlot A.tab Par.f (Expr.var i) (Expr.slot A.tab Par.f (Expr.var p) hLT) hwT hLT) rest) σ ρ hpi
  have hP1 : Par.wert σ1 = Par.wert σ := hrm1.feld Par (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun e => hPr e.symm, fun e => hPl e.symm⟩)
  obtain ⟨σ2, he2, hC, hH, hpi2, hpo, hk2, hn2, hs2⟩ :=
    parStore_ausfuehren O passes R Par i (Expr.slot A.tab Par.f (Expr.var p) hLT) hwT hLT rest σ1 ρ
      (Par.wert σ (ρ.get p).n) (fun w hw => by
        simp only [eval_umTyp, eval]
        have : w.slots A.tab (ρ.get p).n Par.f = σ1.slots A.tab (ρ.get p).n Par.f := by rw [hw]
        rw [this]
        exact congrFun hP1 (ρ.get p).n)
  have hLf : Lf.wert σ2 = Lf.wert σ1 := hC Lf hPl
  have hRf : Rf.wert σ2 = Rf.wert σ1 := hC Rf hPr
  refine ⟨σ2, he1.trans he2, ?_, ?_, ?_, fun j hj1 hj2 => ?_, fun j hj => ?_, ?_, hpi2, fun j hj => ?_,
    hk2.trans hk, fun j => (hn2 j).trans (hn j), hs2.trans hs⟩
  · rw [hRf]; exact hrp
  · rw [hRf]; exact hri
  · rw [hLf]; exact hli
  · rw [hRf]; exact hor j hj1 hj2
  · rw [hLf]; exact hol j hj
  · exact (hH G).trans hg
  · rw [hpo j hj, hP1]

end Bedeutung

end Gabbro.Grammatik
