/-
  File:      Grammatik/ArenaBaumForm.lean
  Subject:   THE EXECUTED FORMS OF THE TREE LINK STORES (PLAN-DYNAMIC.md section 8a.1, step (1), tree half):
             `leaf in` and `leaf out`, at the left or the right child place, as `Block`s over the existing
             statements, with the proof that each executed form leaves exactly the store facts that
             `baum_einfuegen_links/rechts` and `baum_blatt_aus_links/rechts` (`ArenaBaumWelt.lean`) take as
             hypotheses. A tree move names a child place `Cp` (the field it hooks into) and the other child
             place `Co`; the left move is `Cp = Lf, Co = Rf`, the right move the mirror.

    `Block.blattEin Cp Co p i rest`  =  `Cp[i] = nil;  Co[i] = nil;  Cp[p] = i;  rest`
    `Block.blattAus C p voll rest`   =  `let i = C[p] (narrow, else voll);  C[p] = nil;  rest`

  What stays a hypothesis, and why: that `p` is a member of the tree, that `i` is live and not in the tree, that the
  child place `Cp[p]` is empty (leaf in) and that `i` is a leaf (leaf out) are facts about the world BEFORE the
  move; the checker establishes them by names (`N586`) and guards. The two child fields are two fields (`hd`).
-/
import Grammatik.Bausteine.Arena.Struktur.Formen.ArenaLinkForm
import Grammatik.Bausteine.Arena.Struktur.ArenaBaumWelt
import Grammatik.Bausteine.Arena.Struktur.ArenaSibling

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

variable {D : Deklaration}

namespace Block
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable {A : FreiForm D}

/-- The nil marker `count`, at the link field's declared type. -/
def linkNil (C : LinkFeld A) : Expr D Γ Λ (D.typ A.tab C.f) :=
  Expr.umTyp C.hf.symm
    (Expr.widen (lo := D.count A.tab) (hi := D.count A.tab) (lo' := 0) (hi' := D.count A.tab)
      (by have := A.hpos; omega) (Int.le_refl _) (Expr.lit (D.count A.tab)))

/-- The index variable `x`, at the link field's declared type. -/
def linkIdxAlsFeld (C : LinkFeld A) (x : Var Γ (Ty.index (D.count A.tab))) : Expr D Γ Λ (D.typ A.tab C.f) :=
  Expr.umTyp C.hf.symm
    (Expr.widen (lo := 0) (hi := D.count A.tab - 1) (lo' := 0) (hi' := D.count A.tab)
      (by omega) (by omega) (Expr.var x))

/-- **`Cp[i] = nil;  Co[i] = nil;  Cp[p] = i;  rest`** -- hang the slot `i` as the `Cp` child of the member `p`. -/
def blattEin (Cp Co : LinkFeld A) (p i : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (rest : Block D V l Γ Λ Λ') : Block D V l Γ Λ Λ' :=
  .cons (.assignSlot A.tab Cp.f (Expr.var i) (linkNil Cp) hwT hLT)
    (.cons (.assignSlot A.tab Co.f (Expr.var i) (linkNil Co) hwT hLT)
      (.cons (.assignSlot A.tab Cp.f (Expr.var p) (linkIdxAlsFeld Cp i) hwT hLT) rest))

/-- **`let i = C[p] else voll;  C[p] = nil;  rest`** -- cut the `C` child `i` off the member `p`; the binder holds `i`. -/
def blattAus (C : LinkFeld A) (p : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') : Block D V l Γ Λ Λ' :=
  .narrow (Expr.umTyp C.hf (Expr.slot A.tab C.f (Expr.var p) hLT)) 0 (D.count A.tab - 1) voll
    (.cons (.assignSlot A.tab C.f (Expr.var (.there p)) (linkNil C) hwT hLT) rest)

end Block

section Bedeutung
variable (O : Orakel D) (passes : Nat)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {A : FreiForm D} (G : LinkKopf A)

/-- **`leaf in` leaves:** `Cp[p] = i`, both child places of `i` empty, every other place stays, the head stays, and the
    allocator's views stay. Needs `p ≠ i` (a member is not the slot hung below it). Valid for every continuation. -/
theorem blattEin_ausfuehren (Cp Co : LinkFeld A) (hd : Cp.f ≠ Co.f)
    (p i : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (rest : Block D V l Γ Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hpi : (ρ.get p).n ≠ (ρ.get i).n) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R (Block.blattEin Cp Co p i hwT hLT rest) σ ρ
          = execBlock (V := V) O passes R rest σ' ρ ∧
      LinkRahmen A [Cp.f, Co.f] [] σ σ' ∧
      Cp.wert σ' (ρ.get p).n = (ρ.get i).n ∧ Cp.wert σ' (ρ.get i).n = D.count A.tab ∧
      Co.wert σ' (ρ.get i).n = D.count A.tab ∧
      (∀ j, j ≠ (ρ.get p).n → j ≠ (ρ.get i).n → Cp.wert σ' j = Cp.wert σ j) ∧
      (∀ j, j ≠ (ρ.get i).n → Co.wert σ' j = Co.wert σ j) ∧ G.st σ' = G.st σ ∧
      A.kopfSt σ' = A.kopfSt σ ∧ (∀ j, A.naechst σ' j = A.naechst σ j) ∧ A.stand σ' = A.stand σ := by
  refine ⟨_, rfl, ?_, ?_⟩
  · refine ⟨fun C hC => funext fun j => ?_, fun G' _ => rfl⟩
    have h1 : C.f ≠ Cp.f := fun e => hC (by simp [e])
    have h2 : C.f ≠ Co.f := fun e => hC (by simp [e])
    simp [LinkFeld.wert, World.slots_schreibSlot_ne _ _ _ _ _ _ _ _ h1, World.slots_schreibSlot_ne _ _ _ _ _ _ _ _ h2]
  simp only [eval, Block.linkNil, Block.linkIdxAlsFeld, eval_umTyp, Expr.orte, orte_umTyp, List.nil_append,
    LinkKopf.st_schreibSlot, LinkKopf.st_lese, LinkFeld.wert_lese,
    FreiForm.kopfSt_schreibSlot, FreiForm.kopfSt_lese, ArenaForm.stand_lese, ArenaForm.stand_schreibSlot,
    A.naechst_schreibSlot_ne _ _ _ _ _ Cp.h2, A.naechst_schreibSlot_ne _ _ _ _ _ Co.h2, FreiForm.naechst_lese]
  refine ⟨?_, ?_, ?_, fun j hjp hji => ?_, fun j hji => ?_, trivial, trivial, fun _ => trivial, trivial⟩
  · rw [Cp.wert_schreibSlot_selbst]
    exact umTyp_rund_n Cp.hf _
  · simp only [Cp.wert_schreibSlot_anderer _ _ _ _ _ (Ne.symm hpi), LinkFeld.wert_lese,
      Co.wert_schreibSlot_feld Cp hd, Cp.wert_schreibSlot_selbst]
    exact umTyp_rund_n Cp.hf _
  · simp only [Cp.wert_schreibSlot_feld Co hd.symm, LinkFeld.wert_lese, Co.wert_schreibSlot_selbst]
    exact umTyp_rund_n Co.hf _
  · simp only [Cp.wert_schreibSlot_anderer _ _ _ _ _ hjp, LinkFeld.wert_lese,
      Co.wert_schreibSlot_feld Cp hd, Cp.wert_schreibSlot_anderer _ _ _ _ _ hji]
  · simp only [Cp.wert_schreibSlot_feld Co hd.symm, LinkFeld.wert_lese,
      Co.wert_schreibSlot_anderer _ _ _ _ _ hji]

/-- **`leaf out` leaves:** the binder holds `i = C[p]`, the `C` place of `p` is empty, no other place moves, the head
    stays, and the allocator's views stay. `i` must be a slot (`hi`). Valid for every continuation `rest`. -/
theorem blattAus_ausfuehren (C : LinkFeld A) (p : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hi : C.wert σ (ρ.get p).n < D.count A.tab) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock (V := V) O passes R (Block.blattAus C p hwT hLT voll rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons k ρ)).schrumpf ∧
      LinkRahmen A [C.f] [] σ σ' ∧
      k.n = C.wert σ (ρ.get p).n ∧ C.wert σ' (ρ.get p).n = D.count A.tab ∧
      (∀ j, j ≠ (ρ.get p).n → C.wert σ' j = C.wert σ j) ∧
      (∀ C' : LinkFeld A, C'.f ≠ C.f → ∀ j, C'.wert σ' j = C'.wert σ j) ∧ G.st σ' = G.st σ ∧
      A.kopfSt σ' = A.kopfSt σ ∧ (∀ j, A.naechst σ' j = A.naechst σ j) ∧ A.stand σ' = A.stand σ := by
  have hk : (0 : Int) ≤ C.wert σ (ρ.get p).n ∧ C.wert σ (ρ.get p).n ≤ D.count A.tab - 1 :=
    ⟨(Wert.umTyp C.hf (σ.slots A.tab (ρ.get p).n C.f)).lo_le, by omega⟩
  simp only [Block.blattAus, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte]
  rw [dif_pos (by exact hk)]
  refine ⟨?s, ?k, ?e, ?rh, ?n, ?r⟩
  case e => rfl
  case rh =>
    refine ⟨fun C' hC' => funext fun j => ?_, fun G' _ => rfl⟩
    have h1 : C'.f ≠ C.f := fun e => hC' (by simp [e])
    simp [LinkFeld.wert, World.slots_schreibSlot_ne _ _ _ _ _ _ _ _ h1]
  case n => rfl
  case r =>
    simp only [eval, Block.linkNil, eval_umTyp, Expr.orte, orte_umTyp, List.nil_append,
      LinkKopf.st_schreibSlot, LinkKopf.st_lese, LinkFeld.wert_lese, A.kopfSt_schreibSlot, FreiForm.naechst_lese,
      FreiForm.kopfSt_lese, ArenaForm.stand_lese, ArenaForm.stand_schreibSlot,
      A.naechst_schreibSlot_ne _ _ _ _ _ C.h2, Env.get_cons_there, Env.get_cons_here]
    refine ⟨?_, fun j hj => ?_, fun C' hC' j => ?_, trivial, trivial, fun _ => trivial, trivial⟩
    · exact (C.wert_schreibSlot_selbst _ _ _ _).trans (umTyp_rund_n C.hf _)
    · exact C.wert_schreibSlot_anderer _ _ _ _ _ hj
    · exact C.wert_schreibSlot_feld C' hC' _ _ _ _ _

/-! ## The tree invariant on the executed forms -/

/-- **Executed `leaf in` at the left keeps the tree.** `p` is a member with an empty left place, `i` is live and not in
    the tree (what `N586` and the walk establish). Afterwards `i` is a member, and the members are exactly the old ones
    and `i`. Valid for every continuation. -/
theorem baum_einfuegen_links_zug (Lf Rf : LinkFeld A) (hd : Lf.f ≠ Rf.f)
    (p i : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (rest : Block D V l Γ Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hok : A.FreiOk σ) (hb : BaumOk A Lf Rf G σ)
    (hp : InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) (ρ.get p).n)
    (hpl : Lf.wert σ (ρ.get p).n = D.count A.tab) (hi : A.Lebt σ (ρ.get i).n)
    (hnot : ¬ InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) (ρ.get i).n) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R (Block.blattEin Lf Rf p i hwT hLT rest) σ ρ
          = execBlock (V := V) O passes R rest σ' ρ ∧
      LinkRahmen A [Lf.f, Rf.f] [] σ σ' ∧
      BaumOk A Lf Rf G σ' ∧ InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') (ρ.get i).n ∧
      A.FreiOk σ' ∧ (∀ j, A.Lebt σ' j ↔ A.Lebt σ j) ∧
      (∀ j, InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') j ↔
        (j = (ρ.get i).n ∨ InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) j)) := by
  have hpi : (ρ.get p).n ≠ (ρ.get i).n := fun e => hnot (e ▸ hp)
  obtain ⟨σ', he, hrm, hlp, hli, hri, hol, hor, hg, hk, hn, hs⟩ :=
    blattEin_ausfuehren O passes R G Lf Rf hd p i hwT hLT rest σ ρ hpi
  obtain ⟨h1, h2⟩ := baum_einfuegen_links A Lf Rf G hb _ _ hp hpl hi hnot hk hn hs hg hlp hli hri hol hor
  have hc : (ρ.get i).n < D.count A.tab := by have := hi.2.1; have := A.stand_le σ; omega
  have hmem := einfuegen_mitglieder hb hp hpl hi.1 hc hnot hlp hli hri hol hor
  exact ⟨σ', he, hrm, h1, h2, A.freiOk_gleich hk hn hs hok, A.lebt_gleich hk hn hs, by rw [hg]; exact hmem⟩

/-- **Executed `leaf in` at the right keeps the tree** (the mirror). -/
theorem baum_einfuegen_rechts_zug (Lf Rf : LinkFeld A) (hd : Rf.f ≠ Lf.f)
    (p i : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (rest : Block D V l Γ Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hok : A.FreiOk σ) (hb : BaumOk A Lf Rf G σ)
    (hp : InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) (ρ.get p).n)
    (hpr : Rf.wert σ (ρ.get p).n = D.count A.tab) (hi : A.Lebt σ (ρ.get i).n)
    (hnot : ¬ InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) (ρ.get i).n) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R (Block.blattEin Rf Lf p i hwT hLT rest) σ ρ
          = execBlock (V := V) O passes R rest σ' ρ ∧
      LinkRahmen A [Rf.f, Lf.f] [] σ σ' ∧
      BaumOk A Lf Rf G σ' ∧ InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') (ρ.get i).n ∧
      A.FreiOk σ' ∧ (∀ j, A.Lebt σ' j ↔ A.Lebt σ j) ∧
      (∀ j, InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') j ↔
        (j = (ρ.get i).n ∨ InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) j)) := by
  have hpi : (ρ.get p).n ≠ (ρ.get i).n := fun e => hnot (e ▸ hp)
  obtain ⟨σ', he, hrm, hrp, hri, hli, hor, hol, hg, hk, hn, hs⟩ :=
    blattEin_ausfuehren O passes R G Rf Lf hd p i hwT hLT rest σ ρ hpi
  obtain ⟨h1, h2⟩ := baum_einfuegen_rechts A Lf Rf G hb _ _ hp hpr hi hnot hk hn hs hg hrp hri hli hor hol
  have hc : (ρ.get i).n < D.count A.tab := by have := hi.2.1; have := A.stand_le σ; omega
  have hmem := einfuegen_rechts_mitglieder hb hp hpr hi.1 hc hnot hrp hri hli hor hol
  exact ⟨σ', he, hrm, h1, h2, A.freiOk_gleich hk hn hs hok, A.lebt_gleich hk hn hs, by rw [hg]; exact hmem⟩

/-- **Executed `leaf out` at the left keeps the tree.** `p` is a member whose left child `i` is a leaf (both places
    empty). The binder holds `i`, which is live and no longer in the tree, so it may be released; the slot WAS in the
    tree and the new members are among the old ones. -/
theorem baum_blatt_aus_links_zug (Lf Rf : LinkFeld A) (hd : Rf.f ≠ Lf.f)
    (p : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hok : A.FreiOk σ) (hb : BaumOk A Lf Rf G σ)
    (hp : InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) (ρ.get p).n)
    (hi : Lf.wert σ (ρ.get p).n < D.count A.tab)
    (hll : Lf.wert σ (Lf.wert σ (ρ.get p).n) = D.count A.tab)
    (hrl : Rf.wert σ (Lf.wert σ (ρ.get p).n) = D.count A.tab) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock (V := V) O passes R (Block.blattAus Lf p hwT hLT voll rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons k ρ)).schrumpf ∧
      LinkRahmen A [Lf.f] [] σ σ' ∧
      k.n = Lf.wert σ (ρ.get p).n ∧ BaumOk A Lf Rf G σ' ∧ A.FreiOk σ' ∧ (∀ j, A.Lebt σ' j ↔ A.Lebt σ j) ∧
      ¬ InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') k.n ∧ A.Lebt σ' k.n ∧
      InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) k.n ∧
      (∀ j, InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') j →
        InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) j) := by
  obtain ⟨σ', k, he, hrm, hkn, hlp, hol, hoth, hg, hk, hn, hs⟩ :=
    blattAus_ausfuehren O passes R G Lf p hwT hLT voll rest σ ρ hi
  obtain ⟨h1, h2, h3⟩ := baum_blatt_aus_links A Lf Rf G hb _ _ hp rfl hi (hkn ▸ k.lo_le) hll hrl hk hn hs hg hlp hol
    (fun j => hoth Rf hd j)
  have hr : Rf.wert σ' = Rf.wert σ := funext fun j => hoth Rf hd j
  have hmem := blatt_aus_mitglieder hb hp rfl (hkn ▸ k.lo_le) hi hll hrl hlp hol
  have hin : InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) (Lf.wert σ (ρ.get p).n) := hp.links hi
  refine ⟨σ', k, he, hrm, hkn, h1, A.freiOk_gleich hk hn hs hok, A.lebt_gleich hk hn hs, hkn ▸ h2, hkn ▸ h3,
    hkn ▸ hin, fun j hj => ?_⟩
  rw [hr, hg] at hj
  exact (hmem j hj).1

/-- **Executed `leaf out` at the right keeps the tree** (the mirror). -/
theorem baum_blatt_aus_rechts_zug (Lf Rf : LinkFeld A) (hd : Lf.f ≠ Rf.f)
    (p : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hok : A.FreiOk σ) (hb : BaumOk A Lf Rf G σ)
    (hp : InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) (ρ.get p).n)
    (hi : Rf.wert σ (ρ.get p).n < D.count A.tab)
    (hll : Lf.wert σ (Rf.wert σ (ρ.get p).n) = D.count A.tab)
    (hrl : Rf.wert σ (Rf.wert σ (ρ.get p).n) = D.count A.tab) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock (V := V) O passes R (Block.blattAus Rf p hwT hLT voll rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons k ρ)).schrumpf ∧
      LinkRahmen A [Rf.f] [] σ σ' ∧
      k.n = Rf.wert σ (ρ.get p).n ∧ BaumOk A Lf Rf G σ' ∧ A.FreiOk σ' ∧ (∀ j, A.Lebt σ' j ↔ A.Lebt σ j) ∧
      ¬ InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') k.n ∧ A.Lebt σ' k.n ∧
      InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) k.n ∧
      (∀ j, InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') j →
        InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) j) := by
  obtain ⟨σ', k, he, hrm, hkn, hrp, hor, hoth, hg, hk, hn, hs⟩ :=
    blattAus_ausfuehren O passes R G Rf p hwT hLT voll rest σ ρ hi
  obtain ⟨h1, h2, h3⟩ := baum_blatt_aus_rechts A Lf Rf G hb _ _ hp rfl hi (hkn ▸ k.lo_le) hll hrl hk hn hs hg hrp hor
    (fun j => hoth Lf hd j)
  have hl : Lf.wert σ' = Lf.wert σ := funext fun j => hoth Lf hd j
  have hmem := blatt_aus_rechts_mitglieder hb hp rfl (hkn ▸ k.lo_le) hi hll hrl hrp hor
  have hin : InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) (Rf.wert σ (ρ.get p).n) := hp.rechts hi
  refine ⟨σ', k, he, hrm, hkn, h1, A.freiOk_gleich hk hn hs hok, A.lebt_gleich hk hn hs, hkn ▸ h2, hkn ▸ h3,
    hkn ▸ hin, fun j hj => ?_⟩
  rw [hl, hg] at hj
  exact (hmem j hj).1

end Bedeutung

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.blattEin_ausfuehren
#print axioms Gabbro.Grammatik.blattAus_ausfuehren
#print axioms Gabbro.Grammatik.baum_einfuegen_links_zug
#print axioms Gabbro.Grammatik.baum_einfuegen_rechts_zug
#print axioms Gabbro.Grammatik.baum_blatt_aus_links_zug
#print axioms Gabbro.Grammatik.baum_blatt_aus_rechts_zug
