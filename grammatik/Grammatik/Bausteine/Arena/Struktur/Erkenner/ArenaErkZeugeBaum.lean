/-
  File:      Grammatik/ArenaErkZeugeBaum.lean
  Subject:   THE RECOGNIZER ON A REAL ARENA, TREE HALF (PLAN-DYNAMISCH.md section 8a.1, third pass): tree bodies it
             ACCEPTS and RUNS, and planted defects it REJECTS, on the concrete four-slot arena of `ArenaDynZeuge.lean`
             (slot `1` on the free list), declared as an arena with a tree and no list (`KB`: left child = field `2`,
             right child = field `3`, root = word `3`).

  Two worlds: `w0` (the tree `2 (left 0)`) and `w3` (the single node `3`). The bodies are RUN by evaluation (`rfl`), the
  invariant of the world they end in is the recognizer's promise (`erk_koerper`), and each defect ends in a world that a
  theorem of `ArenaErkennerLemmas.lean` rules out, so no derivation can exist:

  Accepted (witnesses, run from the real world):
    * `baumHang`   -- take slot `1` off the free list, read the root `2`, hang the slot at the (empty) right place:
                      the tree is `2 (left 0, right 1)`;
    * `baumSchnitt` -- read the root `2`, cut its leaf child `0` off, release it: the tree is `2`, the free list `0 -> 1`.
  Rejected (planted defects):
    * `doppelHang`  -- one slot hung at BOTH places of the root (a double hang),
    * `fremdHang`   -- the root hung below itself (a slot the body does not own),
    * `frischFrei`  -- a slot released and then hung (use after release).
-/
import Grammatik.Bausteine.Arena.Struktur.Erkenner.ArenaErkennerZeuge

-- v4.35: this linter exceeds its heartbeat budget on the long executed-block proofs below.
set_option linter.constructorNameAsVariable false

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

namespace InvDynZeuge

/-- **The arena of these witnesses carries the tree, and no list.** -/
def KB : Dekl FA where
  liste := none
  baum := some ⟨LL, RR, LG, by decide⟩
  getrennt := fun _ _ h => by cases h

/-- The scenario world `w0` meets the invariant of the arena (the tree `2 (left 0)`). -/
theorem ok_w0B : KB.Ok w0 :=
  ⟨freiOk_w0, Dekl.LOk_none (K := KB) rfl w0,
    (Dekl.BOk_some (K := KB) (b := ⟨LL, RR, LG, by decide⟩) rfl w0).mpr baumOk_w0,
    fun j hj => Dekl.InL_none (K := KB) rfl w0 j hj.1⟩

/-- A world that meets the arena invariant has a well formed tree. -/
theorem baumOk_von {σ : World FD} (h : KB.Ok σ) : BaumOk FA LL RR LG σ :=
  (Dekl.BOk_some (K := KB) (b := ⟨LL, RR, LG, by decide⟩) rfl σ).mp h.2.2.1

/-! ### The second world: the single node `3` -/

def lnN : Int → Int := fun _ => 4

/-- Slot `1` on the free list, the tree is the single node `3`. -/
def w3 : World FD := wd 4 1 3 nx0 lnN lnN

theorem lg_w3 : LG.st w3 = 3 := rfl
theorem ll_w3 (j : Int) : LL.wert w3 j = 4 := by show max 0 (min 4 (lnN j)) = 4; unfold lnN; decide
theorem rr_w3 (j : Int) : RR.wert w3 j = 4 := by show max 0 (min 4 (lnN j)) = 4; unfold lnN; decide

theorem freiOk_w3 : FA.FreiOk w3 :=
  FreiForm.freiOk_gleich FA (σ := w0) (σ' := w3) rfl (fun _ => rfl) rfl freiOk_w0

theorem lebt_w3 (i : Int) : FA.Lebt w3 i ↔ (0 ≤ i ∧ i < 4 ∧ i ≠ 1) := by
  rw [FreiForm.lebt_gleich FA (σ := w0) (σ' := w3) rfl (fun _ => rfl) rfl i]
  exact lebt_w0 i

theorem baumOk_w3 : BaumOk FA LL RR LG w3 := by
  unfold BaumOk
  rw [lg_w3]
  refine ⟨[3], ?_, by decide, ?_⟩
  · have := BaumF.node (c := 4) (l := LL.wert w3) (r := RR.wert w3) 3 (by decide) (by decide) [] []
      (by rw [ll_w3]; exact BaumF.nil) (by rw [rr_w3]; exact BaumF.nil)
    simpa using this
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    exact (lebt_w3 3).mpr (by decide)

theorem ok_w3 : KB.Ok w3 :=
  ⟨freiOk_w3, Dekl.LOk_none (K := KB) rfl w3,
    (Dekl.BOk_some (K := KB) (b := ⟨LL, RR, LG, by decide⟩) rfl w3).mpr baumOk_w3,
    fun j hj => Dekl.InL_none (K := KB) rfl w3 j hj.1⟩

/-! ### The contexts and the `else` branches of the bodies -/

/-- The index context after two binders. -/
abbrev G2' : Ctx := [Ty.index (FD.count FA.tab), Ty.index (FD.count FA.tab)]

def vollG2 : Endblock FD FV false G2' [] := Endblock.ret ErgExpr.empty (List.Perm.refl _)

theorem rein_vollG2 : Rein vollG2 := Rein.ret _ _

/-! ### Accepted: hang a slot -/

/-- Take slot `1` off the free list, read the root, hang the slot at the right place of the root. -/
def baumHang : Block FD FV false [] [] [] :=
  Block.freiNimm FA sieben rfl fdarf rfl (fgdarf _) voll0
    (Block.linkKopfBind LG (fgdarf _) voll1
      (Block.haengen RR LL (.here : Var G2' _) (.there .here : Var G2' _) rfl fdarf vollG2 .nil))

/-- **The recognizer accepts it** -- from a state that knows nothing. -/
theorem erk_baumHang : ∃ a' : Abs, Erk KB Abs.leer baumHang a' :=
  ⟨_, Erk.nimm sieben rfl fdarf rfl (fgdarf _) voll0 _ rein_voll0
    (Erk.wurzelKopf ⟨LL, RR, LG, by decide⟩ rfl (fgdarf _) voll1 _ rein_voll1
      (Erk.haengen ⟨LL, RR, LG, by decide⟩ rfl RR LL (Or.inr ⟨rfl, rfl⟩) (.here : Var G2' _)
        (.there .here : Var G2' _) rfl fdarf vollG2 .nil (by simp [Abs.ext, Var.pos])
        (by simp [Abs.ext, Var.pos]) rein_vollG2 (Erk.nil _)))⟩

set_option maxHeartbeats 1000000 in
/-- **Run on the real world:** the tree `2 (left 0)` gets the right child `1` (the slot that came off the free list),
    the free list is empty, and the invariant holds -- as the recognizer promised. -/
theorem baumHang_zeuge : ∃ σ' : World FD, execBlock (V := FV) oF 0 rF baumHang w0 .nil = .ok σ' .nil ∧
    KB.Ok σ' ∧ RR.wert σ' 2 = 1 ∧ LL.wert σ' 2 = 0 ∧ FA.kopfSt σ' = 4 := by
  obtain ⟨σ', hrun, hf⟩ : ∃ σ' : World FD, execBlock (V := FV) oF 0 rF baumHang w0 .nil = .ok σ' .nil ∧
      (RR.wert σ' 2 = 1 ∧ LL.wert σ' 2 = 0 ∧ FA.kopfSt σ' = 4) := ⟨_, rfl, by decide +kernel⟩
  obtain ⟨a', h⟩ := erk_baumHang
  have hpost := erk_koerper oF 0 rF KB h w0 .nil ok_w0B
  rw [hrun] at hpost
  exact ⟨σ', hrun, hpost.1, hf⟩

/-! ### Accepted: cut a leaf off and release it -/

/-- Read the root `2`, cut its left child (the leaf `0`) off, release it. -/
def baumSchnitt : Block FD FV false [] [] [] :=
  Block.linkKopfBind LG (fgdarf _) voll0
    (Block.abschneiden LL RR LL (.here : Var G1 _) rfl fdarf voll1 vollG2
      (Block.freiVar FA (.here : Var G2' _) rfl fdarf rfl (fgdarf _) .nil))

theorem erk_baumSchnitt : ∃ a' : Abs, Erk KB Abs.leer baumSchnitt a' :=
  ⟨_, Erk.wurzelKopf ⟨LL, RR, LG, by decide⟩ rfl (fgdarf _) voll0 _ rein_voll0
    (Erk.abschneiden ⟨LL, RR, LG, by decide⟩ rfl LL (Or.inl rfl) (.here : Var G1 _) rfl fdarf voll1 vollG2 _
      (by simp [Abs.ext, Var.pos]) rein_voll1 rein_vollG2
      (Erk.frei (.here : Var G2' _) rfl fdarf rfl (fgdarf _) .nil
        (by simp [Abs.ext, Var.pos]) (Erk.nil _)))⟩

/-- **Run on the real world:** the leaf `0` leaves the tree and goes onto the free list; the tree is the root alone. -/
theorem baumSchnitt_zeuge : ∃ σ' : World FD, execBlock (V := FV) oF 0 rF baumSchnitt w0 .nil = .ok σ' .nil ∧
    KB.Ok σ' ∧ LL.wert σ' 2 = 4 ∧ FA.kopfSt σ' = 0 ∧ FA.naechst σ' 0 = 1 := by
  obtain ⟨σ', hrun, hf⟩ : ∃ σ' : World FD, execBlock (V := FV) oF 0 rF baumSchnitt w0 .nil = .ok σ' .nil ∧
      (LL.wert σ' 2 = 4 ∧ FA.kopfSt σ' = 0 ∧ FA.naechst σ' 0 = 1) := ⟨_, rfl, by decide⟩
  obtain ⟨a', h⟩ := erk_baumSchnitt
  have hpost := erk_koerper oF 0 rF KB h w0 .nil ok_w0B
  rw [hrun] at hpost
  exact ⟨σ', hrun, hpost.1, hf⟩

/-! ### Planted defects: bodies with no derivation

  The defect bodies take their slots as PARAMETERS, so the recognizer starts from a state that knows nothing about them
  (every position `offen`) and the soundness theorem applies to every environment. A derivation of such a body would
  promise the invariant at the end of every run; the run below, from a real environment, ends in a world that a theorem
  of `ArenaErkennerLemmas.lean` rules out. -/

/-- The environment of two parameters: the root `3` and the live slot `2`, which is in no structure. -/
def rho32 : Env FD G2' := .cons (idx 3 (by decide) (by decide)) (.cons (idx 2 (by decide) (by decide)) .nil)

/-- The environment of one parameter: the root `3`. -/
def rho3' : Env FD G1 := .cons (idx 3 (by decide) (by decide)) .nil

/-- **One slot hung at BOTH places of the root.** -/
def doppelHang : Block FD FV false G2' [] [] :=
  Block.haengen RR LL (.here : Var G2' _) (.there .here : Var G2' _) rfl fdarf vollG2
    (Block.haengen LL RR (.here : Var G2' _) (.there .here : Var G2' _) rfl fdarf vollG2 .nil)

/-- **A double hang has no derivation:** run on the single node `3` with the live slot `2`, it makes slot `2` both children
    of `3`, so the slot occurs twice in the shape of the tree. -/
theorem doppelHang_abgelehnt (a' : Abs) : ¬ Erk KB Abs.leer doppelHang a' := by
  intro h
  have hpost := erk_koerper oF 0 rF KB h w3 rho32 ok_w3
  obtain ⟨σ', hrun, hf⟩ : ∃ σ' : World FD, execBlock (V := FV) oF 0 rF doppelHang w3 rho32 = .ok σ' rho32 ∧
      (LG.st σ' = 3 ∧ LL.wert σ' 3 = 2 ∧ RR.wert σ' 3 = 2 ∧ LL.wert σ' 2 = 4 ∧ RR.wert σ' 2 = 4) :=
    ⟨_, rfl, by decide⟩
  rw [hrun] at hpost
  exact baum_doppelkind_bricht FA LL RR LG σ' 3 2 (by decide) hf.1 hf.2.1 hf.2.2.1 (by decide) hf.2.2.2.1
    hf.2.2.2.2 (baumOk_von hpost.1)

/-- **The root hung below itself:** a slot the body does not own (it is a member of the tree). -/
def fremdHang : Block FD FV false G1 [] [] :=
  Block.haengen RR LL (.here : Var G1 _) (.here : Var G1 _) rfl fdarf voll1 .nil

/-- **Hanging a slot the body does not own has no derivation:** run on the single node `3` with the parameter `3`, it
    makes `3` its own right child, and no finite tree exists. -/
theorem fremdHang_abgelehnt (a' : Abs) : ¬ Erk KB Abs.leer fremdHang a' := by
  intro h
  have hpost := erk_koerper oF 0 rF KB h w3 rho3' ok_w3
  obtain ⟨σ', hrun, hf⟩ : ∃ σ' : World FD, execBlock (V := FV) oF 0 rF fremdHang w3 rho3' = .ok σ' rho3' ∧
      (LG.st σ' = 3 ∧ RR.wert σ' 3 = 3) := ⟨_, rfl, by decide⟩
  rw [hrun] at hpost
  exact baum_schleife_rechts_bricht FA LL RR LG σ' 3 (by decide) hf.1 hf.2 (baumOk_von hpost.1)

/-- **A slot released and then hung:** use after release. -/
def frischFrei : Block FD FV false G2' [] [] :=
  Block.freiVar FA (.there .here : Var G2' _) rfl fdarf rfl (fgdarf _)
    (Block.haengen RR LL (.here : Var G2' _) (.there .here : Var G2' _) rfl fdarf vollG2 .nil)

/-- **A use after release has no derivation:** run on the single node `3` with the live slot `2`, the released slot `2`
    (the head of the free list) becomes the right child of `3`, and a member of the tree must be live. -/
theorem frischFrei_abgelehnt (a' : Abs) : ¬ Erk KB Abs.leer frischFrei a' := by
  intro h
  have hpost := erk_koerper oF 0 rF KB h w3 rho32 ok_w3
  obtain ⟨σ', hrun, hf⟩ : ∃ σ' : World FD, execBlock (V := FV) oF 0 rF frischFrei w3 rho32 = .ok σ' rho32 ∧
      (LG.st σ' = 3 ∧ RR.wert σ' 3 = 2 ∧ FA.kopfSt σ' = 2) := ⟨_, rfl, by decide⟩
  rw [hrun] at hpost
  have hb := baumOk_von hpost.1
  have hin : InBaum 4 (LL.wert σ') (RR.wert σ') (LG.st σ') 2 := by
    have hb3 : BaumOkF 4 (LL.wert σ') (RR.wert σ') 3 (FA.Lebt σ') := by
      have := hb; unfold BaumOk at this; rwa [hf.1] at this
    have hroot : InBaum 4 (LL.wert σ') (RR.wert σ') (LG.st σ') 3 := by
      rw [hf.1]; exact ArenaKette.InBaum.wurzel hb3 (by decide)
    have := hroot.rechts (by rw [hf.2.1]; decide)
    rwa [hf.2.1] at this
  have hlebt := BaumOkF.lebt_in hb hin
  have hauf : FA.AufListe σ' 2 := by
    rw [← hf.2.2]
    exact FreiForm.aufListe_kopf FA hpost.1.1 (by rw [hf.2.2]; decide)
  exact hlebt.2.2 hauf

end InvDynZeuge

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.InvDynZeuge.erk_baumHang
#print axioms Gabbro.Grammatik.InvDynZeuge.baumHang_zeuge
#print axioms Gabbro.Grammatik.InvDynZeuge.erk_baumSchnitt
#print axioms Gabbro.Grammatik.InvDynZeuge.baumSchnitt_zeuge
#print axioms Gabbro.Grammatik.InvDynZeuge.doppelHang_abgelehnt
#print axioms Gabbro.Grammatik.InvDynZeuge.fremdHang_abgelehnt
#print axioms Gabbro.Grammatik.InvDynZeuge.frischFrei_abgelehnt
