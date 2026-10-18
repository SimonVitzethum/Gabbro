/-
  File:      Grammatik/ArenaErkennerZeuge.lean
  Subject:   THE RECOGNIZER ON A REAL ARENA (PLAN-DYNAMISCH.md section 8a.1, step (3)): bodies it ACCEPTS and RUNS, and
             planted defects it REJECTS, on the concrete four-slot arena of `ArenaDynZeuge.lean` (slot `1` on the free
             list, list `2 -> 0`).

  Accepted (witnesses, run from the real world `w0`):
    * `nimm_push`   -- take slot `1` off the free list and link it in at the head of the list: the list becomes
                       `1 -> 2 -> 0`, the invariant holds, and the recognizer derived it from the syntax;
    * `kopf_unlink_frei` -- read the head `2`, unlink its successor `0`, release it: the list is `2`, the free list is
                       `0 -> 1`.
  Rejected (planted defects, no derivation exists):
    * a double push (a linked slot is not owned any more),
    * a double release and a use after release (a released name is unknown, never owned),
    * a push of a parameter (nothing is known of it),
    * a store into a link field that is no move.
-/
import Grammatik.Bausteine.Arena.Struktur.ArenaErkennerBeweis
import Grammatik.Bausteine.Arena.Struktur.ArenaFormZeuge

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

namespace InvDynZeuge

/-- The index context of the bodies below: one index variable, so far. -/
abbrev G1 : Ctx := [Ty.index (FD.count FA.tab)]

/-- A body that takes a slot off the free list and links it in at the head of the list. -/
def nimmPush (voll : Endblock FD FV false [] []) : Block FD FV false [] [] [] :=
  Block.freiNimm FA sieben rfl fdarf rfl (fgdarf _) voll
    (Block.linkPush LL LG (.here : Var G1 _) rfl fdarf rfl (fgdarf _) .nil)

/-- **The recognizer accepts it** -- from a state that knows nothing. -/
theorem erk_nimmPush (voll : Endblock FD FV false [] []) (hv : Rein voll) :
    Erk FA LL LG Abs.leer (nimmPush voll) (((Abs.leer.ext .frei).set 0 .glied).tail) :=
  Erk.nimm sieben rfl fdarf rfl (fgdarf _) voll _ hv
    (Erk.push (.here : Var G1 _) rfl fdarf rfl (fgdarf _) .nil (by simp [Abs.ext, Var.pos]) (Erk.nil _))

/-- **Run on the real world:** the slot that came off the free list is the new head of the list, and the invariant
    holds -- as the recognizer promised. -/
theorem nimmPush_zeuge (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f) (voll : Endblock FD FV false [] []) (hv : Rein voll) :
    ∃ σ' : World FD, execBlock (V := FV) O passes R (nimmPush voll) w0 .nil = .ok σ' .nil ∧
      StrukturOk FA LL LG σ' ∧ LG.st σ' = 1 := by
  have hpost := erk_koerper O passes R FA LL LG (erk_nimmPush voll hv) w0 .nil ⟨freiOk_w0, listOk_w0⟩
  obtain ⟨σ1, k, he1, hkn, -⟩ := nimmAlloc_ausfuehren O passes R FA sieben rfl fdarf rfl (fgdarf _) voll
    (Block.linkPush LL LG (.here : Var G1 _) rfl fdarf rfl (fgdarf _) .nil) w0 .nil (by rw [kopf_w0]; decide) freiOk_w0
  obtain ⟨σ2, he2, hg2, -⟩ := linkPush_ausfuehren O passes R LL LG (V := FV) (l := false) (Γ := G1) (Λ := []) (Λ' := [])
    .here rfl fdarf rfl (fgdarf _) .nil σ1 (.cons k .nil)
  have hrun : execBlock (V := FV) O passes R (nimmPush voll) w0 .nil = .ok σ2 .nil := by
    unfold nimmPush
    rw [he1]
    simp only [Ausgang.schrumpf]
    rw [he2]
    rfl
  rw [hrun] at hpost
  exact ⟨σ2, hrun, hpost.1, by rw [hg2]; show k.n = 1; rw [hkn, kopf_w0]⟩

/-- The `else` branch of the bodies below: it returns, and stores nothing. -/
def voll0 : Endblock FD FV false [] [] := Endblock.ret ErgExpr.empty (List.Perm.refl _)

theorem rein_voll0 : Rein voll0 := Rein.ret _ _

/-- The same, in the context of one index variable. -/
def voll1 : Endblock FD FV false G1 [] := Endblock.ret ErgExpr.empty (List.Perm.refl _)

theorem rein_voll1 : Rein voll1 := Rein.ret _ _

/-- The index context after two binders. -/
abbrev G2 : Ctx := [Ty.index (FD.count FA.tab), Ty.index (FD.count FA.tab)]

/-- A body that reads the head, unlinks its successor and releases it. -/
def kopfUnlinkFrei : Block FD FV false [] [] [] :=
  Block.linkKopfBind LG (fgdarf _) voll0
    (Block.linkUnlink LL (.here : Var G1 _) rfl fdarf voll1
      (Block.freiVar FA (.here : Var G2 _) rfl fdarf rfl (fgdarf _) .nil))

/-- **The recognizer accepts it:** the head is a member, so its successor may be unlinked; the unlinked slot is owned,
    so it may be released. -/
theorem erk_kopfUnlinkFrei :
    Erk FA LL LG Abs.leer kopfUnlinkFrei
      ((((Abs.leer.ext .glied).entglied.ext .frei).set 0 .offen).tail.tail) :=
  Erk.kopf (fgdarf _) voll0 _ rein_voll0
    (Erk.unlink (.here : Var G1 _) rfl fdarf voll1 _ (by simp [Abs.ext, Var.pos]) rein_voll1
      (Erk.frei (.here : Var G2 _) rfl fdarf rfl (fgdarf _) .nil (by simp [Abs.entglied, Abs.ext, Var.pos])
        (Erk.nil _)))

/-- **Run on the real world:** the list `2 -> 0` becomes `2`, the slot `0` is released onto the free list, and the
    invariant holds. -/
theorem kopfUnlinkFrei_zeuge (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f) :
    ∃ σ' : World FD, execBlock (V := FV) O passes R kopfUnlinkFrei w0 .nil = .ok σ' .nil ∧
      StrukturOk FA LL LG σ' ∧ LL.wert σ' 2 = 4 ∧ FA.kopfSt σ' = 0 := by
  have hpost := erk_koerper O passes R FA LL LG erk_kopfUnlinkFrei w0 .nil ⟨freiOk_w0, listOk_w0⟩
  obtain ⟨k1, he1, hk1⟩ := linkKopfBind_ausfuehren O passes R LG (V := FV) (l := false) (Γ := []) (Λ := []) (Λ' := [])
    (fgdarf _) voll0
    (Block.linkUnlink LL (.here : Var G1 _) rfl fdarf voll1
      (Block.freiVar FA (.here : Var G2 _) rfl fdarf rfl (fgdarf _) .nil)) w0 .nil (by rw [lg_w0]; decide)
  have hk1' : k1.n = 2 := by rw [hk1, lg_w0]
  obtain ⟨σb, k2, he2, hk2, hg2, hnp, ho2, -⟩ := linkUnlink_ausfuehren O passes R LL LG (V := FV) (l := false)
    (Γ := G1) (Λ := []) (Λ' := []) (.here : Var G1 _) rfl fdarf voll1
    (Block.freiVar FA (.here : Var G2 _) rfl fdarf rfl (fgdarf _) .nil) (w0.lese [] [Sum.inr LG.g]) (.cons k1 .nil)
    (by show LL.wert w0 k1.n < 4; rw [hk1', ll_w0]; decide)
  obtain ⟨σc, he3, hkc, -, -, -, hf3⟩ := freiVar_ausfuehren O passes R FA (V := FV) (l := false) (Γ := G2) (Λ := [])
    (Λ' := []) .here rfl fdarf rfl (fgdarf _) .nil σb (.cons k2 (.cons k1 .nil))
  have hrun : execBlock (V := FV) O passes R kopfUnlinkFrei w0 .nil = .ok σc .nil := by
    unfold kopfUnlinkFrei
    rw [he1]
    simp only [Ausgang.schrumpf]
    rw [he2]
    simp only [Ausgang.schrumpf]
    rw [he3]
    rfl
  rw [hrun] at hpost
  have hk2' : k2.n = 0 := by
    have : k2.n = LL.wert w0 k1.n := hk2
    rw [this, hk1', ll_w0]; rfl
  refine ⟨σc, hrun, hpost.1, ?_, ?_⟩
  · have e1 : LL.wert σb k1.n = LL.wert w0 (LL.wert w0 k1.n) := hnp
    have e2 : LL.wert σc = LL.wert σb := LL.wert_fremd' hf3
    have e1' : LL.wert σb 2 = LL.wert w0 (LL.wert w0 2) := by rw [← hk1']; exact e1
    rw [e2, e1', ll_w0, ll_w0]
    simp [ln0]
  · have : FA.kopfSt σc = k2.n := hkc
    rw [this, hk2']

/-! ### Planted defects: bodies with no derivation -/

/-- An oracle for the witness declaration (it has no axioms and no registers, so every answer is vacuous). -/
def oF : Orakel FD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun _ _ => false

/-- A callee for the witness declaration (the bodies below call nothing). -/
def rF : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f := fun _ _ _ => .logik .vorzustand

/- **How a defect is rejected:** the recognizer is SOUND (`erk_koerper`), so a body that breaks the invariant in a real
    run has no derivation. The runs below are computed with the executed forms; each ends in a world that
    `liste_schleife_bricht`, `FreiForm.schleife_bricht` or `liste_freigegeben_bricht` rules out. -/

/-- The slot is linked in TWICE (after being taken off the free list). -/
def nimmPushPush : Block FD FV false [] [] [] :=
  Block.freiNimm FA sieben rfl fdarf rfl (fgdarf _) voll0
    (Block.linkPush LL LG (.here : Var G1 _) rfl fdarf rfl (fgdarf _)
      (Block.linkPush LL LG (.here : Var G1 _) rfl fdarf rfl (fgdarf _) .nil))

/-- **A double push has no derivation:** the slot is linked into itself, so no list exists. -/
theorem nimmPushPush_abgelehnt (a' : Abs) : ¬ Erk FA LL LG Abs.leer nimmPushPush a' := by
  intro h
  have hpost := erk_koerper oF 0 rF FA LL LG h w0 .nil ⟨freiOk_w0, listOk_w0⟩
  obtain ⟨σ1, k, he1, hkn, -⟩ := nimmAlloc_ausfuehren oF 0 rF FA sieben rfl fdarf rfl (fgdarf _) voll0
    (Block.linkPush LL LG (.here : Var G1 _) rfl fdarf rfl (fgdarf _)
      (Block.linkPush LL LG (.here : Var G1 _) rfl fdarf rfl (fgdarf _) .nil)) w0 .nil
    (by rw [kopf_w0]; decide) freiOk_w0
  obtain ⟨σ2, he2, hg2, -⟩ := linkPush_ausfuehren oF 0 rF LL LG (V := FV) (l := false) (Γ := G1) (Λ := []) (Λ' := [])
    .here rfl fdarf rfl (fgdarf _)
    (Block.linkPush LL LG (.here : Var G1 _) rfl fdarf rfl (fgdarf _) .nil) σ1 (.cons k .nil)
  obtain ⟨σ3, he3, hg3, hli3, -⟩ := linkPush_ausfuehren oF 0 rF LL LG (V := FV) (l := false) (Γ := G1) (Λ := [])
    (Λ' := []) .here rfl fdarf rfl (fgdarf _) .nil σ2 (.cons k .nil)
  have hrun : execBlock (V := FV) oF 0 rF nimmPushPush w0 .nil = .ok σ3 .nil := by
    unfold nimmPushPush
    rw [he1]
    simp only [Ausgang.schrumpf]
    rw [he2, he3]
    rfl
  rw [hrun] at hpost
  have hk3 : k.n < 4 := by have := k.le_hi; have hc : FD.count FA.tab = 4 := rfl; show k.n < 4; omega
  have hg2' : LG.st σ2 = k.n := hg2
  have hg3' : LG.st σ3 = k.n := hg3
  have hli3' : LL.wert σ3 k.n = LG.st σ2 := hli3
  exact liste_schleife_bricht FA LL LG σ3 k.n hk3 hg3' (by rw [hli3', hg2']) hpost.1.2

/-- A slot is released TWICE. -/
def nimmFreiFrei : Block FD FV false [] [] [] :=
  Block.freiNimm FA sieben rfl fdarf rfl (fgdarf _) voll0
    (Block.freiVar FA (.here : Var G1 _) rfl fdarf rfl (fgdarf _)
      (Block.freiVar FA (.here : Var G1 _) rfl fdarf rfl (fgdarf _) .nil))

/-- **A double release has no derivation:** the second release makes the head of the free list link to itself. -/
theorem nimmFreiFrei_abgelehnt (a' : Abs) : ¬ Erk FA LL LG Abs.leer nimmFreiFrei a' := by
  intro h
  have hpost := erk_koerper oF 0 rF FA LL LG h w0 .nil ⟨freiOk_w0, listOk_w0⟩
  obtain ⟨σ1, k, he1, hkn, -⟩ := nimmAlloc_ausfuehren oF 0 rF FA sieben rfl fdarf rfl (fgdarf _) voll0
    (Block.freiVar FA (.here : Var G1 _) rfl fdarf rfl (fgdarf _)
      (Block.freiVar FA (.here : Var G1 _) rfl fdarf rfl (fgdarf _) .nil)) w0 .nil
    (by rw [kopf_w0]; decide) freiOk_w0
  obtain ⟨σ2, he2, hk2, -⟩ := freiVar_ausfuehren oF 0 rF FA (V := FV) (l := false) (Γ := G1) (Λ := []) (Λ' := [])
    .here rfl fdarf rfl (fgdarf _)
    (Block.freiVar FA (.here : Var G1 _) rfl fdarf rfl (fgdarf _) .nil) σ1 (.cons k .nil)
  obtain ⟨σ3, he3, hk3, hn3, -⟩ := freiVar_ausfuehren oF 0 rF FA (V := FV) (l := false) (Γ := G1) (Λ := [])
    (Λ' := []) .here rfl fdarf rfl (fgdarf _) .nil σ2 (.cons k .nil)
  have hrun : execBlock (V := FV) oF 0 rF nimmFreiFrei w0 .nil = .ok σ3 .nil := by
    unfold nimmFreiFrei
    rw [he1]
    simp only [Ausgang.schrumpf]
    rw [he2, he3]
    rfl
  rw [hrun] at hpost
  have hkl : k.n < 4 := by have := k.le_hi; have hc : FD.count FA.tab = 4 := rfl; show k.n < 4; omega
  have hk2' : FA.kopfSt σ2 = k.n := hk2
  have hk3' : FA.kopfSt σ3 = k.n := hk3
  have hn3' : FA.naechst σ3 k.n = FA.kopfSt σ2 := hn3
  exact FreiForm.schleife_bricht FA σ3 k.n hkl hk3' (by rw [hn3', hk2']) hpost.1.1

/-- A slot is linked in AFTER it was released. -/
def nimmFreiPush : Block FD FV false [] [] [] :=
  Block.freiNimm FA sieben rfl fdarf rfl (fgdarf _) voll0
    (Block.freiVar FA (.here : Var G1 _) rfl fdarf rfl (fgdarf _)
      (Block.linkPush LL LG (.here : Var G1 _) rfl fdarf rfl (fgdarf _) .nil))

/-- **A use after release has no derivation:** the released slot is the head of the free list AND of the list, and a
    list slot must be live. -/
theorem nimmFreiPush_abgelehnt (a' : Abs) : ¬ Erk FA LL LG Abs.leer nimmFreiPush a' := by
  intro h
  have hpost := erk_koerper oF 0 rF FA LL LG h w0 .nil ⟨freiOk_w0, listOk_w0⟩
  obtain ⟨σ1, k, he1, hkn, -⟩ := nimmAlloc_ausfuehren oF 0 rF FA sieben rfl fdarf rfl (fgdarf _) voll0
    (Block.freiVar FA (.here : Var G1 _) rfl fdarf rfl (fgdarf _)
      (Block.linkPush LL LG (.here : Var G1 _) rfl fdarf rfl (fgdarf _) .nil)) w0 .nil
    (by rw [kopf_w0]; decide) freiOk_w0
  obtain ⟨σ2, he2, hk2, -⟩ := freiVar_ausfuehren oF 0 rF FA (V := FV) (l := false) (Γ := G1) (Λ := []) (Λ' := [])
    .here rfl fdarf rfl (fgdarf _)
    (Block.linkPush LL LG (.here : Var G1 _) rfl fdarf rfl (fgdarf _) .nil) σ1 (.cons k .nil)
  obtain ⟨σ3, he3, hg3, -, -, hk3, -, -⟩ := linkPush_ausfuehren oF 0 rF LL LG (V := FV) (l := false) (Γ := G1) (Λ := [])
    (Λ' := []) .here rfl fdarf rfl (fgdarf _) .nil σ2 (.cons k .nil)
  have hrun : execBlock (V := FV) oF 0 rF nimmFreiPush w0 .nil = .ok σ3 .nil := by
    unfold nimmFreiPush
    rw [he1]
    simp only [Ausgang.schrumpf]
    rw [he2, he3]
    rfl
  rw [hrun] at hpost
  have hkl : k.n < 4 := by have := k.le_hi; have hc : FD.count FA.tab = 4 := rfl; show k.n < 4; omega
  have hk2' : FA.kopfSt σ2 = k.n := hk2
  have hg3' : LG.st σ3 = k.n := hg3
  have hhead : FA.kopfSt σ3 = k.n := by rw [hk3]; exact hk2'
  have hauf : FA.AufListe σ3 (LG.st σ3) := by
    rw [hg3', ← hhead]
    exact FreiForm.aufListe_kopf FA hpost.1.1 (by rw [hhead]; exact hkl)
  exact liste_freigegeben_bricht FA LL LG σ3 (by rw [hg3']; exact hkl) hauf hpost.1.2

/-- A push of a slot the body does not own: a parameter that is already a member of the list. -/
def pushFremd : Block FD FV false G1 [] [] :=
  Block.linkPush LL LG (.here : Var G1 _) rfl fdarf rfl (fgdarf _) .nil

/-- **A push of a slot the body does not own has no derivation:** run on the member `2`, it links `2` into itself. -/
theorem pushFremd_abgelehnt (a' : Abs) : ¬ Erk FA LL LG Abs.leer pushFremd a' := by
  intro h
  have hpost := erk_koerper oF 0 rF FA LL LG h w0 rho2 ⟨freiOk_w0, listOk_w0⟩
  obtain ⟨σ1, he1, hg1, hli1, -⟩ := linkPush_ausfuehren oF 0 rF LL LG (V := FV) (l := false) (Γ := G1) (Λ := [])
    (Λ' := []) .here rfl fdarf rfl (fgdarf _) .nil w0 rho2
  have hrun : execBlock (V := FV) oF 0 rF pushFremd w0 rho2 = .ok σ1 rho2 := by
    unfold pushFremd; rw [he1]; rfl
  rw [hrun] at hpost
  have hg1' : LG.st σ1 = 2 := hg1
  have hli1' : LL.wert σ1 2 = LG.st w0 := hli1
  exact liste_schleife_bricht FA LL LG σ1 2 (by decide) hg1' (by rw [hli1', lg_w0]) hpost.1.2

/-- The first witness, instantiated: a real oracle, a real `else`, a real run. -/
theorem nimmPush_konkret : ∃ σ' : World FD, execBlock (V := FV) oF 0 rF (nimmPush voll0) w0 .nil = .ok σ' .nil ∧
    StrukturOk FA LL LG σ' ∧ LG.st σ' = 1 :=
  nimmPush_zeuge oF 0 rF voll0 rein_voll0

/-- The second witness, instantiated. -/
theorem kopfUnlinkFrei_konkret : ∃ σ' : World FD, execBlock (V := FV) oF 0 rF kopfUnlinkFrei w0 .nil = .ok σ' .nil ∧
    StrukturOk FA LL LG σ' ∧ LL.wert σ' 2 = 4 ∧ FA.kopfSt σ' = 0 :=
  kopfUnlinkFrei_zeuge oF 0 rF

end InvDynZeuge

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.InvDynZeuge.erk_nimmPush
#print axioms Gabbro.Grammatik.InvDynZeuge.nimmPush_konkret
#print axioms Gabbro.Grammatik.InvDynZeuge.erk_kopfUnlinkFrei
#print axioms Gabbro.Grammatik.InvDynZeuge.kopfUnlinkFrei_konkret
#print axioms Gabbro.Grammatik.InvDynZeuge.nimmPushPush_abgelehnt
#print axioms Gabbro.Grammatik.InvDynZeuge.nimmFreiFrei_abgelehnt
#print axioms Gabbro.Grammatik.InvDynZeuge.nimmFreiPush_abgelehnt
#print axioms Gabbro.Grammatik.InvDynZeuge.pushFremd_abgelehnt
