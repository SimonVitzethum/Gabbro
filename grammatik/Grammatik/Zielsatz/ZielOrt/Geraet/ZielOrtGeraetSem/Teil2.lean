module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetSem.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Mono
variable {K K' : Nat → Bool} {Rg Rg' : D.Reg → Bool} (hKK : ∀ n, K n = true → K' n = true)
include hKK

mutual

theorem Stmt.gOk_mono {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → s.gOk K Rg = true → (∀ r ∈ s.regs, Rg' r = true) →
      s.gOk K' Rg' = true
  | .ite _ t e, h, hr => by
      simp only [Stmt.gOk, Stmt.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Block.gOk_mono t h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono e h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .onOption _ p a, h, hr => by
      simp only [Stmt.gOk, Stmt.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Block.gOk_mono p h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono a h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .onTag _ arms, h, hr => by
      simp only [Stmt.gOk, Stmt.regs] at h hr ⊢
      exact Arms.gOk_mono arms h hr
  | .onWhy _ arms, h, hr => by
      simp only [Stmt.gOk, Stmt.regs] at h hr ⊢
      exact GrundArms.gOk_mono arms h hr
  | .locks _ _ body, h, hr => by
      simp only [Stmt.gOk, Stmt.regs] at h hr ⊢
      exact Block.gOk_mono body h hr
  | .breaking _ body, h, hr => by
      simp only [Stmt.gOk, Stmt.regs] at h hr ⊢
      exact Block.gOk_mono body h hr
  | .traverse _ _ body, h, hr => by
      simp only [Stmt.gOk, Stmt.regs] at h hr ⊢
      exact Block.gOk_mono body h hr
  | .consumeTraverse _ _ _ _ _ _ body, h, hr => by
      simp only [Stmt.gOk, Stmt.regs] at h hr ⊢
      exact Block.gOk_mono body h hr
  | .retry _ _ body ueber, h, hr => by
      simp only [Stmt.gOk, Stmt.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Block.gOk_mono body h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono ueber h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .forever _ _ body, h, hr => by
      simp only [Stmt.gOk, Stmt.regs] at h hr ⊢
      exact Block.gOk_mono body h hr
  | .callInd .., h, _ => by
      simp only [Stmt.gOk] at h ⊢
      exact hKK _ h
  | .assignSlot .., _, _ => rfl
  | .assignThru .., _, _ | .assignSlotRef .., _, _ => rfl
  | .assignGlob .., _, _ => rfl
  | .putBytes .., _, _ => rfl
  | .assignVar .., _, _ => rfl
  | .shift .., _, _ => rfl
  | .call .., _, _ => rfl
  | .axiomCall .., _, _ => rfl
  | .regWrite .., _, _ => rfl
  | .transition .., _, _ => rfl
  | .publish .., _, _ => rfl
  | .advances .., _, _ => rfl
  | .retires .., _, _ => rfl
  | .ret .., _, _ => rfl
  | .retWhy .., _, _ => rfl
  | .retScoped .., _, _ => rfl
  | .retWhyScoped .., _, _ => rfl
  | .leave .., _, _ => rfl
  | .next .., _, _ => rfl

theorem Block.gOk_mono {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → b.gOk K Rg = true → (∀ r ∈ b.regs, Rg' r = true) →
      b.gOk K' Rg' = true
  | .nil, _, _ => rfl
  | .cons s rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Stmt.gOk_mono s h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .bind _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .bindCall _ _ _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .bindCallInd _ _ _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true] at h hr ⊢
      exact ⟨hKK _ h.1, Block.gOk_mono rest h.2 hr⟩
  | .bindCallElse _ _ _ _ _ err rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Endblock.gOk_mono err h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Endblock.gOk_mono err h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .bindAxiom _ _ _ _ _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .regRead r _ rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true, List.mem_cons] at h hr ⊢
      exact ⟨hr r (Or.inl rfl), Block.gOk_mono rest h.2 (fun r' h' => hr r' (Or.inr h'))⟩
  | .regReadElse r _ _ sonst rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true, List.mem_cons, List.mem_append]
        at h hr ⊢
      exact ⟨hr r (Or.inl rfl),
        Endblock.gOk_mono sonst h.2.1 (fun r' h' => hr r' (Or.inr (Or.inl h'))),
        Block.gOk_mono rest h.2.2 (fun r' h' => hr r' (Or.inr (Or.inr h')))⟩
  | .awaits _ _ _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .exchange _ _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .narrow _ _ _ sonst rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Endblock.gOk_mono sonst h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .narrowRequired _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .check _ sonst rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Endblock.gOk_mono sonst h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .float _ _ _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .floatLit _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .floatOf _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .floatNarrow _ _ _ sonst rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Endblock.gOk_mono sonst h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩

theorem Endblock.gOk_mono {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → e.gOk K Rg = true → (∀ r ∈ e.regs, Rg' r = true) →
      e.gOk K' Rg' = true
  | .ret .., _, _ => rfl
  | .retWhy .., _, _ => rfl
  | .retScoped .., _, _ => rfl
  | .retWhyScoped .., _, _ => rfl
  | .leave .., _, _ => rfl
  | .next .., _, _ => rfl
  | .cons s rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Stmt.gOk_mono s h.1 (fun r h' => hr r (Or.inl h')),
        Endblock.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .bind _ rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs] at h hr ⊢
      exact Endblock.gOk_mono rest h hr
  | .bindCall _ _ _ _ _ rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs] at h hr ⊢
      exact Endblock.gOk_mono rest h hr
  | .bindCallElse _ _ _ _ _ err rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Endblock.gOk_mono err h.1 (fun r h' => hr r (Or.inl h')),
        Endblock.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .bindAxiom _ _ _ _ _ _ _ rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs] at h hr ⊢
      exact Endblock.gOk_mono rest h hr
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Endblock.gOk_mono err h.1 (fun r h' => hr r (Or.inl h')),
        Endblock.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .regRead r _ rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs, Bool.and_eq_true, List.mem_cons] at h hr ⊢
      exact ⟨hr r (Or.inl rfl), Endblock.gOk_mono rest h.2 (fun r' h' => hr r' (Or.inr h'))⟩
  | .regReadElse r _ _ sonst rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs, Bool.and_eq_true, List.mem_cons, List.mem_append]
        at h hr ⊢
      exact ⟨hr r (Or.inl rfl),
        Endblock.gOk_mono sonst h.2.1 (fun r' h' => hr r' (Or.inr (Or.inl h'))),
        Endblock.gOk_mono rest h.2.2 (fun r' h' => hr r' (Or.inr (Or.inr h')))⟩
  | .awaits _ _ _ _ _ rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs] at h hr ⊢
      exact Endblock.gOk_mono rest h hr
  | .bindCallInd _ _ _ _ _ rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs, Bool.and_eq_true] at h hr ⊢
      exact ⟨hKK _ h.1, Endblock.gOk_mono rest h.2 hr⟩
  | .narrow _ _ _ sonst rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Endblock.gOk_mono sonst h.1 (fun r h' => hr r (Or.inl h')),
        Endblock.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .narrowRequired _ _ _ rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs] at h hr ⊢
      exact Endblock.gOk_mono rest h hr
  | .exchange _ _ _ _ rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs] at h hr ⊢
      exact Endblock.gOk_mono rest h hr
  | .ite _ t e, h, hr => by
      simp only [Endblock.gOk, Endblock.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Endblock.gOk_mono e h.1 (fun r h' => hr r (Or.inl h')),
        Endblock.gOk_mono t h.2 (fun r h' => hr r (Or.inr h'))⟩

theorem Arms.gOk_mono {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} :
    (a : Arms D V l Γ Λ Λ' cs) → a.gOk K Rg = true → (∀ r ∈ a.regs, Rg' r = true) →
      a.gOk K' Rg' = true
  | .nil, _, _ => rfl
  | .cons b rest, h, hr => by
      simp only [Arms.gOk, Arms.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Block.gOk_mono b h.1 (fun r h' => hr r (Or.inl h')),
        Arms.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩

theorem GrundArms.gOk_mono {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} : (a : GrundArms D V l Γ Λ Λ' n) → a.gOk K Rg = true →
      (∀ r ∈ a.regs, Rg' r = true) → a.gOk K' Rg' = true
  | .nil, _, _ => rfl
  | .cons b rest, h, hr => by
      simp only [GrundArms.gOk, GrundArms.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Block.gOk_mono b h.1 (fun r h' => hr r (Or.inl h')),
        GrundArms.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩

end

end Mono

theorem armWahlG_gOk {V : Vertrag D} {K : Nat → Bool} {Rg : D.Reg → Bool} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    arms.gOk K Rg = true → (armWahlG arms v).2.1.gOk K Rg = true
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨⟨0, _⟩, _⟩, h => by
      simp only [Arms.gOk, Bool.and_eq_true] at h
      exact h.1
  | _, .cons _ rest, ⟨⟨_ + 1, _⟩, _⟩, h => by
      simp only [Arms.gOk, Bool.and_eq_true] at h
      exact armWahlG_gOk rest _ h.2

theorem armWahlG_gOk' {V : Vertrag D} {K : Nat → Bool} {Rg : D.Reg → Bool} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs)
    (v : Wert D (.sum cs)) {c : Option Ty} {b : Block D V l (ArmCtx Γ c) Λ Λ'}
    {nutz : Nutzlast D.Fn D.passt c} (hw : armWahlG arms v = ⟨c, b, nutz⟩) (h : arms.gOk K Rg = true) :
    b.gOk K Rg = true := by
  have h0 := armWahlG_gOk arms v h
  rw [hw] at h0
  exact h0

theorem grundWahlG_gOk {V : Vertrag D} {K : Nat → Bool} {Rg : D.Reg → Bool} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    arms.gOk K Rg = true → (grundWahlG arms r).gOk K Rg = true
  | _, .nil, ⟨k, hk⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨0, _⟩, h => by
      simp only [GrundArms.gOk, Bool.and_eq_true] at h
      exact h.1
  | _, .cons _ rest, ⟨_ + 1, _⟩, h => by
      simp only [GrundArms.gOk, Bool.and_eq_true] at h
      exact grundWahlG_gOk rest _ h.2

/-! ## 4. The footprint with the device carriers, and its check -/

/-- The register test: every device carrier of `r` is in `S`. -/
def regP (S : List (D.Tab ⊕ D.Glob)) (r : D.Reg) : Bool :=
  (D.rtraeger r).all fun o => S.any fun o' => decide (o' = o)

theorem regP_ok {S : List (D.Tab ⊕ D.Glob)} {r : D.Reg} (h : regP S r = true) :
    ∀ o ∈ D.rtraeger r, o ∈ S := by
  intro o ho
  obtain ⟨o', ho', he⟩ := List.any_eq_true.mp ((List.all_eq_true.mp h) o ho)
  rw [← of_decide_eq_true he]
  exact ho'

theorem regP_of {S : List (D.Tab ⊕ D.Glob)} {r : D.Reg} (h : ∀ o ∈ D.rtraeger r, o ∈ S) :
    regP S r = true :=
  List.all_eq_true.mpr fun o ho => List.any_eq_true.mpr ⟨o, h o ho, decide_eq_true rfl⟩

/-- **The footprint of `f` with its devices**: the footprint of `ziel_ort`
    (`fussOrte`: contract carriers, body reads, contract carriers of direct
    callees) and the device carriers of every register the body reads. -/
def fussOrteG (P : Programm D) (f : D.Fn) : List (D.Tab ⊕ D.Glob) :=
  fussOrte P f ++ (P.rumpf f).regs.flatMap D.rtraeger

theorem fuss_teilG (P : Programm D) (f : D.Fn) : fussOrte P f ⊆ fussOrteG P f :=
  fun _ h => List.mem_append_left _ h

theorem fuss_rumpfG (P : Programm D) (f : D.Fn) : endblockOrteP P (P.rumpf f) ⊆ fussOrteG P f :=
  fun _ h => fuss_teilG P f (fuss_rumpf P f h)

theorem fuss_ensG (P : Programm D) (f : D.Fn) : (P.ensures f).orte ⊆ fussOrteG P f :=
  fun _ h => fuss_teilG P f (fuss_ens P f h)

theorem fuss_regG (P : Programm D) (f : D.Fn) (r : D.Reg) (hr : r ∈ (P.rumpf f).regs) :
    ∀ o ∈ D.rtraeger r, o ∈ fussOrteG P f :=
  fun _ ho => List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, hr, ho⟩)

/-- **The footprint check with the devices.** Every carrier of the widened
    footprint of `f` -- the device carriers of the registers it reads
    included -- is guarded by a lock that `f` holds BY SIGNATURE, or no
    function writes it. -/
def fussOrtGB (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun f => (fussOrteG P f).all fun o =>
    (waechterVon o).any (fun L => decide (L ∈ D.haelt f)) ||
    fs.all (fun g => !(TraegerSchreibt g o))

/-- The property that `fussOrtGB` decides. -/
def FussOrtGOk (P : Programm D) (f : D.Fn) : Prop :=
  ∀ o ∈ fussOrteG P f,
    (∃ L : D.Lock, Bewacht o L ∧ L ∈ D.haelt f) ∨ (∀ g : D.Fn, TraegerSchreibt g o = false)

theorem fussOrtGB_ok (P : Programm D) (fs : List D.Fn) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (h : fussOrtGB P fs = true) (f : D.Fn) : FussOrtGOk P f := by
  intro o ho
  have h1 := (List.all_eq_true.mp h) f (hvoll f)
  have h2 := (List.all_eq_true.mp h1) o ho
  simp only [Bool.or_eq_true] at h2
  rcases h2 with hg | hfrei
  · obtain ⟨L, hL, hLh⟩ := List.any_eq_true.mp hg
    exact Or.inl ⟨L, waechterVon_mem.mp hL, of_decide_eq_true hLh⟩
  · refine Or.inr fun g => ?_
    have := (List.all_eq_true.mp hfrei) g (hvoll g)
    simpa using this

/-- The widened check covers the old one. -/
theorem fussOrtB_of_G (P : Programm D) (fs : List D.Fn) (h : fussOrtGB P fs = true) :
    fussOrtB P fs = true :=
  List.all_eq_true.mpr fun f hf => List.all_eq_true.mpr fun o ho =>
    (List.all_eq_true.mp ((List.all_eq_true.mp h) f hf)) o (fuss_teilG P f ho)

/-- **The widened fragment, as a decidable program fact**: every body is in
    `gOk` (every form; an indirect call admitted where every function of its
    signature has its contract carriers in the caller's widened footprint). -/
def programmImFragmentG (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun f => (P.rumpf f).gOk (kandB P fs (fussOrteG P f)) (fun _ => true)

/-- The decided fragment gives the fragment the replay reads: every body is
    in `gOk` with the admissibility `KandOk` of its widened footprint, and
    every register it reads has its device carriers there. -/
theorem programmImFragmentG_ok (P : Programm D) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (h : programmImFragmentG P fs = true) (f : D.Fn) :
    (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) = true :=
  Endblock.gOk_mono (kandB_kandP P hvoll _) _ ((List.all_eq_true.mp h) f (hvoll f))
    (fun r hr => regP_of (fuss_regG P f r hr))

/-! ## 5. The residues the replay follows -/

/-- A residue in the widened fragment whose blocks, loop heads and calls
    read only inside the footprint `S`, and whose register reads have their
    device carriers in `S`. -/
def GRest.okG (P : Programm D) (S : List (D.Tab ⊕ D.Glob)) {V : Vertrag D} :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop
  | _, _, _, .ende e => e.gOk (kandP P S) (regP S) = true ∧ endblockOrteP P e ⊆ S
  | _, _, _, .dann b k => b.gOk (kandP P S) (regP S) = true ∧ blockOrteP P b ⊆ S ∧ k.okG P S
  | _, _, _, .schrumpf k => k.okG P S
  | _, _, _, .frei _ k => k.okG P S
  | _, _, _, .trav _ inv body _ k =>
      inv.orte ⊆ S ∧ body.gOk (kandP P S) (regP S) = true ∧ blockOrteP P body ⊆ S ∧ k.okG P S
  | _, _, _, .travRest _ inv body _ k =>
      inv.orte ⊆ S ∧ body.gOk (kandP P S) (regP S) = true ∧ blockOrteP P body ⊆ S ∧ k.okG P S
  | _, _, _, .wieder _ bis body ueber k =>
      bis.orte ⊆ S ∧ body.gOk (kandP P S) (regP S) = true ∧ blockOrteP P body ⊆ S ∧
        ueber.gOk (kandP P S) (regP S) = true ∧
        blockOrteP P ueber ⊆ S ∧ k.okG P S
  | _, _, _, .wiederRest _ bis body ueber k =>
      bis.orte ⊆ S ∧ body.gOk (kandP P S) (regP S) = true ∧ blockOrteP P body ⊆ S ∧
        ueber.gOk (kandP P S) (regP S) = true ∧
        blockOrteP P ueber ⊆ S ∧ k.okG P S
  | _, _, _, .ewig _ _ inv body k =>
      inv.orte ⊆ S ∧ body.gOk (kandP P S) (regP S) = true ∧ blockOrteP P body ⊆ S ∧ k.okG P S
  | _, _, _, .ewigRest _ _ inv body k =>
      inv.orte ⊆ S ∧ body.gOk (kandP P S) (regP S) = true ∧ blockOrteP P body ⊆ S ∧ k.okG P S
  | _, _, _, .wartet b k => b.gOk (kandP P S) (regP S) = true ∧ blockOrteP P b ⊆ S ∧ k.okG P S
  | _, _, _, .wartetSonst _ err b k =>
      err.gOk (kandP P S) (regP S) = true ∧ endblockOrteP P err ⊆ S ∧
        b.gOk (kandP P S) (regP S) = true ∧ blockOrteP P b ⊆ S ∧ k.okG P S
  | _, _, Λ, @GRest.abbruch _ _ _ _ _ Λk k =>
      (∀ L, Res.held L ∈ Λk ↔ Res.held L ∈ Λ) ∧ k.okG P S
  | _, _, _, .leer => True

section OkG

variable {P : Programm D} {S : List (D.Tab ⊕ D.Glob)} {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem okG_dann_cons {Λ Λ' Λ'' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Block D V l Γ Λ' Λ''} {k : GRest D V l Γ Λ''}
    (h : (GRest.dann (.cons s rest) k).okG P S) :
    s.gOk (kandP P S) (regP S) = true ∧ stmtOrteP P s ⊆ S ∧ (GRest.dann rest k).okG P S := by
  obtain ⟨hk, hs, hk'⟩ := h
  simp only [Block.gOk, Bool.and_eq_true] at hk
  simp only [blockOrteP] at hs
  exact ⟨hk.1, (teil_append hs).1, hk.2, (teil_append hs).2, hk'⟩

theorem okG_ende_cons {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Endblock D V l Γ Λ'} (h : (GRest.ende (.cons s rest)).okG P S) :
    s.gOk (kandP P S) (regP S) = true ∧ stmtOrteP P s ⊆ S ∧ (GRest.ende rest).okG P S := by
  obtain ⟨hk, hs⟩ := h
  simp only [Endblock.gOk, Bool.and_eq_true] at hk
  simp only [endblockOrteP] at hs
  exact ⟨hk.1, (teil_append hs).1, hk.2, (teil_append hs).2⟩

/-- **The residue of an `else` branch is in the fragment** (as
    `okV_alsBlock`). -/
theorem okG_alsBlock {Λ Λk : List (Res D)} (e : Endblock D V l Γ Λ) (k : GRest D V l Γ Λk)
    (hΛ : ∀ L, Res.held L ∈ Λk ↔ Res.held L ∈ Λ) (he : e.gOk (kandP P S) (regP S) = true)
    (heS : endblockOrteP P e ⊆ S) (hk : k.okG P S) :
    (GRest.dann e.alsBlock.2 (.abbruch k)).okG P S :=
  ⟨by rw [Endblock.gOk_alsBlock]; exact he, by rw [blockOrteP_alsBlock]; exact heS,
    fun L => (hΛ L).trans (e.alsBlock.2.held_iff L).symm, hk⟩

end OkG

/-! ## 6. The frame semantics of the device forms -/

section Geraet

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  {l : Bool} {Γ : Ctx}

theorem semV_regLies {Λ Λ' : List (Res D)} (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
    (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (D.rtyp r)) (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) = some v)
    (hz : D.rzusage r v = true) :
    semV O passes R (.dann (.regRead r hk rest) k) σ ρ =
      semV O passes R (.dann rest (.schrumpf k)) (σ.fragt (.inr (.inl r))) (.cons v ρ) := by
  rw [semV_dann]
  simp only [execBlock, hv, hz, if_true]
  rfl

theorem semV_regLiesElseWahr {Λ Λ' : List (Res D)} (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
    (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (D.rtyp r)) (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) = some v)
    (hw : wahr? (eval ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) zusage ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) (.cons v ρ)) = true) :
    semV O passes R (.dann (.regReadElse r hk zusage sonst rest) k) σ ρ =
      semV O passes R (.dann rest (.schrumpf k)) ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) (.cons v ρ) := by
  rw [semV_dann]
  simp only [execBlock, hv, hw, if_true]
  rfl

theorem semV_regLiesElseFalsch {Λ Λ' : List (Res D)} (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
    (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (D.rtyp r)) (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) = some v)
    (hw : wahr? (eval ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) zusage ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) (.cons v ρ)) = false) :
    (semV O passes R (.dann (.regReadElse r hk zusage sonst rest) k) σ ρ).folgt
      (semV O passes R (.dann sonst.alsBlock.2 (.abbruch k)) ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) ρ) := by
  rw [semV_dann]
  simp only [execBlock, hv, hw, Bool.false_eq_true, if_false]
  rw [semV_alsBlock]
  exact ZErg.folgt_refl _

theorem semV_awaits {Λ Λ' : List (Res D)} (g : D.Glob) (payload : List D.Glob)
    (hp : payload = D.nutzlast g) (hL : gdarf D g Λ) (hat : D.atomar g = true) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) (hvis : O.sichtbar g (σ.fragt (.inr (.inr g))) = true) :
    semV O passes R (.dann (.awaits g payload hp hL hat rest) k) σ ρ =
      semV O passes R (.dann rest (.schrumpf k)) ((σ.fragt (.inr (.inr g))).lese Λ [.inr g])
        (.cons (((σ.fragt (.inr (.inr g))).lese Λ [.inr g]).globs g) ρ) := by
  rw [semV_dann]
  simp only [execBlock, hvis, if_true]
  rfl

end Geraet

/-! ## 7. The fragment of `ziel_ort_voll` is inside the widened one -/

section AusV

end AusV
end Gabbro.Grammatik
