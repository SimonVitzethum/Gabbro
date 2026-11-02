/- Part 1b of `Satz/T2/Teil1` (C11 split; pure move): held-set
   preservation (`held_mono`, `held_iff`), outcome worlds, and the plain
   release (`BravRet`/`GutRet`). -/
module

public import Grammatik.Kern.Syntax.Satz.T1
public import Grammatik.Kern.Syntax.Satz.T2.Teil1a

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

mutual
theorem Stmt.held_mono : (s : Stmt D V l Γ Λ Λ') → ∀ L, Res.held L ∈ Λ' → Res.held L ∈ Λ
  | .assignSlot .., L, h | .assignThru .., L, h | .assignSlotRef .., L, h | .assignGlob .., L, h | .putBytes .., L, h
  | .assignVar .., L, h | .shift .., L, h | .locks .., L, h | .traverse .., L, h
  | .consumeTraverse .., L, h | .retScoped .., L, h | .retWhyScoped .., L, h
  | .retry .., L, h | .forever .., L, h | .axiomCall .., L, h | .regWrite .., L, h
  | .transition .., L, h | .publish .., L, h | .ret .., L, h | .retWhy .., L, h
  | .leave .., L, h | .next .., L, h => h
  | .ite _ t _, L, h => t.held_mono L h
  | .onOption _ p _, L, h => p.held_mono L h
  | .onTag _ arms, L, h => arms.held_mono L h
  | .onWhy _ arms, L, h => arms.held_mono L h
  | .call f _ _ _, L, h => held_nachSig _ _ L h
  | .callInd (n := n) _ _ _ _, L, h => held_nachSig _ _ L h
  | .axiomCallElse _ _ _ _ _ _ _ _ _, L, h => held_nachSig _ _ L h
  | .callIndElse (n := n) _ _ _ _ _ _, L, h => held_nachSig _ _ L h
  | .breaking _ body, L, h => body.held_mono L h
  | .advances m a _ _, L, h => by
      simp only [List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact List.mem_of_mem_erase h
      · cases h
  | .retires .., L, h => List.mem_of_mem_erase h

theorem Block.held_mono : (b : Block D V l Γ Λ Λ') → ∀ L, Res.held L ∈ Λ' → Res.held L ∈ Λ
  | .nil, L, h => h
  | .cons s rest, L, h => s.held_mono L (rest.held_mono L h)
  | .bind _ rest, L, h | .bindAxiom _ _ _ _ _ _ _ rest, L, h | .regRead _ _ rest, L, h
  | .regReadElse _ _ _ _ rest, L, h | .awaits _ _ _ _ _ rest, L, h | .exchange _ _ _ _ rest, L, h
  | .narrow _ _ _ _ rest, L, h | .narrowRequired _ _ _ rest, L, h | .check _ _ rest, L, h | .float _ _ _ _ _ rest, L, h
  | .floatLit _ _ _ rest, L, h | .floatOf _ _ _ rest, L, h | .floatNarrow _ _ _ _ rest, L, h =>
      rest.held_mono L h
  | .bindCall f _ _ _ _ rest, L, h => held_nachSig _ _ L (rest.held_mono L h)
  | .bindCallInd _ _ _ _ _ rest, L, h => held_nachSig _ _ L (rest.held_mono L h)
  | .bindCallIndElse _ _ _ _ _ _ rest, L, h => held_nachSig _ _ L (rest.held_mono L h)
  | .bindCallElse f _ _ _ _ _ rest, L, h => held_nachSig _ _ L (rest.held_mono L h)
  | .bindAxiomElse _ _ _ _ _ _ _ _ _ rest, L, h => rest.held_mono L h
  | .bindAxiomOpt _ _ _ _ _ _ _ rest, L, h => held_nachSig _ _ L (rest.held_mono L h)
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ _ rest, L, h => held_nachSig _ _ L (rest.held_mono L h)

theorem Arms.held_mono : (a : Arms D V l Γ Λ Λ' cs) → ∀ L, Res.held L ∈ Λ' → Res.held L ∈ Λ
  | .nil, L, h => h
  | .cons b _, L, h => b.held_mono L h

theorem GrundArms.held_mono : (a : GrundArms D V l Γ Λ Λ' n) → ∀ L, Res.held L ∈ Λ' → Res.held L ∈ Λ
  | .nil, L, h => h
  | .cons b _, L, h => b.held_mono L h
end
mutual
theorem Stmt.held_iff : (s : Stmt D V l Γ Λ Λ') → ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ
  | .assignSlot .., _ | .assignThru .., _ | .assignSlotRef .., _ | .assignGlob .., _ | .putBytes .., _
  | .assignVar .., _ | .shift .., _ | .locks .., _ | .traverse .., _
  | .consumeTraverse .., _ | .retScoped .., _ | .retWhyScoped .., _
  | .retry .., _ | .forever .., _ | .axiomCall .., _ | .regWrite .., _
  | .transition .., _ | .publish .., _ | .ret .., _ | .retWhy .., _
  | .leave .., _ | .next .., _ => Iff.rfl
  | .ite _ t _, L => t.held_iff L
  | .onOption _ p _, L => p.held_iff L
  | .onTag _ arms, L => arms.held_iff L
  | .onWhy _ arms, L => arms.held_iff L
  | .call f _ _ _, L => held_nachSig_iff _ _ L
  | .callInd (n := n) _ _ _ _, L => held_nachSig_iff _ _ L
  | .axiomCallElse _ _ _ _ _ _ _ _ _, L => held_nachSig_iff _ _ L
  | .callIndElse (n := n) _ _ _ _ _ _, L => held_nachSig_iff _ _ L
  | .breaking _ body, L => body.held_iff L
  | .advances m a _ _, L => by
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro (h | h)
        · exact List.mem_of_mem_erase h
        · cases h
      · intro h; left; exact (List.mem_erase_of_ne (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])).mpr h
  | .retires .., L => by
      constructor
      · exact List.mem_of_mem_erase
      · intro h; exact (List.mem_erase_of_ne (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])).mpr h

theorem Block.held_iff : (b : Block D V l Γ Λ Λ') → ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ
  | .nil, _ => Iff.rfl
  | .cons s rest, L => (rest.held_iff L).trans (s.held_iff L)
  | .bind _ rest, L | .bindAxiom _ _ _ _ _ _ _ rest, L | .regRead _ _ rest, L
  | .regReadElse _ _ _ _ rest, L | .awaits _ _ _ _ _ rest, L | .exchange _ _ _ _ rest, L
  | .narrow _ _ _ _ rest, L | .narrowRequired _ _ _ rest, L | .check _ _ rest, L | .float _ _ _ _ _ rest, L
  | .floatLit _ _ _ rest, L | .floatOf _ _ _ rest, L | .floatNarrow _ _ _ _ rest, L =>
      rest.held_iff L
  | .bindCall f _ _ _ _ rest, L => (rest.held_iff L).trans (held_nachSig_iff _ _ L)
  | .bindCallInd _ _ _ _ _ rest, L => (rest.held_iff L).trans (held_nachSig_iff _ _ L)
  | .bindCallIndElse _ _ _ _ _ _ rest, L => (rest.held_iff L).trans (held_nachSig_iff _ _ L)
  | .bindCallElse f _ _ _ _ _ rest, L => (rest.held_iff L).trans (held_nachSig_iff _ _ L)
  | .bindAxiomElse _ _ _ _ _ _ _ _ _ rest, L => rest.held_iff L
  | .bindAxiomOpt _ _ _ _ _ _ _ rest, L => (rest.held_iff L).trans (held_nachSig_iff _ _ L)
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ _ rest, L => (rest.held_iff L).trans (held_nachSig_iff _ _ L)

theorem Arms.held_iff : (a : Arms D V l Γ Λ Λ' cs) → ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ
  | .nil, _ => Iff.rfl
  | .cons b _, L => b.held_iff L

theorem GrundArms.held_iff : (a : GrundArms D V l Γ Λ Λ' n) → ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ
  | .nil, _ => Iff.rfl
  | .cons b _, L => b.held_iff L
end
/-- Die Welt eines Ausgangs, wo er eine hat. -/
def Ausgang.welt : Ausgang V l Γ → Option (World D)
  | .ok σ _ => some σ
  | .zurueck σ _ => some σ
  | .why σ _ => some σ
  | .leave _ σ _ => some σ
  | .next _ σ _ => some σ
  | .logik _ => none
  | .hardware _ => none

def EndAusgang.welt : EndAusgang V l Γ → Option (World D)
  | .zurueck σ _ => some σ
  | .why σ _ => some σ
  | .leave _ σ _ => some σ
  | .next _ σ _ => some σ
  | .logik _ => none
  | .hardware _ => none

def RufAusgang.welt {f : D.Fn} : RufAusgang f → Option (World D)
  | .ok σ _ => some σ
  | .why σ _ => some σ
  | .logik _ => none
  | .hardware _ => none

/-- Release-aware trace quality for scoped returns: the held locks change
    exactly by erasing some list (the crossed scopes at use sites), while every
    new event stays good and consistency is preserved. -/
def BravRet (σ σ' : World D) : Prop :=
  (∃ Ls : List D.Lock, σ'.haelt = Ls.foldl (fun h L => h.erase L) σ.haelt) ∧
  (∀ e ∈ σ'.spur, e ∈ σ.spur ∨ e.gut) ∧ (Konsistent σ.spur → Konsistent σ'.spur)

/-- Release-aware frame+trace for scoped returns. -/
def GutRet (W : D.Tab → Bool) (G : D.Glob → Bool) (σ σ' : World D) : Prop :=
  Rahmen W G σ σ' ∧ BravRet σ σ'

theorem offen_gibt_foldl (Ls : List D.Lock) (s : List (Ereignis D)) :
    offen (Ls.map (fun L => Ereignis.gibt (D := D) L) ++ s) =
      Ls.foldl (fun h L => h.erase L) (offen s) := by
  induction Ls generalizing s with
  | nil => rfl
  | cons L Ls ih => simp only [List.map_cons, List.cons_append, offen, ih]

theorem haelt_gibt_foldl (σ : World D) (Ls : List D.Lock) :
    (Ls.foldl World.gibt σ).haelt = Ls.foldl (fun h L => h.erase L) σ.haelt := by
  rw [World.haelt, World.gibt_foldl_spur, offen_gibt_foldl, World.haelt]

theorem BravRet.refl (σ : World D) : BravRet σ σ :=
  ⟨⟨[], rfl⟩, fun e he => .inl he, id⟩

/-- `Brav` is `BravRet` with no release. -/
theorem Brav.toRet {a b : World D} (h : Brav a b) : BravRet a b :=
  ⟨⟨[], by simpa using h.1⟩, h.2.1, h.2.2⟩

/-- `Gut` is `GutRet` with no release. -/
theorem Gut.toRet {W G} {a b : World D} (h : Gut W G a b) : GutRet W G a b :=
  ⟨h.1, h.2.toRet⟩

/-- `Brav` is `BravRet` with no release. -/
theorem Brav.toRet {a b : World D} (h : Brav a b) : BravRet a b := by
  obtain ⟨heq, hgood, hkons⟩ := h
  exact ⟨⟨[], by rw [heq]⟩, hgood, hkons⟩

/-- Membership survives releases: a held lock after releasing was held before. -/
theorem BravRet.mem {a b : World D} (h : BravRet a b) {L : D.Lock} (hm : L ∈ b.haelt) :
    L ∈ a.haelt := by
  obtain ⟨Ls, hLs⟩ := h.1
  have key : ∀ (Ls : List D.Lock) (h : List D.Lock), L ∈ Ls.foldl (fun h M => h.erase M) h →
      L ∈ h := by
    intro Ls
    induction Ls with
    | nil => intro h hm; simpa using hm
    | cons M Ms ih =>
        intro h hm
        simp only [List.foldl_cons] at hm
        exact List.mem_of_mem_erase (ih _ hm)
  rw [hLs] at hm
  exact key Ls _ hm

theorem Brav.transRet {a b c : World D} (h1 : Brav a b) (h2 : BravRet b c) : BravRet a c := by
  obtain ⟨Ls, hLs⟩ := h2.1
  refine ⟨⟨Ls, by rw [hLs, h1.1]⟩, fun e he => match h2.2.1 e he with
    | .inl hb => h1.2.1 e hb
    | .inr g => .inr g, fun k => h2.2.2 (h1.2.2 k)⟩

theorem Gut.transRet {W G} {a b c : World D} (h1 : Gut W G a b) (h2 : GutRet W G b c) :
    GutRet W G a c :=
  ⟨h1.1.trans h2.1, h1.2.transRet h2.2⟩

/-- Release then no release is the same release. -/
theorem BravRet.transGut {a b c : World D} (h1 : BravRet a b) (h2 : Brav b c) : BravRet a c := by
  obtain ⟨Ls, hLs⟩ := h1.1
  refine ⟨⟨Ls, by rw [h2.1, hLs]⟩, fun e he => match h1.2.1 e he with
    | .inl hb => h2.2.1 e hb
    | .inr g => .inr g, fun k => h1.2.2 (h2.2.2 k)⟩

theorem GutRet.transGut {W G} {a b c : World D} (h1 : GutRet W G a b) (h2 : Gut W G b c) :
    GutRet W G a c :=
  ⟨h1.1.trans h2.1, h1.2.transGut h2.2⟩

/-- Release then release is the same combined release (scopes concatenate). -/
theorem BravRet.transRet {a b c : World D} (h1 : BravRet a b) (h2 : BravRet b c) :
    BravRet a c := by
  obtain ⟨Ls1, hLs1⟩ := h1.1
  obtain ⟨Ls2, hLs2⟩ := h2.1
  refine ⟨⟨Ls1 ++ Ls2, ?_⟩, ?_, ?_⟩
  · rw [hLs2, hLs1, List.foldl_append]
  · intro e he
    rcases h2.2.1 e he with h | h
    · rcases h1.2.1 e h with h' | h'
      · exact .inl h'
      · exact .inr h'
    · exact .inr h
  · intro k
    exact h2.2.2 (h1.2.2 k)

/-- A releasing step followed by another is releasing with the concatenated scopes. -/
theorem GutRet.transRet {W G} {a b c : World D} (h1 : GutRet W G a b) (h2 : GutRet W G b c) :
    GutRet W G a c :=
  ⟨h1.1.trans h2.1, h1.2.transRet h2.2⟩

end Gabbro.Grammatik
