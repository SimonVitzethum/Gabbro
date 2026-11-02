module

public import Grammatik.Kern.Syntax.Satz.T1

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

theorem gut_nimmt_gibt {W G} (σ σ1 : World D) (L : D.Lock)
    (hn : (∀ M ∈ σ.haelt, D.rang M < D.rang L) ∧ L ∉ σ.haelt)
    (h : Gut W G (σ.nimmt L) σ1) : Gut W G σ (σ1.gibt L) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (rahmen_gleich (W := W) (G := G) (σ := σ) (σ' := σ.nimmt L) rfl rfl).trans
      (h.1.trans (rahmen_gleich rfl rfl))
  · show (offen σ1.spur).erase L = offen σ.spur
    have := h.haelt
    simp only [World.haelt, World.nimmt, offen] at this
    rw [this]; exact List.erase_cons_head _ _
  · intro e he
    simp only [World.gibt, List.mem_cons] at he
    rcases he with rfl | he
    · exact .inr (show (Ereignis.gibt L).gut from trivial)
    · rcases h.2.2.1 e he with h1 | h1
      · simp only [World.nimmt, List.mem_cons] at h1
        rcases h1 with rfl | h1
        · exact .inr (show (Ereignis.nimmt L σ.haelt).gut from hn)
        · exact .inl h1
      · exact .inr h1
  · intro k
    exact konsistent_cons trivial (h.2.2.2 (konsistent_cons rfl k))

-- Die Orte eines Ausdrucks tragen ihre Waechter -- weil jeder Konstruktor sie verlangt.
mutual
theorem Expr.orte_darf : (e : Expr D Γ Λ τ) → ∀ o ∈ e.orte, OrtDarf Λ o
  | .lit _, _, h | .tru, _, h | .fls, _, h | .var _, _, h | .ptrOf _ _ _ _, _, h
  | .fnref _ _ _, _, h | .none _, _, h | .why _ _, _, h => by simp only [Expr.orte, List.not_mem_nil] at h
  | .refEq a b, o, h => by
      simp only [Expr.orte, List.mem_append] at h
      rcases h with h | h
      · exact a.orte_darf o h
      · exact b.orte_darf o h
  | .slotRef r t _ _ _ hL, o, h => by
      simp only [Expr.orte, List.mem_cons] at h
      rcases h with rfl | h
      · exact hL
      · exact r.orte_darf o h
  | .glob g hL, o, h => by simp only [Expr.orte, List.mem_cons, List.not_mem_nil, or_false] at h; subst h; exact hL
  | .oldG g hL, o, h => by simp only [Expr.orte, List.mem_cons, List.not_mem_nil, or_false] at h; subst h; exact hL
  | .slot t _ i hL, o, h => by
      simp only [Expr.orte, List.mem_cons] at h
      rcases h with rfl | h
      · exact hL
      · exact i.orte_darf o h
  | .oldS t _ i hL, o, h => by
      simp only [Expr.orte, List.mem_cons] at h
      rcases h with rfl | h
      · exact hL
      · exact i.orte_darf o h
  | .getBytes t _ _ _ i _ _ hL, o, h => by
      simp only [Expr.orte, List.mem_cons] at h
      rcases h with rfl | h
      · exact hL
      · exact i.orte_darf o h
  | .thru p t _ _ i hL, o, h => by
      simp only [Expr.orte, List.mem_append, List.mem_cons] at h
      rcases h with h | rfl | h
      · exact p.orte_darf o h
      · exact hL
      · exact i.orte_darf o h
  | .widen _ _ e, o, h => e.orte_darf o h
  | .neg a, o, h | .not a, o, h | .some a, o, h | .istSome a, o, h => a.orte_darf o h
  | .add a b, o, h | .sub a b, o, h | .mul a b, o, h | .div _ _ a b, o, h | .rem _ _ a b, o, h
  | .sdiv _ a b, o, h | .srem _ a b, o, h | .band _ _ a b, o, h | .bor _ _ _ _ _ a b, o, h
  | .bxor _ _ _ _ _ a b, o, h | .shl _ _ _ _ _ a b, o, h | .shr _ _ _ _ _ a b, o, h | .lt a b, o, h
  | .le a b, o, h | .eq a b, o, h | .fllt a b, o, h | .flle a b, o, h | .and a b, o, h
  | .or a b, o, h => by
      simp only [Expr.orte, List.mem_append] at h
      rcases h with h | h
      · exact a.orte_darf o h
      · exact b.orte_darf o h
  | .case _ _ nutz, o, h => nutz.orte_darf o h
  | .forallSlots t body hL, o, h | .existsSlots t body hL, o, h => by
      simp only [Expr.orte, List.mem_cons] at h
      rcases h with rfl | h
      · exact hL
      · exact body.orte_darf o h
  | .reaches t _ _ a b hL, o, h => by
      simp only [Expr.orte, List.mem_cons, List.mem_append] at h
      rcases h with (rfl | h) | h
      · exact hL
      · exact a.orte_darf o h
      · exact b.orte_darf o h
  | .arrNil, _, h => by simp only [Expr.orte, List.not_mem_nil] at h
  | .strLit _ _, _, h => by simp only [Expr.orte, List.not_mem_nil] at h
  | .arrCons a b, o, h => by
      simp only [Expr.orte, List.mem_append] at h
      rcases h with h | h
      · exact a.orte_darf o h
      · exact b.orte_darf o h
  | .arrGet a b, o, h => by
      simp only [Expr.orte, List.mem_append] at h
      rcases h with h | h
      · exact a.orte_darf o h
      · exact b.orte_darf o h
  | .strCat a b, o, h => by
      simp only [Expr.orte, List.mem_append] at h
      rcases h with h | h
      · exact a.orte_darf o h
      · exact b.orte_darf o h
  | .strGet a b, o, h => by
      simp only [Expr.orte, List.mem_append] at h
      rcases h with h | h
      · exact a.orte_darf o h
      · exact b.orte_darf o h
  | .strEq a b, o, h => by
      simp only [Expr.orte, List.mem_append] at h
      rcases h with h | h
      · exact a.orte_darf o h
      · exact b.orte_darf o h
  | .strLt a b, o, h => by
      simp only [Expr.orte, List.mem_append] at h
      rcases h with h | h
      · exact a.orte_darf o h
      · exact b.orte_darf o h
  | .arrSet a i v, o, h => by
      simp only [Expr.orte, List.mem_append] at h
      rcases h with (h | h) | h
      · exact a.orte_darf o h
      · exact i.orte_darf o h
      · exact v.orte_darf o h
  | .strLen s, o, h => s.orte_darf o h
  | .strWeit _ s, o, h => s.orte_darf o h
  | .wenn c a b, o, h => by
      simp only [Expr.orte, List.mem_append] at h
      rcases h with (h | h) | h
      · exact c.orte_darf o h
      · exact a.orte_darf o h
      · exact b.orte_darf o h
  | .eng e _ _ s, o, h => by
      simp only [Expr.orte, List.mem_append] at h
      rcases h with h | h
      · exact e.orte_darf o h
      · exact s.orte_darf o h
  | .intBuiltin1 _ a, o, h => a.orte_darf o h
  | .intBuiltin2 _ a b, o, h => by
      simp only [Expr.orte, List.mem_append] at h
      rcases h with h | h
      · exact a.orte_darf o h
      · exact b.orte_darf o h
  | .count _ body, o, h => body.orte_darf o h

theorem NutzlastExpr.orte_darf : (e : NutzlastExpr D Γ Λ c) → ∀ o ∈ e.orte, OrtDarf Λ o
  | .empty, _, h => by simp only [NutzlastExpr.orte, List.not_mem_nil] at h
  | .val e, o, h => e.orte_darf o h
end
theorem Args.orte_darf : (a : Args D Γ Λ τs) → ∀ o ∈ a.orte, OrtDarf Λ o
  | .nil, _, h => by simp only [orte, List.not_mem_nil] at h
  | .cons e rest, o, h => by
      simp only [Args.orte, List.mem_append] at h
      rcases h with h | h
      · exact e.orte_darf o h
      · exact rest.orte_darf o h

theorem ErgExpr.orte_darf : (e : ErgExpr D Γ Λ τ) → ∀ o ∈ e.orte, OrtDarf Λ o
  | .empty, _, h => by simp only [orte, List.not_mem_nil] at h
  | .val e, o, h => e.orte_darf o h

/-- Zwei Ausdruecke, zusammen. -/
theorem orte_append {Λ : List (Res D)} {a b : List (D.Tab ⊕ D.Glob)} (ha : ∀ o ∈ a, OrtDarf Λ o)
    (hb : ∀ o ∈ b, OrtDarf Λ o) : ∀ o ∈ a ++ b, OrtDarf Λ o := by
  intro o h; simp only [List.mem_append] at h
  rcases h with h | h
  · exact ha o h
  · exact hb o h

/-- Die Sperrzeugnisse eines `Λ` werden von keiner Anweisung erzeugt: was danach `held` ist,
    war es davor. (Marken kommen und gehen; Zeugnisse nur durch `locks`, und das schliesst
    sich.) -/
theorem held_nachSig (S : Signatur D.Tab D.Glob D.Lock D.Marke) (Λ : List (Res D)) (L : D.Lock)
    (h : Res.held L ∈ nachSig D S Λ) : Res.held L ∈ Λ := by
  unfold nachSig at h
  simp only [List.mem_append, List.mem_map] at h
  rcases h with h | ⟨m, _, hm⟩
  · -- ein Fold von `erase` bleibt eine Teilliste
    have key : ∀ (ks : List (D.Marke × Nat)) (Λ : List (Res D)),
        Res.held L ∈ ks.foldl (fun acc m => acc.erase (Res.vonMarke D m)) Λ → Res.held L ∈ Λ := by
      intro ks
      induction ks with
      | nil => intro Λ h; exact h
      | cons k ks ih => intro Λ h; exact List.mem_of_mem_erase (ih _ h)
    exact key _ _ h
  · cases m; simp only [Res.vonMarke, reduceCtorEq] at hm

theorem held_nachSig_iff (S : Signatur D.Tab D.Glob D.Lock D.Marke) (Λ : List (Res D)) (L : D.Lock) :
    Res.held L ∈ nachSig D S Λ ↔ Res.held L ∈ Λ := by
  constructor
  · exact held_nachSig S Λ L
  · intro h
    unfold nachSig
    simp only [List.mem_append]
    left
    have key : ∀ (ks : List (D.Marke × Nat)) (Λ : List (Res D)), Res.held L ∈ Λ →
        Res.held L ∈ ks.foldl (fun acc m => acc.erase (Res.vonMarke D m)) Λ := by
      intro ks
      induction ks with
      | nil => intro Λ h; exact h
      | cons k ks ih =>
          intro Λ h
          apply ih
          apply List.mem_erase_of_ne _ |>.mpr h
          cases k; simp only [Res.vonMarke, ne_eq, reduceCtorEq, not_false_eq_true]
    exact key _ _ h

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

/-- **Release-aware frame+trace that spares the residual and respects the floor**:
    the release list avoids every required lock (`spare`) and every released lock
    ranks at or above the floor (`rank`). Callers transport their holdings through
    such a release: required locks survive by spare, extras by rank + `RufPasst.hx`. -/
def GutRetV (W : D.Tab → Bool) (G : D.Glob → Bool) (haelt : List D.Lock)
    (boden : Option Int) (σ σ' : World D) : Prop :=
  Rahmen W G σ σ' ∧ ∃ Ls : List D.Lock,
    σ'.haelt = Ls.foldl (fun h L => h.erase L) σ.haelt ∧
    (∀ L ∈ Ls, L ∉ haelt) ∧ (∀ L ∈ Ls, ∀ c, boden = some c → c ≤ D.rang L) ∧
    (∀ e ∈ σ'.spur, e ∈ σ.spur ∨ e.gut) ∧ (Konsistent σ.spur → Konsistent σ'.spur)

theorem GutRetV.toRet {W G} {haelt : List D.Lock} {boden : Option Int} {a b : World D}
    (h : GutRetV W G haelt boden a b) : GutRet W G a b := by
  obtain ⟨hr, Ls, heq, _, _, hgood, hkons⟩ := h
  exact ⟨hr, ⟨Ls, heq⟩, hgood, hkons⟩

theorem GutRetV.toBravRet {W G} {haelt : List D.Lock} {boden : Option Int} {a b : World D}
    (h : GutRetV W G haelt boden a b) : BravRet a b := by
  obtain ⟨_, Ls, heq, _, _, hgood, hkons⟩ := h
  exact ⟨⟨Ls, heq⟩, hgood, hkons⟩

/-- `Gut` is `GutRetV` with no release. -/
theorem Gut.toRetV {W G} {haelt : List D.Lock} {boden : Option Int} {a b : World D}
    (h : Gut W G a b) : GutRetV W G haelt boden a b := by
  obtain ⟨hr, heq, hgood, hkons⟩ := h
  refine ⟨hr, [], ?_, ?_, ?_, ?_, ?_⟩
  · simpa using heq
  · intro L hL; simp only [List.not_mem_nil] at hL
  · intro L hL; simp only [List.not_mem_nil] at hL
  · exact hgood
  · exact hkons

theorem Gut.transRetV {W G} {haelt : List D.Lock} {boden : Option Int} {a b c : World D}
    (h1 : Gut W G a b) (h2 : GutRetV W G haelt boden b c) :
    GutRetV W G haelt boden a c := by
  obtain ⟨hr2, Ls, heq2, hsp2, hrk2, hgood2, hkons2⟩ := h2
  obtain ⟨hr1, heq1, hgood1, hkons1⟩ := h1
  refine ⟨hr1.trans hr2, ⟨Ls, ?_, hsp2, hrk2, ?_, ?_⟩⟩
  · rw [heq2, heq1]
  · intro e he
    rcases hgood2 e he with h | h
    · rcases hgood1 e h with h' | h'
      · exact .inl h'
      · exact .inr h'
    · exact .inr h
  · intro k
    exact hkons2 (hkons1 k)

theorem GutRetV.transGut {W G} {haelt : List D.Lock} {boden : Option Int} {a b c : World D}
    (h1 : GutRetV W G haelt boden a b) (h2 : Gut W G b c) :
    GutRetV W G haelt boden a c := by
  obtain ⟨hr1, Ls, heq1, hsp1, hrk1, hgood1, hkons1⟩ := h1
  obtain ⟨hr2, heq2, hgood2, hkons2⟩ := h2
  refine ⟨hr1.trans hr2, ⟨Ls, ?_, hsp1, hrk1, ?_, ?_⟩⟩
  · rw [heq2, heq1]
  · intro e he
    rcases hgood1 e he with h | h
    · rcases hgood2 e h with h' | h'
      · exact .inl h'
      · exact .inr h'
    · exact .inr h
  · intro k
    exact hkons1 (hkons2 k)

theorem GutRetV.transRetV {W G} {haelt : List D.Lock} {boden : Option Int} {a b c : World D}
    (h1 : GutRetV W G haelt boden a b) (h2 : GutRetV W G haelt boden b c) :
    GutRetV W G haelt boden a c := by
  obtain ⟨hr1, Ls1, heq1, hsp1, hrk1, hgood1, hkons1⟩ := h1
  obtain ⟨hr2, Ls2, heq2, hsp2, hrk2, hgood2, hkons2⟩ := h2
  refine ⟨hr1.trans hr2, ⟨Ls1 ++ Ls2, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [heq2, heq1, List.foldl_append]
  · intro L hL
    simp only [List.mem_append] at hL
    rcases hL with hL | hL
    · exact hsp1 L hL
    · exact hsp2 L hL
  · intro L hL c hc
    simp only [List.mem_append] at hL
    rcases hL with hL | hL
    · exact hrk1 L hL c hc
    · exact hrk2 L hL c hc
  · intro e he
    rcases hgood2 e he with h | h
    · rcases hgood1 e h with h' | h'
      · exact .inl h'
      · exact .inr h'
    · exact .inr h
  · intro k
    exact hkons2 (hkons1 k)

/-- A read followed by scope releases is a releasing step with exactly those scopes;
    spare and rank come from the static scope check. -/
theorem gutRetV_retScoped {W G} {haelt : List D.Lock} {boden : Option Int}
    {σ σ1 : World D} (Ls : List D.Lock) (hl : Gut W G σ σ1)
    (hsp : ∀ L ∈ Ls, L ∉ haelt) (hrk : ∀ L ∈ Ls, ∀ c, boden = some c → c ≤ D.rang L) :
    GutRetV W G haelt boden σ (Ls.foldl World.gibt σ1) := by
  have hR := gutRet_retScoped (W := W) (G := G) (σ := σ) (σ1 := σ1) Ls hl
  obtain ⟨hr, ⟨_, heq⟩, hgood, hkons⟩ := hR
  exact ⟨hr, Ls, heq, hsp, hrk, hgood, hkons⟩

/-- A scope release alone is a releasing step with exactly those scopes. -/
theorem gutRetV_retWhyScoped {W G} {haelt : List D.Lock} {boden : Option Int}
    (σ : World D) (Ls : List D.Lock)
    (hsp : ∀ L ∈ Ls, L ∉ haelt) (hrk : ∀ L ∈ Ls, ∀ c, boden = some c → c ≤ D.rang L) :
    GutRetV W G haelt boden σ (Ls.foldl World.gibt σ) := by
  have hR := gutRet_retWhyScoped (W := W) (G := G) (σ := σ) Ls
  obtain ⟨hr, ⟨_, heq⟩, hgood, hkons⟩ := hR
  exact ⟨hr, Ls, heq, hsp, hrk, hgood, hkons⟩

/-- Frame widening for releasing steps (spare and rank are frame-free). -/
theorem GutRetV.weiter {W W' : D.Tab → Bool} {G G' : D.Glob → Bool}
    {haelt : List D.Lock} {boden : Option Int} {a b : World D}
    (hW : ∀ t, W t = true → W' t = true) (hG : ∀ g, G g = true → G' g = true)
    (h : GutRetV W G haelt boden a b) : GutRetV W' G' haelt boden a b := by
  obtain ⟨hr, Ls, heq, hsp, hrk, hgood, hkons⟩ := h
  exact ⟨hr.weiter hW hG, Ls, heq, hsp, hrk, hgood, hkons⟩

/-- Consistency survives scope releases (`gibt` records no constraint). -/
theorem konsistent_gibt_foldl (Ls : List D.Lock) (σ : World D) :
    (Konsistent σ.spur → Konsistent (Ls.foldl World.gibt σ).spur) := by
  induction Ls generalizing σ with
  | nil => exact id
  | cons L Ls ih =>
      intro k
      simp only [List.foldl_cons]
      exact konsistent_cons trivial (ih _ (konsistent_cons trivial k))

/-- Frame survives scope releases (memory kept). -/
theorem rahmen_gibt_foldl {W G} (σ : World D) (Ls : List D.Lock) :
    Rahmen W G σ (Ls.foldl World.gibt σ) := by
  obtain ⟨hs, hg⟩ := World.gibt_foldl_speicher σ Ls
  exact rahmen_gleich (fun _ _ _ _ => by rw [hs]) (fun _ _ => by rw [hg])

/-- A read followed by scope releases is a releasing step with exactly those scopes. -/
theorem gutRet_retScoped {W G} {σ σ1 : World D} (Ls : List D.Lock)
    (hl : Gut W G σ σ1) : GutRet W G σ (Ls.foldl World.gibt σ1) := by
  refine ⟨hl.1.trans (rahmen_gibt_foldl σ1 Ls), ⟨Ls, ?_⟩, ?_, ?_⟩
  · rw [haelt_gibt_foldl, hl.2.1]
  · intro e he
    rw [World.gibt_foldl_spur] at he
    simp only [List.mem_append] at he
    rcases he with he | he
    · simp only [List.mem_map] at he
      obtain ⟨_, _, rfl⟩ := he
      exact .inr trivial
    · rcases hl.2.2.1 e he with h1 | h1
      · exact .inl h1
      · exact .inr h1
  · intro k
    exact konsistent_gibt_foldl Ls σ1 (hl.2.2.2 k)

/-- A scope release alone is a releasing step with exactly those scopes. -/
theorem gutRet_retWhyScoped {W G} (σ : World D) (Ls : List D.Lock) :
    GutRet W G σ (Ls.foldl World.gibt σ) := by
  refine ⟨rahmen_gibt_foldl σ Ls, ⟨Ls, ?_⟩, ?_, ?_⟩
  · rw [haelt_gibt_foldl]
  · intro e he
    rw [World.gibt_foldl_spur] at he
    simp only [List.mem_append] at he
    rcases he with he | he
    · simp only [List.mem_map] at he
      obtain ⟨_, _, rfl⟩ := he
      exact .inr trivial
    · exact .inl he
  · intro k
    exact konsistent_gibt_foldl Ls σ k

/-- Erasing through a taken lock then releasing it is erasing without it,
    when the lock was free before (`locks` premise). -/
theorem erase_nimmt_gibt (L : D.Lock) (Ls : List D.Lock) (h : List D.Lock) (hn : L ∉ h) :
    (Ls.foldl (fun h M => h.erase M) (L :: h)).erase L =
      Ls.foldl (fun h M => h.erase M) h := by
  induction Ls generalizing h with
  | nil => exact List.erase_cons_head L h
  | cons M Ms ih =>
      simp only [List.foldl_cons]
      by_cases heq : M = L
      · subst heq
        simp only [List.erase_cons_head]
        have h_erase : h.erase L = h := List.erase_of_not_mem hn
        rw [h_erase]
        have h_mem : ∀ (h : List D.Lock), L ∉ h →
            L ∉ Ms.foldl (fun h M => h.erase M) h := by
          intro h hn
          induction Ms generalizing h with
          | nil => exact hn
          | cons N Ns ih2 =>
              simp only [List.foldl_cons]
              exact ih2 _ (fun hm => hn (List.mem_of_mem_erase hm))
        exact List.erase_of_not_mem (h_mem h hn)
      · simp only [List.erase_cons_tail _ (Ne.symm heq)]
        exact ih _ (fun hm => hn (List.mem_of_mem_erase hm))

/-- `locks L { … }` with a releasing body keeps the release list. -/
theorem gut_nimmt_gibtRet {W G} (σ σ1 : World D) (L : D.Lock)
    (hn : (∀ M ∈ σ.haelt, D.rang M < D.rang L) ∧ L ∉ σ.haelt)
    (h : GutRet W G (σ.nimmt L) σ1) : GutRet W G σ (σ1.gibt L) := by
  obtain ⟨Ls, hLs⟩ := h.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (rahmen_gleich (W := W) (G := G) (σ := σ) (σ' := σ.nimmt L) rfl rfl).trans
      (h.1.trans (rahmen_gleich rfl rfl))
  · refine ⟨Ls, ?_⟩
    show (offen σ1.spur).erase L = Ls.foldl (fun h M => h.erase M) (offen σ.spur)
    have e1 : σ1.haelt = Ls.foldl (fun h M => h.erase M) (L :: σ.haelt) := by
      have := hLs
      simp only [World.haelt, World.nimmt, offen] at this ⊢
      exact this
    rw [e1]
    exact erase_nimmt_gibt L Ls _ hn.2
  · intro e he
    simp only [World.gibt, List.mem_cons] at he
    rcases he with rfl | he
    · exact .inr trivial
    · rcases h.2.2.1 e he with h1 | h1
      · simp only [World.nimmt, List.mem_cons] at h1
        rcases h1 with rfl | h1
        · exact .inr ⟨hn.1, hn.2⟩
        · exact .inl h1
      · exact .inr h1
  · intro k
    exact konsistent_cons trivial (h.2.2.2 (konsistent_cons rfl k))

/-- `locks L { … }` with a releasing body, keeping spare and rank (same `Ls`). -/
theorem gut_nimmt_gibtRetV {W G} {haelt : List D.Lock} {boden : Option Int}
    (σ σ1 : World D) (L : D.Lock)
    (hn : (∀ M ∈ σ.haelt, D.rang M < D.rang L) ∧ L ∉ σ.haelt)
    (h : GutRetV W G haelt boden (σ.nimmt L) σ1) :
    GutRetV W G haelt boden σ (σ1.gibt L) := by
  obtain ⟨hr, Ls, heq, hsp, hrk, hgood, hkons⟩ := h
  have hR : GutRet W G (σ.nimmt L) σ1 := ⟨hr, ⟨Ls, heq⟩, hgood, hkons⟩
  have hG := gut_nimmt_gibtRet (W := W) (G := G) (σ := σ) (σ1 := σ1) L hn hR
  obtain ⟨hr', ⟨_, heq'⟩, hgood', hkons'⟩ := hG
  exact ⟨hr', Ls, heq', hsp, hrk, hgood', hkons'⟩

/-- Rahmen und Spur eines Ausgangs gegen die Eingangswelt: `ok`/`leave`/`next`
    halten die Sperren, `zurueck`/`why` geben genau die gekreuzten Scopes frei
    (Spare + Rank aus dem statischen Scope-Check). -/
def GutAusgang (W : D.Tab → Bool) (G : D.Glob → Bool) (σ : World D) (o : Ausgang V l Γ) : Prop :=
  ∀ σ', o.welt = some σ' →
    match o with
    | .zurueck _ _ | .why _ _ => GutRetV W G V.haelt V.boden σ σ'
    | _ => Gut W G σ σ'

def GutEnd (W : D.Tab → Bool) (G : D.Glob → Bool) (σ : World D)
    (o : EndAusgang V l Γ) : Prop :=
  ∀ σ', o.welt = some σ' →
    match o with
    | .zurueck _ _ | .why _ _ => GutRetV W G V.haelt V.boden σ σ'
    | _ => Gut W G σ σ'

theorem GutAusgang.schrumpf {W G} {σ : World D} {o : Ausgang V l (τ :: Γ)}
    (h : GutAusgang W G σ o) : GutAusgang W G σ o.schrumpf := by
  intro σ' hs; cases o <;> simp only [Ausgang.welt, Ausgang.schrumpf, Option.some.injEq, reduceCtorEq] at hs ⊢ <;>
    (subst hs; exact h _ rfl)

theorem GutAusgang.schrumpfArm {W G} {σ : World D} (c : Option Ty)
    {o : Ausgang V l (ArmCtx Γ c)} (h : GutAusgang W G σ o) :
    GutAusgang W G σ (o.schrumpfArm c) := by
  cases c with
  | none => exact h
  | some _ => exact h.schrumpf

theorem GutEnd.schrumpf {W G} {σ : World D} {o : EndAusgang V l (τ :: Γ)}
    (h : GutEnd W G σ o) : GutEnd W G σ o.schrumpf := by
  intro σ' hs; cases o <;> simp only [EndAusgang.welt, EndAusgang.schrumpf, Option.some.injEq, reduceCtorEq] at hs ⊢ <;>
    (subst hs; exact h _ rfl)

theorem GutEnd.zuAusgang {W G} {σ : World D} {o : EndAusgang V l Γ} (h : GutEnd W G σ o) :
    GutAusgang W G σ o.zuAusgang := by
  intro σ' hs; cases o <;> simp only [Ausgang.welt, EndAusgang.zuAusgang, Option.some.injEq, reduceCtorEq] at hs ⊢ <;>
    (subst hs; exact h _ rfl)

/-- Ein Schritt, der schon gut ist, zieht durch einen Unterblock hindurch. -/
theorem GutAusgang.vor {W G} {σ σ1 : World D} {o : Ausgang V l Γ}
    (h1 : Gut W G σ σ1) (h : GutAusgang W G σ1 o) : GutAusgang W G σ o := by
  intro σ' hs
  cases o with
  | ok _ _ => exact h1.trans (h _ hs)
  | zurueck _ _ => exact h1.transRetV (h _ hs)
  | why _ _ => exact h1.transRetV (h _ hs)
  | leave _ _ _ => exact h1.trans (h _ hs)
  | next _ _ _ => exact h1.trans (h _ hs)
  | logik _ => cases hs
  | hardware _ => cases hs

theorem GutEnd.vor {W G} {σ σ1 : World D} {o : EndAusgang V l Γ}
    (h1 : Gut W G σ σ1) (h : GutEnd W G σ1 o) : GutEnd W G σ o := by
  intro σ' hs
  cases o with
  | zurueck _ _ => exact h1.transRetV (h _ hs)
  | why _ _ => exact h1.transRetV (h _ hs)
  | leave _ _ _ => exact h1.trans (h _ hs)
  | next _ _ _ => exact h1.trans (h _ hs)
  | logik _ => cases hs
  | hardware _ => cases hs

/-- A releasing step pulls through a sub-block: non-returns keep the release,
    returns concatenate it. -/
theorem GutAusgang.vorRetV {W G} {haelt : List D.Lock} {boden : Option Int}
    {σ σ1 : World D} {o : Ausgang V l Γ}
    (h1 : GutRetV W G haelt boden σ σ1) (h : GutAusgang W G σ1 o) :
    GutAusgang W G σ o := by
  intro σ' hs
  cases o with
  | ok _ _ => exact h1.transGut (h _ hs)
  | zurueck _ _ => exact h1.transRetV (h _ hs)
  | why _ _ => exact h1.transRetV (h _ hs)
  | leave _ _ _ => exact h1.transGut (h _ hs)
  | next _ _ _ => exact h1.transGut (h _ hs)
  | logik _ => cases hs
  | hardware _ => cases hs

theorem GutEnd.vorRetV {W G} {haelt : List D.Lock} {boden : Option Int}
    {σ σ1 : World D} {o : EndAusgang V l Γ}
    (h1 : GutRetV W G haelt boden σ σ1) (h : GutEnd W G σ1 o) : GutEnd W G σ o := by
  intro σ' hs
  cases o with
  | zurueck _ _ => exact h1.transRetV (h _ hs)
  | why _ _ => exact h1.transRetV (h _ hs)
  | leave _ _ _ => exact h1.transGut (h _ hs)
  | next _ _ _ => exact h1.transGut (h _ hs)
  | logik _ => cases hs
  | hardware _ => cases hs

/-- A releasing step pulls through a sub-block (plain release, no spare/rank). -/
theorem GutAusgang.vorRet {W G} {σ σ1 : World D} {o : Ausgang V l Γ}
    (h1 : GutRet W G σ σ1) (h : GutAusgang W G σ1 o) : GutAusgang W G σ o := by
  intro σ' hs
  cases o with
  | ok _ _ => exact h1.transGut (h _ hs)
  | zurueck _ _ => exact h1.transRet (h _ hs)
  | why _ _ => exact h1.transRet (h _ hs)
  | leave _ _ _ => exact h1.transGut (h _ hs)
  | next _ _ _ => exact h1.transGut (h _ hs)
  | logik _ => cases hs
  | hardware _ => cases hs

theorem GutEnd.vorRet {W G} {σ σ1 : World D} {o : EndAusgang V l Γ}
    (h1 : GutRet W G σ σ1) (h : GutEnd W G σ1 o) : GutEnd W G σ o := by
  intro σ' hs
  cases o with
  | zurueck _ _ => exact h1.transRet (h _ hs)
  | why _ _ => exact h1.transRet (h _ hs)
  | leave _ _ _ => exact h1.transGut (h _ hs)
  | next _ _ _ => exact h1.transGut (h _ hs)
  | logik _ => cases hs
  | hardware _ => cases hs

/-- `locks L { … }`: nehmen, Rumpf, geben. -/
theorem GutAusgang.gibt {W G} {σ : World D} (L : D.Lock)
    (hn : (∀ M ∈ σ.haelt, D.rang M < D.rang L) ∧ L ∉ σ.haelt) {o : Ausgang V l Γ}
    (h : GutAusgang W G (σ.nimmt L) o) : GutAusgang W G σ (o.mapWelt (·.gibt L)) := by
  intro σ' hs
  cases o with
  | ok _ _ =>
      simp only [Ausgang.welt, Ausgang.mapWelt, Option.some.injEq] at hs ⊢
      subst hs; exact gut_nimmt_gibt _ _ L hn (h _ rfl)
  | zurueck _ _ =>
      simp only [Ausgang.welt, Ausgang.mapWelt, Option.some.injEq] at hs ⊢
      subst hs; exact gut_nimmt_gibtRetV _ _ L hn (h _ rfl)
  | why _ _ =>
      simp only [Ausgang.welt, Ausgang.mapWelt, Option.some.injEq] at hs ⊢
      subst hs; exact gut_nimmt_gibtRetV _ _ L hn (h _ rfl)
  | leave _ _ _ =>
      simp only [Ausgang.welt, Ausgang.mapWelt, Option.some.injEq] at hs ⊢
      subst hs; exact gut_nimmt_gibt _ _ L hn (h _ rfl)
  | next _ _ _ =>
      simp only [Ausgang.welt, Ausgang.mapWelt, Option.some.injEq] at hs ⊢
      subst hs; exact gut_nimmt_gibt _ _ L hn (h _ rfl)
  | logik _ => simp only [Ausgang.welt, Ausgang.mapWelt, reduceCtorEq] at hs
  | hardware _ => simp only [Ausgang.welt, Ausgang.mapWelt, reduceCtorEq] at hs

/-- Von einem `Λ` zu einem, das hoechstens weniger Zeugnisse nennt, ueber einen guten Schritt. -/
theorem heldGenau_weiter {W G} {σ σ1 : World D} {Λ Λ' : List (Res D)}
    (hm : ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ) (hg : Gut W G σ σ1) (hh : HeldGenau Λ σ.haelt) :
    HeldGenau Λ' σ1.haelt := by
  intro L; rw [hg.haelt, hm L]; exact hh L

theorem held_anfang (S : Signatur D.Tab D.Glob D.Lock D.Marke) (L : D.Lock) :
    Res.held L ∈ Signatur.anfang D S ↔ L ∈ S.haelt := by
  unfold Signatur.anfang
  simp only [List.mem_append, List.mem_map]
  constructor
  · rintro (⟨M, hM, hML⟩ | ⟨m, _, hm⟩)
    · cases hML; exact hM
    · cases m; simp only [Res.vonMarke, reduceCtorEq] at hm
  · intro h; exact .inl ⟨L, h, rfl⟩

theorem held_ende (V : Vertrag D) (L : D.Lock) : Res.held L ∈ V.ende ↔ L ∈ V.haelt := by
  unfold Vertrag.ende
  simp only [List.mem_append, List.mem_map]
  constructor
  · rintro (⟨M, hM, hML⟩ | ⟨m, _, hm⟩)
    · cases hML; exact hM
    · cases m; simp only [Res.vonMarke, reduceCtorEq] at hm
  · intro h; exact .inl ⟨L, h, rfl⟩

/-- Der Rufer haelt genau, was der Gerufene am Eintritt nennt. -/
theorem heldGenau_ruf {S : Signatur D.Tab D.Glob D.Lock D.Marke} {Λ : List (Res D)} {h : List D.Lock}
    (hh' : ∀ L, Res.held L ∈ Λ ↔ L ∈ S.haelt) (hh : HeldGenau Λ h) : HeldGenau (Signatur.anfang D S) h := by
  intro L; rw [held_anfang, ← hh' L]; exact hh L

theorem heldGenau_locks {Λ : List (Res D)} {h : List D.Lock} (L : D.Lock) (hh : HeldGenau Λ h) :
    HeldGenau (Res.held L :: Λ) (L :: h) := by
  intro M
  simp only [List.mem_cons, Res.held.injEq]
  constructor
  · rintro (rfl | hM)
    · exact .inl rfl
    · exact .inr ((hh M).mp hM)
  · rintro (rfl | hM)
    · exact .inl rfl
    · exact .inr ((hh M).mpr hM)

/-- Ein `locks L` nimmt eine Sperre, die der Faden NICHT haelt: alles Gehaltene hat kleineren
    Rang, und `rang L < rang L` ist keine Zahl. -/
theorem nicht_gehalten {Λ : List (Res D)} {h : List D.Lock} (L : D.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L) (hh : HeldGenau Λ h) :
    (∀ M ∈ h, D.rang M < D.rang L) ∧ L ∉ h := by
  refine ⟨fun M hM => hr M ((hh M).mpr hM), ?_⟩
  intro hL
  have := hr L ((hh L).mpr hL)
  omega

/-! #### The floor forms (held-set relaxation, 2026-09-13) -/

theorem heldB_weiter {W G} {bo : Option Int} {σ σ1 : World D} {Λ Λ' : List (Res D)}
    (hm : ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ) (hg : Gut W G σ σ1) (hh : HeldB bo Λ σ.haelt) :
    HeldB bo Λ' σ1.haelt := by
  rw [hg.haelt]
  exact ⟨fun L hL => hh.1 L ((hm L).mp hL), fun L hL hn => hh.2 L hL (fun h => hn ((hm L).mpr h))⟩

/-- Membership survives a release that does not name the lock. -/
theorem mem_foldl_erase (L : D.Lock) (Ks : List D.Lock) (h : List D.Lock)
    (hm : L ∈ h) (hn : L ∉ Ks) : L ∈ Ks.foldl (fun h M => h.erase M) h := by
  induction Ks generalizing h with
  | nil => exact hm
  | cons M Ms ih =>
      simp only [List.foldl_cons]
      have hne : L ≠ M := by intro e; subst e; exact hn List.mem_cons_self
      refine ih _ (List.mem_erase_of_ne hne hm) (fun hcon => hn (List.mem_cons_of_mem _ hcon))

/-- Transport through a spare+rank release: every needed lock survives. Required
    locks survive by spare; extras (held, not required) survive by rank — they
    rank below the floor (`hx`, i.e. `RufPasst.hx` at the call site) while every
    released lock ranks at or above it. Erasure only removes, so the floor part
    rides along (`BravRet.mem`). -/
theorem heldB_weiterRet {W G} {haelt : List D.Lock} {boden : Option Int} {bo : Option Int}
    {σ σ1 : World D} {Λ Λ' : List (Res D)}
    (hm : ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ)
    (hg : GutRetV W G haelt boden σ σ1) (hh : HeldB bo Λ σ.haelt)
    (hx : ∀ L, Res.held L ∈ Λ → L ∉ haelt → ∃ c, boden = some c ∧ D.rang L < c) :
    HeldB bo Λ' σ1.haelt := by
  obtain ⟨_, Ls, heq, hsp, hrk, _, _⟩ := hg
  have hsurv : ∀ L, Res.held L ∈ Λ' → L ∈ σ1.haelt := by
    intro L hL
    have hLΛ : Res.held L ∈ Λ := (hm L).mp hL
    have hLh : L ∈ σ.haelt := hh.1 L hLΛ
    have hnotin : L ∉ Ls := by
      intro hLs
      by_cases hreq : L ∈ haelt
      · exact hsp L hLs hreq
      · obtain ⟨c, hc, hlt⟩ := hx L hLΛ hreq
        have hge := hrk L hLs c hc
        omega
    rw [heq]
    exact mem_foldl_erase L Ls σ.haelt hLh hnotin
  have hbR : BravRet σ σ1 := hg.toBravRet
  exact ⟨fun L hL => hsurv L hL,
    fun L hL hn => hh.2 L (hbR.mem hL) (fun h => hn ((hm L).mpr h))⟩

/-- The callee's entry from the caller's: its signature locks are held
    (`RufPasst.hh`), a new extra lock is below its floor (`RufPasst.hx`), an
    extra lock of the caller is below the caller's floor, hence below the
    callee's (`RufPasst.hb`). -/
theorem heldB_ruf {V : Vertrag D} {S : Signatur D.Tab D.Glob D.Lock D.Marke} {Λ : List (Res D)}
    {h : List D.Lock} {b : Option Int} (hp : RufPasst D V S Λ) (hbV : BodenUnter b V.boden)
    (hh : HeldB b Λ h) : HeldB S.boden (Signatur.anfang D S) h := by
  refine ⟨fun L hL => hh.1 L (hp.hh L ((held_anfang S L).mp hL)), fun L hL hn => ?_⟩
  have hnS : L ∉ S.haelt := fun hm => hn ((held_anfang S L).mpr hm)
  by_cases hΛ : Res.held L ∈ Λ
  · exact hp.hx L hΛ hnS
  · obtain ⟨c, hc, hlt⟩ := hh.2 L hL hΛ
    obtain ⟨c', hc', hle⟩ := hbV c hc
    obtain ⟨c'', hc'', hle'⟩ := hp.hb c' hc'
    exact ⟨c'', hc'', by omega⟩

end Gabbro.Grammatik
