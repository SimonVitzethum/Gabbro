/- Part 2 of 5 of `Satz` (split by instrumente/teile/lean-teilen.py; the umbrella `Satz.lean` imports all parts). -/
import Grammatik.Kern.Syntax.Satz.T1

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

theorem NutzlastExpr.orte_darf : (e : NutzlastExpr D Γ Λ c) → ∀ o ∈ e.orte, OrtDarf Λ o
  | .empty, _, h => by simp only [NutzlastExpr.orte, List.not_mem_nil] at h
  | .num e, o, h => e.orte_darf o h
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
  | .retry .., L, h | .forever .., L, h | .axiomCall .., L, h | .regWrite .., L, h
  | .transition .., L, h | .publish .., L, h | .ret .., L, h | .retWhy .., L, h
  | .leave .., L, h | .next .., L, h => h
  | .ite _ t _, L, h => t.held_mono L h
  | .onOption _ p _, L, h => p.held_mono L h
  | .onTag _ arms, L, h => arms.held_mono L h
  | .onWhy _ arms, L, h => arms.held_mono L h
  | .call f _ _ _, L, h => held_nachSig _ _ L h
  | .callInd (n := n) _ _ _ _, L, h => held_nachSig _ _ L h
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
  | .narrow _ _ _ _ rest, L, h | .check _ _ rest, L, h | .float _ _ _ _ _ rest, L, h
  | .floatLit _ _ _ rest, L, h | .floatOf _ _ _ rest, L, h | .floatNarrow _ _ _ _ rest, L, h =>
      rest.held_mono L h
  | .bindCall f _ _ _ _ rest, L, h => held_nachSig _ _ L (rest.held_mono L h)
  | .bindCallInd _ _ _ _ _ rest, L, h => held_nachSig _ _ L (rest.held_mono L h)
  | .bindCallElse f _ _ _ _ _ rest, L, h => held_nachSig _ _ L (rest.held_mono L h)
  | .bindAxiomElse _ _ _ _ _ _ _ _ _ rest, L, h => rest.held_mono L h

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
  | .retry .., _ | .forever .., _ | .axiomCall .., _ | .regWrite .., _
  | .transition .., _ | .publish .., _ | .ret .., _ | .retWhy .., _
  | .leave .., _ | .next .., _ => Iff.rfl
  | .ite _ t _, L => t.held_iff L
  | .onOption _ p _, L => p.held_iff L
  | .onTag _ arms, L => arms.held_iff L
  | .onWhy _ arms, L => arms.held_iff L
  | .call f _ _ _, L => held_nachSig_iff _ _ L
  | .callInd (n := n) _ _ _ _, L => held_nachSig_iff _ _ L
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
  | .narrow _ _ _ _ rest, L | .check _ _ rest, L | .float _ _ _ _ _ rest, L
  | .floatLit _ _ _ rest, L | .floatOf _ _ _ rest, L | .floatNarrow _ _ _ _ rest, L =>
      rest.held_iff L
  | .bindCall f _ _ _ _ rest, L => (rest.held_iff L).trans (held_nachSig_iff _ _ L)
  | .bindCallInd _ _ _ _ _ rest, L => (rest.held_iff L).trans (held_nachSig_iff _ _ L)
  | .bindCallElse f _ _ _ _ _ rest, L => (rest.held_iff L).trans (held_nachSig_iff _ _ L)
  | .bindAxiomElse _ _ _ _ _ _ _ _ _ rest, L => rest.held_iff L

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

/-- Rahmen und Spur eines Ausgangs gegen die Eingangswelt. -/
def GutAusgang (W : D.Tab → Bool) (G : D.Glob → Bool) (σ : World D) (o : Ausgang V l Γ) : Prop :=
  ∀ σ', o.welt = some σ' → Gut W G σ σ'

def GutEnd (W : D.Tab → Bool) (G : D.Glob → Bool) (σ : World D) (o : EndAusgang V l Γ) : Prop :=
  ∀ σ', o.welt = some σ' → Gut W G σ σ'

theorem GutAusgang.schrumpf {W G} {σ : World D} {o : Ausgang V l (τ :: Γ)}
    (h : GutAusgang W G σ o) : GutAusgang W G σ o.schrumpf := by
  intro σ' hs; cases o <;> simp only [Ausgang.welt, Ausgang.schrumpf, Option.some.injEq, reduceCtorEq] at hs ⊢ <;>
    (subst hs; exact h _ rfl)

theorem GutAusgang.schrumpfArm {W G} {σ : World D} (c : Option (Int × Int))
    {o : Ausgang V l (ArmCtx Γ c)} (h : GutAusgang W G σ o) :
    GutAusgang W G σ (o.schrumpfArm c) := by
  cases c with
  | none => exact h
  | some p => obtain ⟨_, _⟩ := p; exact h.schrumpf

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
    (h1 : Gut W G σ σ1) (h : GutAusgang W G σ1 o) : GutAusgang W G σ o :=
  fun σ' hs => h1.trans (h σ' hs)

theorem GutEnd.vor {W G} {σ σ1 : World D} {o : EndAusgang V l Γ}
    (h1 : Gut W G σ σ1) (h : GutEnd W G σ1 o) : GutEnd W G σ o :=
  fun σ' hs => h1.trans (h σ' hs)

/-- `locks L { … }`: nehmen, Rumpf, geben. -/
theorem GutAusgang.gibt {W G} {σ : World D} (L : D.Lock)
    (hn : (∀ M ∈ σ.haelt, D.rang M < D.rang L) ∧ L ∉ σ.haelt) {o : Ausgang V l Γ}
    (h : GutAusgang W G (σ.nimmt L) o) : GutAusgang W G σ (o.mapWelt (·.gibt L)) := by
  intro σ' hs
  cases o <;> simp only [Ausgang.welt, Ausgang.mapWelt, Option.some.injEq, reduceCtorEq] at hs ⊢ <;>
    (subst hs; exact gut_nimmt_gibt _ _ L hn (h _ rfl))

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

theorem heldB_locks {bo : Option Int} {Λ : List (Res D)} {h : List D.Lock} (L : D.Lock)
    (hh : HeldB bo Λ h) : HeldB bo (Res.held L :: Λ) (L :: h) := by
  refine ⟨fun M hM => ?_, fun M hM hn => ?_⟩
  · rcases List.mem_cons.mp hM with hM | hM
    · cases hM; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hh.1 M hM)
  · rcases List.mem_cons.mp hM with rfl | hM
    · exact absurd List.mem_cons_self hn
    · exact hh.2 M hM (fun h => hn (List.mem_cons_of_mem _ h))

/-- A `locks L` of a body whose every lock ranks at least the floor
    (`c ≤ rang L`) takes a lock that is not held, above everything held. -/
theorem nicht_gehaltenB {bo : Option Int} {Λ : List (Res D)} {h : List D.Lock} (L : D.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L) (hh : HeldB bo Λ h)
    (hc : ∀ c, bo = some c → c ≤ D.rang L) :
    (∀ M ∈ h, D.rang M < D.rang L) ∧ L ∉ h := by
  have key : ∀ M ∈ h, D.rang M < D.rang L := by
    intro M hM
    by_cases hΛ : Res.held M ∈ Λ
    · exact hr M hΛ
    · obtain ⟨c, hc', hlt⟩ := hh.2 M hM hΛ
      have := hc c hc'
      omega
  refine ⟨key, fun hL => ?_⟩
  have := key L hL
  omega

theorem orte_tab {Λ : List (Res D)} {t : D.Tab} (hL : darf D t Λ) : OrtDarf Λ (.inl t) := hL
theorem orte_glob {Λ : List (Res D)} {g : D.Glob} (hL : gdarf D g Λ) : OrtDarf Λ (.inr g) := hL

theorem orte_cons {Λ : List (Res D)} {o : D.Tab ⊕ D.Glob} {os : List (D.Tab ⊕ D.Glob)}
    (h1 : OrtDarf Λ o) (h2 : ∀ o ∈ os, OrtDarf Λ o) : ∀ o' ∈ o :: os, OrtDarf Λ o' := by
  intro o' h; simp only [List.mem_cons] at h
  rcases h with rfl | h
  · exact h1
  · exact h2 o' h

/-- Die Praemissen ueber die Umgebung, benannt: der Ruf haelt Rahmen und Spur seines Gerufenen
    (das ist der Satz eine Ebene tiefer, `rufAt_gut` unten), und die Hardware den Rahmen ihres
    `effects` und laesst Sperren und Spur, wie sie sind (H1 -- eine Annahme). -/
def GutR (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ f σ ρ, HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) σ.haelt →
    ∀ σ', (R f σ ρ).welt = some σ' → Gut (D.schreibt f) (D.gschreibt f) σ σ'

/-- The write events of one axiom over explicit carrier domains, in a fixed
    order (tables, then globals): one `zugriff`-with-`true` per declared table
    write, one `gzugriff`-with-`true` per declared global write -- the
    `schreibSlot`/`World.merke` write-event constructor. The domains ride
    along because carrier types are not enumerable (`stmtTraeger` in
    `Extraktion.lean` takes them for the same reason); `Λ`/`h` ride along
    because a recorded event must name its guards and the held locks. -/
def axiomSpur (tabs : List D.Tab) (globs : List D.Glob) (a : D.Ax)
    (Λ : List (Res D)) (h : List D.Lock) : List (Ereignis D) :=
  (tabs.filter (D.aschreibt a)).map (fun t => Ereignis.zugriff t true Λ h) ++
    (globs.filter (D.agschreibt a)).map (fun g => Ereignis.gzugriff g true Λ h)

/-- Membership in `axiomSpur`: a declared table write or a declared global
    write, with the call's guards and held locks. -/
theorem axiomSpur_mem {tabs : List D.Tab} {globs : List D.Glob} {a : D.Ax}
    {Λ : List (Res D)} {h : List D.Lock} {e : Ereignis D}
    (hmem : e ∈ axiomSpur tabs globs a Λ h) :
    (∃ t, t ∈ tabs ∧ D.aschreibt a t = true ∧ e = Ereignis.zugriff t true Λ h) ∨
      (∃ g, g ∈ globs ∧ D.agschreibt a g = true ∧ e = Ereignis.gzugriff g true Λ h) := by
  simp only [axiomSpur, List.mem_append, List.mem_map] at hmem
  rcases hmem with ⟨t, htf, rfl⟩ | ⟨g, hgf, rfl⟩
  · obtain ⟨hmem, hwr⟩ := List.mem_filter.mp htf
    exact Or.inl ⟨t, hmem, hwr, rfl⟩
  · obtain ⟨hmem, hwr⟩ := List.mem_filter.mp hgf
    exact Or.inr ⟨g, hmem, hwr, rfl⟩

/-- Every `axiomSpur` event records the held locks. -/
theorem axiomSpur_zugriffMit (tabs : List D.Tab) (globs : List D.Glob) (a : D.Ax)
    (Λ : List (Res D)) (h : List D.Lock) :
    ∀ e ∈ axiomSpur tabs globs a Λ h, e.zugriffMit h := by
  intro e hmem
  rcases axiomSpur_mem hmem with ⟨t, _, _, rfl⟩ | ⟨g, _, _, rfl⟩ <;>
    simp only [Ereignis.zugriffMit]

/-- Every `axiomSpur` event is good, when the guards hold it. -/
theorem axiomSpur_gut (tabs : List D.Tab) (globs : List D.Glob) (a : D.Ax)
    (Λ : List (Res D)) (h : List D.Lock)
    (hdt : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hdg : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (hhi : HeldIn Λ h) :
    ∀ e ∈ axiomSpur tabs globs a Λ h, e.gut := by
  intro e hmem
  rcases axiomSpur_mem hmem with ⟨t, _, hwr, rfl⟩ | ⟨g, _, hwr, rfl⟩
  · exact ⟨hdt t hwr, hhi⟩
  · exact ⟨hdg g hwr, hhi⟩

/-- A declared table write is recorded in `axiomSpur`. -/
theorem axiomSpur_write_tab (tabs : List D.Tab) (globs : List D.Glob) (a : D.Ax)
    (Λ : List (Res D)) (h : List D.Lock) (t : D.Tab)
    (hmem : t ∈ tabs) (hwr : D.aschreibt a t = true) :
    Ereignis.zugriff t true Λ h ∈ axiomSpur tabs globs a Λ h := by
  simp only [axiomSpur, List.mem_append]
  exact Or.inl (List.mem_map.mpr ⟨t, List.mem_filter.mpr ⟨hmem, hwr⟩, rfl⟩)

/-- A declared global write is recorded in `axiomSpur`. -/
theorem axiomSpur_write_glob (tabs : List D.Tab) (globs : List D.Glob) (a : D.Ax)
    (Λ : List (Res D)) (h : List D.Lock) (g : D.Glob)
    (hmem : g ∈ globs) (hwr : D.agschreibt a g = true) :
    Ereignis.gzugriff g true Λ h ∈ axiomSpur tabs globs a Λ h := by
  simp only [axiomSpur, List.mem_append]
  exact Or.inr (List.mem_map.mpr ⟨g, List.mem_filter.mpr ⟨hmem, hwr⟩, rfl⟩)

/-- The oracle bound, conditional trace: the answer respects the declared
    footprint and keeps the held locks in every world; in worlds where the
    axiom's lock guards are held (the situation of every real call -- the
    `axiomCall`/`bindAxiom` guard premises `hd`/`hgd` plus `HeldGenau` give
    it at the call site), it records its declared writes as `axiomSpur`
    events over complete domains, with a mark-free guard trace it holds.
    In worlds where the guards are not held the trace is unconstrained:
    no typed execution reaches them. -/
def GutO (O : Orakel D) : Prop :=
  ∀ a σ ρ, Rahmen (D.aschreibt a) (D.agschreibt a) σ (O.wirkt a σ ρ).1 ∧
    (O.wirkt a σ ρ).1.haelt = σ.haelt ∧
    ((∀ t, D.aschreibt a t = true → ∀ L, Sum.inl L ∈ D.braucht t → L ∈ σ.haelt) →
     (∀ g, D.agschreibt a g = true → ∀ L, Sum.inl L ∈ D.gbraucht g → L ∈ σ.haelt) →
     ∃ tabs : List D.Tab, ∃ globs : List D.Glob, ∃ Λe : List (Res D),
      (∀ t, D.aschreibt a t = true → t ∈ tabs) ∧
      (∀ g, D.agschreibt a g = true → g ∈ globs) ∧
      (∀ t, D.aschreibt a t = true → darf D t Λe) ∧
      (∀ g, D.agschreibt a g = true → gdarf D g Λe) ∧
      (∀ m st, Res.marke m st ∉ Λe) ∧
      HeldIn Λe σ.haelt ∧
      (O.wirkt a σ ρ).1.spur = axiomSpur tabs globs a Λe σ.haelt ++ σ.spur)


end Gabbro.Grammatik
