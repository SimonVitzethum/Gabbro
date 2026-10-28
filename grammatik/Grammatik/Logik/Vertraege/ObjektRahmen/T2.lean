/- Part 2 of 3 of `ObjektRahmen` (split by instrumente/teile/lean-teilen.py; the umbrella `ObjektRahmen.lean` imports all parts). -/
import Grammatik.Logik.Vertraege.ObjektRahmen.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Schleifen
variable {W : D.Tab → Int → Prop} {ps : List (ObjPar D)} {V : Vertrag D} {l : Bool}

theorem traverseLauf_obj {τ : Ty} {Γ : Ctx} (hlen : LenOk ps Γ)
    (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, ObjInv W ps ρ → ObjA W ps σ (schritt σ ρ))
    (hi : ∀ σ ρ, SlotRahmen W σ (inv σ ρ).1) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ), ObjInv W ps ρ →
      ObjA W ps σ (traverseLauf (l := l) schritt inv ks σ ρ) := by
  intro ks
  induction ks with
  | nil =>
      intro σ ρ hρ
      simp only [traverseLauf]
      split
      · exact ⟨hi σ ρ, hρ⟩
      · trivial
  | cons k ks ih =>
      intro σ ρ hρ
      simp only [traverseLauf]
      split
      · trivial
      · have hstep := hs (inv σ ρ).1 (.cons k ρ) (hρ.cons hlen k)
        split
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ObjA.vor ((hi σ ρ).trans hstep.1) (ih σ1 ρ1.tail hstep.2.tail)
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ObjA.vor ((hi σ ρ).trans hstep.1) (ih σ1 ρ1.tail hstep.2.tail)
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          split
          · exact ⟨((hi σ ρ).trans hstep.1).trans (hi σ1 ρ1.tail), hstep.2.tail⟩
          · trivial
        · rename_i σ1 v hs1
          rw [hs1] at hstep
          exact (hi σ ρ).trans hstep
        · rename_i σ1 r hs1
          rw [hs1] at hstep
          exact (hi σ ρ).trans hstep
        · trivial
        · trivial

theorem retryLauf_obj {Γ : Ctx} (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueberlauf : World D → Env D Γ → Ausgang V l Γ)
    (hs : ∀ σ ρ, ObjInv W ps ρ → ObjA W ps σ (schritt σ ρ))
    (hb : ∀ σ ρ, SlotRahmen W σ (bis σ ρ).1)
    (hu : ∀ σ ρ, ObjInv W ps ρ → ObjA W ps σ (ueberlauf σ ρ)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ), ObjInv W ps ρ →
      ObjA W ps σ (retryLauf schritt bis ueberlauf n σ ρ) := by
  intro n
  induction n with
  | zero =>
      intro σ ρ hρ
      simp only [retryLauf]
      split
      · exact ⟨hb σ ρ, hρ⟩
      · exact ObjA.vor (hb σ ρ) (hu _ ρ hρ)
  | succ n ih =>
      intro σ ρ hρ
      simp only [retryLauf]
      split
      · exact ⟨hb σ ρ, hρ⟩
      · have hstep := hs (bis σ ρ).1 ρ hρ
        split
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ObjA.vor ((hb σ ρ).trans hstep.1) (ih σ1 ρ1 hstep.2)
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ObjA.vor ((hb σ ρ).trans hstep.1) (ih σ1 ρ1 hstep.2)
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ⟨(hb σ ρ).trans hstep.1, hstep.2⟩
        · rename_i σ1 v hs1
          rw [hs1] at hstep
          exact (hb σ ρ).trans hstep
        · rename_i σ1 r hs1
          rw [hs1] at hstep
          exact (hb σ ρ).trans hstep
        · trivial
        · trivial

theorem foreverLauf_obj {Γ : Ctx} (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, ObjInv W ps ρ → ObjA W ps σ (schritt σ ρ))
    (hi : ∀ σ ρ, SlotRahmen W σ (inv σ ρ).1) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ), ObjInv W ps ρ →
      ObjA W ps σ (foreverLauf (l := l) a schritt inv n σ ρ) := by
  intro n
  induction n with
  | zero => intro σ ρ _; simp only [foreverLauf]; trivial
  | succ n ih =>
      intro σ ρ hρ
      simp only [foreverLauf]
      split
      · trivial
      · have hstep := hs (inv σ ρ).1 ρ hρ
        split
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ObjA.vor ((hi σ ρ).trans hstep.1) (ih σ1 ρ1 hstep.2)
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ObjA.vor ((hi σ ρ).trans hstep.1) (ih σ1 ρ1 hstep.2)
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ⟨(hi σ ρ).trans hstep.1, hstep.2⟩
        · rename_i σ1 v hs1
          rw [hs1] at hstep
          exact (hi σ ρ).trans hstep
        · rename_i σ1 r hs1
          rw [hs1] at hstep
          exact (hi σ ρ).trans hstep
        · trivial
        · trivial

end Schleifen
/-- A completed call admitted by `ObjRufOk` stays inside the caller's frame. -/
theorem ruf_rahmen_in {objs : D.Fn → List (ObjPar D)} {W : D.Tab → Int → Prop}
    {ps : List (ObjPar D)} {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    (hR : ObjTreuR objs R) {Γ : Ctx} {Λ : List (Res D)} {f : D.Fn}
    {args : Args D Γ Λ (D.params f)} {ρ : Env D Γ} (hok : ObjRufOk objs ps f args)
    (hinv : ObjInv W ps ρ) (σ σ1 : World D)
    (hw : (R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).welt =
      some σ1) : SlotRahmen W σ σ1 :=
  (hR f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) σ1 hw).mono
    (objRufOk_rahmen hok hinv _ _)

/-- An axiom that writes no table changes no slot. -/
theorem axiom_rahmen {O : Orakel D} (hO : TreuO O) {W : D.Tab → Int → Prop} {a : D.Ax}
    (hok : KeinTabAx a) (σ : World D) (ρ : Env D (D.aparams a))
    {σ1 : World D} (h : (axiomAntwort O a σ ρ).1 = σ1) : SlotRahmen W σ σ1 := by
  have h1 := axiomAntwort_treu O hO a σ ρ
  rw [h] at h1
  exact fun t k f _ => h1.1.1 t (hok t) k f

/-! ## 7. THE INDUCTION over the whole grammar -/

section Rumpf
variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (objs : D.Fn → List (ObjPar D)) (W : D.Tab → Int → Prop) (ps : List (ObjPar D))
variable (hR : ObjTreuR objs R) (hO : TreuO O)
include hR hO
set_option linter.unusedSectionVars false

mutual

/-- **The frame over objects of one statement**, at EVERY world. -/
theorem stmt_obj {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ (s : Stmt D V l Γ Λ Λ'), oS objs ps s → ∀ (σ : World D) (ρ : Env D Γ),
    LenOk ps Γ → ObjInv W ps ρ → ObjA W ps σ (execStmt O passes R s σ ρ)
  | .assignSlot t f i e hw hL, hok, σ, ρ, _, hinv => by
      obtain ⟨x, rfl, op, hop, hrw, htab, hidx⟩ := hok
      simp only [execStmt]
      exact ⟨slotRahmen_schreib σ _ rfl f _ Λ (schreibOk_in hinv hop hrw htab hidx _ _), hinv⟩
  | .assignThru p t _ f i e hw hL, hok, σ, ρ, _, hinv => by
      obtain ⟨x, rfl, op, hop, hrw, htab, hidx⟩ := hok
      simp only [execStmt]
      exact ⟨slotRahmen_schreib σ _ rfl f _ Λ (schreibOk_in hinv hop hrw htab hidx _ _), hinv⟩
  | .assignGlob g e hw hL, _, σ, ρ, _, hinv => by
      simp only [execStmt]
      exact ⟨slotRahmen_gleich rfl, hinv⟩
  | .putBytes .., hok, _, _, _, _ => hok.elim
  | .assignVar x e, hok, σ, ρ, _, hinv => by
      simp only [execStmt]
      refine ⟨slotRahmen_gleich rfl, ?_⟩
      intro op hop hrw k hk
      rw [Env.unten_set ρ x _ (hok op hop hrw)] at hk
      exact hinv op hop hrw k hk
  | .shift t f hτ i von nach hn he hw hL, hok, σ, ρ, _, hinv => by
      obtain ⟨x, rfl, op, hop, hrw, htab, hidx⟩ := hok
      simp only [execStmt]
      split
      · exact ⟨slotRahmen_schreib σ _ rfl f _ Λ (schreibOk_in hinv hop hrw htab hidx _ _), hinv⟩
      · trivial
  | .ite c t e, hok, σ, ρ, hlen, hinv => by
      simp only [execStmt]
      split
      · exact ObjA.vor (slotRahmen_gleich rfl) (block_obj t hok.1 _ ρ hlen hinv)
      · exact ObjA.vor (slotRahmen_gleich rfl) (block_obj e hok.2 _ ρ hlen hinv)
  | .onOption o p a, hok, σ, ρ, hlen, hinv => by
      simp only [execStmt]
      split
      · rename_i k _
        exact ObjA.vor (slotRahmen_gleich rfl)
          (block_obj p hok.1 _ (.cons k ρ) (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · exact ObjA.vor (slotRahmen_gleich rfl) (block_obj a hok.2 _ ρ hlen hinv)
  | .onTag v arms, hok, σ, ρ, hlen, hinv => by
      simp only [execStmt]
      exact ObjA.vor (slotRahmen_gleich rfl) (arms_obj arms hok _ _ ρ hlen hinv)
  | .onWhy r arms, hok, σ, ρ, hlen, hinv => by
      simp only [execStmt]
      exact ObjA.vor (slotRahmen_gleich rfl) (grund_obj arms hok _ _ ρ hlen hinv)
  | .call f args hp hr, hok, σ, ρ, _, hinv => by
      simp only [execStmt]
      split
      · rename_i σ1 v hR1
        exact ⟨ruf_rahmen_in hR hok hinv σ σ1 (by rw [hR1]; rfl), hinv⟩
      · rename_i σ1 r _; exact keinGrund hr r
      · trivial
      · trivial
  | .callInd .., hok, _, _, _, _ => hok.elim
  | .locks L hr body, hok, σ, ρ, hlen, hinv => by
      simp only [execStmt]
      exact ObjA.gibt L (block_obj body hok (σ.nimmt L) ρ hlen hinv)
  | .breaking _ body, hok, σ, ρ, hlen, hinv => by
      simp only [execStmt]
      exact block_obj body hok σ ρ hlen hinv
  | .traverse t inv body, hok, σ, ρ, hlen, hinv => by
      simp only [execStmt]
      exact traverseLauf_obj hlen _ _ (fun σ ρ h => block_obj body hok σ ρ (hlen.cons _) h)
        (fun _ _ => slotRahmen_gleich rfl) _ σ ρ hinv
  | .retry n bis body ueberlauf, hok, σ, ρ, hlen, hinv => by
      simp only [execStmt]
      exact retryLauf_obj _ _ _ (fun σ ρ h => block_obj body hok.1 σ ρ hlen h)
        (fun _ _ => slotRahmen_gleich rfl) (fun σ ρ h => block_obj ueberlauf hok.2 σ ρ hlen h)
        n σ ρ hinv
  | .forever a inv body, hok, σ, ρ, hlen, hinv => by
      simp only [execStmt]
      exact foreverLauf_obj a _ _ (fun σ ρ h => block_obj body hok σ ρ hlen h)
        (fun _ _ => slotRahmen_gleich rfl) passes σ ρ hinv
  | .axiomCall a args _ hw hg hd hgd, hok, σ, ρ, _, hinv => by
      simp only [execStmt]
      split
      · rename_i σ1 v ha
        refine ⟨?_, hinv⟩
        exact axiom_rahmen hO hok (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) (by rw [ha])
      · trivial
  | .regWrite r _ e, _, σ, ρ, _, hinv => by
      simp only [execStmt]
      exact ⟨slotRahmen_gleich rfl, hinv⟩
  | .transition .., _, σ, ρ, _, hinv => by
      simp only [execStmt]
      exact ⟨SlotRahmen.refl _ _, hinv⟩
  | .publish g e _ _ hw hL, _, σ, ρ, _, hinv => by
      simp only [execStmt]
      exact ⟨slotRahmen_gleich rfl, hinv⟩
  | .advances .., _, σ, ρ, _, hinv => by
      simp only [execStmt]
      exact ⟨SlotRahmen.refl _ _, hinv⟩
  | .retires .., _, σ, ρ, _, hinv => by
      simp only [execStmt]
      exact ⟨SlotRahmen.refl _ _, hinv⟩
  | .ret e _, _, σ, ρ, _, _ => by
      simp only [execStmt]
      exact slotRahmen_gleich rfl
  | .retWhy .., _, σ, ρ, _, _ => by
      simp only [execStmt]
      exact SlotRahmen.refl _ _
  | .leave _, _, σ, ρ, _, hinv => by
      simp only [execStmt]
      exact ⟨SlotRahmen.refl _ _, hinv⟩
  | .next _, _, σ, ρ, _, hinv => by
      simp only [execStmt]
      exact ⟨SlotRahmen.refl _ _, hinv⟩

/-- **The frame over objects of a block.** -/
theorem block_obj {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ (b : Block D V l Γ Λ Λ'), oB objs ps b → ∀ (σ : World D) (ρ : Env D Γ),
    LenOk ps Γ → ObjInv W ps ρ → ObjA W ps σ (execBlock O passes R b σ ρ)
  | .nil, _, σ, ρ, _, hinv => by
      simp only [execBlock]
      exact ⟨SlotRahmen.refl _ _, hinv⟩
  | .cons s rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      have hs := stmt_obj s hok.1 σ ρ hlen hinv
      split
      · rename_i σ1 ρ1 hs1
        rw [hs1] at hs
        exact ObjA.vor hs.1 (block_obj rest hok.2 σ1 ρ1 hlen hs.2)
      · exact hs
  | .bind e rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      exact ObjA.vor (slotRahmen_gleich rfl)
        (block_obj rest hok _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
  | .bindCall f args he hp hr rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · rename_i σ1 v hR1
        exact ObjA.vor (ruf_rahmen_in hR hok.1 hinv σ σ1 (by rw [hR1]; rfl))
          (block_obj rest hok.2 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · rename_i σ1 r _; exact keinGrund hr r
      · trivial
      · trivial
  | .bindCallInd .., hok, _, _, _, _ => hok.elim
  | .bindCallElse f args he hp _ err rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · rename_i σ1 v hR1
        exact ObjA.vor (ruf_rahmen_in hR hok.1 hinv σ σ1 (by rw [hR1]; rfl))
          (block_obj rest hok.2.2 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · rename_i σ1 r hR1
        exact ObjA.vor (ruf_rahmen_in hR hok.1 hinv σ σ1 (by rw [hR1]; rfl))
          (end_obj err hok.2.1 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf.zuAusgang
      · trivial
      · trivial
  | .bindAxiom a args he hw hg hd hgd rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · rename_i σ1 v ha
        exact ObjA.vor (axiom_rahmen hO hok.1 (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) (by rw [ha]))
          (block_obj rest hok.2 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · trivial
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · rename_i σ1 v ha
        exact ObjA.vor (axiom_rahmen hO hok.1 (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
            (by rw [← axiomAntwortSonst_fst, ha]))
          (block_obj rest hok.2.2 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · rename_i σ1 r ha
        exact ObjA.vor (axiom_rahmen hO hok.1 (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
            (by rw [← axiomAntwortSonst_fst, ha]))
          (end_obj err hok.2.1 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf.zuAusgang
      · trivial
  | .regRead r _ rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · split
        · exact (block_obj rest hok _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
        · trivial
      · trivial
  | .regReadElse r _ zusage sonst rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · split
        · exact ObjA.vor (slotRahmen_gleich rfl)
            (block_obj rest hok.2 _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
        · exact ObjA.vor (slotRahmen_gleich rfl) (end_obj sonst hok.1 _ ρ hlen hinv).zuAusgang
      · trivial
  | .awaits g _ _ hL _ rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · exact ObjA.vor (slotRahmen_gleich rfl)
          (block_obj rest hok _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · trivial
  | .exchange g neu hw hL rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      exact ObjA.vor (slotRahmen_gleich rfl)
        (block_obj rest hok _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
  | .narrow e lo' hi' sonst rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · exact ObjA.vor (slotRahmen_gleich rfl)
          (block_obj rest hok.2 _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · exact ObjA.vor (slotRahmen_gleich rfl) (end_obj sonst hok.1 _ ρ hlen hinv).zuAusgang
  | .check c sonst rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · exact ObjA.vor (slotRahmen_gleich rfl) (block_obj rest hok.2 _ ρ hlen hinv)
      · exact ObjA.vor (slotRahmen_gleich rfl) (end_obj sonst hok.1 _ ρ hlen hinv).zuAusgang
  | .float op a b lo hi rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · exact ObjA.vor (slotRahmen_gleich rfl)
          (block_obj rest hok _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · trivial
  | .floatLit q lo hi rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · exact (block_obj rest hok _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · trivial
  | .floatOf e lo hi rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · exact ObjA.vor (slotRahmen_gleich rfl)
          (block_obj rest hok _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · trivial
  | .floatNarrow e lo hi sonst rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · exact ObjA.vor (slotRahmen_gleich rfl)
          (block_obj rest hok.2 _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · exact ObjA.vor (slotRahmen_gleich rfl) (end_obj sonst hok.1 _ ρ hlen hinv).zuAusgang

/-- **The frame over objects of an end block.** -/
theorem end_obj {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    ∀ (b : Endblock D V l Γ Λ), oE objs ps b → ∀ (σ : World D) (ρ : Env D Γ),
    LenOk ps Γ → ObjInv W ps ρ → ObjE W ps σ (execEnd O passes R b σ ρ)
  | .ret e _, _, σ, ρ, _, _ => by
      simp only [execEnd]
      exact slotRahmen_gleich rfl
  | .retWhy .., _, σ, ρ, _, _ => by
      simp only [execEnd]
      exact SlotRahmen.refl _ _
  | .leave _, _, σ, ρ, _, hinv => by
      simp only [execEnd]
      exact ⟨SlotRahmen.refl _ _, hinv⟩
  | .next _, _, σ, ρ, _, hinv => by
      simp only [execEnd]
      exact ⟨SlotRahmen.refl _ _, hinv⟩
  | .cons s rest, hok, σ, ρ, hlen, hinv => by
      simp only [execEnd]
      have hs := stmt_obj s hok.1 σ ρ hlen hinv
      split
      · rename_i σ1 ρ1 hs1
        rw [hs1] at hs
        exact ObjE.vor hs.1 (end_obj rest hok.2 σ1 ρ1 hlen hs.2)
      all_goals first
        | trivial
        | (rename_i hs1; rw [hs1] at hs; exact hs)
  | .bind e rest, hok, σ, ρ, hlen, hinv => by
      simp only [execEnd]
      exact ObjE.vor (slotRahmen_gleich rfl)
        (end_obj rest hok _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
  | .bindCall f args he hp hr rest, hok, σ, ρ, hlen, hinv => by
      simp only [execEnd]
      split
      · rename_i σ1 v hR1
        exact ObjE.vor (ruf_rahmen_in hR hok.1 hinv σ σ1 (by rw [hR1]; rfl))
          (end_obj rest hok.2 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · rename_i σ1 r _; exact keinGrund hr r
      · trivial
      · trivial
  | .bindCallElse f args he hp _ err rest, hok, σ, ρ, hlen, hinv => by
      simp only [execEnd]
      split
      · rename_i σ1 v hR1
        exact ObjE.vor (ruf_rahmen_in hR hok.1 hinv σ σ1 (by rw [hR1]; rfl))
          (end_obj rest hok.2.2 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · rename_i σ1 r hR1
        exact ObjE.vor (ruf_rahmen_in hR hok.1 hinv σ σ1 (by rw [hR1]; rfl))
          (end_obj err hok.2.1 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · trivial
      · trivial
  | .bindAxiom a args he hw hg hd hgd rest, hok, σ, ρ, hlen, hinv => by
      simp only [execEnd]
      split
      · rename_i σ1 v ha
        exact ObjE.vor (axiom_rahmen hO hok.1 (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) (by rw [ha]))
          (end_obj rest hok.2 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · trivial
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, hok, σ, ρ, hlen, hinv => by
      simp only [execEnd]
      split
      · rename_i σ1 v ha
        exact ObjE.vor (axiom_rahmen hO hok.1 (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
            (by rw [← axiomAntwortSonst_fst, ha]))
          (end_obj rest hok.2.2 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · rename_i σ1 r ha
        exact ObjE.vor (axiom_rahmen hO hok.1 (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
            (by rw [← axiomAntwortSonst_fst, ha]))
          (end_obj err hok.2.1 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · trivial
  | .regRead r _ rest, hok, σ, ρ, hlen, hinv => by
      simp only [execEnd]
      split
      · split
        · exact (end_obj rest hok _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
        · trivial
      · trivial
  | .regReadElse r _ zusage sonst rest, hok, σ, ρ, hlen, hinv => by
      simp only [execEnd]
      split
      · split
        · exact ObjE.vor (slotRahmen_gleich rfl)
            (end_obj rest hok.2 _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
        · exact ObjE.vor (slotRahmen_gleich rfl) (end_obj sonst hok.1 _ ρ hlen hinv)
      · trivial
  | .awaits g _ _ hL _ rest, hok, σ, ρ, hlen, hinv => by
      simp only [execEnd]
      split
      · exact ObjE.vor (slotRahmen_gleich rfl)
          (end_obj rest hok _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · trivial
  | .bindCallInd .., hok, _, _, _, _ => hok.elim
  | .narrow e lo' hi' sonst rest, hok, σ, ρ, hlen, hinv => by
      simp only [execEnd]
      split
      · exact ObjE.vor (slotRahmen_gleich rfl)
          (end_obj rest hok.2 _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · exact ObjE.vor (slotRahmen_gleich rfl) (end_obj sonst hok.1 _ ρ hlen hinv)
  | .exchange g neu hw hL rest, hok, σ, ρ, hlen, hinv => by
      simp only [execEnd]
      exact ObjE.vor (slotRahmen_gleich rfl)
        (end_obj rest hok _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
  | .ite c t e, hok, σ, ρ, hlen, hinv => by
      simp only [execEnd]
      split
      · exact ObjE.vor (slotRahmen_gleich rfl) (end_obj t hok.1 _ ρ hlen hinv)
      · exact ObjE.vor (slotRahmen_gleich rfl) (end_obj e hok.2 _ ρ hlen hinv)

theorem arms_obj {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    ∀ (arms : Arms D V l Γ Λ Λ' cs), oA objs ps arms → ∀ (v : Wert D (.sum cs)) (σ : World D)
    (ρ : Env D Γ), LenOk ps Γ → ObjInv W ps ρ → ObjA W ps σ (execArms O passes R arms v σ ρ)
  | .cons b _, hok, ⟨⟨0, _⟩, nutz⟩, σ, ρ, hlen, hinv =>
      (block_obj b hok.1 σ (armEnv nutz ρ) (hlen.arm _) (hinv.arm hlen nutz)).schrumpfArm _
  | .cons _ rest, hok, ⟨⟨_ + 1, _⟩, _⟩, σ, ρ, hlen, hinv => arms_obj rest hok.2 _ σ ρ hlen hinv

theorem grund_obj {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    ∀ (arms : GrundArms D V l Γ Λ Λ' n), oG objs ps arms → ∀ (r : Fin n) (σ : World D)
    (ρ : Env D Γ), LenOk ps Γ → ObjInv W ps ρ → ObjA W ps σ (execGrund O passes R arms r σ ρ)
  | .cons b _, hok, ⟨0, _⟩, σ, ρ, hlen, hinv => block_obj b hok.1 σ ρ hlen hinv
  | .cons _ rest, hok, ⟨_ + 1, _⟩, σ, ρ, hlen, hinv => grund_obj rest hok.2 _ σ ρ hlen hinv

end

end Rumpf
/-! ## 8. THE CALL: `rufAt` keeps the frame over objects, and the frame at a separated call -/

theorem foldl_lese_slots_obj (P : Programm D) :
    ∀ (is : List D.Inv) (σ : World D),
      (is.foldl (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte) σ).slots = σ.slots
  | [], _ => rfl
  | i :: is, σ => foldl_lese_slots_obj P is (σ.lese (invSicht D i) (P.invariante i).orte)

/-- **The model's call keeps the frame over objects, at every depth and every world.** The
    only premise besides the program's discipline is the hardware's frame (H1). -/
theorem rufAt_obj (P : Programm D) (O : Orakel D) (passes : Nat) (hO : TreuO O)
    (objs : D.Fn → List (ObjPar D)) (hP : ProgObjOk objs P) :
    ∀ fuel, ObjTreuR objs (rufAt P O passes fuel) := by
  intro fuel
  induction fuel with
  | zero => intro f σ ρ σ' h; simp only [RufAusgang.welt, rufAt, reduceCtorEq] at h
  | succ n ih =>
      intro f σ ρ σ' h
      simp only [rufAt] at h
      split at h
      · simp only [RufAusgang.welt, reduceCtorEq] at h
      · have hb := end_obj (O := O) (passes := passes) (R := rufAt P O passes n) (objs := objs)
          (W := WVon (objs f) ρ) (ps := objs f) ih hO (P.rumpf f) (hP f).1
          (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ (hP f).2.1
          (objInv_eigen _ ρ)
        split at h
        · rename_i σ2 v hs
          rw [hs] at hb
          split at h
          · simp only [RufAusgang.welt, reduceCtorEq] at h
          · split at h
            · simp only [RufAusgang.welt, reduceCtorEq] at h
            · simp only [RufAusgang.welt, Option.some.injEq] at h
              subst h
              intro t k fld hn
              rw [foldl_lese_slots_obj]
              exact hb t k fld hn
        · rename_i σ2 r hs
          simp only [RufAusgang.welt, Option.some.injEq] at h
          subst h
          rw [hs] at hb
          exact hb
        · rename_i hl _ _ _; exact absurd hl (by decide)
        · rename_i hl _ _ _; exact absurd hl (by decide)
        · simp only [RufAusgang.welt, reduceCtorEq] at h
        · simp only [RufAusgang.welt, reduceCtorEq] at h


end Gabbro.Grammatik
