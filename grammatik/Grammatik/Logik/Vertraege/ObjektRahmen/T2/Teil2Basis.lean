module
public import Grammatik.Kern.Syntax.Typen.Fall

public import Grammatik.Logik.Vertraege.ObjektRahmen.T1
public import Grammatik.Logik.Vertraege.ObjektRahmen.T1a
public import Grammatik.Logik.Vertraege.ObjektRahmen.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
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
  | .consumeTraverse t member edge inv bound mass body, hok, σ, ρ, hlen, hinv => by
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
  | .axiomCallElse _ a args _ hp hd hgd _ err, hok, σ, ρ, hlen, hinv => by
      simp only [execStmt]
      split
      · rename_i σ1 v ha
        refine ⟨?_, hinv⟩
        exact axiom_rahmen hO hok.1 (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) (by rw [← axiomAntwortSonst_fst, ha])
      · rename_i σ1 r ha
        exact ObjA.vor (axiom_rahmen hO hok.1 (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) (by rw [← axiomAntwortSonst_fst, ha]))
          (end_obj err hok.2 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf.zuAusgang
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
  | .retScoped e _, _, σ, ρ, _, _ => by
      simp only [execStmt]
      exact slotRahmen_gleich rfl
  | .retWhyScoped .., _, σ, ρ, _, _ => by
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
  | .bindAxiomOpt e a args he hp hd hgd rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · rename_i σ1 v ha
        cases e with
        | none =>
            simp only [Ausgang.weiterOpt] at *
            exact ObjA.vor (axiom_rahmen hO hok.1 (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) (by rw [ha]))
              (block_obj rest hok.2 σ1 _ hlen hinv)
        | some τ =>
            simp only [Ausgang.weiterOpt] at *
            exact ObjA.vor (axiom_rahmen hO hok.1 (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) (by rw [ha]))
              (block_obj rest hok.2 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · trivial
  | .bindAxiomOptElse e a args he hp hd hgd hr err rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · rename_i σ1 v ha
        cases e with
        | none =>
            simp only [Ausgang.weiterOpt] at *
            exact ObjA.vor (axiom_rahmen hO hok.1 (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) (by rw [← axiomAntwortSonst_fst, ha]))
              (block_obj rest hok.2.2 σ1 _ hlen hinv)
        | some τ =>
            simp only [Ausgang.weiterOpt] at *
            exact ObjA.vor (axiom_rahmen hO hok.1 (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) (by rw [← axiomAntwortSonst_fst, ha]))
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
  | .narrowRequired e lo' hi' rest, hok, σ, ρ, hlen, hinv => by
      simp only [execBlock]
      split
      · exact ObjA.vor (slotRahmen_gleich rfl)
          (block_obj rest hok _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · trivial
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
  | .retScoped e _, _, σ, ρ, _, _ => by
      simp only [execEnd]
      exact slotRahmen_gleich rfl
  | .retWhyScoped .., _, σ, ρ, _, _ => by
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
  | .bindAxiomOpt e a args he hp hd hgd rest, hok, σ, ρ, hlen, hinv => by
      simp only [execEnd]
      split
      · rename_i σ1 v ha
        cases e with
        | none =>
            simp only [EndAusgang.weiterOpt] at *
            exact ObjE.vor (axiom_rahmen hO hok.1 (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) (by rw [ha]))
              (end_obj rest hok.2 σ1 _ hlen hinv)
        | some τ =>
            simp only [EndAusgang.weiterOpt] at *
            exact ObjE.vor (axiom_rahmen hO hok.1 (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) (by rw [ha]))
              (end_obj rest hok.2 σ1 _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · trivial
  | .bindAxiomOptElse e a args he hp hd hgd hr err rest, hok, σ, ρ, hlen, hinv => by
      simp only [execEnd]
      split
      · rename_i σ1 v ha
        cases e with
        | none =>
            simp only [EndAusgang.weiterOpt] at *
            exact ObjE.vor (axiom_rahmen hO hok.1 (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) (by rw [← axiomAntwortSonst_fst, ha]))
              (end_obj rest hok.2.2 σ1 _ hlen hinv)
        | some τ =>
            simp only [EndAusgang.weiterOpt] at *
            exact ObjE.vor (axiom_rahmen hO hok.1 (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) (by rw [← axiomAntwortSonst_fst, ha]))
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
  | .narrowRequired e lo' hi' rest, hok, σ, ρ, hlen, hinv => by
      simp only [execEnd]
      split
      · exact ObjE.vor (slotRahmen_gleich rfl)
          (end_obj rest hok _ _ (hlen.cons _) (hinv.cons hlen _)).schrumpf
      · trivial
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
    {cs : List (Option Ty)} :
    ∀ (arms : Arms D V l Γ Λ Λ' cs), oA objs ps arms → ∀ (v : Wert D (.sum cs)) (σ : World D)
    (ρ : Env D Γ), LenOk ps Γ → ObjInv W ps ρ → ObjA W ps σ (execArms O passes R arms v σ ρ)
  | .cons b _, hok, ⟨⟨0, _⟩, nutz⟩, σ, ρ, hlen, hinv =>
      (block_obj b hok.1 σ (armEnv (Fall.toNutzlast _ _ _ _ nutz) ρ) (hlen.arm _) (hinv.arm hlen (Fall.toNutzlast _ _ _ _ nutz))).schrumpfArm _
  | .cons _ rest, hok, ⟨⟨_ + 1, _⟩, _⟩, σ, ρ, hlen, hinv => arms_obj rest hok.2 _ σ ρ hlen hinv

theorem grund_obj {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    ∀ (arms : GrundArms D V l Γ Λ Λ' n), oG objs ps arms → ∀ (r : Fin n) (σ : World D)
    (ρ : Env D Γ), LenOk ps Γ → ObjInv W ps ρ → ObjA W ps σ (execGrund O passes R arms r σ ρ)
  | .cons b _, hok, ⟨0, _⟩, σ, ρ, hlen, hinv => block_obj b hok.1 σ ρ hlen hinv
  | .cons _ rest, hok, ⟨_ + 1, _⟩, σ, ρ, hlen, hinv => grund_obj rest hok.2 _ σ ρ hlen hinv

end

end Rumpf
end Gabbro.Grammatik
