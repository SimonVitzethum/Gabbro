import Grammatik.Bausteine.Arena.Ownership.Ruhe.Iface

/-! **The ownership judgment across the idle root.** Every derivation of the
body judgment over `P` is a derivation over the translated syntax of
`P.mitRuhe`, with the lifted arena and interfaces and the same contexts. -/

namespace Gabbro.Grammatik.ArenaOwnership.Ruhe

open Source Body

variable {D : Deklaration}

theorem assign_varR (c : Context) {Γ : Ctx} {τ : Ty} (x : Var Γ τ) (o : Option Nat) :
    c.assign (varR x) o = c.assign x o := by
  simp only [Context.assign, varR_unten]

section Ctx

variable {A : FreiForm D} (c : Context)

theorem dropContext_outR {erg : Option Ty} (out : Flow.Output A erg) :
    dropContext c (outR A out) = dropContext c out := by
  cases out <;> rfl

theorem resultContext_outR {erg : Option Ty} (out : Flow.Output A erg) :
    resultContext c (outR A out) = resultContext c out := by
  cases out <;> rfl

end Ctx

section Casts

variable {A : FreiForm D} {I : Interfaces A} {V : Vertrag D} {out : Flow.Output A V.erg}

theorem os_nach {l : Bool} {Γ : Ctx} {Λ Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂) {k c c' : Context}
    {s : Stmt D V l Γ Λ Λ₁} (hs : OS A I out k c s c') : OS A I out k c (Stmt.nachΛ h s) c' := by
  subst h; exact hs

theorem ob_vor {l : Bool} {Γ : Ctx} {Λ₁ Λ₂ Λ' : List (Res D)} (h : Λ₁ = Λ₂) {k c c' : Context}
    {b : Block D V l Γ Λ₁ Λ'} (hb : OB A I out k c b c') : OB A I out k c (Block.vorΛ h b) c' := by
  subst h; exact hb

theorem os_post {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {k c c1 c2 : Context} {s : Stmt D V l Γ Λ Λ'}
    (h : c1 = c2) (hs : OS A I out k c s c1) : OS A I out k c s c2 := h ▸ hs

theorem ob_pre {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {k c1 c2 c' : Context} {b : Block D V l Γ Λ Λ'}
    (h : c1 = c2) (hb : OB A I out k c2 b c') : OB A I out k c1 b c' := h ▸ hb

theorem oe_pre {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {k c1 c2 : Context} {e : Endblock D V l Γ Λ}
    (h : c1 = c2) (he : OE A I out k c2 e) : OE A I out k c1 e := h ▸ he

theorem oe_um {l : Bool} {Γ : Ctx} {Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂) {k c : Context}
    {e : Endblock D V l Γ Λ₁} (he : OE A I out k c e) : OE A I out k c (Endblock.umΛ h e) := by
  subst h; exact he

end Casts

section Plan

variable {Γ : Ctx} {Λ : List (Res D)} (c : Context)

theorem planFits_lift {params : Ctx} (m : Modes params) (args : Args D Γ Λ params) :
    planFits c (modeList (modesR m)) (originList c (ruA args)) = planFits c (modeList m) (originList c args) := by
  rw [modeList_modesR, originList_ruA]

theorem afterCall_lift {params : Ctx} (m : Modes params) (args : Args D Γ Λ params) :
    c.afterCall (modeList (modesR m)) (originList c (ruA args)) = c.afterCall (modeList m) (originList c args) := by
  rw [modeList_modesR, originList_ruA]

end Plan

section Lift

variable {A : FreiForm D} {I : Interfaces A} {V : Vertrag D} {out : Flow.Output A V.erg}

theorem sigCompatible_lift {n : Nat} {J : Modes (D.sigNr n).params} {owner : Bool}
    (h : SigCompatible I n J owner) :
    SigCompatible (D := D.mitRuhe) (liftI I) (n + 1) (modesR J) owner := by
  intro f hf
  cases f with
  | none => simp [Deklaration.mitRuhe, passtM] at hf
  | some f =>
    obtain ⟨h1, h2⟩ := h f hf
    exact ⟨(modeList_modesR _).trans (h1.trans (modeList_modesR J).symm), (isOwner_outR A _).trans h2⟩

mutual

theorem os_lift : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {k c c' : Context} {st : Stmt D V l Γ Λ Λ'},
    OS A I out k c st c' → OS (liftA A) (liftI I) (outR A out) k c (ruS st) c'
  | _, _, _, _, _, _, _, _, .assignSlot t f i e hw hL hn hi he hs =>
    .assignSlot _ _ _ _ _ _ hn (by rw [checkExpression_ruE]; exact hi) (by rw [checkExpression_ruE]; exact he)
      (by rw [storeCheck_ruE]; exact hs)
  | _, _, _, _, _, _, _, _, .assignThru p t ht f i e hw hL hn hp hi he hs =>
    .assignThru _ _ _ _ _ _ _ _ hn (by rw [checkExpression_ruE]; exact hp) (by rw [checkExpression_ruE]; exact hi)
      (by rw [checkExpression_ruE]; exact he) (by rw [storeCheck_ruE]; exact hs)
  | _, _, _, _, _, _, _, _, .assignGlob g e hw hL hg he =>
    .assignGlob _ _ _ _ hg (by rw [checkExpression_ruE]; exact he)
  | _, _, _, _, _, _, _, _, .putBytes t f hf n i hlo hhi e hw hL ht hi he =>
    .putBytes _ _ _ _ _ _ _ _ _ _ ht (by rw [checkExpression_ruE]; exact hi) (by rw [checkExpression_ruE]; exact he)
  | l, _, _, _, k, c, _, _, .assignVar x e he => by
    have h := OS.assignVar (A := liftA A) (I := liftI I) (V := vertragR V) (out := outR A out) (l := l) (k := k) (c := c)
      (varR x) (ruE e) ((checkExpression_ruE A c e).trans he)
    rw [origin_ruE, assign_varR] at h
    exact h
  | _, _, _, _, _, _, _, _, .shift t f hτ i von nach hn he hw hL hl hi hs =>
    .shift _ _ _ _ _ _ _ _ _ _ hl (by rw [checkExpression_ruE]; exact hi) (by rw [storeCheck_ruE]; exact hs)
  | _, _, _, _, _, _, _, _, .ite cond t e hc ht he =>
    .ite _ _ _ (by rw [checkExpression_ruE]; exact hc) (ob_lift ht) (ob_lift he)
  | _, _, _, _, _, _, _, _, .onOption o p a ho hp hw ha =>
    .onOption _ _ _ (by rw [checkExpression_ruE]; exact ho) (ob_lift hp) hw (ob_lift ha)
  | _, _, _, _, _, _, _, _, .onTag v arms hv ha =>
    .onTag _ _ (by rw [checkExpression_ruE]; exact hv) (oarms_lift ha)
  | _, _, _, _, _, _, _, _, .onWhy r arms hr ha =>
    .onWhy _ _ (by rw [checkExpression_ruE]; exact hr) (ogrund_lift ha)
  | _, _, _, _, k, c, _, _, .call f args hp hr ha hplan =>
    os_nach _ (os_post ((congrArg (fun x => dropContext x _) (afterCall_lift c _ args)).trans (dropContext_outR _ _))
      (OS.call (A := liftA A) (I := liftI I) (V := vertragR V) (out := outR A out) (k := k) (c := c)
        (some f) (ruA args) (rufPasstR hp) hr ((checkArguments_ruA A _ args).trans ha)
        ((planFits_lift _ _ args).trans hplan)))
  | _, _, _, _, k, c, _, _, .callInd (n := n) p args hp hr J owner hJ hpc ha hplan =>
    os_nach _ (os_post (congrArg (fun x => dropContextB x owner) (afterCall_lift c J args))
      (OS.callInd (A := liftA A) (I := liftI I) (V := vertragR V) (out := outR A out) (k := k) (c := c)
        (n := n + 1) (ruE p) (ruA args) (rufPasstR hp) hr (modesR J) owner (sigCompatible_lift hJ)
        (by rw [checkExpression_ruE]; exact hpc) ((checkArguments_ruA A _ args).trans ha)
        ((planFits_lift _ J args).trans hplan)))
  | _, _, _, _, _, _, _, _, .locks L hr body hb => .locks _ _ _ (ob_lift hb)
  | _, _, _, _, _, _, _, _, .breaking i body hb => .breaking _ _ (ob_lift hb)
  | _, _, _, _, _, _, _, _, .traverse t inv body hentry hinv hb hback =>
    .traverse _ _ _ hentry (by rw [checkExpression_ruE]; exact hinv) (ob_lift hb) hback
  | _, _, _, _, _, _, _, _, .retry n bis body ueber hentry hbis hb hback hu =>
    .retry _ _ _ _ hentry (by rw [checkExpression_ruE]; exact hbis) (ob_lift hb) hback (ob_lift hu)
  | _, _, _, _, _, _, _, _, .forever a inv body hentry hinv hb hback =>
    .forever _ _ _ hentry (by rw [checkExpression_ruE]; exact hinv) (ob_lift hb) hback
  | _, _, _, _, _, _, _, _, .axiomCall a args h hw hg hd hgd hfree ha =>
    .axiomCall _ _ _ _ _ _ _ hfree ((checkArguments_ruA A _ args).trans ha)
  | _, _, _, _, _, _, _, _, .regWrite r hk e he => .regWrite _ _ _ (by rw [checkExpression_ruE]; exact he)
  | _, _, _, _, _, _, _, _, .transition r hk m hm hl maske bits => .transition _ _ _ _ _ _ _
  | _, _, _, _, _, _, _, _, .publish g e payload hp hw hL hg he =>
    .publish _ _ _ _ _ _ hg (by rw [checkExpression_ruE]; exact he)
  | _, _, _, _, _, _, _, _, .advances m a h hs => os_nach _ (.advances _ _ _ _)
  | _, _, _, _, _, _, _, _, .retires m st h a => os_nach _ (.retires _ _ _ _)
  | _, _, _, _, _, _, _, _, .ret e hΛ he => .ret _ _ ((check_outR A _ out e).trans he)
  | _, _, _, _, _, _, _, _, .retWhy r hΛ hf => .retWhy _ _ hf
  | _, _, _, _, _, _, _, _, .leave h hx => .leave h hx
  | _, _, _, _, _, _, _, _, .next h hx => .next h hx

theorem ob_lift : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {k c c' : Context} {b : Block D V l Γ Λ Λ'},
    OB A I out k c b c' → OB (liftA A) (liftI I) (outR A out) k c (ruB b) c'
  | _, _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, _, .cons s rest hs hr => .cons _ _ (os_lift hs) (ob_lift hr)
  | _, _, _, _, _, _, _, _, .weaken b hb hw => .weaken _ (ob_lift hb) hw
  | _, _, _, _, _, _, _, _, .dead s rest hs => .dead _ _ (fun c1 hb => os_lift (hs c1 hb))
  | _, _, _, _, _, _, _, _, .bind e rest he hr => by
    have h := ob_lift hr
    rw [← origin_ruE] at h
    exact .bind _ _ (by rw [checkExpression_ruE]; exact he) h
  | _, _, _, _, _, _, _, _, .bindCall f args he hp hr rest ha hplan hrest =>
    .bindCall _ _ _ _ _ _ ((checkArguments_ruA A _ args).trans ha)
      ((planFits_lift _ _ args).trans hplan)
      (ob_vor _ (ob_pre ((congrArg (fun x => resultContext x _) (afterCall_lift _ _ args)).trans (resultContext_outR _ _)) (ob_lift hrest)))
  | _, _, _, _, _, _, _, _, .bindCallInd (n := n) p args he hp hr rest J owner hJ hpc ha hplan hrest =>
    .bindCallInd _ _ _ _ _ _ (modesR J) owner (sigCompatible_lift hJ) (by rw [checkExpression_ruE]; exact hpc)
      ((checkArguments_ruA A _ args).trans ha) ((planFits_lift _ J args).trans hplan)
      (ob_vor _ (ob_pre (congrArg (fun x => resultContextB x owner) (afterCall_lift _ J args)) (ob_lift hrest)))
  | _, _, _, _, _, _, _, _, .bindCallElse f args he hp hr err rest ha hplan herr hrest =>
    .bindCallElse _ _ _ _ _ _ _ ((checkArguments_ruA A _ args).trans ha)
      ((planFits_lift _ _ args).trans hplan)
      (oe_um _ (oe_pre (congrArg (fun x => Context.bind x none) (afterCall_lift _ _ args)) (oe_lift herr)))
      (ob_vor _ (ob_pre ((congrArg (fun x => resultContext x _) (afterCall_lift _ _ args)).trans (resultContext_outR _ _)) (ob_lift hrest)))
  | _, _, _, _, _, _, _, _, .bindAxiom a args he hw hg hd hgd rest hfree ha hrest =>
    .bindAxiom _ _ _ _ _ _ _ _ hfree ((checkArguments_ruA A _ args).trans ha) (ob_lift hrest)
  | _, _, _, _, _, _, _, _, .bindAxiomElse a args he hr hw hg hd hgd err rest hfree ha herr hrest =>
    .bindAxiomElse _ _ _ _ _ _ _ _ _ _ hfree ((checkArguments_ruA A _ args).trans ha) (oe_lift herr) (ob_lift hrest)
  | _, _, _, _, _, _, _, _, .regRead r hk rest hrest => .regRead _ _ _ (ob_lift hrest)
  | _, _, _, _, _, _, _, _, .regReadElse r hk z sonst rest hz hs hrest =>
    .regReadElse _ _ _ _ _ (by rw [checkExpression_ruE]; exact hz) (oe_lift hs) (ob_lift hrest)
  | _, _, _, _, _, _, _, _, .awaits g pl hp hL ha rest hrest => .awaits _ _ _ _ _ _ (ob_lift hrest)
  | _, _, _, _, _, _, _, _, .exchange g neu hw hL rest hg hn hrest =>
    .exchange _ _ _ _ _ hg (by rw [checkExpression_ruE]; exact hn) (ob_lift hrest)
  | _, _, _, _, _, _, _, _, .narrow e lo' hi' sonst rest he hs hrest => by
    have h := ob_lift hrest
    rw [← origin_ruE] at h
    exact .narrow _ _ _ _ _ (by rw [checkExpression_ruE]; exact he) (oe_lift hs) h
  | _, _, _, _, _, _, _, _, .check cond sonst rest hc hs hrest =>
    .check _ _ _ (by rw [checkExpression_ruE]; exact hc) (oe_lift hs) (ob_lift hrest)
  | _, _, _, _, _, _, _, _, .float op a b lo hi rest ha hb hrest =>
    .float _ _ _ _ _ _ (by rw [checkExpression_ruE]; exact ha) (by rw [checkExpression_ruE]; exact hb) (ob_lift hrest)
  | _, _, _, _, _, _, _, _, .floatLit q lo hi rest hrest => .floatLit _ _ _ _ (ob_lift hrest)
  | _, _, _, _, _, _, _, _, .floatOf e lo hi rest he hrest =>
    .floatOf _ _ _ _ (by rw [checkExpression_ruE]; exact he) (ob_lift hrest)
  | _, _, _, _, _, _, _, _, .floatNarrow e lo hi sonst rest he hs hrest =>
    .floatNarrow _ _ _ _ _ (by rw [checkExpression_ruE]; exact he) (oe_lift hs) (ob_lift hrest)
  | _, _, _, _, _, _, _, _, .allocList e lo' hi' voll g e2 hwK hLK t f i ev hw hL rest he hhi hg he2 hn hi hev hs
      hvoll hrest =>
    .allocList _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by rw [exprGlob_ruE]; exact he) hhi hg
      (by rw [exprSlotRead_ruE, he2, List.length_map]; rfl) hn
      (by rw [checkExpression_ruE]; exact hi) (by rw [checkExpression_ruE]; exact hev)
      (by rw [storeCheck_ruE]; exact hs) (oe_lift hvoll) (ob_lift hrest)
  | _, _, _, _, _, _, _, _, .allocCounter e lo' hi' voll t f i ev hw hL g e2 hwG hLG rest he hhi hn hg he2 hi hev hs
      hvoll hrest =>
    .allocCounter _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by rw [exprGlob_ruE]; exact he) hhi hn hg
      (by rw [exprSucc_ruE, he2, List.length_map])
      (by rw [checkExpression_ruE]; exact hi) (by rw [checkExpression_ruE]; exact hev)
      (by rw [storeCheck_ruE]; exact hs) (oe_lift hvoll) (ob_lift hrest)
  | _, _, _, _, _, _, _, _, .release t f i e hw hL g e2 hwK hLK rest ht hf hip he hg he2 hc hrest =>
    .release _ _ _ _ _ _ _ _ _ _ _ ht hf (by rw [exprVarPos_ruE]; exact hip) (by rw [exprGlob_ruE]; exact he) hg
      (by rw [exprVarPos_ruE]; exact he2) (by rw [consume_ruE]; exact hc) (ob_lift hrest)

theorem oe_lift : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {k c : Context} {e : Endblock D V l Γ Λ},
    OE A I out k c e → OE (liftA A) (liftI I) (outR A out) k c (ruEnd e)
  | _, _, _, _, _, _, .ret e hΛ he => .ret _ _ ((check_outR A _ out e).trans he)
  | _, _, _, _, _, _, .retWhy r hΛ hf => .retWhy _ _ hf
  | _, _, _, _, _, _, .leave h hx => .leave h hx
  | _, _, _, _, _, _, .next h hx => .next h hx
  | _, _, _, _, _, _, .cons s rest hs hr => .cons _ _ (os_lift hs) (oe_lift hr)
  | _, _, _, _, _, _, .dead s rest hs => .dead _ _ (fun c1 hb => os_lift (hs c1 hb))
  | _, _, _, _, _, _, .bind e rest he hr => by
    have h := oe_lift hr
    rw [← origin_ruE] at h
    exact .bind _ _ (by rw [checkExpression_ruE]; exact he) h
  | _, _, _, _, _, _, .bindCall f args he hp hr rest ha hplan hrest =>
    .bindCall _ _ _ _ _ _ ((checkArguments_ruA A _ args).trans ha)
      ((planFits_lift _ _ args).trans hplan)
      (oe_um _ (oe_pre ((congrArg (fun x => resultContext x _) (afterCall_lift _ _ args)).trans (resultContext_outR _ _)) (oe_lift hrest)))
  | _, _, _, _, _, _, .bindCallElse f args he hp hr err rest ha hplan herr hrest =>
    .bindCallElse _ _ _ _ _ _ _ ((checkArguments_ruA A _ args).trans ha)
      ((planFits_lift _ _ args).trans hplan)
      (oe_um _ (oe_pre (congrArg (fun x => Context.bind x none) (afterCall_lift _ _ args)) (oe_lift herr)))
      (oe_um _ (oe_pre ((congrArg (fun x => resultContext x _) (afterCall_lift _ _ args)).trans (resultContext_outR _ _)) (oe_lift hrest)))
  | _, _, _, _, _, _, .bindAxiom a args he hw hg hd hgd rest hfree ha hrest =>
    .bindAxiom _ _ _ _ _ _ _ _ hfree ((checkArguments_ruA A _ args).trans ha) (oe_lift hrest)
  | _, _, _, _, _, _, .bindAxiomElse a args he hr hw hg hd hgd err rest hfree ha herr hrest =>
    .bindAxiomElse _ _ _ _ _ _ _ _ _ _ hfree ((checkArguments_ruA A _ args).trans ha) (oe_lift herr) (oe_lift hrest)
  | _, _, _, _, _, _, .regRead r hk rest hrest => .regRead _ _ _ (oe_lift hrest)
  | _, _, _, _, _, _, .regReadElse r hk z sonst rest hz hs hrest =>
    .regReadElse _ _ _ _ _ (by rw [checkExpression_ruE]; exact hz) (oe_lift hs) (oe_lift hrest)
  | _, _, _, _, _, _, .awaits g pl hp hL ha rest hrest => .awaits _ _ _ _ _ _ (oe_lift hrest)
  | _, _, _, _, _, _, .bindCallInd (n := n) p args he hp hr rest J owner hJ hpc ha hplan hrest =>
    .bindCallInd _ _ _ _ _ _ (modesR J) owner (sigCompatible_lift hJ) (by rw [checkExpression_ruE]; exact hpc)
      ((checkArguments_ruA A _ args).trans ha) ((planFits_lift _ J args).trans hplan)
      (oe_um _ (oe_pre (congrArg (fun x => resultContextB x owner) (afterCall_lift _ J args)) (oe_lift hrest)))

theorem oarms_lift : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} {k c c' : Context}
    {arms : Arms D V l Γ Λ Λ' cs}, OArms A I out k c arms c' →
      OArms (liftA A) (liftI I) (outR A out) k c (ruArms arms) c'
  | _, _, _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, _, _, .cons (ca := none) b rest hb hw hr => .cons _ _ (ob_lift hb) hw (oarms_lift hr)
  | _, _, _, _, _, _, _, _, _, .cons (ca := some (_, _)) b rest hb hw hr => .cons _ _ (ob_lift hb) hw (oarms_lift hr)

theorem ogrund_lift : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} {k c c' : Context}
    {arms : GrundArms D V l Γ Λ Λ' n}, OGrund A I out k c arms c' →
      OGrund (liftA A) (liftI I) (outR A out) k c (ruGArms arms) c'
  | _, _, _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, _, _, .cons b rest hb hw hr => .cons _ _ (ob_lift hb) hw (ogrund_lift hr)

end

end Lift

/-- **A checked program is checked with its idle root.** -/
theorem checked_mitRuhe {P : Programm D} {A : FreiForm D} {I : Interfaces A} (hc : Checked P A I) :
    Checked P.mitRuhe (liftA A) (liftI I)
  | none => .ret _ _ rfl
  | some f => oe_um _ (oe_pre (parameterContext_modesR _) (oe_lift (hc f)))

#print axioms checked_mitRuhe

end Gabbro.Grammatik.ArenaOwnership.Ruhe
