/- Actual terminal cleanup of a tracked, non-residual source lock. -/
module
public import Grammatik.Kern.Syntax.Satz.T2.ReturnInventoryLoops
@[expose] public section

namespace Gabbro.Grammatik.ReturnInventory
variable {D : Deklaration} {V : Vertrag D} {bo : Option Int}
variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (hR : GutR R) (hO : GutO O) (hbV : BodenUnter bo V.boden)
variable (L : D.Lock) (residual : L ∉ V.haelt)
include hR hO hbV residual
mutual
theorem stmt : ∀ (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ),
    Entry L bo Λ σ → Outcome L σ (execStmt O passes R s σ ρ)
  | .assignSlot .., σ, ρ, entry => by
    apply Outcome.ok
    exact (storeSlot_held ..).trans (lese_haelt ..)
  | .assignThru .., σ, ρ, entry => by
    apply Outcome.ok
    exact (storeSlot_held ..).trans (lese_haelt ..)
  | .assignThruOwn .., σ, ρ, entry => by
    apply Outcome.ok
    exact (storeSlot_held ..).trans (lese_haelt ..)
  | .assignSlotRef .., σ, ρ, entry => by
    apply Outcome.ok
    exact (storeSlot_held ..).trans (lese_haelt ..)
  | .assignGlob .., σ, ρ, entry => by
    apply Outcome.ok
    exact (storeGlob_held ..).trans (lese_haelt ..)
  | .putBytes .., σ, ρ, entry => by
    apply Outcome.ok
    exact (storeBytes_held ..).trans (lese_haelt ..)
  | .assignVar .., σ, ρ, entry => Outcome.ok _ (lese_haelt ..)
  | .shift .., σ, ρ, entry => by
    simp only [execStmt]; split
    · exact Outcome.ok _ ((storeSlot_held ..).trans (lese_haelt ..))
    · exact Outcome.logik _
  | .ite c yes no, σ, ρ, entry => by
    simp only [execStmt]; split
    · exact (block yes _ ρ (entry.same (lese_haelt ..))).vor (lese_haelt ..)
    · exact (block no _ ρ (entry.same (lese_haelt ..))).vor (lese_haelt ..)
  | .onOption e yes no, σ, ρ, entry => by
    simp only [execStmt]; split
    · exact ((block yes _ _ (entry.same (lese_haelt ..))).schrumpf).vor (lese_haelt ..)
    · exact (block no _ ρ (entry.same (lese_haelt ..))).vor (lese_haelt ..)
  | .onTag e arms, σ, ρ, entry =>
    (sumArms arms _ _ ρ (entry.same (lese_haelt ..))).vor (lese_haelt ..)
  | .onWhy e arms, σ, ρ, entry =>
    (reasonArms arms _ _ ρ (entry.same (lese_haelt ..))).vor (lese_haelt ..)
  | .call f args hp hr, σ, ρ, entry => by
    simp only [execStmt]
    apply Outcome.vor (lese_haelt ..)
    refine Outcome.call hR hbV f hp (entry.same (lese_haelt ..)) _ _ _ ?_ ?_
    · intro σ' v en; exact Outcome.ok _ rfl
    · intro σ' r en; exact (keinGrund hr r : False).elim
  | .callInd p args hp hr, σ, ρ, entry => by
    simp only [execStmt]
    generalize he : eval (σ.lese Λ (p.orte ++ args.orte)) p _ ρ = pointer
    obtain ⟨f, hf⟩ := pointer
    apply Outcome.vor (lese_haelt ..)
    refine Outcome.call hR hbV f (RufPasst.vonPasst (D.passt_sig hf) hp)
      (entry.same (lese_haelt ..)) _ _ _ ?_ ?_
    · intro σ' v en; exact Outcome.ok _ rfl
    · intro σ' r en; exact (keinGrundSig hf hr r : False).elim
  | .callIndElse p args he hp hr err, σ, ρ, entry => by
    simp only [execStmt, indSonst]
    generalize hv : eval (σ.lese Λ (p.orte ++ args.orte)) p _ ρ = pointer
    obtain ⟨f, hf⟩ := pointer
    apply Outcome.vor (lese_haelt ..)
    refine Outcome.call hR hbV f (RufPasst.vonPasst (D.passt_sig hf) hp)
      (entry.same (lese_haelt ..)) _ _ _ ?_ ?_
    · intro σ' v en; exact Outcome.ok _ rfl
    · intro σ' r en
      exact ((endBlock err σ' _ (en.nach (D.sigNr _))).schrumpf).zuAusgang
  | .locks K rank body, σ, ρ, entry => by
    have result := block body (σ.nimmt K) ρ (entry.nimmt (K := K))
    simp only [execStmt]
    generalize he : execBlock O passes R body (σ.nimmt K) ρ = outcome at result ⊢
    cases outcome with
    | ok σ1 ρ1 | leave _ σ1 ρ1 | next _ σ1 ρ1 =>
      intro σ' equal; cases equal
      change σ1.haelt.erase K = σ.haelt
      rw [result σ1 rfl]
      exact List.erase_cons_head K σ.haelt
    | zurueck σ1 value | why σ1 value =>
      intro σ' equal; cases equal; exact result σ1 rfl
    | logik e => exact Outcome.logik _
    | hardware e => exact Outcome.hardware _
  | .breaking _ body, σ, ρ, entry => block body σ ρ entry
  | .traverse t inv body, σ, ρ, entry =>
    traverse _ _ (fun σ ρ en => block body σ ρ en) (fun _ _ => lese_haelt ..) _ σ ρ entry
  | .consumeTraverse t member edge inv bound mass body, σ, ρ, entry =>
    consume t _ _ _ _ _ (fun σ ρ en => block body σ ρ en)
      (fun _ _ => lese_haelt ..) (fun _ _ => lese_haelt ..) (fun _ _ => lese_haelt ..) _ σ ρ entry
  | .retry n test body overflow, σ, ρ, entry =>
    retry _ _ _ (fun σ ρ en => block body σ ρ en) (fun _ _ => lese_haelt ..)
      (fun σ ρ en => block overflow σ ρ en) n σ ρ entry
  | .forever a inv body, σ, ρ, entry =>
    forever a _ _ (fun σ ρ en => block body σ ρ en) (fun _ _ => lese_haelt ..) passes σ ρ entry
  | .axiomCall a args _ _ _ _ _, σ, ρ, entry => by
    simp only [execStmt]
    apply Outcome.vor (lese_haelt ..)
    exact Outcome.option (entry.same (lese_haelt ..)) _ (oracle_held O hO ..) _ _
      (fun _ _ _ => Outcome.ok _ rfl)
  | .axiomCallElse _ a args _ _ _ _ _ err, σ, ρ, entry => by
    simp only [execStmt]
    apply Outcome.vor (lese_haelt ..)
    refine Outcome.option (entry.same (lese_haelt ..)) _ (oracleElse_held O hO ..) _ _ ?_
    intro σ' answer en; cases answer with
    | inl v => exact Outcome.ok _ rfl
    | inr r => exact ((endBlock err σ' _ (en.nach (D.asignatur a))).schrumpf).zuAusgang
  | .regWrite .., σ, ρ, entry => Outcome.ok _ (lese_haelt ..)
  | .transition .., σ, ρ, entry => Outcome.ok _ (fragt_haelt ..)
  | .publish .., σ, ρ, entry => Outcome.ok _ ((storeGlob_held ..).trans (lese_haelt ..))
  | .advances .., σ, ρ, entry => Outcome.ok _ rfl
  | .retires .., σ, ρ, entry => Outcome.ok _ rfl
  | .ret e balance, σ, ρ, entry => by
    intro σ' equal; cases equal
    exact (entry.same (lese_haelt ..)).exactReturn balance residual
  | .retWhy r balance, σ, ρ, entry => by
    intro σ' equal; cases equal; exact entry.exactReturn balance residual
  | .retScoped e cleanup, σ, ρ, entry => by
    intro σ' equal; cases equal
    exact (entry.same (lese_haelt ..)).cleanup cleanup residual
  | .retWhyScoped r cleanup, σ, ρ, entry => by
    intro σ' equal; cases equal; exact entry.cleanup cleanup residual
  | .leave _, σ, ρ, entry => by intro σ' equal; cases equal; rfl
  | .next _, σ, ρ, entry => by intro σ' equal; cases equal; rfl

theorem block : ∀ (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ),
    Entry L bo Λ σ → Outcome L σ (execBlock O passes R b σ ρ)
  | .nil, σ, ρ, entry => Outcome.ok _ rfl
  | .cons s rest, σ, ρ, entry => by
    have result := stmt s σ ρ entry
    simp only [execBlock]
    generalize he : execStmt O passes R s σ ρ = outcome at result ⊢
    cases outcome with
    | ok σ1 ρ1 =>
      have same := result σ1 rfl
      exact (block rest σ1 ρ1 ((entry.same same).resources s.held_iff (stmt_heldCount L s))).vor same
    all_goals exact result
  | .bind e rest, σ, ρ, entry =>
    ((block rest _ _ (entry.same (lese_haelt ..))).schrumpf).vor (lese_haelt ..)
  | .bindCall f args he hp hr rest, σ, ρ, entry => by
    simp only [execBlock]; apply Outcome.vor (lese_haelt ..)
    refine Outcome.call hR hbV f hp (entry.same (lese_haelt ..)) _ _ _ ?_ ?_
    · intro σ' v en; exact (block rest σ' _ (en.nach (D.signatur f))).schrumpf
    · intro σ' r en; exact (keinGrund hr r : False).elim
  | .bindCallInd p args he hp hr rest, σ, ρ, entry => by
    simp only [execBlock]
    generalize hv : eval (σ.lese Λ (p.orte ++ args.orte)) p _ ρ = pointer
    obtain ⟨f, hf⟩ := pointer
    apply Outcome.vor (lese_haelt ..)
    refine Outcome.call hR hbV f (RufPasst.vonPasst (D.passt_sig hf) hp)
      (entry.same (lese_haelt ..)) _ _ _ ?_ ?_
    · intro σ' v en; exact (block rest σ' _ (en.nach (D.sigNr _))).schrumpf
    · intro σ' r en; exact (keinGrundSig hf hr r : False).elim
  | .bindCallElse f args he hp hr err rest, σ, ρ, entry => by
    simp only [execBlock]; apply Outcome.vor (lese_haelt ..)
    refine Outcome.call hR hbV f hp (entry.same (lese_haelt ..)) _ _ _ ?_ ?_
    · intro σ' v en; exact (block rest σ' _ (en.nach (D.signatur f))).schrumpf
    · intro σ' r en; exact ((endBlock err σ' _ (en.nach (D.signatur f))).schrumpf).zuAusgang
  | .bindCallIndElse p args he hp hr err rest, σ, ρ, entry => by
    simp only [execBlock, indSonst]
    generalize hv : eval (σ.lese Λ (p.orte ++ args.orte)) p _ ρ = pointer
    obtain ⟨f, hf⟩ := pointer
    apply Outcome.vor (lese_haelt ..)
    refine Outcome.call hR hbV f (RufPasst.vonPasst (D.passt_sig hf) hp)
      (entry.same (lese_haelt ..)) _ _ _ ?_ ?_
    · intro σ' v en; exact (block rest σ' _ (en.nach (D.sigNr _))).schrumpf
    · intro σ' r en; exact ((endBlock err σ' _ (en.nach (D.sigNr _))).schrumpf).zuAusgang
  | .bindAxiom a args he _ _ _ _ rest, σ, ρ, entry => by
    simp only [execBlock]; apply Outcome.vor (lese_haelt ..)
    refine Outcome.option (entry.same (lese_haelt ..)) _ (oracle_held O hO ..) _ _ ?_
    intro σ' v en; exact (block rest σ' _ en).schrumpf
  | .bindAxiomElse a args he _ _ _ _ _ err rest, σ, ρ, entry => by
    simp only [execBlock]; apply Outcome.vor (lese_haelt ..)
    refine Outcome.option (entry.same (lese_haelt ..)) _ (oracleElse_held O hO ..) _ _ ?_
    intro σ' answer en; cases answer with
    | inl v => exact (block rest σ' _ en).schrumpf
    | inr r => exact ((endBlock err σ' _ en).schrumpf).zuAusgang
  | .bindAxiomOpt e a args he _ _ _ rest, σ, ρ, entry => by
    simp only [execBlock]; apply Outcome.vor (lese_haelt ..)
    refine Outcome.option (entry.same (lese_haelt ..)) _ (oracle_held O hO ..) _ _ ?_
    intro σ' v en; exact (block rest σ' _ (en.nach (D.asignatur a))).weiterOpt e
  | .bindAxiomOptElse e a args he _ _ _ _ err rest, σ, ρ, entry => by
    simp only [execBlock]; apply Outcome.vor (lese_haelt ..)
    refine Outcome.option (entry.same (lese_haelt ..)) _ (oracleElse_held O hO ..) _ _ ?_
    intro σ' answer en; cases answer with
    | inl v => exact (block rest σ' _ (en.nach (D.asignatur a))).weiterOpt e
    | inr r => exact ((endBlock err σ' _ (en.nach (D.asignatur a))).schrumpf).zuAusgang
  | .regRead r _ rest, σ, ρ, entry => by
    simp only [execBlock]; split
    · split
      · exact ((block rest _ _ (entry.same (fragt_haelt ..))).schrumpf).vor (fragt_haelt ..)
      · exact Outcome.hardware _
    · exact Outcome.hardware _
  | .regReadElse r _ zusage sonst rest, σ, ρ, entry => by
    simp only [execBlock]; split
    · split
      · exact ((block rest _ _ (entry.same ((lese_haelt ..).trans (fragt_haelt ..)))).schrumpf).vor
          ((lese_haelt ..).trans (fragt_haelt ..))
      · exact (endBlock sonst _ _ (entry.same ((lese_haelt ..).trans (fragt_haelt ..)))).zuAusgang.vor
          ((lese_haelt ..).trans (fragt_haelt ..))
    · exact Outcome.hardware _
  | .awaits g _ _ _ _ rest, σ, ρ, entry => by
    simp only [execBlock]; split
    · exact ((block rest _ _ (entry.same ((lese_haelt ..).trans (fragt_haelt ..)))).schrumpf).vor
        ((lese_haelt ..).trans (fragt_haelt ..))
    · exact Outcome.hardware _
  | .exchange g neu _ _ rest, σ, ρ, entry =>
    ((block rest _ _ (entry.same ((storeGlob_held ..).trans (lese_haelt ..)))).schrumpf).vor
      ((storeGlob_held ..).trans (lese_haelt ..))
  | .narrow e lo hi sonst rest, σ, ρ, entry => by
    simp only [execBlock]; split
    · exact ((block rest _ _ (entry.same (lese_haelt ..))).schrumpf).vor (lese_haelt ..)
    · exact (endBlock sonst _ _ (entry.same (lese_haelt ..))).zuAusgang.vor (lese_haelt ..)
  | .narrowRequired e lo hi rest, σ, ρ, entry => by
    simp only [execBlock]; split
    · exact ((block rest _ _ (entry.same (lese_haelt ..))).schrumpf).vor (lese_haelt ..)
    · exact Outcome.logik _
  | .check c sonst rest, σ, ρ, entry => by
    simp only [execBlock]; split
    · exact (block rest _ _ (entry.same (lese_haelt ..))).vor (lese_haelt ..)
    · exact (endBlock sonst _ _ (entry.same (lese_haelt ..))).zuAusgang.vor (lese_haelt ..)
  | .float _ _ _ _ _ rest, σ, ρ, entry => by
    simp only [execBlock]; split
    · exact ((block rest _ _ (entry.same (lese_haelt ..))).schrumpf).vor (lese_haelt ..)
    · exact Outcome.logik _
  | .floatLit _ _ _ rest, σ, ρ, entry => by
    simp only [execBlock]; split
    · exact (block rest σ _ entry).schrumpf
    · exact Outcome.logik _
  | .floatOf _ _ _ rest, σ, ρ, entry => by
    simp only [execBlock]; split
    · exact ((block rest _ _ (entry.same (lese_haelt ..))).schrumpf).vor (lese_haelt ..)
    · exact Outcome.logik _
  | .floatNarrow _ _ _ sonst rest, σ, ρ, entry => by
    simp only [execBlock]; split
    · exact ((block rest _ _ (entry.same (lese_haelt ..))).schrumpf).vor (lese_haelt ..)
    · exact (endBlock sonst _ _ (entry.same (lese_haelt ..))).zuAusgang.vor (lese_haelt ..)

theorem endBlock : ∀ (b : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ),
    Entry L bo Λ σ → EndOutcome L σ (execEnd O passes R b σ ρ)
  | .ret e balance, σ, ρ, entry => by
    intro σ' equal; cases equal
    exact (entry.same (lese_haelt ..)).exactReturn balance residual
  | .retWhy r balance, σ, ρ, entry => by
    intro σ' equal; cases equal; exact entry.exactReturn balance residual
  | .retScoped e cleanup, σ, ρ, entry => by
    intro σ' equal; cases equal
    exact (entry.same (lese_haelt ..)).cleanup cleanup residual
  | .retWhyScoped r cleanup, σ, ρ, entry => by
    intro σ' equal; cases equal; exact entry.cleanup cleanup residual
  | .leave _, σ, ρ, entry => by intro σ' equal; cases equal; rfl
  | .next _, σ, ρ, entry => by intro σ' equal; cases equal; rfl
  | .cons s rest, σ, ρ, entry => by
    have result := stmt s σ ρ entry
    simp only [execEnd]
    generalize he : execStmt O passes R s σ ρ = outcome at result ⊢
    cases outcome with
    | ok σ1 ρ1 =>
      have same := result σ1 rfl
      exact (endBlock rest σ1 ρ1 ((entry.same same).resources s.held_iff (stmt_heldCount L s))).vor same
    all_goals simpa only [EndOutcome, Outcome, Ausgang.welt, EndAusgang.zuAusgang] using result
  | .bind e rest, σ, ρ, entry =>
    ((endBlock rest _ _ (entry.same (lese_haelt ..))).schrumpf).vor (lese_haelt ..)
  | .bindCall f args he hp hr rest, σ, ρ, entry => by
    simp only [execEnd]; apply EndOutcome.vor (lese_haelt ..)
    refine EndOutcome.call hR hbV f hp (entry.same (lese_haelt ..)) _ _ _ ?_ ?_
    · intro σ' v en; exact (endBlock rest σ' _ (en.nach (D.signatur f))).schrumpf
    · intro σ' r en; exact (keinGrund hr r : False).elim
  | .bindCallInd p args he hp hr rest, σ, ρ, entry => by
    simp only [execEnd]
    generalize hv : eval (σ.lese Λ (p.orte ++ args.orte)) p _ ρ = pointer
    obtain ⟨f, hf⟩ := pointer
    apply EndOutcome.vor (lese_haelt ..)
    refine EndOutcome.call hR hbV f (RufPasst.vonPasst (D.passt_sig hf) hp)
      (entry.same (lese_haelt ..)) _ _ _ ?_ ?_
    · intro σ' v en; exact (endBlock rest σ' _ (en.nach (D.sigNr _))).schrumpf
    · intro σ' r en; exact (keinGrundSig hf hr r : False).elim
  | .bindCallElse f args he hp hr err rest, σ, ρ, entry => by
    simp only [execEnd]; apply EndOutcome.vor (lese_haelt ..)
    refine EndOutcome.call hR hbV f hp (entry.same (lese_haelt ..)) _ _ _ ?_ ?_
    · intro σ' v en; exact (endBlock rest σ' _ (en.nach (D.signatur f))).schrumpf
    · intro σ' r en; exact (endBlock err σ' _ (en.nach (D.signatur f))).schrumpf
  | .bindCallIndElse p args he hp hr err rest, σ, ρ, entry => by
    simp only [execEnd, indSonstE]
    generalize hv : eval (σ.lese Λ (p.orte ++ args.orte)) p _ ρ = pointer
    obtain ⟨f, hf⟩ := pointer
    apply EndOutcome.vor (lese_haelt ..)
    refine EndOutcome.call hR hbV f (RufPasst.vonPasst (D.passt_sig hf) hp)
      (entry.same (lese_haelt ..)) _ _ _ ?_ ?_
    · intro σ' v en; exact (endBlock rest σ' _ (en.nach (D.sigNr _))).schrumpf
    · intro σ' r en; exact (endBlock err σ' _ (en.nach (D.sigNr _))).schrumpf
  | .bindAxiom a args he _ _ _ _ rest, σ, ρ, entry => by
    simp only [execEnd]; apply EndOutcome.vor (lese_haelt ..)
    refine EndOutcome.option (entry.same (lese_haelt ..)) _ (oracle_held O hO ..) _ _ ?_
    intro σ' v en; exact (endBlock rest σ' _ en).schrumpf
  | .bindAxiomElse a args he _ _ _ _ _ err rest, σ, ρ, entry => by
    simp only [execEnd]; apply EndOutcome.vor (lese_haelt ..)
    refine EndOutcome.option (entry.same (lese_haelt ..)) _ (oracleElse_held O hO ..) _ _ ?_
    intro σ' answer en; cases answer with
    | inl v => exact (endBlock rest σ' _ en).schrumpf
    | inr r => exact (endBlock err σ' _ en).schrumpf
  | .bindAxiomOpt e a args he _ _ _ rest, σ, ρ, entry => by
    simp only [execEnd]; apply EndOutcome.vor (lese_haelt ..)
    refine EndOutcome.option (entry.same (lese_haelt ..)) _ (oracle_held O hO ..) _ _ ?_
    intro σ' v en; exact (endBlock rest σ' _ (en.nach (D.asignatur a))).weiterOpt e
  | .bindAxiomOptElse e a args he _ _ _ _ err rest, σ, ρ, entry => by
    simp only [execEnd]; apply EndOutcome.vor (lese_haelt ..)
    refine EndOutcome.option (entry.same (lese_haelt ..)) _ (oracleElse_held O hO ..) _ _ ?_
    intro σ' answer en; cases answer with
    | inl v => exact (endBlock rest σ' _ (en.nach (D.asignatur a))).weiterOpt e
    | inr r => exact (endBlock err σ' _ (en.nach (D.asignatur a))).schrumpf
  | .regRead r _ rest, σ, ρ, entry => by
    simp only [execEnd]; split
    · split
      · exact ((endBlock rest _ _ (entry.same (fragt_haelt ..))).schrumpf).vor (fragt_haelt ..)
      · exact Outcome.hardware _
    · exact Outcome.hardware _
  | .regReadElse r _ zusage sonst rest, σ, ρ, entry => by
    simp only [execEnd]; split
    · split
      · exact ((endBlock rest _ _ (entry.same ((lese_haelt ..).trans (fragt_haelt ..)))).schrumpf).vor
          ((lese_haelt ..).trans (fragt_haelt ..))
      · exact (endBlock sonst _ _ (entry.same ((lese_haelt ..).trans (fragt_haelt ..)))).vor
          ((lese_haelt ..).trans (fragt_haelt ..))
    · exact Outcome.hardware _
  | .awaits g _ _ _ _ rest, σ, ρ, entry => by
    simp only [execEnd]; split
    · exact ((endBlock rest _ _ (entry.same ((lese_haelt ..).trans (fragt_haelt ..)))).schrumpf).vor
        ((lese_haelt ..).trans (fragt_haelt ..))
    · exact Outcome.hardware _
  | .exchange g neu _ _ rest, σ, ρ, entry =>
    ((endBlock rest _ _ (entry.same ((storeGlob_held ..).trans (lese_haelt ..)))).schrumpf).vor
      ((storeGlob_held ..).trans (lese_haelt ..))
  | .narrow e lo hi sonst rest, σ, ρ, entry => by
    simp only [execEnd]; split
    · exact ((endBlock rest _ _ (entry.same (lese_haelt ..))).schrumpf).vor (lese_haelt ..)
    · exact (endBlock sonst _ _ (entry.same (lese_haelt ..))).vor (lese_haelt ..)
  | .narrowRequired e lo hi rest, σ, ρ, entry => by
    simp only [execEnd]; split
    · exact ((endBlock rest _ _ (entry.same (lese_haelt ..))).schrumpf).vor (lese_haelt ..)
    · exact Outcome.logik _
  | .ite c yes no, σ, ρ, entry => by
    simp only [execEnd]; split
    · exact (endBlock yes _ ρ (entry.same (lese_haelt ..))).vor (lese_haelt ..)
    · exact (endBlock no _ ρ (entry.same (lese_haelt ..))).vor (lese_haelt ..)

theorem sumArms : ∀ (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs))
    (σ : World D) (ρ : Env D Γ), Entry L bo Λ σ → Outcome L σ (execArms O passes R arms v σ ρ)
  | .cons b _, ⟨⟨0, _⟩, _⟩, σ, _, entry => (block b σ _ entry).schrumpfArm _
  | .cons _ rest, ⟨⟨_ + 1, _⟩, _⟩, σ, ρ, entry => sumArms rest _ σ ρ entry

theorem reasonArms : ∀ (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n)
    (σ : World D) (ρ : Env D Γ), Entry L bo Λ σ → Outcome L σ (execGrund O passes R arms r σ ρ)
  | .cons b _, ⟨0, _⟩, σ, ρ, entry => block b σ ρ entry
  | .cons _ rest, ⟨_ + 1, _⟩, σ, ρ, entry => reasonArms rest _ σ ρ entry
end

omit residual in
/-- The wrapper reuses the body's frame/trace proof, while its actual typed
    return inventory justifies propagating either completed channel unchanged. -/
theorem locks_gut (rank : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (.held L :: Λ) (.held L :: Λ)) (σ : World D) (ρ : Env D Γ)
    (fresh : (∀ M ∈ σ.haelt, D.rang M < D.rang L) ∧ L ∉ σ.haelt)
    (resid : ResidHeld V Λ) (held : HeldB bo Λ σ.haelt)
    (good : GutAusgang V.schreibt V.gschreibt (σ.nimmt L) (execBlock O passes R body (σ.nimmt L) ρ)) :
    GutAusgang V.schreibt V.gschreibt σ (execStmt O passes R (.locks L rank body) σ ρ) := by
  have outside : L ∉ V.haelt := by
    intro member
    have impossible := rank L (resid L member)
    exact (Int.lt_irrefl _ impossible)
  have entry : Entry L bo Λ σ := by
    refine ⟨held, ?_⟩
    rw [List.count_eq_zero.mpr fresh.2]
    exact Nat.zero_le _
  have inventory := block (O := O) (passes := passes) (R := R) (hR := hR) (hO := hO)
    (hbV := hbV) (L := L) (residual := outside) body (σ.nimmt L) ρ (entry.nimmt (K := L))
  have mapped := GutAusgang.gibt L fresh good
  simp only [execStmt]
  generalize he : execBlock O passes R body (σ.nimmt L) ρ = outcome at good inventory mapped ⊢
  cases outcome with
  | ok σ1 ρ1 | leave _ σ1 ρ1 | next _ σ1 ρ1 =>
    exact mapped
  | logik e | hardware e => exact mapped
  | zurueck σ1 value | why σ1 value =>
    intro σ' equal
    simp only [Ausgang.welt, Option.some.injEq] at equal ⊢
    subst σ'
    exact gut_nimmt_retV σ σ1 L fresh (inventory σ1 rfl) (good σ1 rfl)

end Gabbro.Grammatik.ReturnInventory
