module
public import Grammatik.Kern.Syntax.Typen.Fall

public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Logik.Vertraege.HandlerKongruenz.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Kongruenz
variable {V : Vertrag D} (O : Orakel D) (passes : Nat)
  (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  {Er : Fehlermarke D → Prop}

mutual

/-- **A statement under two handlers.** -/
theorem Stmt.kongruent (hR : HandlerUnter Er R₁ R₂) {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → ∀ (σ : World D) (ρ : Env D Γ),
      AusgangUnter Er (execStmt O passes R₁ s σ ρ) (execStmt O passes R₂ s σ ρ)
  | .ite c t e, σ, ρ => by
      simp only [execStmt]
      exact AusgangUnter.ite (Block.kongruent hR t _ ρ)
        (Block.kongruent hR e _ ρ)
  | .onOption o p a, σ, ρ => by
      simp only [execStmt]
      cases hv : (eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ : Option _) with
      | none => exact Block.kongruent hR a _ ρ
      | some k => exact (Block.kongruent hR p _ (.cons k ρ)).schrumpf
  | .onTag v arms, σ, ρ => by
      simp only [execStmt]
      exact Arms.kongruent hR arms _ _ ρ
  | .onWhy r arms, σ, ρ => by
      simp only [execStmt]
      exact GrundArms.kongruent hR arms _ _ ρ
  | .locks L hr body, σ, ρ => by
      simp only [execStmt]
      exact (Block.kongruent hR body (σ.nimmt L) ρ).mapWelt
  | .breaking i body, σ, ρ => by
      simp only [execStmt]
      exact Block.kongruent hR body σ ρ
  | .traverse t inv body, σ, ρ => by
      simp only [execStmt]
      exact traverseLauf_kongruent _ _ _
        (fun σ' ρ' => Block.kongruent hR body σ' ρ') _ σ ρ
  | .consumeTraverse t member edge inv bound mass body, σ, ρ => by
      simp only [execStmt]
      exact traverseLauf_kongruent _ _ _
        (fun σ' ρ' => Block.kongruent hR body σ' ρ') _ σ ρ
  | .retry n bis body ueber, σ, ρ => by
      simp only [execStmt]
      exact retryLauf_kongruent _ _ _ _ _
        (fun σ' ρ' => Block.kongruent hR body σ' ρ')
        (fun σ' ρ' => Block.kongruent hR ueber σ' ρ') n σ ρ
  | .forever a inv body, σ, ρ => by
      simp only [execStmt]
      exact foreverLauf_kongruent _ _ _ _
        (fun σ' ρ' => Block.kongruent hR body σ' ρ') passes σ ρ
  | .call g args hp hr, σ, ρ => by
      simp only [execStmt]
      rcases hR g (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
        h | ⟨m, h1, hE⟩
      · rw [h]; exact Or.inl rfl
      · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩
  | .callInd p args hp hr, σ, ρ => by
      simp only [execStmt]
      generalize (eval (σ.lese Λ (p.orte ++ args.orte)) p
          (σ.lese Λ (p.orte ++ args.orte)) ρ) = w
      obtain ⟨g, hg⟩ := w
      · dsimp only
        rcases hR g (σ.lese Λ (p.orte ++ args.orte))
            (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
              (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
          h | ⟨m, h1, hE⟩
        · rw [h]; exact Or.inl rfl
        · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩
  | .assignSlot .., _, _ => Or.inl rfl
  | .assignThru .., _, _ | .assignSlotRef .., _, _ => Or.inl rfl
  | .assignGlob .., _, _ => Or.inl rfl
  | .putBytes .., _, _ => Or.inl rfl
  | .assignVar .., _, _ => Or.inl rfl
  | .shift .., _, _ => Or.inl rfl
  | .axiomCall .., _, _ => Or.inl rfl
  | .axiomCallElse _ a args _ _ _ _ _ err, σ, ρ => by
      simp only [execStmt]
      cases hx : axiomAntwortSonst O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ2 ov =>
        rcases ov with _ | v | r
        · exact Or.inl rfl
        · exact Or.inl rfl
        · exact ((Endblock.kongruent hR err _ _).schrumpf).zuAusgang
  | .regWrite .., _, _ => Or.inl rfl
  | .transition .., _, _ => Or.inl rfl
  | .publish .., _, _ => Or.inl rfl
  | .advances .., _, _ => Or.inl rfl
  | .retires .., _, _ => Or.inl rfl
  | .ret .., _, _ => Or.inl rfl
  | .retWhy .., _, _ => Or.inl rfl
  | .retScoped .., _, _ => Or.inl rfl
  | .retWhyScoped .., _, _ => Or.inl rfl
  | .leave .., _, _ => Or.inl rfl
  | .next .., _, _ => Or.inl rfl

/-- **A block under two handlers.** -/
theorem Block.kongruent (hR : HandlerUnter Er R₁ R₂) {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → ∀ (σ : World D) (ρ : Env D Γ),
      AusgangUnter Er (execBlock O passes R₁ b σ ρ) (execBlock O passes R₂ b σ ρ)
  | .nil, σ, ρ => Or.inl rfl
  | .cons s rest, σ, ρ => by
      simp only [execBlock]
      rcases Stmt.kongruent hR s σ ρ with h | ⟨m, h1, hE⟩
      · rw [h]
        cases hx : execStmt O passes R₂ s σ ρ with
        | ok σ' ρ' => exact Block.kongruent hR rest σ' ρ'
        | zurueck σ' v => exact Or.inl rfl
        | why σ' r => exact Or.inl rfl
        | leave hl σ' ρ' => exact Or.inl rfl
        | next hl σ' ρ' => exact Or.inl rfl
        | logik e => exact Or.inl rfl
        | hardware e => exact Or.inl rfl
      · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩
  | .bind e rest, σ, ρ => by
      simp only [execBlock]
      exact (Block.kongruent hR rest _ _).schrumpf
  | .bindCall g args he hp hr rest, σ, ρ => by
      simp only [execBlock]
      rcases hR g (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
        h | ⟨m, h1, hE⟩
      · rw [h]
        cases hx : R₂ g (σ.lese Λ args.orte)
            (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
        | ok σ' v => exact (Block.kongruent hR rest σ' _).schrumpf
        | why σ' r => exact Or.inl rfl
        | logik e => exact Or.inl rfl
        | hardware e => exact Or.inl rfl
      · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩
  | .bindCallInd p args he hp hr rest, σ, ρ => by
      simp only [execBlock]
      generalize (eval (σ.lese Λ (p.orte ++ args.orte)) p
          (σ.lese Λ (p.orte ++ args.orte)) ρ) = w
      obtain ⟨g, hg⟩ := w
      · dsimp only
        rcases hR g (σ.lese Λ (p.orte ++ args.orte))
            (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
              (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
          h | ⟨m, h1, hE⟩
        · rw [h]
          cases hx : R₂ g (σ.lese Λ (p.orte ++ args.orte))
              (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
                (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
          | ok σ' v => exact (Block.kongruent hR rest σ' _).schrumpf
          | why σ' r => exact Or.inl rfl
          | logik e => exact Or.inl rfl
          | hardware e => exact Or.inl rfl
        · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩
  | .bindCallElse g args he hp hr err rest, σ, ρ => by
      simp only [execBlock]
      rcases hR g (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
        h | ⟨m, h1, hE⟩
      · rw [h]
        cases hx : R₂ g (σ.lese Λ args.orte)
            (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
        | ok σ' v => exact (Block.kongruent hR rest σ' _).schrumpf
        | why σ' r =>
            exact ((Endblock.kongruent hR err σ' _).schrumpf).zuAusgang
        | logik e => exact Or.inl rfl
        | hardware e => exact Or.inl rfl
      · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩
  | .bindAxiom a args he hp hw hL hg rest, σ, ρ => by
      simp only [execBlock]
      cases hx : axiomAntwort O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ2 ov =>
        cases ov with
        | none => exact Or.inl rfl
        | some v => exact (Block.kongruent hR rest _ _).schrumpf
  | .bindAxiomElse a args he hr' hp hw hL hg err rest, σ, ρ => by
      simp only [execBlock]
      cases hx : axiomAntwortSonst O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ2 ov =>
        rcases ov with _ | v | r
        · exact Or.inl rfl
        · exact (Block.kongruent hR rest _ _).schrumpf
        · exact ((Endblock.kongruent hR err _ _).schrumpf).zuAusgang
  | .bindAxiomOpt e a args he hp hd hgd rest, σ, ρ => by
      have ihr := fun σ ρ => Block.kongruent hR rest σ ρ
      cases e with
      | none =>
          simp only [execBlock, Ausgang.weiterOpt]
          cases hx : axiomAntwort O a (σ.lese Λ args.orte)
              (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
          | mk σ2 ov =>
            cases ov with
            | none => exact Or.inl rfl
            | some v => exact ihr _ _
      | some τ =>
          simp only [execBlock, Ausgang.weiterOpt]
          cases hx : axiomAntwort O a (σ.lese Λ args.orte)
              (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
          | mk σ2 ov =>
            cases ov with
            | none => exact Or.inl rfl
            | some v => exact (ihr _ _).schrumpf
  | .bindAxiomOptElse e a args he hp hd hgd hr' err rest, σ, ρ => by
      have ihr := fun σ ρ => Block.kongruent hR rest σ ρ
      have ihe := fun σ ρ => Endblock.kongruent hR err σ ρ
      cases e with
      | none =>
          simp only [execBlock, Ausgang.weiterOpt]
          cases hx : axiomAntwortSonst O a (σ.lese Λ args.orte)
              (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
          | mk σ2 ov =>
            rcases ov with _ | v | r
            · exact Or.inl rfl
            · exact ihr _ _
            · exact ((ihe _ _).schrumpf).zuAusgang
      | some τ =>
          simp only [execBlock, Ausgang.weiterOpt]
          cases hx : axiomAntwortSonst O a (σ.lese Λ args.orte)
              (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
          | mk σ2 ov =>
            rcases ov with _ | v | r
            · exact Or.inl rfl
            · exact (ihr _ _).schrumpf
            · exact ((ihe _ _).schrumpf).zuAusgang
  | .regRead r hr rest, σ, ρ => by
      simp only [execBlock]
      cases hx : einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) with
      | none => exact Or.inl rfl
      | some v =>
          exact AusgangUnter.ite ((Block.kongruent hR rest _ (.cons v ρ)).schrumpf)
            (Or.inl rfl)
  | .regReadElse r hr zusage sonst rest, σ, ρ => by
      simp only [execBlock]
      cases hx : einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) with
      | none => exact Or.inl rfl
      | some v =>
          exact AusgangUnter.ite
            ((Block.kongruent hR rest _ (.cons v ρ)).schrumpf)
            ((Endblock.kongruent hR sonst _ ρ).zuAusgang)
  | .awaits g hg hw hL hat rest, σ, ρ => by
      simp only [execBlock]
      by_cases hs : O.sichtbar g (σ.fragt (.inr (.inr g))) = true
      · rw [if_pos hs, if_pos hs]
        exact (Block.kongruent hR rest _ _).schrumpf
      · rw [if_neg hs, if_neg hs]; exact Or.inl rfl
  | .exchange g neu hw hL rest, σ, ρ => by
      simp only [execBlock]
      exact (Block.kongruent hR rest _ _).schrumpf
  | .narrow e lo' hi' sonst rest, σ, ρ => by
      simp only [execBlock]
      exact AusgangUnter.dite (fun _ => (Block.kongruent hR rest _ _).schrumpf)
        (fun _ => (Endblock.kongruent hR sonst _ ρ).zuAusgang)
  | .narrowRequired e lo' hi' rest, σ, ρ => by
      simp only [execBlock]
      exact AusgangUnter.dite (fun _ => (Block.kongruent hR rest _ _).schrumpf)
        (fun _ => Or.inl rfl)
  | .check c sonst rest, σ, ρ => by
      simp only [execBlock]
      exact AusgangUnter.ite (Block.kongruent hR rest _ ρ)
        ((Endblock.kongruent hR sonst _ ρ).zuAusgang)
  | .float op a b lo hi rest, σ, ρ => by
      simp only [execBlock]
      cases hx : gleitPasst lo hi (gleitRechne op
          (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
          (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) with
      | none => exact Or.inl rfl
      | some v => exact (Block.kongruent hR rest _ _).schrumpf
  | .floatLit q lo hi rest, σ, ρ => by
      simp only [execBlock]
      cases hx : gleitPasst lo hi (bruch q) with
      | none => exact Or.inl rfl
      | some v => exact (Block.kongruent hR rest _ _).schrumpf
  | .floatOf e lo hi rest, σ, ρ => by
      simp only [execBlock]
      cases hx : gleitPasst lo hi (gleitAusInt
          (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n) with
      | none => exact Or.inl rfl
      | some v => exact (Block.kongruent hR rest _ _).schrumpf
  | .floatNarrow e lo hi sonst rest, σ, ρ => by
      simp only [execBlock]
      cases hx : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x with
      | none => exact (Endblock.kongruent hR sonst _ ρ).zuAusgang
      | some v => exact (Block.kongruent hR rest _ _).schrumpf

/-- **A terminal block under two handlers** -- the form the two consumers
    use, since a function body is an `Endblock`. -/
theorem Endblock.kongruent (hR : HandlerUnter Er R₁ R₂) {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} :
    (b : Endblock D V l Γ Λ) → ∀ (σ : World D) (ρ : Env D Γ),
      EndUnter Er (execEnd O passes R₁ b σ ρ) (execEnd O passes R₂ b σ ρ)
  | .ret .., _, _ => Or.inl rfl
  | .retWhy .., _, _ => Or.inl rfl
  | .retScoped .., _, _ => Or.inl rfl
  | .retWhyScoped .., _, _ => Or.inl rfl
  | .leave .., _, _ => Or.inl rfl
  | .next .., _, _ => Or.inl rfl
  | .cons s rest, σ, ρ => by
      simp only [execEnd]
      rcases Stmt.kongruent hR s σ ρ with h | ⟨m, h1, hE⟩
      · rw [h]
        cases hx : execStmt O passes R₂ s σ ρ with
        | ok σ' ρ' => exact Endblock.kongruent hR rest σ' ρ'
        | zurueck σ' v => exact Or.inl rfl
        | why σ' r => exact Or.inl rfl
        | leave hl σ' ρ' => exact Or.inl rfl
        | next hl σ' ρ' => exact Or.inl rfl
        | logik e => exact Or.inl rfl
        | hardware e => exact Or.inl rfl
      · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩
  | .bind e rest, σ, ρ => by
      simp only [execEnd]
      exact (Endblock.kongruent hR rest _ _).schrumpf
  | .bindCall g args he hp hr rest, σ, ρ => by
      simp only [execEnd]
      rcases hR g (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
        h | ⟨m, h1, hE⟩
      · rw [h]
        cases hx : R₂ g (σ.lese Λ args.orte)
            (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
        | ok σ' v => exact (Endblock.kongruent hR rest σ' _).schrumpf
        | why σ' r => exact Or.inl rfl
        | logik e => exact Or.inl rfl
        | hardware e => exact Or.inl rfl
      · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩
  | .bindCallElse g args he hp hr err rest, σ, ρ => by
      simp only [execEnd]
      rcases hR g (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
        h | ⟨m, h1, hE⟩
      · rw [h]
        cases hx : R₂ g (σ.lese Λ args.orte)
            (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
        | ok σ' v => exact (Endblock.kongruent hR rest σ' _).schrumpf
        | why σ' r =>
            exact ((Endblock.kongruent hR err σ' _).schrumpf)
        | logik e => exact Or.inl rfl
        | hardware e => exact Or.inl rfl
      · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩
  | .bindAxiom a args he hp hw hL hg rest, σ, ρ => by
      simp only [execEnd]
      cases hx : axiomAntwort O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ2 ov =>
        cases ov with
        | none => exact Or.inl rfl
        | some v => exact (Endblock.kongruent hR rest _ _).schrumpf
  | .bindAxiomElse a args he hr' hp hw hL hg err rest, σ, ρ => by
      simp only [execEnd]
      cases hx : axiomAntwortSonst O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ2 ov =>
        rcases ov with _ | v | r
        · exact Or.inl rfl
        · exact (Endblock.kongruent hR rest _ _).schrumpf
        · exact (Endblock.kongruent hR err _ _).schrumpf
  | .bindAxiomOpt e a args he hp hd hgd rest, σ, ρ => by
      have ihr := fun σ ρ => Endblock.kongruent hR rest σ ρ
      cases e with
      | none =>
          simp only [execEnd, EndAusgang.weiterOpt]
          cases hx : axiomAntwort O a (σ.lese Λ args.orte)
              (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
          | mk σ2 ov =>
            cases ov with
            | none => exact Or.inl rfl
            | some v => exact ihr _ _
      | some τ =>
          simp only [execEnd, EndAusgang.weiterOpt]
          cases hx : axiomAntwort O a (σ.lese Λ args.orte)
              (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
          | mk σ2 ov =>
            cases ov with
            | none => exact Or.inl rfl
            | some v => exact (ihr _ _).schrumpf
  | .bindAxiomOptElse e a args he hp hd hgd hr' err rest, σ, ρ => by
      have ihr := fun σ ρ => Endblock.kongruent hR rest σ ρ
      have ihe := fun σ ρ => Endblock.kongruent hR err σ ρ
      cases e with
      | none =>
          simp only [execEnd, EndAusgang.weiterOpt]
          cases hx : axiomAntwortSonst O a (σ.lese Λ args.orte)
              (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
          | mk σ2 ov =>
            rcases ov with _ | v | r
            · exact Or.inl rfl
            · exact ihr _ _
            · exact (ihe _ _).schrumpf
      | some τ =>
          simp only [execEnd, EndAusgang.weiterOpt]
          cases hx : axiomAntwortSonst O a (σ.lese Λ args.orte)
              (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
          | mk σ2 ov =>
            rcases ov with _ | v | r
            · exact Or.inl rfl
            · exact (ihr _ _).schrumpf
            · exact (ihe _ _).schrumpf
  | .regRead r hr rest, σ, ρ => by
      simp only [execEnd]
      cases hx : einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) with
      | none => exact Or.inl rfl
      | some v =>
          exact EndUnter.ite ((Endblock.kongruent hR rest _ (.cons v ρ)).schrumpf)
            (Or.inl rfl)
  | .regReadElse r hr zusage sonst rest, σ, ρ => by
      simp only [execEnd]
      cases hx : einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) with
      | none => exact Or.inl rfl
      | some v =>
          exact EndUnter.ite
            ((Endblock.kongruent hR rest _ (.cons v ρ)).schrumpf)
            (Endblock.kongruent hR sonst _ ρ)
  | .awaits g hg hw hL hat rest, σ, ρ => by
      simp only [execEnd]
      by_cases hs : O.sichtbar g (σ.fragt (.inr (.inr g))) = true
      · rw [if_pos hs, if_pos hs]
        exact (Endblock.kongruent hR rest _ _).schrumpf
      · rw [if_neg hs, if_neg hs]; exact Or.inl rfl
  | .bindCallInd p args he hp hr rest, σ, ρ => by
      simp only [execEnd]
      generalize (eval (σ.lese Λ (p.orte ++ args.orte)) p
          (σ.lese Λ (p.orte ++ args.orte)) ρ) = w
      obtain ⟨g, hg⟩ := w
      · dsimp only
        rcases hR g (σ.lese Λ (p.orte ++ args.orte))
            (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
              (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
          h | ⟨m, h1, hE⟩
        · rw [h]
          cases hx : R₂ g (σ.lese Λ (p.orte ++ args.orte))
              (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
                (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
          | ok σ' v => exact (Endblock.kongruent hR rest σ' _).schrumpf
          | why σ' r => exact Or.inl rfl
          | logik e => exact Or.inl rfl
          | hardware e => exact Or.inl rfl
        · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩
  | .narrow e lo' hi' sonst rest, σ, ρ => by
      simp only [execEnd]
      exact EndUnter.dite (fun _ => (Endblock.kongruent hR rest _ _).schrumpf)
        (fun _ => Endblock.kongruent hR sonst _ ρ)
  | .narrowRequired e lo' hi' rest, σ, ρ => by
      simp only [execEnd]
      exact EndUnter.dite (fun _ => (Endblock.kongruent hR rest _ _).schrumpf)
        (fun _ => Or.inl rfl)
  | .exchange g neu hw hL rest, σ, ρ => by
      simp only [execEnd]
      exact (Endblock.kongruent hR rest _ _).schrumpf
  | .ite c t e, σ, ρ => by
      simp only [execEnd]
      exact EndUnter.ite (Endblock.kongruent hR t _ ρ) (Endblock.kongruent hR e _ ρ)

theorem Arms.kongruent (hR : HandlerUnter Er R₁ R₂) {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} :
    (a : Arms D V l Γ Λ Λ' cs) → ∀ (v : Wert D (.sum cs)) (σ : World D) (ρ : Env D Γ),
      AusgangUnter Er (execArms O passes R₁ a v σ ρ) (execArms O passes R₂ a v σ ρ)
  | .nil, ⟨⟨k, hk⟩, _⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | .cons b rest, ⟨⟨0, _⟩, nutz⟩, σ, ρ => by
      simp only [execArms]
      exact (Block.kongruent hR b σ (armEnv (Fall.toNutzlast _ _ _ _ nutz) ρ)).schrumpfArm
  | .cons b rest, ⟨⟨i + 1, hk⟩, nutz⟩, σ, ρ => by
      simp only [execArms]
      exact Arms.kongruent hR rest _ σ ρ

theorem GrundArms.kongruent (hR : HandlerUnter Er R₁ R₂) {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} :
    (a : GrundArms D V l Γ Λ Λ' n) → ∀ (r : Fin n) (σ : World D) (ρ : Env D Γ),
      AusgangUnter Er (execGrund O passes R₁ a r σ ρ) (execGrund O passes R₂ a r σ ρ)
  | .nil, r, _, _ => r.elim0
  | .cons b rest, ⟨0, _⟩, σ, ρ => by
      simp only [execGrund]
      exact Block.kongruent hR b σ ρ
  | .cons b rest, ⟨i + 1, hk⟩, σ, ρ => by
      simp only [execGrund]
      exact GrundArms.kongruent hR rest _ σ ρ

end

end Kongruenz


end Gabbro.Grammatik
