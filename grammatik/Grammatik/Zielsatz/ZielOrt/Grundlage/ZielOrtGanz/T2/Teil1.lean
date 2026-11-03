module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz.T1

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

section LogikFrei

variable {V : Vertrag D}

theorem Ausgang.schrumpf_logik {l : Bool} {Γ : Ctx} {τ : Ty} {o : Ausgang V l (τ :: Γ)}
    {e : Logik D} (h : o.schrumpf = .logik e) : o = .logik e := by
  cases o <;> simp_all [Ausgang.schrumpf]

theorem EndAusgang.schrumpf_logik {l : Bool} {Γ : Ctx} {τ : Ty} {o : EndAusgang V l (τ :: Γ)}
    {e : Logik D} (h : o.schrumpf = .logik e) : o = .logik e := by
  cases o <;> simp_all [EndAusgang.schrumpf]

theorem EndAusgang.zuAusgang_logik {l : Bool} {Γ : Ctx} {o : EndAusgang V l Γ}
    {e : Logik D} (h : o.zuAusgang = .logik e) : o = .logik e := by
  cases o <;> simp_all [EndAusgang.zuAusgang]

theorem Ausgang.weiterOpt_logik {l : Bool} {Γ : Ctx} {e : Option Ty}
    {o : Ausgang V l (ErgCtx Γ e)} {x : Logik D} (h : Ausgang.weiterOpt e o = .logik x) :
    o = .logik x := by
  cases e with
  | none => exact h
  | some τ => exact Ausgang.schrumpf_logik h

theorem EndAusgang.weiterOpt_logik {l : Bool} {Γ : Ctx} {e : Option Ty}
    {o : EndAusgang V l (ErgCtx Γ e)} {x : Logik D} (h : EndAusgang.weiterOpt e o = .logik x) :
    o = .logik x := by
  cases e with
  | none => exact h
  | some τ => exact EndAusgang.schrumpf_logik h

theorem Ausgang.mapWelt_logik {l : Bool} {Γ : Ctx} {o : Ausgang V l Γ}
    {f : World D → World D} {e : Logik D} (h : o.mapWelt f = .logik e) : o = .logik e := by
  cases o <;> simp_all [Ausgang.mapWelt]

/-- A `retry` loop ends in a `logik` outcome only with one its step or its fallback gives; the
    property `Ok` of such an outcome carries over (with `Ok := fun _ => False`: none at all). -/
theorem retryLauf_ohneLogik {Ok : Logik D → Prop} {l : Bool} {Γ : Ctx}
    (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueber : World D → Env D Γ → Ausgang V l Γ)
    (hs : ∀ σ ρ e, schritt σ ρ = .logik e → Ok e) (hu : ∀ σ ρ e, ueber σ ρ = .logik e → Ok e) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ) (e : Logik D),
      retryLauf schritt bis ueber n σ ρ = .logik e → Ok e
  | 0, σ, ρ, e => by
      intro h
      simp only [retryLauf] at h
      split at h
      · cases h
      · exact hu _ ρ e h
  | n + 1, σ, ρ, e => by
      intro h
      simp only [retryLauf] at h
      split at h
      · cases h
      · split at h
        · exact retryLauf_ohneLogik schritt bis ueber hs hu n _ _ e h
        · exact retryLauf_ohneLogik schritt bis ueber hs hu n _ _ e h
        · cases h
        · cases h
        · cases h
        · rename_i heq
          cases h
          exact hs _ _ _ heq
        · cases h

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {Ok : Logik D → Prop}

/-! The soundness of `logikFrei`: a `logik` outcome of such a body is one a callee answered, so
    every property `Ok` of the callees' `logik` answers carries over to the body's (with
    `Ok := fun _ => False`: no `logik` outcome at all; with "no precondition failure": a caller
    of callees without `requires` never blames itself). -/

mutual

theorem Stmt.logikFrei_ok (hR : ∀ g σ ρ e, R g σ ρ = RufAusgang.logik e → Ok e)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → s.logikFrei = true →
      ∀ (σ : World D) (ρ : Env D Γ) (e : Logik D), execStmt O passes R s σ ρ = .logik e → Ok e
  | .ite c t e, h, σ, ρ, e', he => by
      simp only [Stmt.logikFrei, Bool.and_eq_true] at h
      simp only [execStmt] at he
      split at he
      · exact Block.logikFrei_ok hR t h.1 _ _ _ he
      · exact Block.logikFrei_ok hR e h.2 _ _ _ he
  | .onOption o p a, h, σ, ρ, e', he => by
      simp only [Stmt.logikFrei, Bool.and_eq_true] at h
      simp only [execStmt] at he
      split at he
      · exact Block.logikFrei_ok hR p h.1 _ _ _ (Ausgang.schrumpf_logik he)
      · exact Block.logikFrei_ok hR a h.2 _ _ _ he
  | .locks L hr body, h, σ, ρ, e', he => by
      simp only [Stmt.logikFrei] at h
      simp only [execStmt] at he
      exact Block.logikFrei_ok hR body h _ _ _ (Ausgang.mapWelt_logik he)
  | .breaking i body, h, σ, ρ, e', he => by
      simp only [Stmt.logikFrei] at h
      simp only [execStmt] at he
      exact Block.logikFrei_ok hR body h _ _ _ he
  | .retry n bis body ueber, h, σ, ρ, e', he => by
      simp only [Stmt.logikFrei, Bool.and_eq_true] at h
      simp only [execStmt] at he
      exact retryLauf_ohneLogik _ _ _ (fun σ ρ e => Block.logikFrei_ok hR body h.1 σ ρ e)
        (fun σ ρ e => Block.logikFrei_ok hR ueber h.2 σ ρ e) n σ ρ e' he
  | .call g args hp hr, _, σ, ρ, e', he => by
      simp only [execStmt] at he
      split at he
      · cases he
      · rename_i r _
        exact (Fin.cast hr r).elim0
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
      · cases he
  | .callInd p args hp hr, _, σ, ρ, e', he => by
      simp only [execStmt] at he
      split at he
      rename_i f hf _
      split at he
      · cases he
      · rename_i r _
        exact keinGrundSig hf hr r
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
      · cases he
  | .callIndElse p args he hp hr err, h, σ, ρ, e', he' => by
      simp only [Stmt.logikFrei] at h
      simp only [execStmt, indSonst] at he'
      generalize hpv : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pv at he'
      obtain ⟨f, hf⟩ := pv
      simp only at he'
      split at he'
      · cases he'
      · exact Endblock.logikFrei_ok hR err h _ _ _ (EndAusgang.schrumpf_logik (EndAusgang.zuAusgang_logik he'))
      · rename_i heq
        cases he'
        exact hR _ _ _ _ heq
      · cases he'
  | .axiomCall a args h' hw hg hd hgd, _, σ, ρ, e', he => by
      simp only [execStmt, axiomAntwort] at he
      split at he <;> cases he
  | .shift .., h, _, _, _, _ => by simp only [Stmt.logikFrei, Bool.false_eq_true] at h
  | .traverse .., h, _, _, _, _ => by simp only [Stmt.logikFrei, Bool.false_eq_true] at h
  | .consumeTraverse .., h, _, _, _, _ => by simp only [Stmt.logikFrei, Bool.false_eq_true] at h
  | .forever .., h, _, _, _, _ => by simp only [Stmt.logikFrei, Bool.false_eq_true] at h
  | .onTag .., h, _, _, _, _ => by simp only [Stmt.logikFrei, Bool.false_eq_true] at h
  | .onWhy .., h, _, _, _, _ => by simp only [Stmt.logikFrei, Bool.false_eq_true] at h
  | .assignSlot .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .assignThru .., _, _, _, _, he | .assignThruOwn .., _, _, _, _, he | .assignSlotRef .., _, _, _, _, he => by simp only [execStmt, List.append_assoc, reduceCtorEq] at he
  | .assignGlob .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .putBytes .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .assignVar .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .regWrite .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .transition .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .publish .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .advances .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .retires .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .ret .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .retWhy .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .retScoped .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .retWhyScoped .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .leave .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .next .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .axiomCallElse _ a args _ _ _ _ _ err, h, σ, ρ, e', he' => by
      simp only [Stmt.logikFrei] at h
      simp only [execStmt] at he'
      split at he'
      · cases he'
      · exact Endblock.logikFrei_ok hR err h _ _ _
          (EndAusgang.schrumpf_logik (EndAusgang.zuAusgang_logik he'))
      · cases he'

theorem Block.logikFrei_ok (hR : ∀ g σ ρ e, R g σ ρ = RufAusgang.logik e → Ok e)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → b.logikFrei = true →
      ∀ (σ : World D) (ρ : Env D Γ) (e : Logik D), execBlock O passes R b σ ρ = .logik e → Ok e
  | .nil, _, σ, ρ, e, he => by simp only [execBlock, reduceCtorEq] at he
  | .cons s rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h.2 _ _ _ he
      · exact Stmt.logikFrei_ok hR s h.1 σ ρ e he
  | .bind x rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock] at he
      exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
  | .bindCall g args he' hp hr rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
      · rename_i r _
        exact (Fin.cast hr r).elim0
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
      · cases he
  | .bindCallInd p args he' hp hr rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock] at he
      split at he
      rename_i f hf _
      split at he
      · exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
      · rename_i r _
        exact keinGrundSig hf hr r
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
      · cases he
  | .bindCallIndElse p args he' hp hr err rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock, indSonst] at he
      generalize hpv : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pv at he
      obtain ⟨f, hf⟩ := pv
      simp only at he
      split at he
      · exact Block.logikFrei_ok hR rest h.2 _ _ _ (Ausgang.schrumpf_logik he)
      · exact Endblock.logikFrei_ok hR err h.1 _ _ _
          (EndAusgang.schrumpf_logik (EndAusgang.zuAusgang_logik he))
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
      · cases he
  | .bindCallElse g args he' hp hr err rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h.2 _ _ _ (Ausgang.schrumpf_logik he)
      · exact Endblock.logikFrei_ok hR err h.1 _ _ _
          (EndAusgang.schrumpf_logik (EndAusgang.zuAusgang_logik he))
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
      · cases he
  | .bindAxiom a args he' hw hg hd hgd rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock, axiomAntwort] at he
      split at he
      · exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
      · cases he
  | .bindAxiomElse a args he' hr hw hg hd hgd err rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h.2 _ _ _ (Ausgang.schrumpf_logik he)
      · exact Endblock.logikFrei_ok hR err h.1 _ _ _
          (EndAusgang.schrumpf_logik (EndAusgang.zuAusgang_logik he))
      · cases he
  | .bindAxiomOpt _ a args he' hp hd hgd rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.weiterOpt_logik he)
      · cases he
  | .bindAxiomOptElse _ a args he' hp hd hgd hr err rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h.2 _ _ _ (Ausgang.weiterOpt_logik he)
      · exact Endblock.logikFrei_ok hR err h.1 _ _ _
          (EndAusgang.schrumpf_logik (EndAusgang.zuAusgang_logik he))
      · cases he
  | .regRead r hk rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock] at he
      split at he
      · split at he
        · exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
        · cases he
      · cases he
  | .regReadElse r hk zusage sonst rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · split at he
        · exact Block.logikFrei_ok hR rest h.2 _ _ _ (Ausgang.schrumpf_logik he)
        · exact Endblock.logikFrei_ok hR sonst h.1 _ _ _ (EndAusgang.zuAusgang_logik he)
      · cases he
  | .awaits g payload hp hL hat rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
      · cases he
  | .exchange g neu hw hL rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock] at he
      exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
  | .narrow x lo' hi' sonst rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h.2 _ _ _ (Ausgang.schrumpf_logik he)
      · exact Endblock.logikFrei_ok hR sonst h.1 _ _ _ (EndAusgang.zuAusgang_logik he)
  | .narrowRequired .., h, _, _, _, _ => by simp only [Block.logikFrei, Bool.false_eq_true] at h
  | .check c sonst rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h.2 _ _ _ he
      · exact Endblock.logikFrei_ok hR sonst h.1 _ _ _ (EndAusgang.zuAusgang_logik he)
  | .float .., h, _, _, _, _ => by simp only [Block.logikFrei, Bool.false_eq_true] at h
  | .floatLit q lo hi rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h.2 _ _ _ (Ausgang.schrumpf_logik he)
      · rename_i hn
        rw [hn] at h
        simp only [Option.isSome_none, Bool.false_eq_true, false_and] at h
  | .floatOf .., h, _, _, _, _ => by simp only [Block.logikFrei, Bool.false_eq_true] at h
  | .floatNarrow x lo hi sonst rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h.2 _ _ _ (Ausgang.schrumpf_logik he)
      · exact Endblock.logikFrei_ok hR sonst h.1 _ _ _ (EndAusgang.zuAusgang_logik he)

theorem Endblock.logikFrei_ok (hR : ∀ g σ ρ e, R g σ ρ = RufAusgang.logik e → Ok e)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (b : Endblock D V l Γ Λ) → b.logikFrei = true →
      ∀ (σ : World D) (ρ : Env D Γ) (e : Logik D), execEnd O passes R b σ ρ = .logik e → Ok e
  | .ret .., _, _, _, _, he => by simp only [execEnd, reduceCtorEq] at he
  | .retWhy .., _, _, _, _, he => by simp only [execEnd, reduceCtorEq] at he
  | .retScoped .., _, _, _, _, he => by simp only [execEnd, reduceCtorEq] at he
  | .retWhyScoped .., _, _, _, _, he => by simp only [execEnd, reduceCtorEq] at he
  | .leave .., _, _, _, _, he => by simp only [execEnd, reduceCtorEq] at he
  | .next .., _, _, _, _, he => by simp only [execEnd, reduceCtorEq] at he
  | .cons s rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei, Bool.and_eq_true] at h
      simp only [execEnd] at he
      split at he
      · exact Endblock.logikFrei_ok hR rest h.2 _ _ _ he
      · cases he
      · cases he
      · cases he
      · cases he
      · rename_i heq
        cases he
        exact Stmt.logikFrei_ok hR s h.1 σ ρ e heq
      · cases he
  | .bind x rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei] at h
      simp only [execEnd] at he
      exact Endblock.logikFrei_ok hR rest h _ _ _ (EndAusgang.schrumpf_logik he)
  | .bindCall g args he' hp hr rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei] at h
      simp only [execEnd] at he
      split at he
      · exact Endblock.logikFrei_ok hR rest h _ _ _ (EndAusgang.schrumpf_logik he)
      · rename_i r _
        exact (Fin.cast hr r).elim0
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
      · cases he
  | .bindCallElse g args he' hp hr err rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei, Bool.and_eq_true] at h
      simp only [execEnd] at he
      split at he
      · exact Endblock.logikFrei_ok hR rest h.2 _ _ _ (EndAusgang.schrumpf_logik he)
      · exact Endblock.logikFrei_ok hR err h.1 _ _ _
          (EndAusgang.schrumpf_logik he)
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
      · cases he
  | .bindAxiom a args he' hw hg hd hgd rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei] at h
      simp only [execEnd, axiomAntwort] at he
      split at he
      · exact Endblock.logikFrei_ok hR rest h _ _ _ (EndAusgang.schrumpf_logik he)
      · cases he
  | .bindAxiomElse a args he' hr hw hg hd hgd err rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei, Bool.and_eq_true] at h
      simp only [execEnd] at he
      split at he
      · exact Endblock.logikFrei_ok hR rest h.2 _ _ _ (EndAusgang.schrumpf_logik he)
      · exact Endblock.logikFrei_ok hR err h.1 _ _ _ (EndAusgang.schrumpf_logik he)
      · cases he
  | .bindAxiomOpt _ a args he' hp hd hgd rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei] at h
      simp only [execEnd] at he
      split at he
      · exact Endblock.logikFrei_ok hR rest h _ _ _ (EndAusgang.weiterOpt_logik he)
      · cases he
  | .bindAxiomOptElse _ a args he' hp hd hgd hr err rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei, Bool.and_eq_true] at h
      simp only [execEnd] at he
      split at he
      · exact Endblock.logikFrei_ok hR rest h.2 _ _ _ (EndAusgang.weiterOpt_logik he)
      · exact Endblock.logikFrei_ok hR err h.1 _ _ _ (EndAusgang.schrumpf_logik he)
      · cases he
  | .regRead r hk rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei] at h
      simp only [execEnd] at he
      split at he
      · split at he
        · exact Endblock.logikFrei_ok hR rest h _ _ _ (EndAusgang.schrumpf_logik he)
        · cases he
      · cases he
  | .regReadElse r hk zusage sonst rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei, Bool.and_eq_true] at h
      simp only [execEnd] at he
      split at he
      · split at he
        · exact Endblock.logikFrei_ok hR rest h.2 _ _ _ (EndAusgang.schrumpf_logik he)
        · exact Endblock.logikFrei_ok hR sonst h.1 _ _ _ he
      · cases he
  | .awaits g payload hp hL hat rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei] at h
      simp only [execEnd] at he
      split at he
      · exact Endblock.logikFrei_ok hR rest h _ _ _ (EndAusgang.schrumpf_logik he)
      · cases he
  | .bindCallInd p args he' hp hr rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei] at h
      simp only [execEnd] at he
      split at he
      rename_i f hf _
      split at he
      · exact Endblock.logikFrei_ok hR rest h _ _ _ (EndAusgang.schrumpf_logik he)
      · rename_i r _
        exact keinGrundSig hf hr r
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
      · cases he
  | .bindCallIndElse p args he' hp hr err rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei, Bool.and_eq_true] at h
      simp only [execEnd, indSonstE] at he
      generalize hpv : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pv at he
      obtain ⟨f, hf⟩ := pv
      simp only at he
      split at he
      · exact Endblock.logikFrei_ok hR rest h.2 _ _ _ (EndAusgang.schrumpf_logik he)
      · exact Endblock.logikFrei_ok hR err h.1 _ _ _
          (EndAusgang.schrumpf_logik he)
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
      · cases he
  | .narrow x lo' hi' sonst rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei, Bool.and_eq_true] at h
      simp only [execEnd] at he
      split at he
      · exact Endblock.logikFrei_ok hR rest h.2 _ _ _ (EndAusgang.schrumpf_logik he)
      · exact Endblock.logikFrei_ok hR sonst h.1 _ _ _ he
  | .narrowRequired .., h, _, _, _, _ => by simp only [Endblock.logikFrei, Bool.false_eq_true] at h
  | .exchange g neu hw hL rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei] at h
      simp only [execEnd] at he
      exact Endblock.logikFrei_ok hR rest h _ _ _ (EndAusgang.schrumpf_logik he)
  | .ite c t e', h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei, Bool.and_eq_true] at h
      simp only [execEnd] at he
      split at he
      · exact Endblock.logikFrei_ok hR t h.1 _ _ _ he
      · exact Endblock.logikFrei_ok hR e' h.2 _ _ _ he

end

end LogikFrei
/-- **A body without `logik` sources meets `KeineLogik`** -- for every
    declared axiom ensures, without any reasoning about the program. -/
theorem logikFrei_keineLogik {P : Programm D} (passes : Nat) (Q : AxEns D) {f : D.Fn}
    (h : (P.rumpf f).logikFrei = true) : KeineLogik P passes Q f :=
  fun O' _ _ _ R _ hR σ ρ _ e =>
    Endblock.logikFrei_ok O' passes R (Ok := fun _ => False) (fun g σ ρ e h => hR g σ ρ e h) (P.rumpf f) h
      σ ρ e

/-- The program-level check over a member list. -/
def programmLogikFrei (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun f => (P.rumpf f).logikFrei

theorem programmLogikFrei_ok {P : Programm D} {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (h : programmLogikFrei P fs = true) (passes : Nat) (Q : AxEns D) :
    ∀ f, KeineLogik P passes Q f :=
  fun f => logikFrei_keineLogik passes Q ((List.all_eq_true.mp h) f (hvoll f))

#print axioms Gabbro.Grammatik.logikFrei_keineLogik
#print axioms Gabbro.Grammatik.programmLogikFrei_ok

/-! ## 6. The conclusion: no reachable machine is stuck at a `logik` check -/

end Gabbro.Grammatik
