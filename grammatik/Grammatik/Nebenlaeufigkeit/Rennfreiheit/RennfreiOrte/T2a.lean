module
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiOrte.T1
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Reading foreign arguments and applying the declared oracle frame bounds the
    whole event delta, independently of the result channel and continuation. -/
theorem axiom_lese_ev (O : Orakel D) (hO : GutO O)
    {C W : D.Tab ⊕ D.Glob → Bool} {Γ : Ctx} {Λ : List (Res D)}
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (σ : World D) (ρ : Env D Γ)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (hh : HeldIn Λ σ.haelt)
    (hw : ∀ t, D.aschreibt a t = true → W (.inl t) = true)
    (hg : ∀ g, D.agschreibt a g = true → W (.inr g) = true)
    (hC : args.orte.all C = true) {σ' : World D}
    (hσ : σ' = (O.wirkt a ((σ.lese Λ args.orte).fragt (.inl a))
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).1) :
    ∃ X, σ'.spur = X ++ σ.spur ∧ EvOk C W X := by
  have hl := gut_lese (W := fun _ => true) (G := fun _ => true) σ Λ _
    (Args.orte_darf args) hh
  obtain ⟨X, hX, hok⟩ := axiom_ev (C := C) (W := W) O hO a
    ((σ.lese Λ args.orte).fragt (.inl a))
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
    hd hgd (hl.heldIn hh) hw hg
  refine ⟨X ++ ([Ereignis.fremd (.inl a)] ++ leseEv σ Λ args.orte), ?_,
    evOk_append hok (evOk_append (evOk_fremd _) (evOk_lese σ Λ hC))⟩
  rw [hσ, hX, List.append_assoc]
  rfl

/-- **The events of a leaf**: its reads lie on its read carriers
    (`stmtOrteP`), its writes on carriers its contract may write. -/
theorem blatt_ev (P : Programm D) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (hO : GutO O)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (C : D.Tab ⊕ D.Glob → Bool) :
    ∀ (s : Stmt D V l Γ Λ Λ'), s.istBlatt = true → (stmtOrteP P s).all C = true →
      ∀ (σ : World D) (ρ : Env D Γ), HeldIn Λ σ.haelt → ∀ σ',
        (execStmt O passes R s σ ρ).welt = some σ' →
          ∃ X, σ'.spur = X ++ σ.spur ∧ EvOk C (schreibV V) X
  | .assignSlot t f i e hw hL, _, hC, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      refine ⟨_ :: leseEv σ Λ (i.orte ++ e.orte), rfl, ?_⟩
      exact evOk_append (X := [_]) (evOk_schreibT hw) (evOk_lese σ Λ hC)
  | .assignThru p t _ f i e hw hL, _, hC, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      refine ⟨_ :: leseEv σ Λ (p.orte ++ i.orte ++ e.orte), rfl, ?_⟩
      exact evOk_append (X := [_]) (evOk_schreibT hw) (evOk_lese σ Λ hC)
  | .assignThruOwn p t _ _ i e _ _ _ _ _ hw hL, _, hC, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      refine ⟨_ :: leseEv σ Λ (p.orte ++ i.orte ++ e.orte), rfl, ?_⟩
      exact evOk_append (X := [_]) (evOk_schreibT hw) (evOk_lese σ Λ hC)
  | .assignSlotRef r t _ ho f e hw hL, _, hC, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      refine ⟨_ :: leseEv σ Λ (r.orte ++ e.orte), rfl, ?_⟩
      exact evOk_append (X := [_]) (evOk_schreibT hw) (evOk_lese σ Λ hC)
  | .assignGlob g e hw hL, _, hC, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      refine ⟨_ :: leseEv σ Λ e.orte, rfl, ?_⟩
      exact evOk_append (X := [_]) (evOk_schreibG hw) (evOk_lese σ Λ hC)
  | .putBytes t f hf n i _ _ e hw hL, _, hC, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      obtain ⟨X, hX, hok⟩ := schreibBytes_ev (C := C) (W := schreibV V) t f hf Λ hw
        (zahlZuBytes n (eval (σ.lese Λ (i.orte ++ e.orte)) e (σ.lese Λ (i.orte ++ e.orte)) ρ).n)
        (σ.lese Λ (i.orte ++ e.orte))
        (eval (σ.lese Λ (i.orte ++ e.orte)) i (σ.lese Λ (i.orte ++ e.orte)) ρ).n
      refine ⟨X ++ leseEv σ Λ (i.orte ++ e.orte), ?_, evOk_append hok (evOk_lese σ Λ hC)⟩
      rw [hX, List.append_assoc]
      rfl
  | .assignVar x e, _, hC, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact ⟨leseEv σ Λ e.orte, rfl, evOk_lese σ Λ hC⟩
  | .shift t f hτ i von nach hn he hw hL, _, hC, σ, ρ, _, σ', h => by
      simp only [execStmt] at h
      split at h
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        refine ⟨_ :: leseEv σ Λ (.inl t :: i.orte), rfl, ?_⟩
        exact evOk_append (X := [_]) (evOk_schreibT hw) (evOk_lese σ Λ hC)
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .axiomCall a args _ hw hg hd hgd, _, hC, σ, ρ, hh, σ', h => by
      simp only [execStmt] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh
      split at h
      · rename_i σ1 v ha
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        have e1 : σ1 = (O.wirkt a ((σ.lese Λ args.orte).fragt (.inl a))
            (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).1 := by
          have := congrArg Prod.fst ha
          simp only [axiomAntwort] at this
          exact this.symm
        obtain ⟨X, hX, hok⟩ := axiom_ev (C := C) (W := schreibV V) O hO a ((σ.lese Λ args.orte).fragt (.inl a))
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldIn hh)
          hw hg
        refine ⟨X ++ ([Ereignis.fremd (.inl a)] ++ leseEv σ Λ args.orte), ?_,
          evOk_append hok (evOk_append (evOk_fremd _) (evOk_lese σ Λ hC))⟩
        rw [e1, hX, List.append_assoc]
        rfl
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .regWrite r _ e, _, hC, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact ⟨leseEv σ Λ e.orte, rfl, evOk_lese σ Λ hC⟩
  | .transition .., _, _, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact ⟨[.fremd _], rfl, evOk_fremd _⟩
  | .publish g e _ _ hw hL, _, hC, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      refine ⟨_ :: leseEv σ Λ e.orte, rfl, ?_⟩
      exact evOk_append (X := [_]) (evOk_schreibG hw) (evOk_lese σ Λ hC)
  | .advances .., _, _, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact ⟨[], rfl, evOk_nil⟩
  | .retires .., _, _, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact ⟨[], rfl, evOk_nil⟩
  | .ret e _, _, hC, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact ⟨leseEv σ Λ e.orte, rfl, evOk_lese σ Λ hC⟩
  | .retWhy .., _, _, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact ⟨[], rfl, evOk_nil⟩
  | .retScoped e Rr, _, hC, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      refine ⟨Rr.scopes.reverse.map (fun L => Ereignis.gibt L) ++ leseEv σ Λ e.orte, ?_,
        evOk_append (evOk_gibt _) (evOk_lese σ Λ hC)⟩
      rw [World.gibt_foldl_spur, List.append_assoc]
      rfl
  | .retWhyScoped r Rr, _, _, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      refine ⟨Rr.scopes.reverse.map (fun L => Ereignis.gibt L), ?_, evOk_gibt _⟩
      rw [World.gibt_foldl_spur]
  | .leave _, _, _, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact ⟨[], rfl, evOk_nil⟩
  | .next _, _, _, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact ⟨[], rfl, evOk_nil⟩
  | .ite .., hleaf, _, _, _, _, _, _ => by simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | .onOption .., hleaf, _, _, _, _, _, _ => by simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | .onTag .., hleaf, _, _, _, _, _, _ => by simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | .onWhy .., hleaf, _, _, _, _, _, _ => by simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | .call .., hleaf, _, _, _, _, _, _ => by simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | .callInd .., hleaf, _, _, _, _, _, _ => by simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | .callIndElse .., hleaf, _, _, _, _, _, _ => by simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | .locks .., hleaf, _, _, _, _, _, _ => by simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | .breaking .., hleaf, _, _, _, _, _, _ => by simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | .traverse .., hleaf, _, _, _, _, _, _ => by simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | .consumeTraverse .., hleaf, _, _, _, _, _, _ => by simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | .axiomCallElse .., hleaf, _, _, _, _, _, _ => by simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | .retry .., hleaf, _, _, _, _, _, _ => by simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | .forever .., hleaf, _, _, _, _, _, _ => by simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf

set_option hygiene false in
/-- A step whose trace grows by the reads of one list of carriers of the
    head residue. -/
macro "leseO" : tactic => `(tactic| (
  simp only [rufUpdateG_self]
  rw [‹(M.faeden f).kopf.rest = _›] at hC
  dsimp only at hC ⊢
  simp only [GRest.oR, endblockOrteP, blockOrteP, stmtOrteP, blockOrteP_alsBlock,
    List.all_append, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true,
    Bool.true_and] at hC
  subst_vars
  first
    | exact ⟨[], rfl, evOk_nil⟩
    | exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ (by simp_all)⟩))


end Gabbro.Grammatik
