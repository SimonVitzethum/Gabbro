/- Part 2 of 3 of `RennfreiOrte` (split by instrumente/teile/lean-teilen.py; the umbrella `RennfreiOrte.lean` imports all parts). -/
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiOrte.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}

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
  | .locks .., hleaf, _, _, _, _, _, _ => by simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | .breaking .., hleaf, _, _, _, _, _, _ => by simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | .traverse .., hleaf, _, _, _, _, _, _ => by simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
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

set_option maxHeartbeats 4000000 in
/-- **The events of one step, bounded**: given the read bound `C` of the
    acting frame's residue, every read event of the step is on a carrier in
    `C` and every write event on a carrier the acting frame's function may
    write. -/
theorem schritt_ev {P : Programm D} {O : Orakel D} {passes : Nat} (hO : GutO O)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    {C : D.Tab ⊕ D.Glob → Bool} (hC : (M.faeden f).kopf.rest.2.2.2.2.oR P C) :
    ∃ X, (M'.faeden f).spur = X ++ (M.faeden f).spur ∧
      EvOk C (TraegerSchreibt (M.faeden f).kopf.f) X := by
  have hW : ∀ c, schreibV (vertragVon D (M.faeden f).kopf.f) c =
      TraegerSchreibt (M.faeden f).kopf.f c := schreibV_vertragVon _
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, endblockOrteP, List.all_append, Bool.and_eq_true] at hC
      obtain ⟨X, hX, hok⟩ := blatt_ev P O passes keinRuf hO C s hleaf hC.1 (M.weltVon f) ρ hΛ
        σ' (by rw [hstep]; rfl)
      exact ⟨X, hX, fun e he c w hz => by rw [← hW]; exact hok e he c w hz⟩
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, blockOrteP, List.all_append, Bool.and_eq_true] at hC
      obtain ⟨X, hX, hok⟩ := blatt_ev P O passes keinRuf hO C s hleaf hC.1.1 (M.weltVon f) ρ hΛ
        σ' (by rw [hstep]; rfl)
      exact ⟨X, hX, fun e he c w hz => by rw [← hW]; exact hok e he c w hz⟩
  | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei =>
      simp only [rufUpdateG_self]
      exact ⟨[_], rfl, evOk_sperre _ rfl⟩
  | freiGib l Γ Λ L k ρ hhead =>
      simp only [rufUpdateG_self]
      exact ⟨[_], rfl, evOk_sperre _ rfl⟩
  | peelFreiLeave l Γ Λ L rest k ρ hl hhead =>
      simp only [rufUpdateG_self]
      exact ⟨[_], rfl, evOk_sperre _ rfl⟩
  | peelFreiNext l Γ Λ L rest k ρ hl hhead =>
      simp only [rufUpdateG_self]
      exact ⟨[_], rfl, evOk_sperre _ rfl⟩
  | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hl hhead σ' ρ' neu hstep hneu hkein σ₁ hs₁ hw
      neu₁ hneu₁ hΛ =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, List.all_append, Bool.and_eq_true] at hC
      rw [hs₁, leave_welt' _ _ _ _ _ _ _ _ hstep]
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC.2.1⟩
  | dannNextTrav l Γ Λ t inv body is k rest i ρ hl hhead σ' ρ' neu hstep =>
      simp only [rufUpdateG_self]
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      exact ⟨[], rfl, evOk_nil⟩
  | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hl hhead σ' ρ' neu hstep =>
      simp only [rufUpdateG_self]
      rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
      exact ⟨[], rfl, evOk_nil⟩
  | dannNextWieder l Γ Λ n bis body ueber k rest ρ hl hhead σ' ρ' neu hstep =>
      simp only [rufUpdateG_self]
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      exact ⟨[], rfl, evOk_nil⟩
  | dannLeaveEwig l Γ Λ a n inv body k rest ρ hl hhead σ' ρ' neu hstep =>
      simp only [rufUpdateG_self]
      rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
      exact ⟨[], rfl, evOk_nil⟩
  | dannNextEwig l Γ Λ a n inv body k rest ρ hl hhead σ' ρ' neu hstep =>
      simp only [rufUpdateG_self]
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      exact ⟨[], rfl, evOk_nil⟩
  | dannExchange l Γ Λ Λ' g neuE hw hL rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, blockOrteP, List.all_append, List.all_cons, Bool.and_eq_true] at hC
      subst hs₂ hs₁
      refine ⟨_ :: leseEv (M.weltVon f) Λ (Sum.inr g :: neuE.orte), rfl, ?_⟩
      refine evOk_append (X := [_]) (evOk_schreibG ?_) (evOk_lese _ _ ?_)
      · rw [← hW]; exact hw
      · simp only [List.all_cons, Bool.and_eq_true]
        exact ⟨hC.1.1.1, hC.1.1.2⟩
  | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, blockOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs₁
      have hl := gut_lese (W := fun _ => true) (G := fun _ => true) (M.weltVon f) Λ _
        (Args.orte_darf args) hΛ
      have e2 : σ₂ = (O.wirkt a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)).1 := by
        have := congrArg Prod.fst hax
        simp only [axiomAntwort] at this
        exact this.symm
      obtain ⟨X, hX, hok⟩ := axiom_ev (C := C) (W := TraegerSchreibt (M.faeden f).kopf.f) O hO a
        (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ) hd hgd
        (hl.heldIn hΛ) (fun t ht => hw t ht) (fun g hgg => hg g hgg)
      refine ⟨X ++ ([Ereignis.fremd (.inl a)] ++ leseEv (M.weltVon f) Λ args.orte), ?_,
        evOk_append hok (evOk_append (evOk_fremd _) (evOk_lese _ _ hC.1.1))⟩
      rw [e2, hX, List.append_assoc]
      rfl
  | dannBindAxiomElseOk l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, blockOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs₁
      have hl := gut_lese (W := fun _ => true) (G := fun _ => true) (M.weltVon f) Λ _
        (Args.orte_darf args) hΛ
      have e2 : σ₂ = (O.wirkt a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)).1 := by
        have := congrArg Prod.fst hax
        simp only [axiomAntwortSonst] at this
        exact this.symm
      obtain ⟨X, hX, hok⟩ := axiom_ev (C := C) (W := TraegerSchreibt (M.faeden f).kopf.f) O hO a
        (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ) hd hgd
        (hl.heldIn hΛ) (fun t ht => hw t ht) (fun g hgg => hg g hgg)
      refine ⟨X ++ ([Ereignis.fremd (.inl a)] ++ leseEv (M.weltVon f) Λ args.orte), ?_,
        evOk_append hok (evOk_append (evOk_fremd _) (evOk_lese _ _ hC.1.1.1))⟩
      rw [e2, hX, List.append_assoc]
      rfl
  | dannBindAxiomElseGrund l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, blockOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs₁
      have hl := gut_lese (W := fun _ => true) (G := fun _ => true) (M.weltVon f) Λ _
        (Args.orte_darf args) hΛ
      have e2 : σ₂ = (O.wirkt a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)).1 := by
        have := congrArg Prod.fst hax
        simp only [axiomAntwortSonst] at this
        exact this.symm
      obtain ⟨X, hX, hok⟩ := axiom_ev (C := C) (W := TraegerSchreibt (M.faeden f).kopf.f) O hO a
        (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ) hd hgd
        (hl.heldIn hΛ) (fun t ht => hw t ht) (fun g hgg => hg g hgg)
      refine ⟨X ++ ([Ereignis.fremd (.inl a)] ++ leseEv (M.weltVon f) Λ args.orte), ?_,
        evOk_append hok (evOk_append (evOk_fremd _) (evOk_lese _ _ hC.1.1.1))⟩
      rw [e2, hX, List.append_assoc]
      rfl
  | endeBindAxiom l Γ Λ τ a args he hw hg hd hgd rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, endblockOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs₁
      have hl := gut_lese (W := fun _ => true) (G := fun _ => true) (M.weltVon f) Λ _
        (Args.orte_darf args) hΛ
      have e2 : σ₂ = (O.wirkt a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)).1 := by
        have := congrArg Prod.fst hax
        simp only [axiomAntwort] at this
        exact this.symm
      obtain ⟨X, hX, hok⟩ := axiom_ev (C := C) (W := TraegerSchreibt (M.faeden f).kopf.f) O hO a
        (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ) hd hgd
        (hl.heldIn hΛ) (fun t ht => hw t ht) (fun g hgg => hg g hgg)
      refine ⟨X ++ ([Ereignis.fremd (.inl a)] ++ leseEv (M.weltVon f) Λ args.orte), ?_,
        evOk_append hok (evOk_append (evOk_fremd _) (evOk_lese _ _ hC.1))⟩
      rw [e2, hX, List.append_assoc]
      rfl
  | endeBindAxiomElseOk l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, endblockOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs₁
      have hl := gut_lese (W := fun _ => true) (G := fun _ => true) (M.weltVon f) Λ _
        (Args.orte_darf args) hΛ
      have e2 : σ₂ = (O.wirkt a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)).1 := by
        have := congrArg Prod.fst hax
        simp only [axiomAntwortSonst] at this
        exact this.symm
      obtain ⟨X, hX, hok⟩ := axiom_ev (C := C) (W := TraegerSchreibt (M.faeden f).kopf.f) O hO a
        (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ) hd hgd
        (hl.heldIn hΛ) (fun t ht => hw t ht) (fun g hgg => hg g hgg)
      refine ⟨X ++ ([Ereignis.fremd (.inl a)] ++ leseEv (M.weltVon f) Λ args.orte), ?_,
        evOk_append hok (evOk_append (evOk_fremd _) (evOk_lese _ _ hC.1.1))⟩
      rw [e2, hX, List.append_assoc]
      rfl
  | endeBindAxiomElseGrund l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, endblockOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs₁
      have hl := gut_lese (W := fun _ => true) (G := fun _ => true) (M.weltVon f) Λ _
        (Args.orte_darf args) hΛ
      have e2 : σ₂ = (O.wirkt a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)).1 := by
        have := congrArg Prod.fst hax
        simp only [axiomAntwortSonst] at this
        exact this.symm
      obtain ⟨X, hX, hok⟩ := axiom_ev (C := C) (W := TraegerSchreibt (M.faeden f).kopf.f) O hO a
        (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ) hd hgd
        (hl.heldIn hΛ) (fun t ht => hw t ht) (fun g hgg => hg g hgg)
      refine ⟨X ++ ([Ereignis.fremd (.inl a)] ++ leseEv (M.weltVon f) Λ args.orte), ?_,
        evOk_append hok (evOk_append (evOk_fremd _) (evOk_lese _ _ hC.1.1))⟩
      rw [e2, hX, List.append_assoc]
      rfl
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, endblockOrteP, stmtOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs0
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC.1.1⟩
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, blockOrteP, stmtOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs0
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC.1.1.1⟩
  | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, blockOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs0
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC.1.1.1⟩
  | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho hrho neu
      hneu =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, blockOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs0
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC.1.1.1.1⟩
  | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, blockOrteP, stmtOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs0
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ (by
        simp only [List.all_append, Bool.and_eq_true]; exact hC.1.1)⟩
  | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, endblockOrteP, stmtOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs0
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ (by
        simp only [List.all_append, Bool.and_eq_true]; exact hC.1)⟩
  | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho
      neu hneu =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, blockOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs0
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ (by
        simp only [List.all_append, Bool.and_eq_true]; exact hC.1.1)⟩
  | rueck caller rst hpop Γ Λ e hperm ρ hh g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
      simp only [rufUpdateG_self]
      rw [hh] at hC
      simp only [GRest.oR, endblockOrteP] at hC
      subst hs1
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC⟩
  | rueckCons caller rst hpop Γ Λ e hperm rest ρ hh g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu
      hnw =>
      simp only [rufUpdateG_self]
      rw [hh] at hC
      simp only [GRest.oR, endblockOrteP, stmtOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs1
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC.1⟩
  | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv
      neu hneu hnw =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, blockOrteP, stmtOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs1
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC.1.1⟩
  | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hh g hfg rho hrho s0
      hs0 hΛ s1 hs1 v hv he neu hneu =>
      simp only [rufUpdateG_self]
      rw [hh] at hC
      simp only [GRest.oR, endblockOrteP] at hC
      subst hs1
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC⟩
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
      hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, blockOrteP, stmtOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs1
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC.1.1⟩
  | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller
      hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, endblockOrteP, stmtOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs1
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC.1⟩
  | dannRegLies l Γ Λ Λ' r hk rest k ρ hhead v hv hz hΛ =>
      simp only [rufUpdateG_self]
      exact ⟨[.fremd (.inr (.inl r))], rfl, evOk_fremd _⟩
  | dannRegLiesElseWahr l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      dsimp only at hC ⊢
      simp only [GRest.oR, endblockOrteP, blockOrteP, stmtOrteP, blockOrteP_alsBlock,
        List.all_append, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true,
        Bool.true_and] at hC
      subst hs₁
      exact ⟨leseEv ((M.weltVon f).fragt (.inr (.inl r))) Λ zusage.orte ++ [.fremd (.inr (.inl r))],
        by rw [List.append_assoc]; rfl, evOk_append (evOk_lese _ _ (by simp_all)) (evOk_fremd _)⟩
  | dannRegLiesElseFalsch l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      dsimp only at hC ⊢
      simp only [GRest.oR, endblockOrteP, blockOrteP, stmtOrteP, blockOrteP_alsBlock,
        List.all_append, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true,
        Bool.true_and] at hC
      subst hs₁
      exact ⟨leseEv ((M.weltVon f).fragt (.inr (.inl r))) Λ zusage.orte ++ [.fremd (.inr (.inl r))],
        by rw [List.append_assoc]; rfl, evOk_append (evOk_lese _ _ (by simp_all)) (evOk_fremd _)⟩
  | dannAwaits l Γ Λ Λ' g payload hp hL hat rest k ρ hhead hvis σ₁ hs₁ neu hneu hΛ =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      dsimp only at hC ⊢
      simp only [GRest.oR, endblockOrteP, blockOrteP, stmtOrteP, blockOrteP_alsBlock,
        List.all_append, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true,
        Bool.true_and] at hC
      subst hs₁
      exact ⟨leseEv ((M.weltVon f).fragt (.inr (.inr g))) Λ [.inr g] ++ [.fremd (.inr (.inr g))],
        by rw [List.append_assoc]; rfl, evOk_append (evOk_lese _ _ (by simp_all)) (evOk_fremd _)⟩
  | _ => leseO

/-! ## 5. Every access of a step is bounded by its function -/

/-- The access set of a step is its bounded events. -/
theorem zugriffe_ev {M M' : RufMaschineG D} {f : Faden} {C W : D.Tab ⊕ D.Glob → Bool}
    {X : List (Ereignis D)} (hX : (M'.faeden f).spur = X ++ (M.faeden f).spur)
    (hok : EvOk C W X) {c : D.Tab ⊕ D.Glob} {w : Bool} (h : (c, w) ∈ zugriffe M M' f) :
    (w = false → C c = true) ∧ (w = true → W c = true) := by
  rw [zugriffe_ereignisse, ereignisse_eq hX, List.mem_filterMap] at h
  obtain ⟨e, he, hz⟩ := h
  exact hok e he c w hz


end Gabbro.Grammatik
