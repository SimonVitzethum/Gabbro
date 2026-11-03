module

public import Grammatik.Kern.Syntax.Extensions.Extraktion.T6

@[expose] public section



namespace Gabbro.Grammatik.Extraktion

variable {D : Deklaration}

/-- A fired non-oracle leaf step carries exactly its statement footprint:
    every new event names the statement `Λ`, and every carrier it touches
    sits in the written carrier plus the `stmtOrte` read hull. `axiomCall`
    is excluded: the oracle (`O.wirkt`) answers with an arbitrary world, so
    its events carry arbitrary `Λ`/carriers (remainder S13 below). -/
theorem execEreignis_aus_blatt_ohne_axiomCall
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (s : Stmt D V l Γ Λ Λ') (hleaf : s.istBlatt = true)
    (hax : match s with | .axiomCall _ _ _ _ _ _ _ => False | _ => True)
    (tabs : List D.Tab) (globs : List D.Glob)
    (σ : World D) (ρ : Env D Γ) (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf s σ ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ σ.spur) :
    (∀ e ∈ neu, e.lambda = Λ ∨ e.lambda = []) ∧
      (∀ e ∈ neu, ∀ o, e.traeger = some o →
        o ∈ stmtTraeger tabs globs s ++ stmtOrte s) := by
  cases s with
  | assignSlot t f i e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          [Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt] ++
          (i.orte ++ e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        refine Or.inl ?_
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          rfl
        · exact (mem_leseEr h1).1
      · intro e' he' o ho
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          have ho' : o = .inl t := by simpa [Ereignis.traeger] using ho.symm
          subst ho'
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
        · have hmem : o ∈ i.orte ++ e.orte := (mem_leseEr h1).2 o ho
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inr hmem)
  | assignThru p t ht f i e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          [Ereignis.zugriff t true Λ
            (σ.lese Λ (p.orte ++ i.orte ++ e.orte)).haelt] ++
          (p.orte ++ i.orte ++ e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        refine Or.inl ?_
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          rfl
        · exact (mem_leseEr h1).1
      · intro e' he' o ho
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          have ho' : o = .inl t := by simpa [Ereignis.traeger] using ho.symm
          subst ho'
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
        · have hmem : o ∈ p.orte ++ i.orte ++ e.orte := (mem_leseEr h1).2 o ho
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inr hmem)
  | assignThruOwn p t ht f i e m s ho he hg hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          [Ereignis.zugriff t true Λ
            (σ.lese Λ (p.orte ++ i.orte ++ e.orte)).haelt] ++
          (p.orte ++ i.orte ++ e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        refine Or.inl ?_
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          rfl
        · exact (mem_leseEr h1).1
      · intro e' he' o ho
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          have ho' : o = .inl t := by simpa [Ereignis.traeger] using ho.symm
          subst ho'
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
        · have hmem : o ∈ p.orte ++ i.orte ++ e.orte := (mem_leseEr h1).2 o ho
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inr hmem)
  | assignSlotRef r t ht ho f e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          [Ereignis.zugriff t true Λ
            (σ.lese Λ (r.orte ++ e.orte)).haelt] ++
          (r.orte ++ e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        refine Or.inl ?_
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          rfl
        · exact (mem_leseEr h1).1
      · intro e' he' o ho
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          have ho' : o = .inl t := by simpa [Ereignis.traeger] using ho.symm
          subst ho'
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
        · have hmem : o ∈ r.orte ++ e.orte := (mem_leseEr h1).2 o ho
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inr hmem)
  | assignGlob g e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          [Ereignis.gzugriff g true Λ (σ.lese Λ e.orte).haelt] ++
          (e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        refine Or.inl ?_
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          rfl
        · exact (mem_leseEr h1).1
      · intro e' he' o ho
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          have ho' : o = .inr g := by simpa [Ereignis.traeger] using ho.symm
          subst ho'
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
        · have hmem : o ∈ e.orte := (mem_leseEr h1).2 o ho
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inr hmem)
  | putBytes t f hf n i hlo hhi e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          List.replicate (zahlZuBytes n
            (eval (σ.lese Λ (i.orte ++ e.orte)) e
              (σ.lese Λ (i.orte ++ e.orte)) ρ).n).length
            (Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt) ++
          ((i.orte ++ e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur) := by
        rw [← hstep, schreibBytes_spur_eq]; rfl
      rw [hspur, ← List.append_assoc] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        refine Or.inl ?_
        rcases List.mem_append.mp he' with h1 | h1
        · have heq : e' =
              Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt :=
            (List.mem_replicate.mp h1).2
          rw [heq]
          rfl
        · exact (mem_leseEr h1).1
      · intro e' he' o ho
        rcases List.mem_append.mp he' with h1 | h1
        · have heq : e' =
              Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt :=
            (List.mem_replicate.mp h1).2
          rw [heq] at ho
          have ho' : o = .inl t := by simpa [Ereignis.traeger] using ho.symm
          subst ho'
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
        · have hmem : o ∈ i.orte ++ e.orte := (mem_leseEr h1).2 o ho
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inr hmem)
  | assignVar x e =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          (e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        refine Or.inl ?_
        exact (mem_leseEr he').1
      · intro e' he' o ho
        have hmem : o ∈ e.orte := (mem_leseEr he').2 o ho
        simp only [stmtTraeger, stmtOrte]
        exact List.mem_append.mpr (Or.inr hmem)
  | shift t f hτ i von nach hn he hw hL =>
      obtain ⟨h1, h2⟩ := uebergang_ereignis_aus_blatt O passes l tabs globs t f hτ i von nach
        hn he hw hL σ ρ σ' neu hstep hneu
      exact ⟨fun e he => Or.inl (h1 e he), h2⟩
  | ite c t e => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | onOption o p a => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | onTag v arms => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | onWhy r arms => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | call f args hp hr => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | callInd p args hp hr => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | callIndElse p args he hp hr err => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | locks L hr body => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | breaking i body => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | traverse t inv body => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | retry n bis body ueberlauf => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | forever a inv body => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | axiomCallElse => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | consumeTraverse => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | axiomCall a args h hw hg hd hgd => exact False.elim hax
  | regWrite r hk e =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          (e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        refine Or.inl ?_
        exact (mem_leseEr he').1
      · intro e' he' o ho
        have hmem : o ∈ e.orte := (mem_leseEr he').2 o ho
        simp only [stmtTraeger, stmtOrte]
        exact List.mem_append.mpr (Or.inr hmem)
  | transition r hk m hm hl maske bits =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur = [Ereignis.fremd (.inr (.inl m))] ++ σ.spur := by rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        simp only [List.mem_singleton] at he'
        subst he'
        exact Or.inr rfl
      · intro e' he' o ho
        simp only [List.mem_singleton] at he'
        subst he'
        simp only [Ereignis.traeger, reduceCtorEq] at ho
  | publish g e payload hp hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          [Ereignis.gzugriff g true Λ (σ.lese Λ e.orte).haelt] ++
          (e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        refine Or.inl ?_
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          rfl
        · exact (mem_leseEr h1).1
      · intro e' he' o ho
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          have ho' : o = .inr g := by simpa [Ereignis.traeger] using ho.symm
          subst ho'
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
        · have hmem : o ∈ e.orte := (mem_leseEr h1).2 o ho
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inr hmem)
  | advances m a h hs =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur = ([] : List (Ereignis D)) ++ σ.spur := by rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        refine Or.inl ?_
        simp only [List.not_mem_nil] at he'
      · intro e' he' o ho
        simp only [List.not_mem_nil] at he'
  | retires m s h a =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur = ([] : List (Ereignis D)) ++ σ.spur := by rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        refine Or.inl ?_
        simp only [List.not_mem_nil] at he'
      · intro e' he' o ho
        simp only [List.not_mem_nil] at he'
  | ret e hΛ =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          (e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        refine Or.inl ?_
        exact (mem_leseEr he').1
      · intro e' he' o ho
        have hmem : o ∈ e.orte := (mem_leseEr he').2 o ho
        simp only [stmtTraeger, stmtOrte]
        exact List.mem_append.mpr (Or.inr hmem)
  | retWhy r hΛ =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur = ([] : List (Ereignis D)) ++ σ.spur := by rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        refine Or.inl ?_
        simp only [List.not_mem_nil] at he'
      · intro e' he' o ho
        simp only [List.not_mem_nil] at he'
  | retScoped e Rr =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          (Rr.scopes.reverse.map (fun L => Ereignis.gibt (D := D) L) ++
            (e.orte).map (fun o => match o with
              | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
              | .inr g => Ereignis.gzugriff g false Λ σ.haelt)) ++ σ.spur := by
        rw [← hstep, World.gibt_foldl_spur, List.append_assoc]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        rcases List.mem_append.mp he' with h | h
        · obtain ⟨L, -, rfl⟩ := List.mem_map.mp h
          simp [Ereignis.lambda]
        · exact Or.inl (mem_leseEr h).1
      · intro e' he' o ho
        rcases List.mem_append.mp he' with h | h
        · obtain ⟨L, -, rfl⟩ := List.mem_map.mp h
          simp [Ereignis.traeger] at ho
        · have hmem : o ∈ e.orte := (mem_leseEr h).2 o ho
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inr hmem)
  | retWhyScoped r Rr =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          Rr.scopes.reverse.map (fun L => Ereignis.gibt (D := D) L) ++ σ.spur := by
        rw [← hstep, World.gibt_foldl_spur]
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        obtain ⟨L, -, rfl⟩ := List.mem_map.mp he'
        simp [Ereignis.lambda]
      · intro e' he' o ho
        obtain ⟨L, -, rfl⟩ := List.mem_map.mp he'
        simp [Ereignis.traeger] at ho
  | leave h =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur = ([] : List (Ereignis D)) ++ σ.spur := by rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        refine Or.inl ?_
        simp only [List.not_mem_nil] at he'
      · intro e' he' o ho
        simp only [List.not_mem_nil] at he'
  | next h =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur = ([] : List (Ereignis D)) ++ σ.spur := by rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        refine Or.inl ?_
        simp only [List.not_mem_nil] at he'
      · intro e' he' o ho
        simp only [List.not_mem_nil] at he'
end Gabbro.Grammatik.Extraktion
