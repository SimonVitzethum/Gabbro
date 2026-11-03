module

public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.ScopeBalance

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Keep arbitrary residues folded so that frame equations rewrite the
    entire sigma before its dependent projections are reduced. -/
private theorem restScopeBalance_mk {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (ρ : Env D Γ) (r : GRest D V l Γ Λ) :
    RestScopeBalance ⟨l, Γ, Λ, ρ, r⟩ ↔ r.scopeChain := Iff.rfl

private theorem cons_cons_ne_self {α : Type} (a b : α) (xs : List α) :
    a :: b :: xs ≠ xs := by
  intro he
  have hn := congrArg List.length he
  simp only [List.length_cons] at hn
  omega

private theorem heldCountEq_refl (Λ : List (Res D)) : HeldCountEq Λ Λ := fun _ => rfl

private theorem heldCountEq_symm {Λ Λ' : List (Res D)}
    (h : HeldCountEq Λ Λ') : HeldCountEq Λ' Λ := fun L => (h L).symm

/-- Forward closure uses two existing witnesses; backward application would
    invent an intermediate resource list and recursively search for it. -/
private theorem heldCountEq_trans {Λ Λ' Λ'' : List (Res D)}
    (h : HeldCountEq Λ Λ') (h' : HeldCountEq Λ' Λ'') : HeldCountEq Λ Λ'' :=
  fun L => (h L).trans (h' L)

private theorem heldCountEq_block {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') : HeldCountEq Λ' Λ :=
  fun L => block_heldCount L b

private theorem heldCountEq_alsBlock {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (e : Endblock D V l Γ Λ) : HeldCountEq e.alsBlock.1 Λ :=
  heldCountEq_block e.alsBlock.2

private theorem heldCountEq_stmt {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') : HeldCountEq Λ' Λ :=
  fun L => stmt_heldCount L s

private theorem heldCountEq_nach (S : Signatur D.Tab D.Glob D.Lock D.Marke)
    (Λ : List (Res D)) : HeldCountEq (nachSig D S Λ) Λ :=
  fun L => count_held_nachSig S Λ L

private theorem heldCountEq_nach_left (S : Signatur D.Tab D.Glob D.Lock D.Marke)
    (Λ Λ' : List (Res D)) : HeldCountEq (nachSig D S Λ) Λ' ↔ HeldCountEq Λ Λ' := by
  simp only [HeldCountEq, count_held_nachSig]

private theorem heldCountEq_nach_right (S : Signatur D.Tab D.Glob D.Lock D.Marke)
    (Λ Λ' : List (Res D)) : HeldCountEq Λ (nachSig D S Λ') ↔ HeldCountEq Λ Λ' := by
  simp only [HeldCountEq, count_held_nachSig]

theorem ScopeBalanceReplay.scopeChain_weiterOpt {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (e : Option Ty) (k : GRest D V l Γ Λ') :
    (GRest.weiterOpt (Λ := Λ) e k).scopeChain ↔ k.scopeChain := by
  cases e <;> exact Iff.rfl

private theorem antwortRestG_scopeChain {V : Vertrag D} (g : D.Fn)
    (a : ErgVal D (vertragVon D g).erg ⊕ Fin (vertragVon D g).gruende)
    (c c' : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ)
    (hc : RestScopeBalance c) (ha : antwortRestG g a c = some c') :
    RestScopeBalance c' := by
  obtain ⟨l, Γ, Λ, ρ, r⟩ := c
  cases a with
  | inl v =>
      cases r with
      | wartet b k | wartetSonst _ _ b k =>
          simp only [antwortRestG] at ha
          split at ha
          · simp only [Option.some.injEq] at ha
            subst c'
            exact hc
          · cases ha
      | _ =>
          simp only [antwortRestG, Option.some.injEq] at ha
          subst c'
          exact hc
  | inr grund =>
      cases r with
      | wartetSonst n err b k =>
          simp only [antwortRestG] at ha
          split at ha
          · simp only [Option.some.injEq] at ha
            subst c'
            refine ⟨?_, hc⟩
            exact heldCountEq_trans (heldCountEq_block err.alsBlock.2)
              (fun L => (block_heldCount L b).symm)
          · cases ha
      | _ => simp only [antwortRestG, reduceCtorEq] at ha

private theorem rufAntwortG_scopeChain {z z' : RufFadenG D} {vor σ : World D}
    {a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende}
    (hz : FadenScopeBalanceG z) (ha : rufAntwortG z vor σ a = some z') :
    FadenScopeBalanceG z' := by
  cases hst : z.stapel with
  | nil =>
      simp only [rufAntwortG, hst, Option.some.injEq] at ha
      subst z'
      exact ⟨trivial, by simp⟩
  | cons c st =>
      obtain ⟨r, hr⟩ : ∃ r, antwortRestG z.kopf.f a c.rest = some r := by
        cases hr : antwortRestG z.kopf.f a c.rest with
        | none => simp [rufAntwortG, hst, hr] at ha
        | some r => exact ⟨r, rfl⟩
      simp [rufAntwortG, hst, hr] at ha
      subst z'
      refine ⟨antwortRestG_scopeChain _ _ _ _ (hz.2 c (by simp [hst])) hr, ?_⟩
      intro F hF
      exact hz.2 F (by simp only [hst, List.mem_cons]; exact Or.inr hF)

/-- Frame-local preservation under the three stack movements. This lets a
    cost segment ignore arbitrary suspended callers below its entry. -/
structure ScopeBalanceMove (z z' : RufFadenG D) : Prop where
  same : z'.stapel = z.stapel → RestScopeBalance z.kopf.rest → RestScopeBalance z'.kopf.rest
  push : ∀ c, z'.stapel = c :: z.stapel → RestScopeBalance z.kopf.rest → RestScopeBalance c.rest
  pop : ∀ c st, z.stapel = c :: st → z'.stapel = st →
    RestScopeBalance c.rest → RestScopeBalance z'.kopf.rest

private theorem rufAntwortG_scopeMove {z z' : RufFadenG D} {vor σ : World D}
    {a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende}
    (ha : rufAntwortG z vor σ a = some z') : ScopeBalanceMove z z' := by
  cases hst : z.stapel with
  | nil =>
      simp only [rufAntwortG, hst, Option.some.injEq] at ha
      subst z'
      refine ⟨fun _ _ => trivial, ?_, ?_⟩ <;> simp [hst]
  | cons c st =>
      obtain ⟨r, hr⟩ : ∃ r, antwortRestG z.kopf.f a c.rest = some r := by
        cases hr : antwortRestG z.kopf.f a c.rest with
        | none => simp [rufAntwortG, hst, hr] at ha
        | some r => exact ⟨r, rfl⟩
      simp [rufAntwortG, hst, hr] at ha
      subst z'
      refine ⟨?_, ?_, ?_⟩
      · intro he _
        have := congrArg List.length he
        simp only [hst, List.length_cons] at this
        omega
      · intro c' he _
        have := congrArg List.length he
        simp only [hst, List.length_cons] at this
        omega
      · intro c' st' he _ hc
        rw [hst] at he
        obtain ⟨rfl, rfl⟩ := List.cons.inj he
        exact antwortRestG_scopeChain _ _ _ _ hc hr

namespace ScopeBalanceReplay

/-- One structural proof supplies both whole-thread and frame-local replay. -/
structure Step (z z' : RufFadenG D) : Prop where
  move : ScopeBalanceMove z z'
  preserves : FadenScopeBalanceG z → FadenScopeBalanceG z'

private theorem impossible_stack {α : Type} {xs ys : List α} {a : α}
    (he : xs = a :: ys) (hn : xs.length ≤ ys.length) : False := by
  have hl := congrArg List.length he
  simp only [List.length_cons] at hl
  omega

theorem localStep {z : RufFadenG D} {c : RufRahmenG D}
    {sp : List (Ereignis D)} {log : List (RufEreignisF D)}
    (hc : RestScopeBalance z.kopf.rest → RestScopeBalance c.rest) :
    Step z ⟨z.stapel, c, sp, log⟩ := by
  refine ⟨⟨fun _ => hc, ?_, ?_⟩, ?_⟩
  · intro c' he _
    exact (impossible_stack he (Nat.le_refl _)).elim
  · intro c' st he he' _
    exact (impossible_stack he (Nat.le_of_eq (congrArg List.length he'))).elim
  · intro h
    exact ⟨hc h.1, h.2⟩

/-- Rewrite the entire residue before looking at any dependent projection. -/
theorem headChain {z : RufFadenG D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D z.kopf.f) l Γ Λ}
    (he : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩) (h : RestScopeBalance z.kopf.rest) :
    r.scopeChain := by
  rw [he] at h
  exact (restScopeBalance_mk ρ r).mp h

theorem headStep {z : RufFadenG D}
    {l l' : Bool} {Γ Γ' : Ctx} {Λ Λ' : List (Res D)}
    {ρ : Env D Γ} {ρ' : Env D Γ'}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ}
    {r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ'}
    {sp : List (Ereignis D)} {log : List (RufEreignisF D)}
    (he : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩) (hr : r.scopeChain → r'.scopeChain) :
    Step z ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩,
      sp, log⟩ :=
  localStep (fun h => hr (headChain he h))

/-- Enter the callee once; only the suspended caller depends on the old head. -/
theorem enterStep {z : RufFadenG D} {P : Programm D} {g : D.Fn}
    {rho : Env D (D.params g)} {s0 : World D} {c : RufRahmenG D}
    {sp : List (Ereignis D)} {log : List (RufEreignisF D)}
    (hc : RestScopeBalance z.kopf.rest → RestScopeBalance c.rest) :
    Step z ⟨c :: z.stapel, ⟨g, rho, s0,
      ⟨false, D.params g, Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩,
      sp, log⟩ := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro he _
    have hl := congrArg List.length he
    simp only [List.length_cons] at hl
    omega
  · intro c' he h
    have hh := (List.cons.inj he).1
    rw [← hh]
    exact hc h
  · intro c' st he he' _
    have hl := congrArg List.length he
    have hl' := congrArg List.length he'
    simp only [List.length_cons] at hl hl'
    omega
  · intro h
    refine ⟨GRest.scopeChain_eintritt (P := P) g, ?_⟩
    intro c' hm
    rcases List.mem_cons.mp hm with he | hm
    · subst c'
      exact hc h.1
    · exact h.2 c' hm

theorem popStep {z : RufFadenG D} {c c' : RufRahmenG D} {st : List (RufRahmenG D)}
    {sp : List (Ereignis D)} {log : List (RufEreignisF D)}
    (he : z.stapel = c :: st)
    (hc : RestScopeBalance c.rest → RestScopeBalance c'.rest) :
    Step z ⟨st, c', sp, log⟩ := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro he' _
    exact (impossible_stack he (Nat.le_of_eq (congrArg List.length he').symm)).elim
  · intro c'' he' _
    have hl := congrArg List.length he
    have hl' := congrArg List.length he'
    simp only [List.length_cons] at hl hl'
    omega
  · intro c'' st' he' _ h
    have hh := (List.cons.inj (he.symm.trans he')).1
    rw [← hh] at h
    exact hc h
  · intro h
    refine ⟨hc (h.2 c (by rw [he]; exact List.mem_cons_self)), ?_⟩
    intro d hd
    exact h.2 d (by rw [he]; exact List.mem_cons_of_mem _ hd)

theorem enterHeadStep {z : RufFadenG D} {P : Programm D} {g : D.Fn}
    {rho : Env D (D.params g)} {s0 : World D}
    {l l' : Bool} {Γ Γ' : Ctx} {Λ Λ' : List (Res D)}
    {ρ : Env D Γ} {ρ' : Env D Γ'}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ}
    {r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ'}
    {sp : List (Ereignis D)} {log : List (RufEreignisF D)}
    (he : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩) (hr : r.scopeChain → r'.scopeChain) :
    Step z ⟨⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩ :: z.stapel,
      ⟨g, rho, s0, ⟨false, D.params g, Signatur.anfang D (D.signatur g),
        rho, .ende (P.rumpf g)⟩⟩, sp, log⟩ :=
  enterStep (fun h => hr (headChain he h))

theorem waitingChain {c : RufRahmenG D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {τ : Ty}
    {b : Block D (vertragVon D c.f) l (τ :: Γ) Λ Λ'}
    {k : GRest D (vertragVon D c.f) l Γ Λ'} {ρ : Env D Γ}
    (he : RufWartetHeadG c b k ρ) (h : RestScopeBalance c.rest) : k.scopeChain := by
  rcases he with he | ⟨n, err, he⟩
  · rw [he] at h
    exact h
  · rw [he] at h
    exact h

/-- Source blocks preserve the count even when their contexts differ. -/
theorem branchChain {V : Vertrag D} {l : Bool} {Γ Γb : Ctx} {Λ Λ' : List (Res D)}
    (err : Endblock D V l Γ Λ) (b : Block D V l Γb Λ Λ')
    (k : GRest D V l Γ Λ') (h : k.scopeChain) :
    (GRest.dann err.alsBlock.2 (.abbruch k)).scopeChain :=
  ⟨heldCountEq_trans (heldCountEq_alsBlock err) (heldCountEq_symm (heldCountEq_block b)), h⟩

theorem waitingStep {z : RufFadenG D} {c : RufRahmenG D} {st : List (RufRahmenG D)}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    {b : Block D (vertragVon D c.f) l (τ :: Γ) Λ Λ'}
    {k : GRest D (vertragVon D c.f) l Γ Λ'} {ρ : Env D Γ} {ρ' : Env D (τ :: Γ)}
    {sp : List (Ereignis D)} {log : List (RufEreignisF D)}
    (he : z.stapel = c :: st) (hc : RufWartetHeadG c b k ρ) :
    Step z ⟨st, ⟨c.f, c.rho, c.s0, ⟨l, τ :: Γ, Λ, ρ', .dann b (.schrumpf k)⟩⟩,
      sp, log⟩ := popStep he (fun h => waitingChain hc h)

theorem reasonStep {z : RufFadenG D} {c : RufRahmenG D} {st : List (RufRahmenG D)}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} {n : Nat}
    {err : Endblock D (vertragVon D c.f) l (.why n :: Γ) Λ}
    {b : Block D (vertragVon D c.f) l (τ :: Γ) Λ Λ'}
    {k : GRest D (vertragVon D c.f) l Γ Λ'} {ρ : Env D Γ} {ρ' : Env D (.why n :: Γ)}
    {sp : List (Ereignis D)} {log : List (RufEreignisF D)}
    (he : z.stapel = c :: st)
    (hc : c.rest = ⟨l, Γ, Λ, ρ, .wartetSonst n err b k⟩) :
    Step z ⟨st, ⟨c.f, c.rho, c.s0,
      ⟨l, .why n :: Γ, Λ, ρ', .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩⟩,
      sp, log⟩ := by
  apply popStep he
  intro h
  rw [hc] at h
  exact branchChain err b (.schrumpf k) h

theorem statementChain {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (h : HeldCountEq Λ V.ende) : HeldCountEq Λ' V.ende :=
  heldCountEq_trans (heldCountEq_stmt s) h

theorem formChain {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ) (h : HeldCountEq Λ V.ende) :
    (GRest.dann e.alsBlock.2 (.abbruch (Λk := Λ) .leer)).scopeChain :=
  ⟨heldCountEq_alsBlock e, h⟩

theorem signatureChain {V : Vertrag D} (S : Signatur D.Tab D.Glob D.Lock D.Marke)
    {Λ : List (Res D)} (h : HeldCountEq Λ V.ende) : HeldCountEq (nachSig D S Λ) V.ende :=
  (heldCountEq_nach_left S Λ V.ende).mpr h

theorem answerStep {z z' : RufFadenG D} {vor σ : World D}
    {a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende}
    (ha : rufAntwortG z vor σ a = some z') : Step z z' :=
  ⟨rufAntwortG_scopeMove ha, fun h => rufAntwortG_scopeChain h ha⟩

end ScopeBalanceReplay

end Gabbro.Grammatik
