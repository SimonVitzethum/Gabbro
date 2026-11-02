/- Extracted lowering cases; recursive subterms are supplied as induction hypotheses. -/
module
public import Stage0.Senke.Anweisung.Faelle.Kontext
public import Stage0.Senke.Anweisung.Bindung.TorLauf
public import Stage0.Senke.Welt.Spans.CellStore
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

theorem assignSlotRef_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat}
    (r : Expr D Γ Λ (.ref n)) (t : D.Tab) (ht : D.tabNr n = some t) (ho : D.offen t = true)
    (field : D.Feld t) (e : Expr D Γ Λ (D.typ t field)) {hw : _} {hL : _} :
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex
      (show Stmt D (vertragVon D f) l Γ Λ Λ from .assignSlotRef r t ht ho field e hw hL) reserved := by
  intro c top h hK _ hW m pc σ ρ hp _ hlo2 _ _ hWa hpr
  simp only [lowS, ← hlo0, resultWords_vertragVon, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨ce, te⟩, he, ⟨cr, tr⟩, hr, hc⟩ := h
  simp only [execStmt, Sim]
  have hks := hW.ks
  have tops := slotStoreC_top hc
  generalize hσE : σ.lese Λ _ = σE
  have hWaE : WeltAt m L σE := by rw [← hσE]; exact hWa
  have pre := PreS.welt hp hks hWaE hW.lay hW.lo
  have refWord : ∀ m pc, Pre L m pc fp Ks (frei Γ reserved + valueWords (D.typ t field)) cr ρ
      (fun m => WeltAt m L σE) reserved →
      Ok m pc fp Ks (frei Γ reserved + valueWords (D.typ t field)) cr (Enc L _ (eval σE r σE ρ)) :=
    fun m pc hp => (lowE_ok σE σE (fun _ h => h) hW.lay r _ cr tr hr (by simp only at tops; omega) m pc ρ hp).word trivial
  -- the reference's cell is known only after its code ran; it lies in the declared table's represented cells
  have indexPre : Pre L m (pc + BitVec.ofNat 64 (16 * ce.length)) fp Ks
      (frei Γ reserved + valueWords (D.typ t field)) cr ρ (fun m => WeltAt m L σE) reserved := by
    unfold slotStoreC at hc
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨⟨ca, ta⟩, hca, rfl, rfl⟩ := hc
    unfold cellAddressC at hca
    split at hca
    · simp only [Option.some.injEq, Prod.mk.injEq] at hca
      obtain ⟨rfl, rfl⟩ := hca
      exact (pre.left.next (Agree.refl _ _ _ _) (Nat.le_add_right _ _) (by omega)).left
    · cases hca
  obtain ⟨_, _, _, _, _, hv⟩ := refWord m _ indexPre
  obtain ⟨_, _, t', ht', _, hk⟩ := hv
  have same : t' = t := Option.some.inj (ht'.symm.trans ht)
  subst same
  obtain ⟨m', s', a', hw'⟩ := slotStoreC_ok (σ := σE) (kn := (eval σE r σE ρ).zelle) hc (by omega) hk
    hW.lay hW.dis hW.lo pre
    (fun m pc hp => lowE_ok σE σE (fun _ h => h) hW.lay e _ ce te he (by omega) m pc ρ hp)
    (fun m pc hp => (refWord m pc hp).mono fun w hw => hw.1)
  exact ⟨m', s', (a'.widen hks).mono hlo2,
    envAt_agreeW hp.env a' hW.lo (by have := hp.frame.room; omega) (Nat.le_refl _) (by omega), hw',
    keeps_of_agreeW hW (a'.widen hks) hpr (by omega)⟩

theorem leave_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
     {proof0 : _} :
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Stmt D (vertragVon D f) l Γ Λ Λ from .leave proof0) reserved := by
  intro c top h _ _ _ m pc σ ρ hp _ _ _ _ hWa _
  simp only [lowS, ← hlo0, resultWords_vertragVon] at h
  split at h
  · next hl =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [execStmt, Sim]
    exact jmp_reach hp.code hl hp.env hWa
  · cases h

theorem next_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
     {proof0 : _} :
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Stmt D (vertragVon D f) l Γ Λ Λ from .next proof0) reserved := by
  intro c top h _ _ _ m pc σ ρ hp _ _ _ _ hWa _
  simp only [lowS, ← hlo0, resultWords_vertragVon] at h
  split at h
  · next hl =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [execStmt, Sim]
    exact jmp_reach hp.code hl hp.env hWa
  · cases h

theorem endLeave_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
     {proof0 : _} :
    EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Endblock D (vertragVon D f) l Γ Λ from .leave proof0) reserved := by
  intro c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr
  simp only [lowEnd, ← hlo0, resultWords_vertragVon] at h
  split at h
  · next hl =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact jmp_reach hp.code hl hp.env hWa
  · cases h

theorem endNext_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
     {proof0 : _} :
    EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Endblock D (vertragVon D f) l Γ Λ from .next proof0) reserved := by
  intro c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr
  simp only [lowEnd, ← hlo0, resultWords_vertragVon] at h
  split at h
  · next hl =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact jmp_reach hp.code hl hp.env hWa
  · cases h

theorem axiomCall_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
     {a : D.Ax} {args : Args D Γ Λ (D.aparams a)} {hn : _} {proof0 : _} {proof1 : _} {proof2 : _} {proof3 : _} :
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Stmt D (vertragVon D f) l Γ Λ Λ from .axiomCall a args hn proof0 proof1 proof2 proof3) reserved := by
  intro c top h hK _ hW m pc σ ρ hp _ hlo2 _ _ hWa hpr
  simp only [lowS, ← hlo0, resultWords_vertragVon] at h
  have hks := hW.ks
  have h7 := torC_top h
  obtain ⟨m1, w, s1, a1, _, hw1, _⟩ := torC0_ok (O := O) (σ := σ.lese Λ args.orte) h (by omega) hW hp hWa
  obtain ⟨u, hu⟩ := einpassenErg_none (z := O.zeiger) hn
    (O.wirkt a ((σ.lese Λ args.orte).fragt (.inl a)) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).2
  simp only [execStmt]
  rw [axiomAntwort_eq, hu]
  exact ⟨m1, s1, a1.mono hlo2, envAt_agreeWIn hW hp.env a1 (Nat.le_refl _) (by omega), hw1,
    keeps_of_agreeW hW a1 hpr (by omega)⟩

end Gabbro.Stage0.Senke
