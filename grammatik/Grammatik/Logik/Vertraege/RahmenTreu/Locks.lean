module

public import Grammatik.Logik.Vertraege.RahmenTreu.Teil1
public import Grammatik.Kern.Syntax.Satz.T4.ReturnInventory

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}

/-- One occurrence in the actual release witness cancels the acquired occurrence. -/
theorem erase_fold_acquired (L : D.Lock) (Ls h : List D.Lock) (released : L ∈ Ls) :
    Ls.foldl (fun h M => h.erase M) (L :: h) =
      (Ls.erase L).foldl (fun h M => h.erase M) h := by
  revert released
  induction Ls generalizing h with
  | nil => intro released; simp only [List.not_mem_nil] at released
  | cons M Ms ih =>
    intro released
    by_cases same : M = L
    · subst M
      simp only [List.foldl_cons, List.erase_cons_head]
    · have tail : L ∈ Ms := by
        simpa only [List.mem_cons, Ne.symm same, false_or] using released
      rw [List.erase_cons_tail (by simpa [beq_iff_eq] using same), List.foldl_cons,
        List.foldl_cons, List.erase_cons_tail (by simpa [beq_iff_eq] using Ne.symm same)]
      exact ih (h.erase M) tail

/-- A terminal count bound certifies that the acquired lock was really released.
    Rebase the release witness, without executing another release in the world. -/
theorem TreuRet.without_acquisition {W G} {haelt : List D.Lock} {boden : Option Int}
    {σ σ1 : World D} (L : D.Lock) (h : TreuRet W G haelt boden (σ.nimmt L) σ1)
    (count : σ1.haelt.count L ≤ σ.haelt.count L) : TreuRet W G haelt boden σ σ1 := by
  obtain ⟨frame, Ls, held, spare, rank⟩ := h
  have acquired : (σ.nimmt L).haelt = L :: σ.haelt := rfl
  rw [acquired] at held
  have released : L ∈ Ls := by
    apply List.count_pos_iff.mp
    rw [held, ReturnInventory.count_foldl_erase, List.count_cons_self] at count
    omega
  refine ⟨(rahmen_gleich (σ := σ) (σ' := σ.nimmt L) rfl rfl).trans frame,
    Ls.erase L, held.trans (erase_fold_acquired L Ls σ.haelt released), ?_, ?_⟩
  · intro M hM
    exact spare M (List.mem_of_mem_erase hM)
  · intro M hM c hc
    exact rank M (List.mem_of_mem_erase hM) c hc

/-- The handler frame restores all inherited holdings at either call exit. -/
theorem TreuR.callHeld {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    (hR : TreuR R) : ReturnInventory.CallHeld R := by
  intro f σ ρ hh σ' world
  have frame := hR f σ ρ hh σ' world
  cases answer : R f σ ρ with
  | ok _ _ => rw [answer] at frame; exact frame.2
  | why _ _ => rw [answer] at frame; exact (frame.toTreu_entry hh).2
  | logik _ => simp only [answer, RufAusgang.welt, reduceCtorEq] at world
  | hardware _ => simp only [answer, RufAusgang.welt, reduceCtorEq] at world

theorem TreuO.oracleHeld {O : Orakel D} (hO : TreuO O) : ReturnInventory.OracleHeld O :=
  fun a σ ρ => (hO a σ ρ).2

/-- Ordinary exits discharge this wrapper; terminal exits already discharged
    their actual lexical cleanup, certified by the canonical inventory. -/
theorem treu_locks (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (hR : TreuR R) (hO : TreuO O) (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (L : D.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (.held L :: Λ) (.held L :: Λ)) (σ : World D) (ρ : Env D Γ)
    (hh : HeldB bo Λ σ.haelt)
    (frame : TreuAusgang V.schreibt V.gschreibt (σ.nimmt L)
      (execBlock O passes R body (σ.nimmt L) ρ) (ResidHeld V (.held L :: Λ))) :
    TreuAusgang V.schreibt V.gschreibt σ
      (execStmt O passes R (.locks L hr body) σ ρ) (ResidHeld V Λ) := by
  have inventory (resid : ResidHeld V Λ) :
      ReturnInventory.Outcome (slack := σ.haelt.count L) L (σ.nimmt L)
        (execBlock O passes R body (σ.nimmt L) ρ) := by
    have outside : L ∉ V.haelt := fun hL => (lt_irrefl _) (hr L (resid L hL))
    have entry : ReturnInventory.Entry (slack := σ.haelt.count L) L bo Λ σ :=
      ⟨hh, by omega⟩
    exact ReturnInventory.block (O := O) (passes := passes) (R := R)
      (hCall := hR.callHeld) (hOracle := hO.oracleHeld) (hbV := hbV)
      (L := L) (residual := outside) body (σ.nimmt L) ρ entry.nimmt
  simp only [execStmt]
  generalize bodyEq : execBlock O passes R body (σ.nimmt L) ρ = outcome at frame inventory ⊢
  cases outcome with
  | ok σ1 ρ1 | leave _ σ1 ρ1 | next _ σ1 ρ1 =>
    intro σ' equal
    cases equal
    exact treu_nimmt_gibt σ σ1 L (frame σ1 rfl)
  | zurueck σ1 value | why σ1 value =>
    intro σ' equal resid
    cases equal
    exact (frame σ1 rfl (fun M hM => List.mem_cons_of_mem _ (resid M hM))).without_acquisition
      L (inventory resid σ1 rfl)
  | logik _ | hardware _ => intro σ' equal; cases equal

end Gabbro.Grammatik
