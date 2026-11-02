module

public import Grammatik.Korpus.Programme.Korpus124.Teil1a
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section



namespace Gabbro.Grammatik


namespace K124

/-- The call `setze(30)` inside `hauptA`'s lock. -/
def kRufA : Stmt kD (vertragVon kD kHauptA) false [] kL kL :=
  .call kSetze (.cons k30 .nil) kHpSetzeA rfl

/-- `hauptA`'s `locks L { setze(30); }`. -/
def kLocksA : Stmt kD (vertragVon kD kHauptA) false [] [] [] :=
  .locks () (fun _ h => nomatch h) (.cons kRufA .nil)

/-- `pruefeA();` (the answer dropped). -/
def kRufP : Stmt kD (vertragVon kD kHauptA) false [] [] [] :=
  .call kPruefeA .nil kHpPruefe rfl

/-- `pruefeA(); return` -- the tail of `hauptA`. -/
def kRestA : Endblock kD (vertragVon kD kHauptA) false [] [] :=
  .cons kRufP (.ret .empty List.Perm.nil)

/-- `hauptA`, as in the source. -/
def kRumpfA : Endblock kD (vertragVon kD kHauptA) false [] [] :=
  .cons kA0 (.cons kA1 (.cons kLocksA kRestA))

/-- `privB.slots[0].stand = 5;` -/
def kB0 : Stmt kD (vertragVon kD kHauptB) false [] [] [] :=
  .assignSlot KTab.privB () kI0 k5 rfl (kDarfB _)

/-- The call `setze(70)` inside `hauptB`'s lock. -/
def kRufB : Stmt kD (vertragVon kD kHauptB) false [] kL kL :=
  .call kSetze (.cons k70 .nil) kHpSetzeB rfl

/-- `hauptB`'s `locks L { setze(70); }`. -/
def kLocksB : Stmt kD (vertragVon kD kHauptB) false [] [] [] :=
  .locks () (fun _ h => nomatch h) (.cons kRufB .nil)

/-- `hauptB`, as in the source. -/
def kRumpfB : Endblock kD (vertragVon kD kHauptB) false [] [] :=
  .cons kB0 (.cons kLocksB (.ret .empty List.Perm.nil))

/-- **The program of `beispiele/124`**: the source's bodies and the source's
    contracts (`setze`'s `ensures` matches the source since lane 204; see the
    header for the history). -/
def kP : Programm kD where
  invariante := fun i => (nomatch i)
  requires
    | .setze => kGleich
    | .pruefeA => kA7
    | _ => .tru
  ensures
    | .setze => .and kGleich (.eq (.slot KTab.konto () kI0 kDarfK) (.var .here))
    | .hauptA => kA7
    | .pruefeA => .eq (.var .here) k7
    | _ => .tru
  rumpf
    | .setze => kRumpfSetze
    | .hauptA => kRumpfA
    | .hauptB => kRumpfB
    | .pruefeA => kRumpfP

def kFs : List kD.Fn := [kSetze, kHauptA, kHauptB, kPruefeA]

theorem kFs_voll : ∀ g : kD.Fn, g ∈ kFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- **The lock invariant `konto[0] == konto[1]`**, protecting `konto`. -/
def kSI : SperrInv kD :=
  ⟨fun _ => [.inl KTab.konto], fun _ s => decide ((s.slots KTab.konto 0 ()).n = (s.slots KTab.konto 1 ()).n)⟩

theorem kSI_ok : SperrInvOk kSI := by
  refine ⟨fun L c hc => ?_, fun L s s' h => ?_⟩
  · cases L
    rw [List.mem_singleton.mp hc]
    exact List.mem_singleton.mpr rfl
  · have e : s.slots KTab.konto = s'.slots KTab.konto := h (.inl KTab.konto) List.mem_cons_self
    show decide ((s.slots KTab.konto 0 ()).n = (s.slots KTab.konto 1 ()).n) =
      decide ((s'.slots KTab.konto 0 ()).n = (s'.slots KTab.konto 1 ()).n)
    rw [e]

theorem kLocks_voll : ∀ L : kD.Lock, L ∈ ([()] : List kD.Lock) := fun L => by
  cases L; exact List.mem_singleton_self _

def kCs : List (kD.Tab ⊕ kD.Glob) := [.inl KTab.konto, .inl KTab.privA, .inl KTab.privB]

theorem kCs_voll : ∀ c : kD.Tab ⊕ kD.Glob, c ∈ kCs := fun c => by
  rcases c with t | g
  · cases t <;> simp only [kCs, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]
  · exact (nomatch g)

/-- **The checker accepts the program** with its declared starts `hauptA`,
    `hauptB` (`concurrent { hauptA, hauptB }`). -/
theorem kP_akzeptiert : Akzeptiert kP kSI kFs [()] kCs [kHauptA, kHauptB] [] = true := by decide

/-! ## 3. The user obligations -/

theorem kA_schreib {S : SperrInv kD} {O : Orakel kD} {U : Umwelt kD} {passes : Nat}
    {R : ∀ f : kD.Fn, World kD → Env kD (kD.params f) → RufAusgang f} (σ : World kD)
    (ρ : Env kD (kD.params kHauptA)) :
    ∃ σ2 : World kD, execEndH S O U passes R kRumpfA σ ρ =
        execEndH S O U passes R (.cons kLocksA kRestA) σ2 ρ ∧
      (σ2.slots KTab.privA 0 ()).n = 7 ∧ (σ2.slots KTab.privA 1 ()).n = 7 :=
  ⟨_, rfl, rfl, rfl⟩

theorem kInv_of_ens {κ σ2 : World kD} {ρk : Env kD (kD.params kSetze)}
    {v : ErgVal kD (kD.erg kSetze)} (h : EnsAmRueck kP kSetze κ σ2 ρk v) :
    kSI.inv () σ2.speicher = true := by
  have h' : (decide ((σ2.slots KTab.konto 0 ()).n = (σ2.slots KTab.konto 1 ()).n) &&
      decide ((σ2.slots KTab.konto 0 ()).n = (ρk.get .here).n)) = true := h
  simp only [Bool.and_eq_true] at h'
  exact h'.1

theorem kA_req {W : World kD} (h : (W.slots KTab.privA 0 ()).n = 7) :
    ReqAmEintritt kP kPruefeA W .nil := by
  show decide ((W.slots KTab.privA 0 ()).n = 7) = true
  simp only [h, decide_true]

theorem kA_lauf {O : Orakel kD} {U : Umwelt kD} (hU : HavocOk kSI U)
    {R : ∀ f : kD.Fn, World kD → Env kD (kD.params f) → RufAusgang f} (hR : RespektiertRahmen kP R)
    (σ : World kD) (ρ : Env kD (kD.params kHauptA)) {σ' : World kD} {v : ErgVal kD (kD.erg kHauptA)}
    (hrun : execEndH kSI O U 0 R kRumpfA σ ρ = .zurueck σ' v) :
    (σ'.slots KTab.privA 0 ()).n = 7 := by
  obtain ⟨σ2, e2, h20, _⟩ := kA_schreib (S := kSI) (O := O) (U := U) (passes := 0) (R := R) σ ρ
  rw [e2] at hrun
  simp only [execEndH, kLocksA] at hrun
  erw [execStmtH_locks_eins] at hrun
  have hU2 : (U () σ2).slots KTab.privA = σ2.slots KTab.privA :=
    (hU () σ2).2.1 (.inl KTab.privA) (fun h => by have := List.mem_singleton.mp h; cases this)
  rcases execStmtH_call_fall (S := kSI) (O := O) (U := U) (passes := 0) (R := R)
    (l := false) (Γ := []) kSetze (.cons k30 .nil) kHpSetzeA rfl ((U () σ2).nimmt ()) ρ with
    ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
  · have hf1 := (hR.2 _ _ _ _ _ hR1).1.1 KTab.privA rfl
    cases hi : kSI.inv () σ1.speicher with
    | false => simp only [freiH, hi, Bool.false_eq_true, if_false] at hrun; cases hrun
    | true =>
      simp only [freiH, hi, if_true] at hrun
      simp only [kRestA, kRufP, execEndH] at hrun
      rcases execStmtH_call_fall (S := kSI) (O := O) (U := U) (passes := 0) (R := R)
        (l := false) (Γ := []) kPruefeA .nil kHpPruefe rfl (σ1.gibt ()) ρ with
        ⟨σ3, v3, hR3, h3⟩ | ⟨e3, he3, h3⟩ | ⟨e3, h3⟩ <;> erw [h3] at hrun
      · simp only at hrun
        cases hrun
        have hf3 := (hR.2 _ _ _ _ _ hR3).1.1 KTab.privA rfl
        have e0 : σ3.slots KTab.privA 0 () = σ2.slots KTab.privA 0 () :=
          (hf3 0 ()).trans ((hf1 0 ()).trans (congrFun (congrFun hU2 0) ()))
        show (σ3.slots KTab.privA 0 ()).n = 7
        rw [e0]
        exact h20
      · cases hrun
      · cases hrun
  · simp only [freiH] at hrun; cases hrun
  · simp only [freiH] at hrun; cases hrun

/-- `hauptA`: `ensures privA[0] == 7` from its write (the lock's move and the
    callees' frames leave `privA` alone); the caller duty of both calls from
    the lock invariant at the acquire and from the frames; no `logik` outcome
    because the release check follows from `setze`'s `ensures`. -/
theorem kP_koerper_A : KoerperGutS kP 0 (axWahr kD) kSI kHauptA := by
  have hr : kP.rumpf kHauptA = kRumpfA := rfl
  refine ⟨fun O' _ _ _ U hU R hR hOV σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U hU R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    have h := kA_lauf hU hR σ ρ hrun
    show decide ((σ'.slots KTab.privA 0 ()).n = 7) = true
    simp only [h, decide_true]
  · rw [hr] at hrun
    obtain ⟨σ2, e2, h20, _⟩ := kA_schreib (S := kSI) (O := O') (U := U) (passes := 0)
      (R := torRuf kP R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, kLocksA] at hrun
    erw [execStmtH_locks_eins] at hrun
    have hU2 : (U () σ2).slots KTab.privA = σ2.slots KTab.privA :=
      (hU () σ2).2.1 (.inl KTab.privA) (fun h => by have := List.mem_singleton.mp h; cases this)
    have hreq : ReqAmEintritt kP kSetze (((U () σ2).nimmt ()).lese kL [])
        (evalArgs (((U () σ2).nimmt ()).lese kL []) (Args.cons (Λ := kL) (Γ := []) k30 .nil)
          (((U () σ2).nimmt ()).lese kL []) ρ) := (hU () σ2).2.2
    have htor : ∀ w a, ReqAmEintritt kP kSetze w a → torRuf kP R kSetze w a = R kSetze w a :=
      fun _ _ h => if_pos h
    rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := torRuf kP R)
      (l := false) (Γ := []) kSetze (.cons k30 .nil) kHpSetzeA rfl ((U () σ2).nimmt ()) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hR1' := (htor _ _ hreq).symm.trans hR1
      have hf1 := (hR.2 _ _ _ _ _ hR1').1.1 KTab.privA rfl
      cases hi : kSI.inv () σ1.speicher with
      | false => simp only [freiH, hi, Bool.false_eq_true, if_false] at hrun; cases hrun
      | true =>
        simp only [freiH, hi, if_true] at hrun
        simp only [kRestA, kRufP, execEndH] at hrun
        have e0 : ((σ1.gibt ()).lese [] []).slots KTab.privA 0 () = σ2.slots KTab.privA 0 () :=
          (hf1 0 ()).trans (congrFun (congrFun hU2 0) ())
        have hreq3 : ReqAmEintritt kP kPruefeA ((σ1.gibt ()).lese [] []) .nil :=
          kA_req (by rw [e0]; exact h20)
        rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := torRuf kP R)
          (l := false) (Γ := []) kPruefeA .nil kHpPruefe rfl (σ1.gibt ()) ρ with
          ⟨σ3, v3, hR3, h3⟩ | ⟨e3, he3, h3⟩ | ⟨e3, h3⟩ <;> erw [h3] at hrun
        · cases hrun
        · cases hrun
          have htor3 : torRuf kP R kPruefeA ((σ1.gibt ()).lese [] []) .nil =
              R kPruefeA ((σ1.gibt ()).lese [] []) .nil := if_pos hreq3
          exact hOV _ _ _ _ (htor3.symm.trans he3) g rfl
        · cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOV _ _ _ _ ((htor _ _ hreq).symm.trans he1) g rfl
    · simp only [freiH] at hrun; cases hrun
  · rw [hr] at hrun
    obtain ⟨σ2, e2, _, _⟩ := kA_schreib (S := kSI) (O := O') (U := U) (passes := 0) (R := R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, kLocksA] at hrun
    erw [execStmtH_locks_eins] at hrun
    have hreq : ReqAmEintritt kP kSetze (((U () σ2).nimmt ()).lese kL [])
        (evalArgs (((U () σ2).nimmt ()).lese kL []) (Args.cons (Λ := kL) (Γ := []) k30 .nil)
          (((U () σ2).nimmt ()).lese kL []) ρ) := (hU () σ2).2.2
    rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := R)
      (l := false) (Γ := []) kSetze (.cons k30 .nil) kHpSetzeA rfl ((U () σ2).nimmt ()) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hinv := kInv_of_ens (hR.1 _ _ _ hreq σ1 v1 hR1)
      simp only [freiH, hinv, if_true] at hrun
      simp only [kRestA, kRufP, execEndH] at hrun
      rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := R)
        (l := false) (Γ := []) kPruefeA .nil kHpPruefe rfl (σ1.gibt ()) ρ with
        ⟨σ3, v3, hR3, h3⟩ | ⟨e3, he3, h3⟩ | ⟨e3, h3⟩ <;> erw [h3] at hrun
      · cases hrun
      · cases hrun
        exact hOL _ _ _ _ he3
      · cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOL _ _ _ _ he1
    · simp only [freiH] at hrun; cases hrun

theorem kB_schreib {S : SperrInv kD} {O : Orakel kD} {U : Umwelt kD} {passes : Nat}
    {R : ∀ f : kD.Fn, World kD → Env kD (kD.params f) → RufAusgang f} (σ : World kD)
    (ρ : Env kD (kD.params kHauptB)) :
    ∃ σ2 : World kD, execEndH S O U passes R kRumpfB σ ρ =
        execEndH S O U passes R (.cons kLocksB (.ret .empty List.Perm.nil)) σ2 ρ :=
  ⟨_, rfl⟩

end K124
end Gabbro.Grammatik
