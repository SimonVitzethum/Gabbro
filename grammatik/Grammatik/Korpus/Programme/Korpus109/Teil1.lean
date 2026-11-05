module

public import Grammatik.Korpus.Programme.Korpus109.Teil1a
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

namespace K109

instance : DecidableEq kD.Ax := inferInstanceAs (DecidableEq Empty)

/-- `write_a(i)`: `T.slots[i].v = 1;`. -/
def kRumpfWriteA : Endblock kD (vertragVon kD kWriteA) false [Ty.index 4] kLA :=
  .cons (.assignSlot KTab.t () (.var .here) kEins rfl kDarfTA)
    (.ret .empty (by first | exact List.Perm.refl _ | (simp [Vertrag.ende, nach, nachSig, Signatur.anfang, vertragVon, Vertrag.vonSig])))

/-- `write_b(i)`: `U.slots[i].v = 2;`. -/
def kRumpfWriteB : Endblock kD (vertragVon kD kWriteB) false [Ty.index 4] kLB :=
  .cons (.assignSlot KTab.u () (.var .here) kZwei rfl kDarfUB)
    (.ret .empty (by first | exact List.Perm.refl _ | (simp [Vertrag.ende, nach, nachSig, Signatur.anfang, vertragVon, Vertrag.vonSig])))

/-- The call `write_a(0)` inside `distribute_a`'s lock. -/
def kRufA : Stmt kD (vertragVon kD kDistA) false [] kLA kLA :=
  .call kWriteA (.cons kJ0 .nil) kHpWriteA rfl

/-- `distribute_a`'s `locks L { write_a(0); }`. -/
def kLocksA : Stmt kD (vertragVon kD kDistA) false [] [] [] :=
  .locks KLock.l (fun _ h => nomatch h) (.cons kRufA .nil)

/-- `distribute_a`, as in the source. -/
def kRumpfDistA : Endblock kD (vertragVon kD kDistA) false [] [] :=
  .cons kLocksA (.ret .empty List.Perm.nil)

/-- The call `write_b(0)` inside `distribute_b`'s lock. -/
def kRufB : Stmt kD (vertragVon kD kDistB) false [] kLB kLB :=
  .call kWriteB (.cons kJ0 .nil) kHpWriteB rfl

/-- `distribute_b`'s `locks M { write_b(0); }`. -/
def kLocksB : Stmt kD (vertragVon kD kDistB) false [] [] [] :=
  .locks KLock.m (fun _ h => nomatch h) (.cons kRufB .nil)

/-- `distribute_b`, as in the source. -/
def kRumpfDistB : Endblock kD (vertragVon kD kDistB) false [] [] :=
  .cons kLocksB (.ret .empty List.Perm.nil)

/-- **The program of `beispiele/109`**: the source's bodies; trivial contracts
    (the source declares no `requires`/`ensures` on these four functions). -/
def kP : Programm kD where
  invariante := fun i => (nomatch i)
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf
    | .writeA => kRumpfWriteA
    | .distA => kRumpfDistA
    | .writeB => kRumpfWriteB
    | .distB => kRumpfDistB

def kFs : List kD.Fn := [kWriteA, kDistA, kWriteB, kDistB]

theorem kFs_voll : ∀ g : kD.Fn, g ∈ kFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- **The lock family**: `L` protects `T`, `M` protects `U`; the source
    declares no invariant, so both are trivially true. -/
def kSI : SperrInv kD :=
  ⟨fun | KLock.l => [.inl KTab.t] | KLock.m => [.inl KTab.u], fun _ _ => true⟩

theorem kSI_ok : SperrInvOk kSI := by
  refine ⟨fun L c hc => ?_, fun L s s' h => rfl⟩
  · cases L
    · rw [List.mem_singleton.mp hc]; exact List.mem_singleton.mpr rfl
    · rw [List.mem_singleton.mp hc]; exact List.mem_singleton.mpr rfl

theorem kLocks_voll : ∀ L : kD.Lock, L ∈ ([KLock.l, KLock.m] : List kD.Lock) := fun L => by
  cases L
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

def kCs : List (kD.Tab ⊕ kD.Glob) := [.inl KTab.t, .inl KTab.u]

theorem kCs_voll : ∀ c : kD.Tab ⊕ kD.Glob, c ∈ kCs := fun c => by
  rcases c with t | g
  · cases t <;> simp only [kCs, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]
  · exact (nomatch g)

/-- **The checker accepts the program** with its declared starts
    `distribute_a`, `distribute_b` (the two entry dispatch roots). -/
theorem kP_akzeptiert : Akzeptiert kP kSI kFs [KLock.l, KLock.m] kCs [kDistA, kDistB] [] = true := by decide

/-! ## 3. The user obligations -/

/-- Every `requires` is `.tru`, at every function, world and environment. -/
theorem kReqWahr (f : kD.Fn) (W : World kD) (ρ : Env kD (kD.params f)) :
    ReqAmEintritt kP f W ρ := by rfl

theorem kP_koerper_writeA : KoerperGutS kP 0 (axWahr kD) kSI kWriteA := by
  have hr : kP.rumpf kWriteA = kRumpfWriteA := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [kRumpfWriteA, execEndH, execStmtH] at hrun
    cases hrun
    cases ρ with
    | cons x rest =>
      cases rest
      rfl
  · rw [hr] at hrun
    simp only [kRumpfWriteA, execEndH, execStmtH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [kRumpfWriteA, execEndH, execStmtH] at hrun
    cases hrun

theorem kP_koerper_writeB : KoerperGutS kP 0 (axWahr kD) kSI kWriteB := by
  have hr : kP.rumpf kWriteB = kRumpfWriteB := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [kRumpfWriteB, execEndH, execStmtH] at hrun
    cases hrun
    cases ρ with
    | cons x rest =>
      cases rest
      rfl
  · rw [hr] at hrun
    simp only [kRumpfWriteB, execEndH, execStmtH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [kRumpfWriteB, execEndH, execStmtH] at hrun
    cases hrun

theorem kDistA_schreib {S : SperrInv kD} {O : Orakel kD} {U : Umwelt kD} {passes : Nat}
    {R : ∀ f : kD.Fn, World kD → Env kD (kD.params f) → RufAusgang f} (σ : World kD)
    (ρ : Env kD (kD.params kDistA)) :
    ∃ σ2 : World kD, execEndH S O U passes R kRumpfDistA σ ρ =
        execEndH S O U passes R (.cons kLocksA (.ret .empty List.Perm.nil)) σ2 ρ :=
  ⟨_, rfl⟩

theorem kDistB_schreib {S : SperrInv kD} {O : Orakel kD} {U : Umwelt kD} {passes : Nat}
    {R : ∀ f : kD.Fn, World kD → Env kD (kD.params f) → RufAusgang f} (σ : World kD)
    (ρ : Env kD (kD.params kDistB)) :
    ∃ σ2 : World kD, execEndH S O U passes R kRumpfDistB σ ρ =
        execEndH S O U passes R (.cons kLocksB (.ret .empty List.Perm.nil)) σ2 ρ :=
  ⟨_, rfl⟩

/-- `distribute_a`: `ensures` is `.tru`; the caller duty of the call from the
    trivial `requires`; no `logik` outcome because the release check is the
    trivially-true invariant. -/
theorem kP_koerper_distA : KoerperGutS kP 0 (axWahr kD) kSI kDistA := by
  have hr : kP.rumpf kDistA = kRumpfDistA := rfl
  refine ⟨fun O' _ _ _ U hU R hR hOV σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    obtain ⟨σ2, e2⟩ := kDistA_schreib (S := kSI) (O := O') (U := U) (passes := 0)
      (R := torRuf kP R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, kLocksA] at hrun
    erw [execStmtH_locks_eins] at hrun
    have hreq : ReqAmEintritt kP kWriteA (((U KLock.l σ2).nimmt KLock.l).lese kLA [])
        (evalArgs (((U KLock.l σ2).nimmt KLock.l).lese kLA []) (Args.cons (Λ := kLA) (Γ := []) kJ0 .nil)
          (((U KLock.l σ2).nimmt KLock.l).lese kLA []) ρ) := kReqWahr _ _ _
    rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := torRuf kP R)
      (l := false) (Γ := []) kWriteA (.cons kJ0 .nil) kHpWriteA rfl ((U KLock.l σ2).nimmt KLock.l) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hinv : kSI.inv KLock.l σ1.speicher = true := rfl
      simp only [freiH, hinv, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      have htor : torRuf kP R kWriteA _ _ = R kWriteA _ _ := if_pos hreq
      exact hOV _ _ _ _ (htor.symm.trans he1) g rfl
    · simp only [freiH] at hrun; cases hrun
  · rw [hr] at hrun
    obtain ⟨σ2, e2⟩ := kDistA_schreib (S := kSI) (O := O') (U := U) (passes := 0) (R := R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, kLocksA] at hrun
    erw [execStmtH_locks_eins] at hrun
    rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := R)
      (l := false) (Γ := []) kWriteA (.cons kJ0 .nil) kHpWriteA rfl ((U KLock.l σ2).nimmt KLock.l) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hinv : kSI.inv KLock.l σ1.speicher = true := rfl
      simp only [freiH, hinv, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOL _ _ _ _ he1
    · simp only [freiH] at hrun; cases hrun

/-- `distribute_b`: the mirror image over `M`/`U`. -/
theorem kP_koerper_distB : KoerperGutS kP 0 (axWahr kD) kSI kDistB := by
  have hr : kP.rumpf kDistB = kRumpfDistB := rfl
  refine ⟨fun O' _ _ _ U hU R hR hOV σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    obtain ⟨σ2, e2⟩ := kDistB_schreib (S := kSI) (O := O') (U := U) (passes := 0)
      (R := torRuf kP R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, kLocksB] at hrun
    erw [execStmtH_locks_eins] at hrun
    have hreq : ReqAmEintritt kP kWriteB (((U KLock.m σ2).nimmt KLock.m).lese kLB [])
        (evalArgs (((U KLock.m σ2).nimmt KLock.m).lese kLB []) (Args.cons (Λ := kLB) (Γ := []) kJ0 .nil)
          (((U KLock.m σ2).nimmt KLock.m).lese kLB []) ρ) := kReqWahr _ _ _
    rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := torRuf kP R)
      (l := false) (Γ := []) kWriteB (.cons kJ0 .nil) kHpWriteB rfl ((U KLock.m σ2).nimmt KLock.m) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hinv : kSI.inv KLock.m σ1.speicher = true := rfl
      simp only [freiH, hinv, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      have htor : torRuf kP R kWriteB _ _ = R kWriteB _ _ := if_pos hreq
      exact hOV _ _ _ _ (htor.symm.trans he1) g rfl
    · simp only [freiH] at hrun; cases hrun
  · rw [hr] at hrun
    obtain ⟨σ2, e2⟩ := kDistB_schreib (S := kSI) (O := O') (U := U) (passes := 0) (R := R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, kLocksB] at hrun
    erw [execStmtH_locks_eins] at hrun
    rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := R)
      (l := false) (Γ := []) kWriteB (.cons kJ0 .nil) kHpWriteB rfl ((U KLock.m σ2).nimmt KLock.m) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hinv : kSI.inv KLock.m σ1.speicher = true := rfl
      simp only [freiH, hinv, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOL _ _ _ _ he1
    · simp only [freiH] at hrun; cases hrun

theorem kP_koerper : ∀ f : kD.Fn, KoerperGutS kP 0 (axWahr kD) kSI f := by
  intro f
  cases f
  · exact kP_koerper_writeA
  · exact kP_koerper_distA
  · exact kP_koerper_writeB
  · exact kP_koerper_distB

theorem kP_inv : ∀ f : kD.Fn, InvGutS kP 0 (axWahr kD) kSI f :=
  fun _ => invGutS_ohne fun i _ => (nomatch i)

theorem kP_ohneEwig : ohneEwigB kP kFs = true := by decide

theorem kP_koerper_alle : ∀ (passes : Nat) (f : kD.Fn), KoerperGutS kP passes (axWahr kD) kSI f :=
  koerperGutS_alle kFs_voll kP_ohneEwig kP_koerper

theorem kP_inv_alle : ∀ (passes : Nat) (f : kD.Fn), InvGutS kP passes (axWahr kD) kSI f :=
  invGutS_alle kFs_voll kP_ohneEwig kP_inv

/-! ## 4. The program as one declaration, and every premise group -/

/-- The start memory: every slot zero. -/
def kSp : Speicher kD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

end K109
end Gabbro.Grammatik
