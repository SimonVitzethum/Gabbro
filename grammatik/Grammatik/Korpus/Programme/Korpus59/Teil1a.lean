module

public import Grammatik.Zielsatz.Kern.Proben
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

public import Grammatik.Korpus.Programme.Korpus59.Teil1
@[expose] public section

namespace Gabbro.Grammatik

namespace K59
instance : DecidableEq kD.Ax := inferInstanceAs (DecidableEq Empty)

/-- `zaehle(i)`: `Takte.slots[i].stand = 1;`. -/
def kRumpfZaehle : Endblock kD (vertragVon kD kZaehle) false [Ty.index 64] kLT :=
  .cons (.assignSlot KTab.takte () (.var .here) kEins rfl kDarfTakte)
    (.ret .empty (by first | exact List.Perm.refl _ | (simp [Vertrag.ende, nach, nachSig, Signatur.anfang, vertragVon, Vertrag.vonSig])))

/-- `bearbeite(i)`: `Auftraege.slots[i].stand = 1;`. -/
def kRumpfBearbeite : Endblock kD (vertragVon kD kBearbeite) false [Ty.index 16] kLR :=
  .cons (.assignSlot KTab.auftraege () (.var .here) kEins rfl kDarfAuftr)
    (.ret .empty (by first | exact List.Perm.refl _ | (simp [Vertrag.ende, nach, nachSig, Signatur.anfang, vertragVon, Vertrag.vonSig])))

/-- The call `zaehle(0)` inside `takt_verteiler`'s lock. -/
def kRufZ : Stmt kD (vertragVon kD kTaktVert) false [] kLT kLT :=
  .call kZaehle (.cons kJ0T .nil) kHpZaehle rfl

/-- `takt_verteiler`'s `locks TAKT { zaehle(0); }`. -/
def kLocksT : Stmt kD (vertragVon kD kTaktVert) false [] [] [] :=
  .locks KLock.takt (fun _ h => nomatch h) (.cons kRufZ .nil)

/-- `takt_verteiler`, as in the source. -/
def kRumpfTaktVert : Endblock kD (vertragVon kD kTaktVert) false [] [] :=
  .cons kLocksT (.ret .empty List.Perm.nil)

/-- The call `bearbeite(0)` inside `ruf_verteiler`'s lock. -/
def kRufB : Stmt kD (vertragVon kD kRufVert) false [] kLR kLR :=
  .call kBearbeite (.cons kJ0U .nil) kHpBearbeite rfl

/-- `ruf_verteiler`'s `locks RING { bearbeite(0); }`. -/
def kLocksR : Stmt kD (vertragVon kD kRufVert) false [] [] [] :=
  .locks KLock.ring (fun _ h => nomatch h) (.cons kRufB .nil)

/-- `ruf_verteiler`, as in the source. -/
def kRumpfRufVert : Endblock kD (vertragVon kD kRufVert) false [] [] :=
  .cons kLocksR (.ret .empty List.Perm.nil)

/-- **The program of `beispiele/59`**: the source's bodies; trivial contracts
    (the source declares no `requires`/`ensures` on these four functions); the interrupt
    handler `takt_verteiler` (its entry is `via idt`, Opus agent H 2026-09-26). -/
def kP : Programm kD where
  invariante := fun i => (nomatch i)
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf
    | .zaehle => kRumpfZaehle
    | .taktVert => kRumpfTaktVert
    | .bearbeite => kRumpfBearbeite
    | .rufVert => kRumpfRufVert
  -- `entry zeitgeber vector 32 via idt … dispatch takt_verteiler`: the one root entered by
  -- hardware (Opus agent H, 2026-09-26); `ruf_verteiler`'s entry is a system call (no `via`)
  unterbricht
    | .taktVert => true
    | _ => false

def kFs : List kD.Fn := [kZaehle, kTaktVert, kBearbeite, kRufVert]

theorem kFs_voll : ∀ g : kD.Fn, g ∈ kFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- **The lock family**: `TAKT` protects `Takte`, `RING` protects `Auftraege`;
    the source declares no invariant, so both are trivially true. -/
def kSI : SperrInv kD :=
  ⟨fun | KLock.takt => [.inl KTab.takte] | KLock.ring => [.inl KTab.auftraege], fun _ _ => true⟩

theorem kSI_ok : SperrInvOk kSI := by
  refine ⟨fun L c hc => ?_, fun L s s' h => rfl⟩
  · cases L
    · rw [List.mem_singleton.mp hc]; exact List.mem_singleton.mpr rfl
    · rw [List.mem_singleton.mp hc]; exact List.mem_singleton.mpr rfl

theorem kLocks_voll : ∀ L : kD.Lock, L ∈ ([KLock.takt, KLock.ring] : List kD.Lock) := fun L => by
  cases L
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

def kCs : List (kD.Tab ⊕ kD.Glob) := [.inl KTab.takte, .inl KTab.auftraege]

theorem kCs_voll : ∀ c : kD.Tab ⊕ kD.Glob, c ∈ kCs := fun c => by
  rcases c with t | g
  · cases t <;> simp only [kCs, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]
  · exact (nomatch g)

/-- **The checker accepts the program** with its declared starts
    `takt_verteiler`, `ruf_verteiler` (the two entry dispatch roots). -/
theorem kP_akzeptiert : Akzeptiert kP kSI kFs [KLock.takt, KLock.ring] kCs [kTaktVert, kRufVert] [] = true := by decide

/-! ## 3. The user obligations -/

/-- Every `requires` is `.tru`, at every function, world and environment. -/
theorem kReqWahr (f : kD.Fn) (W : World kD) (ρ : Env kD (kD.params f)) :
    ReqAmEintritt kP f W ρ := by rfl

theorem kP_koerper_zaehle : KoerperGutS kP 0 (axWahr kD) kSI kZaehle := by
  have hr : kP.rumpf kZaehle = kRumpfZaehle := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [kRumpfZaehle, execEndH, execStmtH] at hrun
    cases hrun
    cases ρ with
    | cons x rest =>
      cases rest
      rfl
  · rw [hr] at hrun
    simp only [kRumpfZaehle, execEndH, execStmtH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [kRumpfZaehle, execEndH, execStmtH] at hrun
    cases hrun

theorem kP_koerper_bearbeite : KoerperGutS kP 0 (axWahr kD) kSI kBearbeite := by
  have hr : kP.rumpf kBearbeite = kRumpfBearbeite := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [kRumpfBearbeite, execEndH, execStmtH] at hrun
    cases hrun
    cases ρ with
    | cons x rest =>
      cases rest
      rfl
  · rw [hr] at hrun
    simp only [kRumpfBearbeite, execEndH, execStmtH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [kRumpfBearbeite, execEndH, execStmtH] at hrun
    cases hrun

theorem kTakt_schreib {S : SperrInv kD} {O : Orakel kD} {U : Umwelt kD} {passes : Nat}
    {R : ∀ f : kD.Fn, World kD → Env kD (kD.params f) → RufAusgang f} (σ : World kD)
    (ρ : Env kD (kD.params kTaktVert)) :
    ∃ σ2 : World kD, execEndH S O U passes R kRumpfTaktVert σ ρ =
        execEndH S O U passes R (.cons kLocksT (.ret .empty List.Perm.nil)) σ2 ρ :=
  ⟨_, rfl⟩

theorem kRuf_schreib {S : SperrInv kD} {O : Orakel kD} {U : Umwelt kD} {passes : Nat}
    {R : ∀ f : kD.Fn, World kD → Env kD (kD.params f) → RufAusgang f} (σ : World kD)
    (ρ : Env kD (kD.params kRufVert)) :
    ∃ σ2 : World kD, execEndH S O U passes R kRumpfRufVert σ ρ =
        execEndH S O U passes R (.cons kLocksR (.ret .empty List.Perm.nil)) σ2 ρ :=
  ⟨_, rfl⟩

/-- `takt_verteiler`: `ensures` is `.tru`; the caller duty of the call from
    the trivial `requires`; no `logik` outcome because the release check is
    the trivially-true invariant. -/
theorem kP_koerper_taktVert : KoerperGutS kP 0 (axWahr kD) kSI kTaktVert := by
  have hr : kP.rumpf kTaktVert = kRumpfTaktVert := rfl
  refine ⟨fun O' _ _ _ U hU R hR hOV σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    obtain ⟨σ2, e2⟩ := kTakt_schreib (S := kSI) (O := O') (U := U) (passes := 0)
      (R := torRuf kP R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, kLocksT] at hrun
    erw [execStmtH_locks_eins] at hrun
    have hreq : ReqAmEintritt kP kZaehle (((U KLock.takt σ2).nimmt KLock.takt).lese kLT [])
        (evalArgs (((U KLock.takt σ2).nimmt KLock.takt).lese kLT []) (Args.cons (Λ := kLT) (Γ := []) kJ0T .nil)
          (((U KLock.takt σ2).nimmt KLock.takt).lese kLT []) ρ) := kReqWahr _ _ _
    rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := torRuf kP R)
      (l := false) (Γ := []) kZaehle (.cons kJ0T .nil) kHpZaehle rfl ((U KLock.takt σ2).nimmt KLock.takt) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hinv : kSI.inv KLock.takt σ1.speicher = true := rfl
      simp only [freiH, hinv, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      have htor : torRuf kP R kZaehle _ _ = R kZaehle _ _ := if_pos hreq
      exact hOV _ _ _ _ (htor.symm.trans he1) g rfl
    · simp only [freiH] at hrun; cases hrun
  · rw [hr] at hrun
    obtain ⟨σ2, e2⟩ := kTakt_schreib (S := kSI) (O := O') (U := U) (passes := 0) (R := R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, kLocksT] at hrun
    erw [execStmtH_locks_eins] at hrun
    rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := R)
      (l := false) (Γ := []) kZaehle (.cons kJ0T .nil) kHpZaehle rfl ((U KLock.takt σ2).nimmt KLock.takt) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hinv : kSI.inv KLock.takt σ1.speicher = true := rfl
      simp only [freiH, hinv, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOL _ _ _ _ he1
    · simp only [freiH] at hrun; cases hrun

/-- `ruf_verteiler`: the mirror image over `RING`/`Auftraege`. -/
theorem kP_koerper_rufVert : KoerperGutS kP 0 (axWahr kD) kSI kRufVert := by
  have hr : kP.rumpf kRufVert = kRumpfRufVert := rfl
  refine ⟨fun O' _ _ _ U hU R hR hOV σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    obtain ⟨σ2, e2⟩ := kRuf_schreib (S := kSI) (O := O') (U := U) (passes := 0)
      (R := torRuf kP R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, kLocksR] at hrun
    erw [execStmtH_locks_eins] at hrun
    have hreq : ReqAmEintritt kP kBearbeite (((U KLock.ring σ2).nimmt KLock.ring).lese kLR [])
        (evalArgs (((U KLock.ring σ2).nimmt KLock.ring).lese kLR []) (Args.cons (Λ := kLR) (Γ := []) kJ0U .nil)
          (((U KLock.ring σ2).nimmt KLock.ring).lese kLR []) ρ) := kReqWahr _ _ _
    rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := torRuf kP R)
      (l := false) (Γ := []) kBearbeite (.cons kJ0U .nil) kHpBearbeite rfl ((U KLock.ring σ2).nimmt KLock.ring) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hinv : kSI.inv KLock.ring σ1.speicher = true := rfl
      simp only [freiH, hinv, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      have htor : torRuf kP R kBearbeite _ _ = R kBearbeite _ _ := if_pos hreq
      exact hOV _ _ _ _ (htor.symm.trans he1) g rfl
    · simp only [freiH] at hrun; cases hrun
  · rw [hr] at hrun
    obtain ⟨σ2, e2⟩ := kRuf_schreib (S := kSI) (O := O') (U := U) (passes := 0) (R := R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, kLocksR] at hrun
    erw [execStmtH_locks_eins] at hrun
    rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := R)
      (l := false) (Γ := []) kBearbeite (.cons kJ0U .nil) kHpBearbeite rfl ((U KLock.ring σ2).nimmt KLock.ring) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hinv : kSI.inv KLock.ring σ1.speicher = true := rfl
      simp only [freiH, hinv, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOL _ _ _ _ he1
    · simp only [freiH] at hrun; cases hrun

theorem kP_koerper : ∀ f : kD.Fn, KoerperGutS kP 0 (axWahr kD) kSI f := by
  intro f
  cases f
  · exact kP_koerper_zaehle
  · exact kP_koerper_taktVert
  · exact kP_koerper_bearbeite
  · exact kP_koerper_rufVert

end K59
end Gabbro.Grammatik
