module

public import Core.Ast.LowLevel.Proofs.DeviceDma
public import Core.Ast.LowLevel.Proofs.DeviceLend
public import Core.Ast.LowLevel.Proofs.DeviceTransition

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel.Device

open Katalog Maschine Annahme

private def selectedDevice : Binding Plattform.x86_64.katalog where
  handle := ⟨0, ⟨⟨.virtio, 0⟩, 0⟩, [.read, .write]⟩
  row := Plattform.x86_64.virtio
  selected := by
    simp only [Katalog.enthaelt, Plattform.katalog, Plattform.zeilen, Plattform.endpunkte,
      List.map_cons, List.mem_append, List.mem_cons, eq_self, or_true, true_or]
  described := rfl

private def owner : Kontext := .faden 0

private def ownedRegion : LoanRegion := ⟨⟨0, 0⟩, ⟨0, 4096⟩, true, true⟩

private def readyState (phase : GeraetePhase) : State :=
  let boot : State :=
    Zustand.start (fun _ => { phases := fun o => if o = selectedDevice.object then some phase else none })
      (fun _ => .laeuft) (fun _ => ⟨some owner, .nutzer, (), fun _ => false, 0, false, []⟩)
      ⟨fun _ => true, fun _ => 0⟩ (fun _ => 0) (.leer (fun _ => 0))
  { boot with buchung := { boot.buchung with
      geraet := fun o => if o = selectedDevice.object then some (owner, .frei) else none
      aussengriff := fun c h right => c = owner ∧ h = selectedDevice.handle ∧ right ∈ h.rights
      umfang := fun i => if i = 0 then List.range 4096 else []
      haelt := fun c h _right => c = owner ∧ h = ownedRegion.handle } }

private theorem selectedAuthority (phase : GeraetePhase) (mode : RegisterAccess)
    (admitted : registerZugriff selectedDevice.row mode.operation = true) :
    Befugt selectedDevice phase mode (readyState phase) owner := by
  refine ⟨rfl, rfl, ?_, admitted⟩
  intro z inAccess
  change z ∈ [⟨selectedDevice.handle, mode.operation.required⟩] at inAccess
  cases List.mem_singleton.mp inAccess
  refine ⟨rfl, rfl, ?_⟩
  cases mode with
  | read _ | fallibleRead _ _ => exact List.mem_cons_self
  | write _ _ => exact List.mem_cons_of_mem _ List.mem_cons_self

def RegisterIssueErfuellbarAussage (mode : RegisterAccess) : Prop :=
  ∃ (k : Katalog) (binding : Binding k) c before plan after,
    Rule binding mode .ready none c before plan after ∧
    plan.aktion = .frage (binding.question mode)

private theorem selectedIssue (mode : RegisterAccess)
    (admitted : registerZugriff selectedDevice.row mode.operation = true) :
    RegisterIssueErfuellbarAussage mode :=
  ⟨_, selectedDevice, owner, readyState .ready, _, _,
    .issue (selectedAuthority _ mode admitted) rfl, rfl⟩

theorem registerRead_erfuellbar : RegisterIssueErfuellbarAussage (.read 0x70) :=
  selectedIssue _ rfl

theorem registerWrite_erfuellbar : RegisterIssueErfuellbarAussage (.write 0x70 1) :=
  selectedIssue _ rfl

theorem registerReadElse_erfuellbar :
    ∃ range, RegisterIssueErfuellbarAussage (.fallibleRead 0x70 range) :=
  ⟨⟨1, 1, Nat.le_refl _⟩, selectedIssue _ rfl⟩

def TransitionErfuellbarAussage : Prop :=
  ∃ (k : Katalog) (binding : Binding k) offset value (change : RegisterTransition k binding)
    c before plan after,
    Rule binding (.write offset value) change.prior (some change.after) c before plan after ∧
    plan.aktion = .frage (binding.question (.write offset value))

theorem registerTransition_erfuellbar : TransitionErfuellbarAussage := by
  let change : RegisterTransition Plattform.x86_64.katalog selectedDevice :=
    ⟨.reset, .start, .ready, .start, Or.inr rfl, Or.inl rfl⟩
  exact ⟨_, selectedDevice, 0x70, 1, change, owner, readyState .reset, _, _,
    .issue (selectedAuthority _ (.write 0x70 1) rfl) rfl, rfl⟩

private def mapped : LoanState :=
  ⟨readyState .ready, fun o =>
    if o = selectedDevice.object then some ⟨ownedRegion.handle, ownedRegion.extent, true, true⟩ else none,
    fun _ => none⟩

private def lentState : LoanState :=
  setLoan mapped owner selectedDevice.object 0 (.lending ownedRegion.loan)
    (.verliehen ownedRegion.loan) (.verliehen selectedDevice.object) (some ⟨ownedRegion, .live, []⟩)

private theorem selectedLend :
    lend selectedDevice ownedRegion owner mapped (.geraet .virtio (.lend ownedRegion.loan)) lentState := by
  refine ⟨⟨⟨rfl, rfl⟩, rfl, ?_, fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, fun _ _ h => h.1⟩,
    rfl, rfl, rfl, rfl, ?_, ?_, rfl, rfl⟩
  · intro address
    simp only [mapped, readyState, ownedRegion, if_pos rfl, List.mem_range, Strecke.drin,
      Nat.zero_le, true_and]
  · exact ⟨⟨ownedRegion.handle, ownedRegion.extent, true, true⟩, rfl,
      rfl, ⟨Nat.le_refl _, by change 0 < 4096; omega, Nat.le_refl _⟩, fun h => h, fun h => h⟩
  · apply GeraeteUebergang.lend rfl
    change 0 < 4096 ∧ 4096 ≤ 2 ^ (52 : Nat) ∧ 0 % 4096 = 0 ∧ 4096 % 4096 = 0
    omega

theorem deviceLend_erfuellbar :
    ∃ (k : Katalog) (binding : Binding k) region c before event after, lend binding region c before event after :=
  ⟨_, selectedDevice, ownedRegion, owner, mapped, _, lentState, selectedLend⟩

theorem deviceDma_erfuellbar :
    ∃ (k : Katalog) (binding : Binding k) region c before lendEvent after dmaEvent transfer,
      lend binding region c before lendEvent after ∧ DmaStep binding c after dmaEvent transfer := by
  let access := DmaZugriff.read ownedRegion.loan.token 0 1
  have loaned := device_lend.2 _ _ _ _ _ _ _ selectedLend
  have allowed : DmaBefugt selectedDevice lentState owner ⟨ownedRegion, .live, []⟩ access := by
    refine ⟨loaned.2.2.1, rfl, selectedLend.2.2.2.2.2.1, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · exact Nat.zero_lt_succ _
    · change 1 ≤ 4096
      omega
  exact ⟨_, selectedDevice, ownedRegion, owner, mapped, _, lentState, _, _, selectedLend, .issue allowed⟩

private theorem loanAtStage {state : LoanState} {session : LoanSession}
    (lent : selectedDevice.Lent state owner session) (stage : Revocation) :
    selectedDevice.Lent (setSession state selectedDevice.object { session with revocation := stage })
      owner { session with revocation := stage } := by
  refine ⟨Function.update_self _ _ _, ?_⟩
  exact lent.2

def TakeBackErfuellbarAussage : Prop :=
  ∃ (k : Katalog) (binding : Binding k) c region before loanEvent lent stopped revoked invalidated
    synchronized session resultEvent after,
    lend binding region c before loanEvent lent ∧
    RevokeStep binding c lent (.stopped binding.object) stopped ∧
    RevokeStep binding c stopped (.unmapped binding.object) revoked ∧
    RevokeStep binding c revoked (.translationCacheInvalidated binding.object) invalidated ∧
    RevokeStep binding c invalidated (.cpuCacheSynchronized binding.object) synchronized ∧
    takeBack binding c session synchronized
      (.returned (after.machine.rechte.ausgeben region.handle.objekt)) resultEvent after

theorem deviceTakeBack_erfuellbar : TakeBackErfuellbarAussage := by
  let session : LoanSession := ⟨ownedRegion, .live, []⟩
  let stopping := { session with revocation := .stopped }
  let unmapped := { session with revocation := .revoked }
  let coherent := { session with revocation := .invalidated }
  let returned := { session with revocation := .synchronized }
  let stop := setSession lentState selectedDevice.object stopping
  let unmap := { setSession stop selectedDevice.object unmapped with
    mappings := Function.update stop.mappings selectedDevice.object none }
  let invalidate := setSession unmap selectedDevice.object coherent
  let synchronize := setSession invalidate selectedDevice.object returned
  have initialLoan : selectedDevice.Lent lentState owner session :=
    (device_lend.2 _ _ _ _ _ _ _ selectedLend).2.2.1
  have stoppedLoan : selectedDevice.Lent stop owner stopping := loanAtStage initialLoan .stopped
  have unmappedLoan : selectedDevice.Lent unmap owner unmapped := loanAtStage stoppedLoan .revoked
  have invalidatedLoan : selectedDevice.Lent invalidate owner coherent := loanAtStage unmappedLoan .invalidated
  have synchronizedLoan : selectedDevice.Lent synchronize owner returned := loanAtStage invalidatedLoan .synchronized
  exact ⟨_, selectedDevice, owner, ownedRegion, mapped, _, lentState, stop, unmap, invalidate,
    synchronize, returned, _, returnRegion synchronize owner selectedDevice.object ownedRegion,
    selectedLend, .stop initialLoan rfl, .revoke stoppedLoan rfl, .invalidate unmappedLoan rfl rfl,
    .synchronize invalidatedLoan rfl rfl, synchronizedLoan, rfl, rfl, rfl, .takeBack _, rfl, rfl, rfl⟩

end Gabbro.Core.Ast.LowLevel.Device

