module

public import Stage0.Senke.Images.Correctness
import Grammatik.Logik.Vertraege.Pruefer.Goal
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Stage0.Senke
  Runner Runner.IR Runner.Beweis Runner.Mach
  Gabbro.Stage0.Senke.BildMehr

variable [Kern]

private theorem exitGroup_request {M : MemSys} {θ : Type} {act : θ → Res θ} {before : Cfg M θ}
    {last : List Ev} {status : W} (terminal : Tr M act before last (.exit status) 1) :
    ∃ i t req k, before.ths[i]? = some (some t) ∧ act t = .ask (.sys req) k ∧
      last = [(i, req, none)] ∧ req.nr.toNat = NR_EXIT_GROUP ∧ req.a1 = status := by
  have notExit (rest : Res θ) : Runner.Mach.Res.ende rest ≠ some (.exit status) := by
    cases rest <;> intro equal <;> cases equal
  cases terminal with
  | tau _ suffix => cases suffix
  | priv _ _ suffix => cases suffix
  | ask _ _ _ _ _ suffix => cases suffix
  | exit _ _ _ suffix => cases suffix
  | cloneNo _ _ _ _ _ suffix => cases suffix
  | clone _ _ _ _ _ _ suffix => cases suffix
  | stop _ stopped | askStop _ _ _ _ stopped | cloneNoStop _ _ _ _ stopped =>
    exact (notExit _ stopped).elim
  | exitGroup found asked number => exact ⟨_, _, _, _, found, asked, rfl, number, rfl⟩

/-- The last x86 step of an actual process exit identifies the same request
    in the related IR thread. The only additional IR work is silent
    normalization at unchanged memory. -/
theorem image_exit_group_boundary {before : Cfg imageTSO Runner.X86.X}
    {ir : Cfg imageTSO (Res T)} {last : List Ev} {status : W}
    (related : Rel L0 ir before) (terminal : Tr imageTSO (actX L0) before last (.exit status) 1) :
    ∃ armed steps i req k, ProcessPrefix imageTSO actI ir [] steps armed ∧ Rel L0 armed before ∧
      armed.ms = ir.ms ∧ armed.ths[i]? = some (some (.ask (.sys req) k)) ∧
      last = [(i, req, none)] ∧ req.nr.toNat = NR_EXIT_GROUP ∧ req.a1 = status := by
  obtain ⟨i, _, req, _, found, asked, events, number, arg⟩ := exitGroup_request terminal
  obtain ⟨armed, rest, matched, slot, control, notNext, steps, silent⟩ :=
    norm_prefix cinv_L0 related found
  rcases inv_ask control asked notNext with ⟨_, _, different, _⟩ | ⟨k, rfl, _⟩
  · cases different
  · exact ⟨armed, steps, i, req, k, silent, matched, matched.ms.trans related.ms.symm, slot,
      events, number, arg⟩

/-- If the terminal step is the process exit emitted for the boot-thread
    clone guard, its status and the refused clone come from the actual
    runner observations. No source transition is needed for this stop. -/
theorem image_clone_refusal_stop {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {O : Orakel (declOf output.compiled.unit)}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {before : Cfg imageTSO Runner.X86.X} {ir : Cfg imageTSO (Res T)}
    {earlier last : List Ev} {status : W} {id extra : W}
    (related : Rel L0 ir before) (terminal : Tr imageTSO (actX L0) before last (.exit status) 1)
    (bootThread : ∀ i req, (i, req, none) ∈ last → i = 0)
    (cloneStatus : status = BitVec.ofNat 64 cloneCode)
    (history : (earlier.filter (fun event => event.1 == 0)).getLast? = some (0, cloneReq, some (id, extra)))
    (refused : id.toInt < 0) :
    ImageStopMatches output O state earlier last (.exit status) := by
  obtain ⟨_, _, i, req, _, _, _, _, _, events, number, arg⟩ :=
    image_exit_group_boundary related terminal
  have issuing := bootThread i req (events.symm ▸ List.mem_cons_self)
  subst i
  obtain ⟨prior, appended⟩ := List.getLast?_eq_some_iff.mp history
  exact ⟨0, req, events, number, congrArg Ende.exit arg.symm,
    Or.inr (Or.inr (Or.inr ⟨rfl, arg.trans cloneStatus, prior, id, extra, appended, refused⟩))⟩

/-- The compiler's depth-guard status cannot be explained as a source
    outcome of a void entry with no foreign routines. In particular it
    must never be confused with a normal void return, which emits zero. -/
theorem ImageStopMatches.no_depth_guard {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {O : Orakel (declOf output.compiled.unit)}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe} {earlier last : List Ev}
    (noResult : (declOf output.compiled.unit).erg output.compiled.main = none)
    (noForeign : output.compiled.unit.axs.length = 0) :
    ¬ ImageStopMatches output O state earlier last (.exit (BitVec.ofNat 64 105)) := by
  rintro ⟨_, req, _, _, ended, explained⟩
  have status := Ende.exit.inj ended
  rcases explained with returned | never | hardware | refused
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, zero⟩ := returned
    exact (by decide : (BitVec.ofNat 64 105) ≠ 0) (status.trans (zero noResult))
  · obtain ⟨_, _, routine, _, _, _, _⟩ := never
    exact Nat.not_lt_zero routine.val (noForeign ▸ routine.isLt)
  · obtain ⟨_, cause, _, code⟩ := hardware
    have impossible := status.trans code
    cases cause <;> simp only [hwCode] at impossible <;> revert impossible <;> decide
  · exact (by decide : BitVec.ofNat 64 105 ≠ BitVec.ofNat 64 cloneCode) (status.trans refused.2.1)

/-- A byte of an actual startup stack belongs to exactly one reservation. -/
theorem imageStackFootprint_disjoint {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {i j : Nat} {address : W}
    (first : imageStackFootprint output i address) (second : imageStackFootprint output j address) :
    i = j := by
  have ordered {a b : Nat} (h : a < b)
      (left : imageStackFootprint output a address) (right : imageStackFootprint output b address) : False := by
    have order := Nat.mul_le_mul_left output.image.Ks h
    exact Nat.not_le_of_lt left.2.2 (right.2.1.trans' (Nat.add_le_add_left (Nat.mul_le_mul_left 8 order) _))
  exact (lt_trichotomy i j).elim (fun lt => (ordered lt first second).elim)
    (fun rest => rest.elim id fun gt => (ordered gt second first).elim)

/-- The emitted frame array fits below the world and below the address limit. -/
theorem Emitted.stackReservation_bounds {src : String} {reserve : Nat} {options : Profil.Options}
    (output : Emitted src reserve options) :
    output.image.fp0 + 8 * (output.image.Ks * (output.starts.length + 1)) ≤ output.image.Y.lo ∧
      output.image.Y.lo < 2 ^ 64 := by
  obtain ⟨_, _, _, layout, _, _, _, _⟩ := bild_lage output.emission output.funktionen_voll
    (fun base bound => layU_in output.compiled.unit output.tor base bound)
    (fun base => layU_dis output.compiled.unit output.tor base)
    (fun base => by simp only [layU]; omega)
    (fun base => layU_sync output.compiled.unit output.tor base)
  have room := layout.hyord
  have allocated := layout.hyhi
  have limit := layout.hfit
  exact ⟨by simpa only [Emitted.starts, List.length_map] using layout.hylo, by omega⟩

/-- All emitted stack reservations lie before the compiled world's bytes. -/
theorem imageStackFootprint_before_world {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {i : Nat} {address : W}
    (owned : imageStackFootprint output i address) : address.toNat < output.image.Y.lo := by
  have endOrder := Nat.mul_le_mul_left output.image.Ks (Nat.succ_le_succ owned.1)
  exact owned.2.2.trans_le ((Nat.add_le_add_left (Nat.mul_le_mul_left 8 endOrder) _).trans
    output.stackReservation_bounds.1)

/-- Every byte touched by a startup-frame store is covered by the actual
    reservation of the executing thread. In particular, the word address
    calculation cannot wrap around. -/
theorem imageStackFootprint_slot {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {i index : Nat} {address : W}
    (declared : i ≤ output.starts.length) (inside : index < output.image.Ks)
    (touches : fenster
      (slot (BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * i))) (BitVec.ofNat 64 index))
      address) :
    imageStackFootprint output i address := by
  let base := output.image.fp0 + 8 * (output.image.Ks * i)
  let fp := BitVec.ofNat 64 base
  let word := slot fp (BitVec.ofNat 64 index)
  have endOrder := Nat.mul_le_mul_left output.image.Ks (Nat.succ_le_succ declared)
  have room := (Nat.add_le_add_left (Nat.mul_le_mul_left 8 endOrder) output.image.fp0).trans
    output.stackReservation_bounds.1
  rw [Nat.mul_succ, Nat.mul_add, ← Nat.add_assoc] at room
  change base + 8 * output.image.Ks ≤ output.image.Y.lo at room
  have limit := room.trans_lt output.stackReservation_bounds.2
  have exactBase : fp.toNat = base := by
    change (BitVec.ofNat 64 base).toNat = base
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) limit)]
  have exactWord : word.toNat = base + 8 * index := by
    have bounds : fp.toNat + 8 * output.image.Ks ≤ 2 ^ 64 := by rw [exactBase]; exact limit.le
    change (slot fp (BitVec.ofNat 64 index)).toNat = base + 8 * index
    rw [slot_toNat bounds inside, exactBase]
  change (address - word).toNat < 8 at touches
  have fits : (address - word).toNat + word.toNat < 2 ^ 64 := by rw [exactWord]; omega
  have exactAddress := congrArg BitVec.toNat (BitVec.sub_add_cancel address word)
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt fits, exactWord] at exactAddress
  refine ⟨declared, ?_, ?_⟩
  · change base ≤ address.toNat
    omega
  · rw [Nat.mul_succ, Nat.mul_add, ← Nat.add_assoc]
    change address.toNat < base + 8 * output.image.Ks
    omega

/-- An in-range emitted startup store meets the SC projection's private
    write condition for every touched byte. -/
theorem imageStackStore_projected {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {i index : Nat} (value : W)
    (declared : i ≤ output.starts.length) (inside : index < output.image.Ks) :
    ProjectedRequest (imageStackFootprint output) i (.wr
      (slot (BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * i))) (BitVec.ofNat 64 index)) value) :=
  .owned rfl (fun _ touches => imageStackFootprint_slot declared inside touches)
    (fun _ _ touches _ other => imageStackFootprint_disjoint other (imageStackFootprint_slot declared inside touches))

/-- The two process models use exactly the same machine memory and
    controls. Only the permitted answers at the host boundary differ. -/
def imageToTSO {θ : Type} (machine : Cfg imageTSO θ) : Cfg (TSO L0) θ :=
  ⟨machine.ms, machine.ths⟩

def tsoToImage {θ : Type} (machine : Cfg (TSO L0) θ) : Cfg imageTSO θ :=
  ⟨machine.ms, machine.ths⟩

/-- Forget the host restrictions while retaining the actual configuration,
    observation and transition. -/
theorem image_step_tso {θ : Type} {act : θ → Res θ}
    {before after : Cfg imageTSO θ} {events : List Ev}
    (step : ProcessStep imageTSO act before events after) :
    ProcessStep (TSO L0) act (imageToTSO before) events (imageToTSO after) := by
  cases step with
  | tau flush => exact .tau flush
  | priv ready move => exact .priv ready move
  | ask ready ask ordinary answer next => exact .ask ready ask ordinary answer.1 next
  | exit ready ask kind => exact .exit ready ask kind
  | cloneNo ready ask answer refusal next => exact .cloneNo ready ask answer.1 refusal next
  | clone ready ask answer success parent child =>
    exact .clone ready ask answer.1 success parent child

/-- The number of steps and the complete observation list survive this
    projection. -/
theorem image_prefix_tso {θ : Type} {act : θ → Res θ}
    {before after : Cfg imageTSO θ} {events : List Ev} {count : Nat}
    (run : ProcessPrefix imageTSO act before events count after) :
    ProcessPrefix (TSO L0) act (imageToTSO before) events count (imageToTSO after) := by
  induction run with
  | nil c => exact .nil (imageToTSO c)
  | cons step _ next => exact .cons (image_step_tso step) next

private theorem quiet_answer {before after : (TSO L0).St} {i : Nat} {op : Op} {answer : Ans}
    (quiet : lbl i op answer = []) (accepted : (TSO L0).ans before i op answer after) :
    imageTSO.ans before i op answer after := by
  cases op with
  | rd | wr | cas | fp => exact ⟨accepted, True.intro⟩
  | sys => cases quiet

/-- A silent TSO step cannot use a host answer, so the same step is
    available in the actual image model with its host restrictions. -/
theorem tso_silent_step_image {θ : Type} {act : θ → Res θ}
    {before after : Cfg (TSO L0) θ} {events : List Ev}
    (step : ProcessStep (TSO L0) act before events after) (quiet : events = []) :
    ProcessStep imageTSO act (tsoToImage before) events (tsoToImage after) := by
  cases step with
  | tau flush => exact .tau flush
  | priv ready move => exact .priv ready move
  | ask ready request ordinary answered next =>
    exact .ask ready request ordinary (quiet_answer quiet answered) next
  | exit | cloneNo | clone => cases quiet

/-- Silent prefixes retain the same endpoints in both memory models. -/
theorem tso_silent_prefix_image {θ : Type} {act : θ → Res θ}
    {before after : Cfg (TSO L0) θ} {events : List Ev} {count : Nat}
    (run : ProcessPrefix (TSO L0) act before events count after) (quiet : events = []) :
    ProcessPrefix imageTSO act (tsoToImage before) events count (tsoToImage after) := by
  induction run with
  | nil c => exact .nil (tsoToImage c)
  | cons step _ rest =>
    obtain ⟨head, tail⟩ := List.append_eq_nil_iff.mp quiet
    exact .cons (tso_silent_step_image step head) (rest tail)

/-- The actual host-constrained runner path projects to the SC memory
    steps used by the compiler refinement. Flushes carry no program step.
    The request classifier is the compiler-side obligation. -/
theorem image_memory_prefix_projects {footprint : Nat → W → Prop}
    {initial final : Cfg imageTSO (Res T)} {count : Nat}
    (run : ProcessPrefix imageTSO actI initial [] count final)
    (buffers : PrivateBuffers footprint initial.ms.1)
    (classify : ∀ {c : Cfg imageTSO (Res T)} {n},
      ProcessPrefix imageTSO actI initial [] n c →
      ∀ {i : Nat} {op : Op} {resume : Ans → Res T} {response : Ans} {after : (TSO L0).St},
        c.ths[i]? = some (some (.ask op resume)) → op.special = false → lbl i op response = [] →
        (TSO L0).ans c.ms i op response after → ProjectedRequest footprint i op) :
    PrivateBuffers footprint final.ms.1 ∧
      SCErreichbar L0 ⟨projectSCState footprint initial.ms, initial.ths⟩
        ⟨projectSCState footprint final.ms, final.ths⟩ :=
  tso_memory_process_projects (image_prefix_tso run) buffers
    (fun seen => classify (tso_silent_prefix_image seen rfl))

private theorem image_clone_answer {state : imageTSO.St} {i : Nat} {id extra : W} (nonzero : id ≠ 0) :
    imageTSO.ans state i (.sys cloneReq) (some (id, extra)) state := by
  refine ⟨True.intro, ?_⟩
  change (if cloneReq = cloneReq then _ else _)
  rw [ite_eq_left rfl]
  exact ⟨rfl, id, extra, rfl, nonzero⟩

/-- The decoded startup clone is an actual transition in the host-restricted
    runner. Its positive reply preserves memory and appends precisely the
    child addresses read from the parent's own buffered view. -/
theorem image_bootClone_run {before : Cfg imageTSO (Res T)} {i : Nat} {parent child : T}
    {dest index pad : BitVec 32} {id extra : W}
    (running : before.ths[i]? = some (some (.next parent)))
    (instruction : InsAt (before.ms.1.view i) parent.pc 24 dest index pad)
    (entry : (before.ms.1.view i).rd64 (slot parent.fp (sx index)) = some child.pc)
    (frame : (before.ms.1.view i).rd64 (slot parent.fp (sx index) + 8) = some child.fp)
    (positive : 0 < id.toInt) :
    let threads := before.ths.set i (some (ret1 parent id)) ++ [some (.next child)]
    ProcessPrefix imageTSO actI before [(i, cloneReq, some (id, extra))] 6 ⟨before.ms, threads⟩ ∧
      threads[before.ths.length]? = some (some (.next child)) := by
  intro threads
  let pending : Res T := .ask (.sys cloneReq) fun result =>
    opt result fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1
  let ready : Cfg imageTSO (Res T) := ⟨before.ms, before.ths.set i (some pending)⟩
  have fetched : ProcessPrefix imageTSO actI before [] 5 ready :=
    tso_silent_prefix_image (bootClone_read_prefix (before := imageToTSO before) running instruction entry frame) rfl
  have indexed : ready.ths[i]? = some (some pending) :=
    List.getElem?_set_self (List.getElem?_eq_some_iff.mp running).1
  have nonzero : id ≠ 0 := by
    intro zero
    subst id
    exact (by decide : ¬ (0 < (0 : W).toInt)) positive
  obtain ⟨created, found⟩ := bootClone_step (before := ready) (parent := parent) (child := child)
    indexed (image_clone_answer nonzero) positive
  constructor
  · simpa only [ready, threads, List.nil_append, List.set_set, Nat.reduceAdd] using
      fetched.trans (ProcessPrefix.ofStep created)
  · simpa only [ready, threads, List.length_set, List.set_set] using found

/-- A negative host reply is recorded at the same decoded clone. It
    leaves all memory and slot allocations unchanged and returns the
    actual negative result to the waiting parent. -/
theorem image_bootClone_refused {before : Cfg imageTSO (Res T)} {i : Nat} {parent child : T}
    {dest index pad : BitVec 32} {id extra : W}
    (running : before.ths[i]? = some (some (.next parent)))
    (instruction : InsAt (before.ms.1.view i) parent.pc 24 dest index pad)
    (entry : (before.ms.1.view i).rd64 (slot parent.fp (sx index)) = some child.pc)
    (frame : (before.ms.1.view i).rd64 (slot parent.fp (sx index) + 8) = some child.fp)
    (negative : id.toInt < 0) :
    ProcessPrefix imageTSO actI before [(i, cloneReq, some (id, extra))] 6
      ⟨before.ms, before.ths.set i (some (ret1 parent id))⟩ := by
  let resume : Ans → Res T := fun result =>
    opt result fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1
  let ready : Cfg imageTSO (Res T) := ⟨before.ms, before.ths.set i (some (.ask (.sys cloneReq) resume))⟩
  have fetched : ProcessPrefix imageTSO actI before [] 5 ready :=
    tso_silent_prefix_image (bootClone_read_prefix (before := imageToTSO before) running instruction entry frame) rfl
  have indexed : ready.ths[i]? = some (some (.ask (.sys cloneReq) resume)) :=
    List.getElem?_set_self (List.getElem?_eq_some_iff.mp running).1
  have nonzero : id ≠ 0 := by
    intro zero
    subst id
    exact (by decide : ¬ ((0 : W).toInt < 0)) negative
  have refused : ProcessStep imageTSO actI ready [(i, cloneReq, some (id, extra))]
      ⟨ready.ms, ready.ths.set i (some (ret1 parent id))⟩ := by
    refine .cloneNo indexed rfl (image_clone_answer nonzero) ?_ ?_
    · intro result additional same
      cases same
      exact not_lt_of_ge negative.le
    · simp only [resume, opt_some, ite_eq_right nonzero]
  simpa only [ready, List.nil_append, List.set_set, Nat.reduceAdd] using fetched.trans (ProcessPrefix.ofStep refused)

/-- Appending the successful startup clone activates the same next source
    slot. Earlier threads may already have executed model steps. Their
    local states, including the retired threads' recorded heads, are kept. -/
theorem ImageSlotsMatch.activate_clone {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {O : Orakel (declOf output.compiled.unit)} {history : List Ev}
    {before : Cfg imageTSO (Res T)} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {parent child : T} {id extra : W}
    (slots : ImageSlotsMatch output E O history before state)
    (entry : before.ths[0]? = some (some (.next parent)))
    (waiting : state.wartet 0 = [])
    (declared : before.ths.length < E.starts.length) :
    let i := before.ths.length
    let threads := before.ths.set 0 (some (ret1 parent id)) ++ [some (.next child)]
    ∃ next actualStart, E.starts[i]? = some actualStart ∧
      FadenSchrittX E.P.mitRuhe O.mitRuhe output.image.passes
        (GeteiltV (D := declOf output.compiled.unit) E.P E.ws) state next ∧
      ImageSlotsMatch output E O (history ++ [(0, cloneReq, some (id, extra))]) ⟨before.ms, threads⟩ next ∧ next.m = state.m ∧
      ∀ {body : PCfg} {snapshots positions committed},
        MTRel E.P.mitRuhe O.mitRuhe output.image.passes output.image.Y.withIdle
          body state snapshots positions committed →
        MTRel E.P.mitRuhe O.mitRuhe output.image.passes output.image.Y.withIdle
          ⟨body.m, body.ths ++ [none]⟩ next snapshots positions committed := by
  intro i threads
  have parentInside := (List.getElem?_eq_some_iff.mp entry).1
  have parentLive : state.lebt 0 = true := (slots.1 0).mpr parentInside
  have childIdle : state.lebt i = false := by
    cases ready : state.lebt i with
    | false => rfl
    | true => exact ((Nat.lt_irrefl _) ((slots.1 i).mp ready)).elim
  let next : FadenMaschine (declOf output.compiled.unit).mitRuhe :=
    ⟨state.m, fun j => if j = i then true else state.lebt j, state.wartet,
      fun j => if j = i then state.rang 0 + 1 else state.rang j, state.uhr + 1⟩
  have activate : FadenSchrittX E.P.mitRuhe O.mitRuhe output.image.passes
      (GeteiltV (D := declOf output.compiled.unit) E.P E.ws) state next :=
    .kind state 0 i parentLive waiting childIdle
  have size : threads.length = i + 1 := by
    simp only [threads, i, List.length_append, List.length_set, List.length_singleton]
  have childSlot : threads[i]? = some (some (.next child)) := by
    change (before.ths.set 0 _ ++ [some (.next child)])[before.ths.length]? = _
    rw [List.getElem?_append_right (by rw [List.length_set]), List.length_set, Nat.sub_self]
    rfl
  refine ⟨next, E.starts[i]'declared, List.getElem?_eq_getElem declared, activate, ⟨?_, ?_⟩, rfl, ?_⟩
  · intro j
    change (if j = i then true else state.lebt j) = true ↔ j < threads.length
    rw [size]
    by_cases equal : j = i
    · subst j
      simp
    · rw [ite_eq_right equal, slots.1]
      change j < i ↔ j < i + 1
      exact ⟨fun lt => lt.trans (Nat.lt_succ_self i),
        fun lt => Nat.lt_of_le_of_ne (Nat.le_of_lt_succ lt) equal⟩
  · intro j retired
    change threads[j]? = some none at retired
    have newBound := (List.getElem?_eq_some_iff.mp retired).1
    rw [size] at newBound
    have oldBound : j < i := by
      by_contra outside
      have equal : j = i := Nat.le_antisymm (Nat.le_of_lt_succ newBound) (Nat.le_of_not_gt outside)
      subst j
      rw [childSlot] at retired
      cases retired
    have atParent : j ≠ 0 := by
      intro equal
      subst j
      have within : 0 < (before.ths.set 0 (some (ret1 parent id))).length := by simpa using parentInside
      simp only [threads, List.getElem?_append_left within, List.getElem?_set_self parentInside] at retired
      cases retired
    have within : j < (before.ths.set 0 (some (ret1 parent id))).length := by simpa [i] using oldBound
    have wasRetired : before.ths[j]? = some none := by
      simpa only [threads, List.getElem?_append_left within, List.getElem?_set_ne (Ne.symm atParent)] using retired
    obtain done | ⟨atExit, req, earlier, fromStart, since, sameHead, matched, kind, last⟩ := slots.2 j wasRetired
    · exact Or.inl done
    · refine Or.inr ⟨atExit, req, earlier, fromStart, .schritt state next since activate,
        sameHead, matched, kind, ?_⟩
      simp only [List.filter_append, List.filter_cons, beq_eq_false_iff_ne.mpr (Ne.symm atParent),
        Bool.false_eq_true, ite_false, List.filter_nil, List.append_nil, last]
  · intro body snapshots positions committed related
    apply related.append_pending_root (after := next) rfl rfl
    intro j live
    change (if j = i then true else state.lebt j) = true
    simp only [live, ite_self]

/-- A prepared startup clone in the actual emitted code advances the same
    declared GX slot and carries the entire goal to the new configuration. -/
theorem Emitted.image_declared_clone_goal {src : String} {reserve : Nat} {options : Profil.Options}
    (output : Emitted src reserve options) {E : Einheit (declOf output.compiled.unit)}
    {O : Orakel (declOf output.compiled.unit)} (unit : ImageModelUnit output E)
    (accepted : akzeptiertX_pruefer.akzeptiert E output.fsA.1 output.lsA.1 output.csA.1 = true)
    (calls : CallSitePflicht E) (binding : ForeignVertrag E O) (hardware : HardwareAnnahmenHw O E.Q)
    {before : Cfg imageTSO (Res T)} {history : List Ev}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe} {j : Nat} {id extra : W}
    {start : Σ f : (declOf output.compiled.unit).Fn, Env (declOf output.compiled.unit) ((declOf output.compiled.unit).params f)}
    (declared : output.starts[j]? = some start)
    (code : BytesAt (before.ms.1.view 0) codeBase (output.image.code.flatMap encII))
    (position : before.ths.length = j + 1)
    (slots : ImageSlotsMatch output E O history before state) (waiting : state.wartet 0 = [])
    (reached : ImageReach output E O (imageSourceStart E) state) (positive : 0 < id.toInt) :
    let parent : T := ⟨BitVec.ofNat 64 codeBase + BitVec.ofNat 64 (16 * (10 * j)) +
      BitVec.ofNat 64 (16 * 2), BitVec.ofNat 64 output.image.fp0⟩
    let child : T := ⟨BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length + startLen + startLen * j)),
      BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (j + 1)))⟩
    let scratch := slot parent.fp (sx (II.f (startScratch output.compiled.main)))
    before.ths[0]? = some (some (.next parent)) →
    (before.ms.1.view 0).rd64 scratch = some child.pc →
    (before.ms.1.view 0).rd64 (scratch + 8) = some child.fp →
    let after : Cfg imageTSO (Res T) :=
      ⟨before.ms, before.ths.set 0 (some (ret1 parent id)) ++ [some (.next child)]⟩
    ProcessPrefix imageTSO actI before [(0, cloneReq, some (id, extra))] 6 after ∧
    after.ths[j + 1]? = some (some (.next child)) ∧ E.starts[j + 1]? = some start ∧
    ∃ next, ImageSlotsMatch output E O (history ++ [(0, cloneReq, some (id, extra))]) after next ∧
      next.m.faeden (j + 1) = (imageSourceStart E).m.faeden (j + 1) ∧
      ImageReach output E O (imageSourceStart E) next ∧ ImageGoalAt output E O next := by
  intro parent child scratch running entry frame after
  obtain ⟨site, _, _⟩ := output.loaded_boot_site E.Q code declared
  have instruction : InsAt (before.ms.1.view 0) parent.pc 24
      (II.f ((startScratch output.compiled.main + 2 : Nat) : Int))
      (II.f (startScratch output.compiled.main)) (II.f 0) :=
    site 2 (by rw [spawnOne_len]; decide)
  obtain ⟨run, childSlot⟩ := image_bootClone_run running instruction entry frame positive
  have head : E.starts[j + 1]? = some start := by
    rw [unit.starts]
    exact declared
  have bound : before.ths.length < E.starts.length := position ▸ (List.getElem?_eq_some_iff.mp head).1
  obtain ⟨next, _, _, stepped, matched, unchanged, _⟩ :=
    slots.activate_clone (child := child) (id := id) (extra := extra) running waiting bound
  have dormant : state.lebt (j + 1) = false :=
    Bool.eq_false_iff.mpr (fun live => Nat.lt_irrefl _ (position ▸ (slots.1 _).mp live))
  have nextReached : ImageReach output E O (imageSourceStart E) next := .schritt state next reached stepped
  have duties := nutzerPflicht_of_akzeptiert output.fsA output.lsA accepted
  refine ⟨run, position ▸ childSlot, head, next, matched,
    unchanged.symm ▸ (fadenInvX_erreichbar reached).schlaeft _ dormant, nextReached, ?_⟩
  exact gabbro_ziel akzeptiertX_pruefer _ E output.fsA output.lsA output.csA accepted duties calls unit.postDeckt
    O binding hardware output.image.passes _ _ (laufzeit_initRuhe E) _ _ nextReached

/-- A declared non-returning thread exit retires just its own slot.
    The source stays at the exact call head, and the exit is entered in
    the history of that thread only. -/
theorem ImageSlotsMatch.retire_never {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {O : Orakel (declOf output.compiled.unit)} {history : List Ev}
    {before : Cfg imageTSO (Res T)} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {i : Nat} {req : Req} {resume : Ans → Res T}
    (slots : ImageSlotsMatch output E O history before state)
    (reached : ImageReach output E O (imageSourceStart E) state)
    (ready : before.ths[i]? = some (some (.ask (.sys req) resume)))
    (number : req.nr.toNat = NR_EXIT) (matching : ImageNeverRequest output O state i req) :
    let after : Cfg imageTSO (Res T) := ⟨before.ms, before.ths.set i none⟩
    ProcessStep imageTSO actI before [(i, req, none)] after ∧
      ImageSlotsMatch output E O (history ++ [(i, req, none)]) after state := by
  intro after
  refine ⟨.exit ready rfl number, ?_, ?_⟩
  · intro j
    simpa only [after, List.length_set] using slots.1 j
  · intro j retired
    by_cases same : j = i
    · subst j
      refine Or.inr ⟨state, req, history.filter (fun event => event.1 == i),
        reached, .start, rfl, matching, number, ?_⟩
      simp only [List.filter_append, List.filter_cons, beq_self_eq_true, ite_true, List.filter_nil]
    · have unchanged : before.ths[j]? = some none := by
        simpa only [after, List.getElem?_set_ne (Ne.symm same)] using retired
      obtain finished | ⟨atExit, call, earlier, fromStart, since, sameHead, matched, kind, last⟩ :=
        slots.2 j unchanged
      · exact Or.inl finished
      · refine Or.inr ⟨atExit, call, earlier, fromStart, since, sameHead, matched, kind, ?_⟩
        simp only [List.filter_append, List.filter_cons, beq_eq_false_iff_ne.mpr (Ne.symm same),
          Bool.false_eq_true, ite_false, List.filter_nil, List.append_nil, last]

end Gabbro.Stage0
