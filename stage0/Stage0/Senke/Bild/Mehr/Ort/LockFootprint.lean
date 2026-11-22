module

public import Stage0.Senke.Bild.Mehr.Ort.LockState
public import Stage0.Senke.Bild.Mehr.ImageTransition
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Stage0.Senke.BildMehr Runner Runner.IR Runner.Mach Runner.Beweis

def Zelle.carrier {D : Deklaration} : Senke.Zelle D → D.Tab ⊕ D.Glob
  | .glob global => .inr global
  | .elem table .. => .inl table

/-- A protected cell is private only to a thread holding all the
    guards required by its carrier. A cell with no guard is not
    assigned on the basis of the lock state. -/
def protectedCellFootprint {D : Deklaration} (layout : Lay D) (source : RufMaschineG D)
    (thread : Nat) (address : W) : Prop :=
  ∃ cell : Senke.Zelle D, cell.da layout ∧
    cell.adr layout ≤ address.toNat ∧ address.toNat < cell.adr layout + cell.bytes ∧
    (∃ guard, Bewacht (Zelle.carrier cell) guard) ∧
    ∀ guard, Bewacht (Zelle.carrier cell) guard → guard ∈ offen (source.faeden thread).spur

theorem protectedCellFootprint_bounds {D : Deklaration} {layout : Lay D}
    {source : RufMaschineG D} {thread : Nat} {address : W}
    (inLayout : LayIn layout) (owned : protectedCellFootprint layout source thread address) :
    layout.lo ≤ address.toNat ∧ address.toNat < layout.hi := by
  obtain ⟨cell, allocated, first, last, _, _⟩ := owned
  have inside : layout.lo ≤ cell.adr layout ∧ cell.adr layout + cell.bytes ≤ layout.hi := by
    cases cell with
    | glob global => exact inLayout.2.1 global
    | elem table field index => exact inLayout.1 table field index allocated
  exact ⟨inside.1.trans first, last.trans_le inside.2⟩

/-- Distinct allocated cells cannot overlap. If the same cell was
    claimed twice, its physical ticket queue identifies the same owner. -/
theorem ImageTicketStates.protected_exclusive {D : Deklaration} {N : Nat}
    {layout : Lay D} {memory : Mem} {source : RufMaschineG D} {states : D.Lock → Zustand N}
    (locks : ImageTicketStates layout memory source states) (cells : LayDis layout)
    {first second : Nat} {address : W}
    (left : protectedCellFootprint layout source first address)
    (right : protectedCellFootprint layout source second address) : first = second := by
  obtain ⟨cell, existsLeft, lowLeft, highLeft, ⟨guard, guards⟩, firstOwns⟩ := left
  obtain ⟨other, existsRight, lowRight, highRight, _, secondOwns⟩ := right
  have equalCell : cell = other := by
    by_contra different
    rcases cells.spans cell other existsLeft existsRight different with before | after <;> omega
  subst other
  have heldLeft := firstOwns guard guards
  have heldRight := secondOwns guard guards
  have firstInside : first < N := by
    by_contra outside
    exact (locks.owners guard).outside first (Nat.le_of_not_gt outside) heldLeft
  have secondInside : second < N := by
    by_contra outside
    exact (locks.owners guard).outside second (Nat.le_of_not_gt outside) heldRight
  have leftTicket := ((locks.owners guard).inside ⟨first, firstInside⟩).mpr heldLeft
  have rightTicket := ((locks.owners guard).inside ⟨second, secondInside⟩).mpr heldRight
  exact congrArg Fin.val ((locks.protocol guard).ausschluss leftTicket rightTicket)

theorem protectedCellFootprint_lock_disjoint {D : Deklaration} {layout : Lay D}
    {source : RufMaschineG D} {thread : Nat} {address : W} {locked : D.Lock}
    (inLayout : LayIn layout) (synchronized : LaySync layout)
    (owned : protectedCellFootprint layout source thread address) : ¬ LockBytes layout locked address := by
  intro lockByte
  exact (Nat.not_le_of_lt (protectedCellFootprint_bounds inLayout owned).2)
    ((synchronized.1 locked).1.trans lockByte.1)

/-- The image's fixed stack reservation and the currently protected
    cells use the same TSO projection. Other carrier permissions are
    handled by their own source access rules. -/
def imageProtectedFootprint {src : String} {reserve : Nat} {options : Profil.Options}
    (output : Emitted src reserve options) (source : RufMaschineG (declOf output.compiled.unit).mitRuhe)
    (thread : Nat) (address : W) : Prop :=
  imageStackFootprint output thread address ∨
    protectedCellFootprint output.image.Y.withIdle source thread address

theorem imageProtectedFootprint_initial {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {source : RufMaschineG (declOf output.compiled.unit).mitRuhe}
    {N : Nat} {memory : Mem}
    (locks : ImageTicketStates output.image.Y.withIdle memory source (fun _ => start N)) :
    imageProtectedFootprint output source = imageStackFootprint output := by
  funext thread address
  apply propext
  constructor
  · rintro (stack | ⟨cell, _, _, _, ⟨guard, guards⟩, held⟩)
    · exact stack
    · have owns := held guard guards
      by_cases inside : thread < N
      · have impossible := ((locks.owners guard).inside ⟨thread, inside⟩).mpr owns
        cases impossible
      · exact ((locks.owners guard).outside thread (Nat.le_of_not_gt inside) owns).elim
  · exact Or.inl

/-- The mapped image and its accepted model share one initial projection.
    No protected cell has an owner before the first image step. -/
theorem _root_.Gabbro.Stage0.MappedImage.initial_lock_projection [Kern]
    {src : String} {reserve : Nat} {options : Profil.Options} {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {machine : Cfg imageTSO Runner.X86.X}
    (mapped : MappedImage output machine) (unit : ImageModelUnit output E)
    (accepted : akzeptiertX_pruefer.akzeptiert E output.fsA.1 output.lsA.1 output.csA.1 = true)
    (O : Orakel (declOf output.compiled.unit)) :
    let ir : Cfg imageTSO (Res T) := ⟨machine.ms, [some t4]⟩
    let source := imageSourceStart E
    Rel L0 ir machine ∧ ImageSlotsMatch output E O [] ir source ∧
      ImageForeignTrace output [] source ∧
      ImageRuntimeMatchesAt (imageProtectedFootprint output source.m) output E O [] ir source ∧
      ImageTicketStates output.image.Y.withIdle machine.ms.1.m source.m
        (fun _ => start (output.starts.length + 1)) ∧
      PrivateBuffers (imageProtectedFootprint output source.m) machine.ms.1 ∧
      (projectSCState (imageProtectedFootprint output source.m) machine.ms).1 = machine.ms.1.m := by
  intro ir source
  obtain ⟨runner, slots, events, runtime⟩ := mapped.source_start unit O
  have locks := output.loaded_ticketStates mapped.bytes accepted
  have projection := imageProtectedFootprint_initial locks
  refine ⟨runner, slots, events, ?_, locks, privateBuffers_empty mapped.emptyBuffers, ?_⟩
  · rw [projection]
    exact runtime
  · change mergedView machine.ms.1 (imageProtectedFootprint output source.m) = machine.ms.1.m
    rw [projection, mergedView_empty _ _ mapped.emptyBuffers]

theorem imageProtectedFootprint_exclusive [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {source : RufMaschineG (declOf output.compiled.unit).mitRuhe}
    {N : Nat} {memory : Mem} {states : _ → Zustand N}
    (locks : ImageTicketStates output.image.Y.withIdle memory source states)
    (inLayout : LayIn output.image.Y.withIdle) (cells : LayDis output.image.Y.withIdle)
    {first second : Nat} {address : W}
    (left : imageProtectedFootprint output source first address)
    (right : imageProtectedFootprint output source second address) : first = second := by
  rcases left with left | left <;> rcases right with right | right
  · exact imageStackFootprint_disjoint left right
  · exact ((Nat.not_le_of_lt (imageStackFootprint_before_world left))
      (protectedCellFootprint_bounds inLayout right).1).elim
  · exact ((Nat.not_le_of_lt (imageStackFootprint_before_world right))
      (protectedCellFootprint_bounds inLayout left).1).elim
  · exact locks.protected_exclusive cells left right

theorem imageProtectedFootprint_lock_disjoint [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {source : RufMaschineG (declOf output.compiled.unit).mitRuhe}
    {thread : Nat} {address : W} {lock : (declOf output.compiled.unit).Lock}
    (inLayout : LayIn output.image.Y.withIdle) (synchronized : LaySync output.image.Y.withIdle)
    (order : output.image.Y.lo ≤ output.image.Y.hi)
    (owned : imageProtectedFootprint output source thread address) :
    ¬ LockBytes output.image.Y.withIdle lock address := by
  rcases owned with stack | data
  · intro lockByte
    have below := imageStackFootprint_before_world stack
    exact (Nat.not_le_of_lt below) (order.trans ((synchronized.1 lock).1.trans lockByte.1))
  · exact protectedCellFootprint_lock_disjoint inLayout synchronized data

/-- Changing the current source trace of the CAS issuer leaves every
    pending store assigned to the same owning thread. The actual TSO
    rule requires the issuer's buffer to have drained before answering. -/
theorem privateBuffers_after_release [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options}
    {source target : RufMaschineG (declOf output.compiled.unit).mitRuhe}
    {before after : imageTSO.St} {thread : Nat} {N : Nat} {states : _ → Zustand N}
    {address expected word : W} {reply : Ans}
    (answered : imageTSO.ans before thread (.cas address expected word) reply after)
    (old : PrivateBuffers (imageProtectedFootprint output source) before.1)
    (locks : ImageTicketStates output.image.Y.withIdle after.1.m target states)
    (inLayout : LayIn output.image.Y.withIdle) (cells : LayDis output.image.Y.withIdle)
    (others : ∀ issuer, issuer ≠ thread → ∀ lock,
      lock ∈ offen (source.faeden issuer).spur → lock ∈ offen (target.faeden issuer).spur) :
    PrivateBuffers (imageProtectedFootprint output source) after.1 ∧
      PrivateBuffers (imageProtectedFootprint output target) after.1 ∧
      projectSCState (imageProtectedFootprint output target) after =
        projectSCState (imageProtectedFootprint output source) after := by
  have drained : before.1.buf thread = [] := answered.1.1
  have buffers : after.1.buf = before.1.buf := by
    rcases answered.1.2 with ⟨_, _, same⟩ | ⟨_, _, _, _, changed⟩
    · rw [same]
    · have bufferEq := congrArg TSt.buf changed
      exact bufferEq
  have oldAfter : PrivateBuffers (imageProtectedFootprint output source) after.1 := by
    intro issuer store pending byte hit
    rw [buffers] at pending
    exact old issuer store pending byte hit
  have newAfter : PrivateBuffers (imageProtectedFootprint output target) after.1 := by
    intro issuer store pending byte hit
    have different : issuer ≠ thread := by
      intro same
      rw [same, buffers, drained] at pending
      cases pending
    have previous := (oldAfter issuer store pending byte hit).1
    have current : imageProtectedFootprint output target issuer byte := by
      rcases previous with stack | ⟨cell, present, low, high, guarded, held⟩
      · exact .inl stack
      · exact .inr ⟨cell, present, low, high, guarded,
          fun lock guards => others issuer different lock (held lock guards)⟩
    exact ⟨current, fun _ assigned => imageProtectedFootprint_exclusive locks inLayout cells assigned current⟩
  exact ⟨oldAfter, newAfter, projectSCState_reassign oldAfter newAfter⟩

/-- The CAS publishes the serving word in the SC projection while
    reassigning the protected cells according to the new source owner.
    The physical lock words themselves stay outside the private views. -/
theorem image_release_projected [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options}
    {source target : RufMaschineG (declOf output.compiled.unit).mitRuhe}
    {before after : imageTSO.St} {N : Nat} {thread : Fin N} {states : _ → Zustand N}
    {lock : (declOf output.compiled.unit).Lock} {start released : Zustand N}
    {expected word : W} {reply : Ans}
    (answered : imageTSO.ans before thread.val
      (.cas (BitVec.ofNat 64 (output.image.Y.lk lock + 8)) expected word) reply after)
    (old : PrivateBuffers (imageProtectedFootprint output source) before.1)
    (locks : ImageTicketStates output.image.Y.withIdle after.1.m target states)
    (prior : TicketOwnership source lock start) (next : TicketOwnership target lock released)
    (releasedPC : released.pc = upd start.pc thread .gibW)
    (otherLocks : OtherLockOwners (D := (declOf output.compiled.unit).mitRuhe) lock source target)
    (inLayout : LayIn output.image.Y.withIdle) (cells : LayDis output.image.Y.withIdle)
    (synchronized : LaySync output.image.Y.withIdle) (bound : output.image.Y.sye ≤ 2 ^ 64)
    (order : output.image.Y.lo ≤ output.image.Y.hi) :
    PrivateBuffers (imageProtectedFootprint output target) after.1 ∧
      (SC L0).ans (projectSCState (imageProtectedFootprint output source) before) thread.val
        (.cas (BitVec.ofNat 64 (output.image.Y.lk lock + 8)) expected word) reply
        (projectSCState (imageProtectedFootprint output target) after) := by
  have transferred (other : Nat) (different : other ≠ thread.val) (guard : (declOf output.compiled.unit).Lock)
      (held : guard ∈ offen (source.faeden other).spur) : guard ∈ offen (target.faeden other).spur := by
    by_cases selected : guard = lock
    · subst guard
      apply (prior.thread_frame next other ?_).mp held
      intro inside
      rw [releasedPC, upd_ne _ _ (fun equal => different (congrArg Fin.val equal))]
    · exact (otherLocks guard selected other).mpr held
  obtain ⟨_, pending, projection⟩ := privateBuffers_after_release answered old locks inLayout cells transferred
  have shared (byte : W) (hit : fenster (BitVec.ofNat 64 (output.image.Y.lk lock + 8)) byte) :
      ∀ other, ¬ imageProtectedFootprint output source other byte := by
    intro other owned
    have fits : output.image.Y.withIdle.lk lock + 24 ≤ 2 ^ 64 := (synchronized.1 lock).2.trans bound
    exact imageProtectedFootprint_lock_disjoint inLayout synchronized order owned
      (lockWord_in_bytes fits (by decide) hit)
  refine ⟨pending, ?_⟩
  rw [projection]
  exact projectSCState_cas_shared answered.1 _ shared

/-- A release at the actual serving-word CAS publishes the old
    holder's buffered changes before removing its source authority.
    This is one native process request, one GX scoped release, and one
    update to the common lock registry. -/
theorem image_release_scope [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {O : Orakel (declOf output.compiled.unit)}
    {source : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {machine : Cfg imageTSO (Res T)} {memory : imageTSO.St} {reply : Ans} {resume : Ans → Res T}
    {lock : (declOf output.compiled.unit).mitRuhe.Lock} {N : Nat} {thread : Fin N} {states : _ → Zustand N}
    {ticket expected : Nat}
    (locks : ImageTicketStates output.image.Y.withIdle machine.ms.1.m source.m states)
    (buffers : PrivateBuffers (imageProtectedFootprint output source.m) machine.ms.1)
    (inLayout : LayIn output.image.Y.withIdle) (cells : LayDis output.image.Y.withIdle)
    (synchronized : LaySync output.image.Y.withIdle) (bound : output.image.Y.sye ≤ 2 ^ 64)
    (order : output.image.Y.lo ≤ output.image.Y.hi) (limit : N ≤ 2147483647)
    (saved : (states lock).pc thread = .gibC ticket expected)
    (writable : Mem.all machine.ms.1.m.wr (BitVec.ofNat 64 (output.image.Y.lk lock + 8)) 8 = true)
    (waiting : machine.ths[thread.val]? = some (some (.ask
      (.cas (BitVec.ofNat 64 (output.image.Y.lk lock + 8))
        (BitVec.ofNat 64 expected) (BitVec.ofNat 64 (expected + 1))) resume)))
    (answered : imageTSO.ans machine.ms thread.val
      (.cas (BitVec.ofNat 64 (output.image.Y.lk lock + 8))
        (BitVec.ofNat 64 expected) (BitVec.ofNat 64 (expected + 1))) reply memory)
    (live : source.lebt thread.val = true) (ready : source.wartet thread.val = [])
    {l : Bool} {Γ : Ctx} {Λ : List (Res (declOf output.compiled.unit).mitRuhe)}
    (k : GRest _ (vertragVon _ (source.m.faeden thread.val).kopf.f) l Γ Λ)
    (env : Env _ Γ)
    (head : (source.m.faeden thread.val).kopf.rest = ⟨l, Γ, Res.held lock :: Λ, env, .frei lock k⟩)
    (unique : (offen (source.m.faeden thread.val).spur).Nodup) :
    let after := Cfg.mk memory (machine.ths.set thread.val (some (resume reply)))
    let prior := states lock
    let released : Zustand N :=
      ⟨⟨prior.w.next, prior.w.serv + 1, prior.w.wait⟩, upd prior.pc thread .gibW, prior.q.tail⟩
    ProcessStep imageTSO actI machine [] after ∧ reply = some (BitVec.ofNat 64 expected, 0) ∧
      machine.ms.1.buf thread.val = [] ∧
      ∃ next, FadenSchrittX E.P.mitRuhe O.mitRuhe output.image.passes
          (GeteiltV (D := declOf output.compiled.unit) E.P E.ws) source next ∧
        next.m.speicher = source.m.speicher ∧
        imageSourceForeignEvents next.m.lauf = imageSourceForeignEvents source.m.lauf ∧
        ImageTicketStates output.image.Y.withIdle memory.1.m next.m
          (fun other => if other = lock then released else states other) ∧
        PrivateBuffers (imageProtectedFootprint output next.m) memory.1 ∧
        (SC L0).ans (projectSCState (imageProtectedFootprint output source.m) machine.ms) thread.val
          (.cas (BitVec.ofNat 64 (output.image.Y.lk lock + 8))
            (BitVec.ofNat 64 expected) (BitVec.ofNat 64 (expected + 1))) reply
          (projectSCState (imageProtectedFootprint output next.m) memory) := by
  intro after prior released
  have fits := (synchronized.1 lock).2.trans bound
  obtain ⟨step, result, written, lockWords, valid, next, advanced, store, trace, owners, others⟩ :=
    image_ticket_release_GX (P := E.P.mitRuhe) (O := O.mitRuhe) (passes := output.image.passes)
      (Tg := GeteiltV (D := declOf output.compiled.unit) E.P E.ws)
      output.image.Y.withIdle (locks.owners lock) limit (locks.protocol lock) saved fits
      (locks.words lock) writable waiting answered live ready k env head unique
  have stable : GleichAuf (fun byte => ¬ LockBytes output.image.Y.withIdle lock byte)
      memory.1.m machine.ms.1.m := by
    rw [written]
    intro byte outside
    exact (write_nurIn _ _ _).gleichAt
      (fun hit => outside (lockWord_in_bytes fits (by decide) hit))
  have registered := locks.update synchronized bound stable others lockWords valid owners
  obtain ⟨privatelyOwned, projected⟩ := image_release_projected answered buffers registered
    (locks.owners lock) owners rfl others inLayout cells synchronized bound order
  have quiet : imageSourceForeignEvents next.m.lauf = imageSourceForeignEvents source.m.lauf := by
    rw [trace]
    simp only [imageSourceForeignEvents, List.filterMap_append, rufEigenG, List.reverse_singleton,
      List.map_cons, List.map_nil, List.filterMap_cons_none, List.filterMap_nil, List.append_nil]
  exact ⟨step, result, answered.1.1, next, advanced, store, quiet, registered, privatelyOwned, projected⟩

/-- A successful serving read acquires the guard in GX and grants its
    carriers to the same physical thread. No previously buffered store
    loses its owner, so the read still projects to the same SC answer. -/
theorem image_admit_scope [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {O : Orakel (declOf output.compiled.unit)}
    {source : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {machine : Cfg imageTSO (Res T)} {memory : imageTSO.St} {reply : Ans} {resume : Ans → Res T}
    {lock : (declOf output.compiled.unit).mitRuhe.Lock} {N : Nat} {thread : Fin N} {states : _ → Zustand N}
    {ticket : Nat}
    (locks : ImageTicketStates output.image.Y.withIdle machine.ms.1.m source.m states)
    (buffers : PrivateBuffers (imageProtectedFootprint output source.m) machine.ms.1)
    (inLayout : LayIn output.image.Y.withIdle) (cells : LayDis output.image.Y.withIdle)
    (synchronized : LaySync output.image.Y.withIdle) (bound : output.image.Y.sye ≤ 2 ^ 64)
    (order : output.image.Y.lo ≤ output.image.Y.hi) (limit : N ≤ 2147483647)
    (spins : output.image.Y.lockWait = .spin → SpinState (states lock))
    (saved : (states lock).pc thread = .ladeS ticket)
    (waiting : machine.ths[thread.val]? = some (some (.ask
      (.rd 8 (BitVec.ofNat 64 (output.image.Y.lk lock + 8))) resume)))
    (answered : imageTSO.ans machine.ms thread.val
      (.rd 8 (BitVec.ofNat 64 (output.image.Y.lk lock + 8))) reply memory)
    (matched : ∃ extra, reply = some (BitVec.ofNat 64 ticket, extra))
    (live : source.lebt thread.val = true) (ready : source.wartet thread.val = [])
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res (declOf output.compiled.unit).mitRuhe)}
    (ordered : ∀ M, Res.held M ∈ Λ → (declOf output.compiled.unit).mitRuhe.rang M <
      (declOf output.compiled.unit).mitRuhe.rang lock)
    (body : Block _ (vertragVon _ (source.m.faeden thread.val).kopf.f) l Γ
      (Res.held lock :: Λ) (Res.held lock :: Λ))
    (rest : Block _ (vertragVon _ (source.m.faeden thread.val).kopf.f) l Γ Λ Λ')
    (k : GRest _ (vertragVon _ (source.m.faeden thread.val).kopf.f) l Γ Λ')
    (env : Env _ Γ)
    (head : (source.m.faeden thread.val).kopf.rest =
      ⟨l, Γ, Λ, env, .dann (.cons (.locks lock ordered body) rest) k⟩)
    (ranks : ∀ earlier ∈ offen (source.m.faeden thread.val).spur,
      (declOf output.compiled.unit).mitRuhe.rang earlier < (declOf output.compiled.unit).mitRuhe.rang lock) :
    let after := Cfg.mk memory (machine.ths.set thread.val (some (resume reply)))
    let admitted := (states lock).mit thread (.drin ticket)
    ProcessStep imageTSO actI machine [] after ∧ memory = machine.ms ∧
      ∃ next, FadenSchrittX E.P.mitRuhe O.mitRuhe output.image.passes
          (GeteiltV (D := declOf output.compiled.unit) E.P E.ws) source next ∧
        next.m.speicher = source.m.speicher ∧
        imageSourceForeignEvents next.m.lauf = imageSourceForeignEvents source.m.lauf ∧
        ImageTicketStates output.image.Y.withIdle memory.1.m next.m
          (fun other => if other = lock then admitted else states other) ∧
        PrivateBuffers (imageProtectedFootprint output next.m) memory.1 ∧
        (SC L0).ans (projectSCState (imageProtectedFootprint output source.m) machine.ms) thread.val
          (.rd 8 (BitVec.ofNat 64 (output.image.Y.lk lock + 8))) reply
          (projectSCState (imageProtectedFootprint output next.m) memory) := by
  intro after admitted
  have fits := (synchronized.1 lock).2.trans bound
  have shared (byte : W) (hit : fenster (BitVec.ofNat 64 (output.image.Y.lk lock + 8)) byte) :
      ∀ owner, ¬ imageProtectedFootprint output source.m owner byte := by
    intro owner owned
    exact imageProtectedFootprint_lock_disjoint inLayout synchronized order owned
      (lockWord_in_bytes fits (by decide) hit)
  obtain ⟨step, unchanged, _, words, valid, next, advanced, store, trace, owners, others⟩ :=
    image_ticket_admit_GX (P := E.P.mitRuhe) (O := O.mitRuhe) (passes := output.image.passes)
      (Tg := GeteiltV (D := declOf output.compiled.unit) E.P E.ws)
      output.image.Y.withIdle (locks.owners lock) output.image.Y.lockWait spins limit (locks.protocol lock)
      saved (locks.words lock) _ buffers shared waiting answered matched live ready ordered body rest k env head ranks
  have untouched : GleichAuf (fun byte => ¬ LockBytes output.image.Y.withIdle lock byte)
      memory.1.m machine.ms.1.m := by
    rw [unchanged]
    exact fun byte _ => GleichAt.refl _ byte
  have registered := locks.update synchronized bound untouched others words valid owners
  have retained (owner : Nat) (guard : (declOf output.compiled.unit).mitRuhe.Lock)
      (held : guard ∈ offen (source.m.faeden owner).spur) :
      guard ∈ offen (next.m.faeden owner).spur := by
    by_cases selected : guard = lock
    · subst guard
      by_cases issuer : owner = thread.val
      · subst owner
        have occupied := ((locks.owners lock).inside thread).mpr held
        rw [saved] at occupied
        cases occupied
      · apply ((locks.owners lock).thread_frame owners owner ?_).mp held
        intro inside
        exact upd_ne _ _ (fun same => issuer (congrArg Fin.val same))
    · exact (others guard selected owner).mpr held
  have oldAtAnswer : PrivateBuffers (imageProtectedFootprint output source.m) memory.1 := unchanged.symm ▸ buffers
  have nextBuffers : PrivateBuffers (imageProtectedFootprint output next.m) memory.1 := by
    intro owner pending member byte hit
    have previous := (oldAtAnswer owner pending member byte hit).1
    have current : imageProtectedFootprint output next.m owner byte := by
      rcases previous with stack | ⟨cell, present, low, high, guarded, held⟩
      · exact .inl stack
      · exact .inr ⟨cell, present, low, high, guarded, fun guard protects => retained owner guard (held guard protects)⟩
    exact ⟨current, fun _ assigned => imageProtectedFootprint_exclusive registered inLayout cells assigned current⟩
  have quiet : imageSourceForeignEvents next.m.lauf = imageSourceForeignEvents source.m.lauf := by
    rw [trace]
    simp only [imageSourceForeignEvents, List.filterMap_append, rufEigenG, List.reverse_singleton,
      List.map_cons, List.map_nil, List.filterMap_cons_none, List.filterMap_nil, List.append_nil]
  refine ⟨step, unchanged, next, advanced, store, quiet, registered, nextBuffers, ?_⟩
  rw [projectSCState_reassign oldAtAnswer nextBuffers]
  exact projectSCState_read_shared answered.1 _ shared (fun owner pending member byte hit =>
    (buffers owner pending member byte hit).1)

end Gabbro.Stage0.Senke.Faeden
