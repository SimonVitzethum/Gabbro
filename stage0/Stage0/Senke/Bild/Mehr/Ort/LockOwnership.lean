module

public import Stage0.Senke.Sperre.Bindung.ImageFutex

@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

open Gabbro.Grammatik Gabbro.Stage0.Senke.BildMehr Runner Runner.IR Runner.Mach Runner.Beweis Runner.Mem

/-- A ticket lock and the source traces name the same owner. Source
    slots outside the fixed image's reservations hold no lock. -/
structure TicketOwnership {D : Deklaration} {N : Nat}
    (source : RufMaschineG D) (lock : D.Lock) (state : Zustand N) : Prop where
  inside : ∀ thread : Fin N, (state.pc thread).haelt = true ↔
    lock ∈ offen (source.faeden thread.val).spur
  outside : ∀ thread, N ≤ thread → lock ∉ offen (source.faeden thread).spur

/-- Physical admission establishes the scheduler side of the source
    lock rule even when other threads are queued. -/
theorem TicketOwnership.free_at_admission {D : Deklaration} {N : Nat}
    {source : RufMaschineG D} {lock : D.Lock} {before : Zustand N} {thread : Fin N} {ticket : Nat}
    (owners : TicketOwnership source lock before)
    (limit : N ≤ 2147483647) (invariant : Inv N before)
    (saved : before.pc thread = .ladeS ticket)
    (served : before.w.serv % 2 ^ 64 = ticket % 2 ^ 64) :
    lock ∉ offen (source.faeden thread.val).spur ∧ RufFreiG source thread.val lock := by
  let next := before.mit thread (.drin ticket)
  have after := invariant.schritt limit (show Schritt before thread next from .tritt saved served)
  have holds : (next.pc thread).haelt = true := by
    change (upd before.pc thread (.drin ticket) thread).haelt = true
    rw [upd_self]
    rfl
  constructor
  · intro held
    have impossible := (owners.inside thread).mpr held
    rw [saved] at impossible
    cases impossible
  · intro other different held
    by_cases valid : other < N
    · let otherThread : Fin N := ⟨other, valid⟩
      have distinct : otherThread ≠ thread := fun same => different (congrArg Fin.val same)
      have still : (next.pc otherThread).haelt = true := by
        change (upd before.pc thread (.drin ticket) otherThread).haelt = true
        rw [upd_ne _ _ distinct]
        exact (owners.inside otherThread).mpr held
      exact distinct (after.ausschluss still holds)
    · exact owners.outside other (Nat.le_of_not_gt valid) held

/-- A change in one ticket slot preserves owner agreement when the
    corresponding source transition updates that same thread. -/
theorem TicketOwnership.update {D : Deklaration} {N : Nat}
    {source target : RufMaschineG D} {lock : D.Lock} {before after : Zustand N}
    (owners : TicketOwnership source lock before) (thread : Fin N) (position : Ort)
    (physical : after.pc = upd before.pc thread position)
    (others : ∀ other, other ≠ thread.val → target.faeden other = source.faeden other)
    (owner : position.haelt = true ↔ lock ∈ offen (target.faeden thread.val).spur) :
    TicketOwnership target lock after where
  inside other := by
    rw [physical]
    by_cases same : other = thread
    · subst other
      rw [upd_self]
      exact owner
    · rw [upd_ne _ _ same, others other.val (fun equal => same (Fin.ext equal))]
      exact owners.inside other
  outside other bound := by
    rw [others other (fun equal => (Nat.not_lt_of_ge bound) (equal.symm ▸ thread.isLt))]
    exact owners.outside other bound

/-- An admitted ticket advances the actual GX head through the scoped
    lock entry. The physical and source owner then agree again. -/
theorem TicketOwnership.enter {D : Deklaration} {N : Nat} {P : Programm D}
    {O : Orakel D} {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    {source : FadenMaschine D} {lock : D.Lock} {before : Zustand N}
    {thread : Fin N} {ticket : Nat}
    (owners : TicketOwnership source.m lock before)
    (limit : N ≤ 2147483647) (invariant : Inv N before)
    (saved : before.pc thread = .ladeS ticket)
    (served : before.w.serv % 2 ^ 64 = ticket % 2 ^ 64)
    (live : source.lebt thread.val = true) (ready : source.wartet thread.val = [])
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (ordered : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang lock)
    (body : Block D (vertragVon D (source.m.faeden thread.val).kopf.f) l Γ
      (Res.held lock :: Λ) (Res.held lock :: Λ))
    (rest : Block D (vertragVon D (source.m.faeden thread.val).kopf.f) l Γ Λ Λ')
    (k : GRest D (vertragVon D (source.m.faeden thread.val).kopf.f) l Γ Λ')
    (env : Env D Γ)
    (head : (source.m.faeden thread.val).kopf.rest =
      ⟨l, Γ, Λ, env, .dann (.cons (.locks lock ordered body) rest) k⟩)
    (ranks : ∀ earlier ∈ offen (source.m.faeden thread.val).spur, D.rang earlier < D.rang lock) :
    ∃ next, FadenSchrittX P O passes Tg source next ∧ next.m.speicher = source.m.speicher ∧
      TicketOwnership next.m lock (before.mit thread (.drin ticket)) := by
  obtain ⟨unheld, free⟩ := owners.free_at_admission limit invariant saved served
  have step := RufSchrittG2.dannLocks (P := P) (O := O) (passes := passes)
    source.m thread.val l Γ Λ Λ' lock ordered body rest k env head unheld ranks free
  refine ⟨_, .lauf source thread.val _ live ready (gx_aus_g (.g2 step)), rfl, ?_⟩
  apply owners.update thread (.drin ticket) rfl
  · intro other different
    exact rufUpdateG_noteq _ _ _ different _
  · change (Ort.drin ticket).haelt = true ↔
      lock ∈ offen (rufUpdateG source.m.faeden thread.val _ thread.val).spur
    rw [rufUpdateG_self]
    exact ⟨fun _ => List.mem_cons_self, fun _ => rfl⟩

/-- The corresponding GX scope exit forgets the owner at the serving
    word's publication point. The shared source store is preserved. -/
theorem TicketOwnership.leave {D : Deklaration} {N : Nat} {P : Programm D}
    {O : Orakel D} {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    {source : FadenMaschine D} {lock : D.Lock} {before : Zustand N}
    {thread : Fin N} {ticket sampled : Nat}
    (owners : TicketOwnership source.m lock before) (saved : before.pc thread = .gibC ticket sampled)
    (live : source.lebt thread.val = true) (ready : source.wartet thread.val = [])
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (k : GRest D (vertragVon D (source.m.faeden thread.val).kopf.f) l Γ Λ)
    (env : Env D Γ)
    (head : (source.m.faeden thread.val).kopf.rest = ⟨l, Γ, Res.held lock :: Λ, env, .frei lock k⟩)
    (unique : (offen (source.m.faeden thread.val).spur).Nodup) :
    let released : Zustand N := ⟨⟨before.w.next, before.w.serv + 1, before.w.wait⟩,
      upd before.pc thread .gibW, before.q.tail⟩
    ∃ next, FadenSchrittX P O passes Tg source next ∧ next.m.speicher = source.m.speicher ∧
      lock ∈ offen (source.m.faeden thread.val).spur ∧ TicketOwnership next.m lock released := by
  intro released
  have step := RufSchrittG2.freiGib (P := P) (O := O) (passes := passes)
    source.m thread.val l Γ Λ lock k env head
  refine ⟨_, .lauf source thread.val _ live ready (gx_aus_g (.g2 step)), rfl, ?_, ?_⟩
  · apply (owners.inside thread).mp
    rw [saved]
    rfl
  · apply owners.update thread .gibW rfl
    · intro other different
      exact rufUpdateG_noteq _ _ _ different _
    · change Ort.gibW.haelt = true ↔
        lock ∈ offen (rufUpdateG source.m.faeden thread.val _ thread.val).spur
      rw [rufUpdateG_self]
      exact Iff.intro (fun impossible => Bool.noConfusion impossible)
        (fun member => (List.Nodup.not_mem_erase unique member).elim)

/-- The actual image CAS and the corresponding GX scope exit agree
    at a single publication point. The successor retains both
    the physical ticket invariant and the source owner relation. -/
theorem image_ticket_release_GX [Kern] {D : Deklaration} {N : Nat}
    {P : Programm D} {O : Orakel D} {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    {machine : Cfg imageTSO (Res T)} {memory : imageTSO.St} {reply : Ans} {resume : Ans → Res T}
    {source : FadenMaschine D} {lock : D.Lock} {before : Zustand N}
    {thread : Fin N} {ticket expected : Nat} (layout : Lay D)
    (owners : TicketOwnership source.m lock before)
    (limit : N ≤ 2147483647) (invariant : Inv N before)
    (saved : before.pc thread = .gibC ticket expected)
    (fits : layout.lk lock + 24 ≤ 2 ^ 64)
    (represented : TicketWordsAt machine.ms.1.m (layout.lk lock) before)
    (writable : all machine.ms.1.m.wr (BitVec.ofNat 64 (layout.lk lock + 8)) 8 = true)
    (waiting : machine.ths[thread.val]? = some (some (.ask
      (.cas (BitVec.ofNat 64 (layout.lk lock + 8)) (BitVec.ofNat 64 expected) (BitVec.ofNat 64 (expected + 1))) resume)))
    (answered : imageTSO.ans machine.ms thread.val
      (.cas (BitVec.ofNat 64 (layout.lk lock + 8)) (BitVec.ofNat 64 expected) (BitVec.ofNat 64 (expected + 1))) reply memory)
    (live : source.lebt thread.val = true) (ready : source.wartet thread.val = [])
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (k : GRest D (vertragVon D (source.m.faeden thread.val).kopf.f) l Γ Λ)
    (env : Env D Γ)
    (head : (source.m.faeden thread.val).kopf.rest = ⟨l, Γ, Res.held lock :: Λ, env, .frei lock k⟩)
    (unique : (offen (source.m.faeden thread.val).spur).Nodup) :
    let after : Cfg imageTSO (Res T) := ⟨memory, machine.ths.set thread.val (some (resume reply))⟩
    let released : Zustand N := ⟨⟨before.w.next, before.w.serv + 1, before.w.wait⟩,
      upd before.pc thread .gibW, before.q.tail⟩
    ProcessStep imageTSO actI machine [] after ∧ reply = some (BitVec.ofNat 64 expected, 0) ∧
      TicketWordsAt memory.1.m (layout.lk lock) released ∧ Inv N released ∧
      ∃ target, FadenSchrittX P O passes Tg source target ∧ target.m.speicher = source.m.speicher ∧
        TicketOwnership target.m lock released := by
  obtain ⟨process, returned, _, _, words, invariant', _, _⟩ :=
    image_ticket_release limit invariant saved fits represented writable waiting answered
  obtain ⟨target, advances, store, _, owners'⟩ :=
    owners.leave (P := P) (O := O) (passes := passes) (Tg := Tg) saved live ready k env head unique
  exact ⟨process, returned, words, invariant', target, advances, store, owners'⟩

/-- When the actual serving read reports the caller's ticket, the same
    transition enters the corresponding source lock scope. -/
theorem image_ticket_admit_GX [Kern] {D : Deklaration} {N : Nat}
    {P : Programm D} {O : Orakel D} {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    {machine : Cfg imageTSO (Res T)} {memory : imageTSO.St} {reply : Ans} {resume : Ans → Res T}
    {source : FadenMaschine D} {lock : D.Lock} {before : Zustand N}
    {thread : Fin N} {ticket : Nat} (layout : Lay D)
    (owners : TicketOwnership source.m lock before) (strategy : LockWait)
    (spins : strategy = .spin → SpinState before)
    (limit : N ≤ 2147483647) (invariant : Inv N before)
    (saved : before.pc thread = .ladeS ticket)
    (represented : TicketWordsAt machine.ms.1.m (layout.lk lock) before)
    (footprint : Nat → W → Prop) (buffers : PrivateBuffers footprint machine.ms.1)
    (shared : ∀ byte, fenster (BitVec.ofNat 64 (layout.lk lock + 8)) byte →
      ∀ owner, ¬ footprint owner byte)
    (waiting : machine.ths[thread.val]? = some (some (.ask
      (.rd 8 (BitVec.ofNat 64 (layout.lk lock + 8))) resume)))
    (answered : imageTSO.ans machine.ms thread.val (.rd 8 (BitVec.ofNat 64 (layout.lk lock + 8))) reply memory)
    (matched : ∃ extra, reply = some (BitVec.ofNat 64 ticket, extra))
    (live : source.lebt thread.val = true) (ready : source.wartet thread.val = [])
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (ordered : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang lock)
    (body : Block D (vertragVon D (source.m.faeden thread.val).kopf.f) l Γ
      (Res.held lock :: Λ) (Res.held lock :: Λ))
    (rest : Block D (vertragVon D (source.m.faeden thread.val).kopf.f) l Γ Λ Λ')
    (k : GRest D (vertragVon D (source.m.faeden thread.val).kopf.f) l Γ Λ')
    (env : Env D Γ)
    (head : (source.m.faeden thread.val).kopf.rest =
      ⟨l, Γ, Λ, env, .dann (.cons (.locks lock ordered body) rest) k⟩)
    (ranks : ∀ earlier ∈ offen (source.m.faeden thread.val).spur, D.rang earlier < D.rang lock) :
    let after : Cfg imageTSO (Res T) := ⟨memory, machine.ths.set thread.val (some (resume reply))⟩
    let admitted := before.mit thread (.drin ticket)
    ProcessStep imageTSO actI machine [] after ∧ memory = machine.ms ∧
      BindingStep strategy before thread admitted ∧ TicketWordsAt memory.1.m (layout.lk lock) admitted ∧
      Inv N admitted ∧ ∃ target, FadenSchrittX P O passes Tg source target ∧
        target.m.speicher = source.m.speicher ∧ TicketOwnership target.m lock admitted := by
  obtain ⟨process, memorySame, ⟨extra, observed⟩, next, binds, words, _, successor⟩ :=
    image_ticket_serving_read strategy spins saved represented footprint buffers shared waiting answered
  obtain ⟨expectedExtra, expected⟩ := matched
  have same := congrArg (fun pair : W × W => pair.1.toNat) (Option.some.inj (observed.symm.trans expected))
  have served : before.w.serv % 2 ^ 64 = ticket % 2 ^ 64 := by
    simpa only [BitVec.toNat_ofNat] using same
  rw [successor served] at binds words
  have ticketStep := Schritt.tritt saved served
  exact ⟨process, memorySame, binds, words, invariant.schritt limit ticketStep,
    owners.enter limit invariant saved served live ready ordered body rest k env head ranks⟩

end Gabbro.Stage0.Senke.Faeden
