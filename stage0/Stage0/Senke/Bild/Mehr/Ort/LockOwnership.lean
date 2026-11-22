module

public import Stage0.Senke.Sperre.Bindung.ImageFutex

@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

open Gabbro.Grammatik

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

end Gabbro.Stage0.Senke.Faeden
