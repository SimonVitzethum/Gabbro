/-
  File:      stage0/Stage0/Senke/Sperre/Faeden/Bild.lean
  Subject:   THE EMITTED LOCK REFINES THE ABSTRACT TICKET LOCK. `bild` maps a state of the emitted lock run by many
             threads (Faeden/Maschine.lean) to the abstract ticket lock (Faeden/Abstrakt.lean): the head of the ghost
             ticket queue is the holder when it holds, the other threads with a ticket wait, in ticket order. Every
             step of a thread is at most one abstract step of the same thread (`Schritt.bild`): the successful `cas`
             on `next` draws (`Zieht`), the serving test that finds the own ticket enters (`Tritt`), the successful
             `cas` on `serving` gives (`Gibt`); every other step -- the waiter count, FUTEX_WAIT (blocking,
             returning at once, spurious return), FUTEX_WAKE of all waiters, the failed `cas` loops -- stutters.
             `bild_glied`: the waiting threads of the abstract lock are exactly the threads with a ticket that do
             not hold it, so a thread blocked in FUTEX_WAIT is a thread waiting at the lock (`bild_schlaeft`).
-/
module
public import Stage0.Senke.Sperre.Faeden.Rahmen
@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

variable {N : Nat}

/-- The abstract lock of places `pc` and the ghost ticket queue. -/
def bildAus (pc : Fin N → Ort) : List (Fin N) → Abs (Fin N)
  | [] => ⟨none, []⟩
  | u :: r => if (pc u).haelt = true then ⟨some u, r⟩ else ⟨none, u :: r⟩

/-- **The abstraction** of a state of the emitted lock. -/
def bild (σ : Zustand N) : Abs (Fin N) := bildAus σ.pc σ.q

theorem bildAus_ja {pc : Fin N → Ort} {u : Fin N} {r : List (Fin N)} (hu : (pc u).haelt = true) :
    bildAus pc (u :: r) = ⟨some u, r⟩ := by
  simp [bildAus, hu]

theorem bildAus_nein {pc : Fin N → Ort} {u : Fin N} {r : List (Fin N)} (hu : (pc u).haelt = false) :
    bildAus pc (u :: r) = ⟨none, u :: r⟩ := by
  simp [bildAus, hu]

theorem bildAus_frei {pc : Fin N → Ort} : (q : List (Fin N)) → (∀ u ∈ q, (pc u).haelt = false) →
    bildAus pc q = ⟨none, q⟩
  | [], _ => rfl
  | u :: _, h => bildAus_nein (h u List.mem_cons_self)

theorem bildAus_gleich {pc pc' : Fin N → Ort} (h : ∀ u, (pc' u).haelt = (pc u).haelt) :
    (q : List (Fin N)) → bildAus pc' q = bildAus pc q
  | [] => rfl
  | u :: r => by simp only [bildAus, h u]

/-- A step that keeps the queue and every thread's holding keeps the abstract lock. -/
theorem bild_upd {σ : Zustand N} {t : Fin N} {o : Ort} {w' : Wort} (hh : o.haelt = (σ.pc t).haelt) :
    bild ⟨w', upd σ.pc t o, σ.q⟩ = bild σ :=
  bildAus_gleich (upd_eq_of Ort.haelt σ.pc t o hh) σ.q

theorem bild_weckt {σ : Zustand N} {t : Fin N} (h : σ.pc t = .weck) :
    bild ⟨σ.w, upd (wecke σ.pc) t .frei, σ.q⟩ = bild σ := by
  refine bildAus_gleich (fun u => ?_) σ.q
  by_cases hu : u = t
  · simp [hu, upd_self, h, Ort.haelt]
  · simp only [upd_ne _ _ hu, wecke_apply, geweckt_haelt]

/-! ## 1. The three abstract steps -/

theorem bild_zieht {σ : Zustand N} (hI : Inv N σ) {t : Fin N} {l : Nat} (h : σ.pc t = .casN l) :
    Zieht t (bild σ) (bild ⟨⟨σ.w.next + 1, σ.w.serv, σ.w.wait⟩, upd σ.pc t (.ladeS σ.w.next), σ.q ++ [t]⟩) := by
  have htq : t ∉ σ.q := fun hm => by
    have hx := (hI.mem t).1 hm
    simp [h, Ort.ticket] at hx
  show Zieht t (bildAus σ.pc σ.q) (bildAus (upd σ.pc t (.ladeS σ.w.next)) (σ.q ++ [t]))
  have hnew : (upd σ.pc t (.ladeS σ.w.next) t).haelt = false := by simp [upd_self, Ort.haelt]
  cases hq : σ.q with
  | nil =>
    show Zieht t ⟨none, []⟩ (bildAus (upd σ.pc t (.ladeS σ.w.next)) [t])
    rw [bildAus_nein hnew]
    exact ⟨List.not_mem_nil, by simp, rfl⟩
  | cons u r =>
    have hut : u ≠ t := fun e => htq (by rw [hq, e]; exact List.mem_cons_self)
    have htr : t ∉ r := fun hm => htq (by rw [hq]; exact List.mem_cons_of_mem u hm)
    have hh : (upd σ.pc t (.ladeS σ.w.next) u).haelt = (σ.pc u).haelt := by rw [upd_ne _ _ hut]
    show Zieht t (bildAus σ.pc (u :: r)) (bildAus (upd σ.pc t (.ladeS σ.w.next)) (u :: (r ++ [t])))
    cases hu : (σ.pc u).haelt with
    | true =>
      rw [bildAus_ja hu, bildAus_ja (hh.trans hu)]
      exact ⟨htr, fun e => hut (Option.some.inj e), rfl⟩
    | false =>
      rw [bildAus_nein hu, bildAus_nein (hh.trans hu)]
      exact ⟨fun hm => htq (by rw [hq]; exact hm), by simp, rfl⟩

theorem bild_tritt (hN : N ≤ 2147483647) {σ : Zustand N} (hI : Inv N σ) {t : Fin N} {k : Nat}
    (h : σ.pc t = .ladeS k) (e : σ.w.serv % 18446744073709551616 = k % 18446744073709551616) :
    Tritt t (bild σ) (bild (σ.mit t (.drin k))) := by
  obtain ⟨r, hr⟩ := List.head?_eq_some_iff.1 (hI.tritt hN h e)
  have h1 : (σ.pc t).haelt = false := by simp [h, Ort.haelt]
  have h2 : (upd σ.pc t (.drin k) t).haelt = true := by simp [upd_self, Ort.haelt]
  show Tritt t (bildAus σ.pc σ.q) (bildAus (upd σ.pc t (.drin k)) σ.q)
  rw [hr, bildAus_nein h1, bildAus_ja h2]
  exact ⟨rfl, rfl, rfl⟩

theorem bild_gibt {σ : Zustand N} (hI : Inv N σ) {t : Fin N} {k ls : Nat} (h : σ.pc t = .gibC k ls) :
    Gibt t (bild σ) (bild ⟨⟨σ.w.next, σ.w.serv + 1, σ.w.wait⟩, upd σ.pc t .gibW, σ.q.tail⟩) := by
  have h1 : (σ.pc t).haelt = true := by simp [h, Ort.haelt]
  have hhead := hI.haelt t h1
  obtain ⟨r, hr⟩ := List.head?_eq_some_iff.1 hhead
  have hn := hI.nodup
  rw [hr] at hn
  have htr : t ∉ r := (List.nodup_cons.1 hn).1
  have hfrei : ∀ u ∈ r, (upd σ.pc t .gibW u).haelt = false := by
    intro u hu
    have hut : u ≠ t := fun e => htr (by rw [← e]; exact hu)
    rw [upd_ne _ _ hut]
    cases hx : (σ.pc u).haelt with
    | false => rfl
    | true =>
      have hx' := hI.haelt u hx
      rw [hhead] at hx'
      exact absurd (Option.some.inj hx').symm hut
  show Gibt t (bildAus σ.pc σ.q) (bildAus (upd σ.pc t .gibW) σ.q.tail)
  rw [hr, List.tail_cons, bildAus_ja h1, bildAus_frei r hfrei]
  exact ⟨rfl, rfl⟩

/-! ## 2. Every step is at most one abstract step of the same thread -/

/-- **The refinement step**: one step of thread `t` of the emitted lock is a stutter or one step of `t` of the
    abstract ticket lock. -/
theorem Schritt.abbild (hN : N ≤ 2147483647) {σ σ' : Zustand N} {t : Fin N} (hI : Inv N σ)
    (hs : Schritt σ t σ') : Opt (AbsSchritt t) (bild σ) (bild σ') := by
  cases hs with
  | zieht h e => exact Or.inr (.zieht (bild_zieht hI h))
  | tritt h e => exact Or.inr (.tritt (bild_tritt hN hI h e))
  | gibt h e => exact Or.inr (.gibt (bild_gibt hI h))
  | gibtNicht h e => exact absurd (show _ = _ from hI.ort_an h).symm e
  | weckt h => exact Or.inl (bild_weckt h).symm
  | ruht h => exact Or.inl rfl
  | arbeitet h => exact Or.inl rfl
  | _ => exact Or.inl (bild_upd (by simp_all [Ort.haelt])).symm

/-- One abstract step is one `Weg` (the shape of what one step of machine G does to one lock). -/
theorem Opt.weg {τ : Type} {u : τ} {a b : Abs τ} (h : Opt (AbsSchritt u) a b) : Weg u a b := by
  rcases h with h | h
  · exact ⟨a, a, Or.inl rfl, Or.inl rfl, Or.inl h⟩
  · cases h with
    | zieht h => exact ⟨a, b, Or.inl rfl, Or.inr h, Or.inl rfl⟩
    | tritt h => exact ⟨a, a, Or.inl rfl, Or.inl rfl, Or.inr h⟩
    | gibt h => exact ⟨b, b, Or.inr h, Or.inl rfl, Or.inl rfl⟩

/-! ## 3. What the abstraction shows -/

/-- The abstract lock is well formed. -/
theorem bild_ok {σ : Zustand N} (hI : Inv N σ) : AbsOK (bild σ) := by
  have hn := hI.nodup
  show AbsOK (bildAus σ.pc σ.q)
  cases hq : σ.q with
  | nil => exact ⟨List.nodup_nil, fun x hx => by simp [bildAus] at hx⟩
  | cons u r =>
    rw [hq] at hn
    cases hu : (σ.pc u).haelt with
    | true =>
      rw [bildAus_ja hu]
      refine ⟨(List.nodup_cons.1 hn).2, fun x hx => ?_⟩
      have hxu : u = x := Option.some.inj hx
      rw [← hxu]
      exact (List.nodup_cons.1 hn).1
    | false =>
      rw [bildAus_nein hu]
      exact ⟨hn, fun x hx => by simp at hx⟩

/-- **The holder** of the abstract lock is the thread that holds the emitted lock. -/
theorem bild_halter {σ : Zustand N} (hI : Inv N σ) (u : Fin N) :
    (bild σ).holder = some u ↔ (σ.pc u).haelt = true := by
  show (bildAus σ.pc σ.q).holder = some u ↔ (σ.pc u).haelt = true
  constructor
  · intro hb
    cases hq : σ.q with
    | nil =>
      rw [hq] at hb
      simp [bildAus] at hb
    | cons v r =>
      rw [hq] at hb
      cases hv : (σ.pc v).haelt with
      | true =>
        rw [bildAus_ja hv] at hb
        rw [← Option.some.inj hb]
        exact hv
      | false =>
        rw [bildAus_nein hv] at hb
        simp at hb
  · intro hu
    have hh := hI.haelt u hu
    obtain ⟨r, hr⟩ := List.head?_eq_some_iff.1 hh
    simp only [hr, bildAus_ja (r := r) hu]

/-- **The waiting threads** of the abstract lock are the threads with a ticket that do not hold the lock. -/
theorem bild_glied {σ : Zustand N} (hI : Inv N σ) (u : Fin N) :
    u ∈ (bild σ).queue ↔ (σ.pc u).ticket.isSome = true ∧ (σ.pc u).haelt = false := by
  show u ∈ (bildAus σ.pc σ.q).queue ↔ _
  have hm := hI.mem u
  have hn := hI.nodup
  cases hq : σ.q with
  | nil =>
    rw [hq] at hm
    exact ⟨fun hx => absurd hx List.not_mem_nil, fun hx => absurd (hm.2 hx.1) List.not_mem_nil⟩
  | cons v r =>
    rw [hq] at hm hn
    cases hv : (σ.pc v).haelt with
    | true =>
      rw [bildAus_ja hv]
      constructor
      · intro hu
        refine ⟨hm.1 (List.mem_cons_of_mem v hu), ?_⟩
        cases hx : (σ.pc u).haelt with
        | false => rfl
        | true =>
          have hh := hI.haelt u hx
          rw [hq] at hh
          have hvu : v = u := Option.some.inj hh
          rw [← hvu] at hu
          exact absurd hu (List.nodup_cons.1 hn).1
      · intro hx
        rcases List.mem_cons.1 (hm.2 hx.1) with e | e
        · rw [e, hv] at hx
          cases hx.2
        · exact e
    | false =>
      rw [bildAus_nein hv]
      constructor
      · intro hu
        refine ⟨hm.1 hu, ?_⟩
        cases hx : (σ.pc u).haelt with
        | false => rfl
        | true =>
          have hh := hI.haelt u hx
          rw [hq] at hh
          have hvu : v = u := Option.some.inj hh
          rw [← hvu, hv] at hx
          cases hx
      · intro hx
        exact hm.2 hx.1

/-- **A thread blocked in FUTEX_WAIT waits at the lock.** -/
theorem bild_schlaeft {σ : Zustand N} (hI : Inv N σ) {u : Fin N} (hs : (σ.pc u).schlaeft = true) :
    u ∈ (bild σ).queue := by
  refine (bild_glied hI u).2 ?_
  cases hp : σ.pc u with
  | blockiert k s0 => exact ⟨rfl, rfl⟩
  | _ => rw [hp] at hs; cases hs

end Gabbro.Stage0.Senke.Faeden
