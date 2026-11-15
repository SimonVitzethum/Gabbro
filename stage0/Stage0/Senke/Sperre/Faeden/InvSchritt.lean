/-
  File:      stage0/Stage0/Senke/Sperre/Faeden/InvSchritt.lean
  Subject:   The invariant across the steps of the acquire path of the emitted lock: the draw (`cas` on `next`),
             the serving test (enter or wait), the waiter increment and decrement (`cas` on the waiter word) and
             FUTEX_WAIT blocking. The give path and the main theorem are in InvLauf.lean.
-/
module
public import Stage0.Senke.Sperre.Faeden.Inv
@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

variable {N : Nat}

/-- **The draw**: a successful `cas` on `next` appends the thread to the queue with ticket `next`. -/
theorem Inv.zieht {σ : Zustand N} (hI : Inv N σ) {t : Fin N} {l : Nat} (h : σ.pc t = .casN l) :
    Inv N ⟨⟨σ.w.next + 1, σ.w.serv, σ.w.wait⟩, upd σ.pc t (.ladeS σ.w.next), σ.q ++ [t]⟩ := by
  have htq : t ∉ σ.q := fun hm => by
    have hx := (hI.mem t).1 hm
    simp [h, Ort.ticket] at hx
  refine ⟨?_, fun u => ?_, fun i u hi => ?_, ?_, fun u hu => ?_, ?_, fun u => ?_, fun u k s0 hu => ?_⟩
  · show (σ.q ++ [t]).Nodup
    refine List.nodup_append.2 ⟨hI.nodup, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro x hx y hy hxy
    rw [List.mem_singleton] at hy
    rw [hxy, hy] at hx
    exact htq hx
  · show u ∈ σ.q ++ [t] ↔ (upd σ.pc t (.ladeS σ.w.next) u).ticket.isSome = true
    by_cases hut : u = t
    · rw [hut, upd_self]
      simp [Ort.ticket]
    · rw [upd_ne σ.pc _ hut, List.mem_append, List.mem_singleton, ← hI.mem u]
      exact ⟨fun hh => hh.resolve_right hut, Or.inl⟩
  · show (upd σ.pc t (.ladeS σ.w.next) u).ticket = some (σ.w.serv + i)
    have hlt : i < (σ.q ++ [t]).length := (List.getElem?_eq_some_iff.1 hi).1
    have hlen : (σ.q ++ [t]).length = σ.q.length + 1 := by simp
    by_cases hil : i < σ.q.length
    · rw [List.getElem?_append_left hil] at hi
      have hut : u ≠ t := fun hut => htq (by rw [← hut]; exact List.mem_iff_getElem?.2 ⟨i, hi⟩)
      rw [upd_ne σ.pc _ hut]
      exact hI.tk i u hi
    · have hieq : i = σ.q.length := by omega
      rw [List.getElem?_append_right (Nat.not_lt.1 hil), hieq, Nat.sub_self] at hi
      have h0 : [t][0]? = some t := rfl
      have hut : t = u := Option.some.inj (h0.symm.trans hi)
      rw [← hut, upd_self]
      show some σ.w.next = some (σ.w.serv + i)
      rw [hI.next, hieq]
  · show σ.w.next + 1 = σ.w.serv + (σ.q ++ [t]).length
    have h1 := hI.next
    have h2 : (σ.q ++ [t]).length = σ.q.length + 1 := by simp
    omega
  · show (σ.q ++ [t]).head? = some u
    by_cases hut : u = t
    · simp [hut, upd_self, Ort.haelt] at hu
    · simp only [upd_ne σ.pc _ hut] at hu
      obtain ⟨r, hr⟩ := List.head?_eq_some_iff.1 (hI.haelt u hu)
      simp [hr]
  · show σ.w.wait = (σ.q ++ [t]).countP (fun u => (upd σ.pc t (.ladeS σ.w.next) u).gezaehlt)
    have h1 : σ.q.countP (fun u => (upd σ.pc t (.ladeS σ.w.next) u).gezaehlt) =
        σ.q.countP (fun u => (σ.pc u).gezaehlt) :=
      List.countP_congr (fun x hx => by rw [upd_ne σ.pc _ (fun e : x = t => htq (e ▸ hx))])
    have h2 : [t].countP (fun u => (upd σ.pc t (.ladeS σ.w.next) u).gezaehlt) = 0 := by
      simp [List.countP_cons, upd_self, Ort.gezaehlt]
    rw [List.countP_append, h1, h2]
    have h3 := hI.wait
    omega
  · show OrtOK N ⟨σ.w.next + 1, σ.w.serv, σ.w.wait⟩ (upd σ.pc t (.ladeS σ.w.next) u)
    by_cases hut : u = t
    · rw [hut, upd_self]
      exact trivial
    · rw [upd_ne σ.pc _ hut]
      exact OrtOK.wort rfl _ (hI.ort u)
  · exact hI.nolost_upd (o := .ladeS σ.w.next) rfl (fun hw => by simp [h, Ort.weckt] at hw)
      ⟨σ.w.next + 1, σ.w.serv, σ.w.wait⟩ rfl u k s0 hu

/-- **Enter**: the serving word equals the ticket word only for the head of the queue. -/
theorem Inv.tritt (hN : N ≤ 2147483647) {σ : Zustand N} (hI : Inv N σ) {t : Fin N} {k : Nat}
    (h : σ.pc t = .ladeS k) (e : σ.w.serv % 18446744073709551616 = k % 18446744073709551616) :
    σ.q.head? = some t := by
  obtain ⟨i, hi, hki, hil⟩ := hI.platz (by simp [h, Ort.ticket] : (σ.pc t).ticket = some k)
  have hl := hI.laenge
  rw [hki] at e
  have hi0 : i = 0 := by omega
  rw [hi0] at hi
  rw [List.head?_eq_getElem?]
  exact hi

theorem Inv.tritt_inv (hN : N ≤ 2147483647) {σ : Zustand N} (hI : Inv N σ) {t : Fin N} {k : Nat}
    (h : σ.pc t = .ladeS k) (e : σ.w.serv % 18446744073709551616 = k % 18446744073709551616) :
    Inv N (σ.mit t (.drin k)) := by
  have hhead := hI.tritt hN h e
  have hf : (fun u => (upd σ.pc t (.drin k) u).gezaehlt) = (fun u => (σ.pc u).gezaehlt) :=
    funext (upd_eq_of Ort.gezaehlt σ.pc t _ (by simp [h, Ort.gezaehlt]))
  refine hI.updW (o := .drin k) σ.w rfl rfl (by simp [h, Ort.ticket]) (fun _ => hhead) ?_ trivial rfl
    (fun hw => by simp [h, Ort.weckt] at hw)
  rw [hf]
  exact hI.wait

/-- **Wait**: a thread that does not find its ticket served loads a serving value below its ticket. -/
theorem Inv.wartet {σ : Zustand N} (hI : Inv N σ) {t : Fin N} {k : Nat} (h : σ.pc t = .ladeS k)
    (e : σ.w.serv % 18446744073709551616 ≠ k % 18446744073709551616) :
    Inv N (σ.mit t (.incL k σ.w.serv)) := by
  obtain ⟨i, _, hki, hil⟩ := hI.platz (by simp [h, Ort.ticket] : (σ.pc t).ticket = some k)
  have hl := hI.laenge
  refine hI.still (o := .incL k σ.w.serv) h rfl rfl rfl rfl rfl ?_
  show σ.w.serv ≤ σ.w.serv ∧ σ.w.serv < k ∧ k < σ.w.serv + N
  have hne : k ≠ σ.w.serv := fun hk => e (by rw [hk])
  omega

/-- **The waiter increment**: the successful `cas` counts the thread. -/
theorem Inv.erhoeht (hN : N ≤ 2147483647) {σ : Zustand N} (hI : Inv N σ) {t : Fin N} {k s0 lw : Nat}
    (h : σ.pc t = .incC k s0 lw) (e : σ.w.wait = lw) :
    Inv N ⟨⟨σ.w.next, σ.w.serv, (lw + 1) % 18446744073709551616⟩, upd σ.pc t (.futexW k s0), σ.q⟩ := by
  have htq : t ∈ σ.q := (hI.mem t).2 (by simp [h, Ort.ticket])
  have hc : σ.q.countP (fun u => (upd σ.pc t (.futexW k s0) u).gezaehlt) =
      σ.q.countP (fun u => (σ.pc u).gezaehlt) + 1 :=
    countP_auf (fun u hu => by simp only [upd_ne σ.pc _ hu]) hI.nodup htq
      (by simp [h, Ort.gezaehlt]) (by simp [upd_self, Ort.gezaehlt])
  have hb := List.countP_le_length (p := fun u => (σ.pc u).gezaehlt) (l := σ.q)
  have hl := hI.laenge
  have hw := hI.wait
  have ho : OrtOK N σ.w (σ.pc t) := hI.ort t
  rw [h] at ho
  refine hI.updW (o := .futexW k s0) ⟨σ.w.next, σ.w.serv, (lw + 1) % 18446744073709551616⟩ rfl rfl
    (by simp [h, Ort.ticket]) (fun hh => by simp [Ort.haelt] at hh) ?_ ho rfl
    (fun hk => by simp [h, Ort.weckt] at hk)
  rw [hc]
  show (lw + 1) % 18446744073709551616 = _
  omega

/-- **The waiter decrement**: the successful `cas` uncounts the thread; the count was at least one. -/
theorem Inv.senkt (hN : N ≤ 2147483647) {σ : Zustand N} (hI : Inv N σ) {t : Fin N} {k s0 lw : Nat}
    (h : σ.pc t = .decC k s0 lw) (e : σ.w.wait = lw) :
    Inv N ⟨⟨σ.w.next, σ.w.serv, wrapDec lw⟩,
      upd σ.pc t (.ladeS k), σ.q⟩ := by
  have htq : t ∈ σ.q := (hI.mem t).2 (by simp [h, Ort.ticket])
  have hc : σ.q.countP (fun u => (upd σ.pc t (.ladeS k) u).gezaehlt) + 1 =
      σ.q.countP (fun u => (σ.pc u).gezaehlt) :=
    countP_ab (fun u hu => by simp only [upd_ne σ.pc _ hu]) hI.nodup htq
      (by simp [h, Ort.gezaehlt]) (by simp [upd_self, Ort.gezaehlt])
  have hb := List.countP_le_length (p := fun u => (σ.pc u).gezaehlt) (l := σ.q)
  have hl := hI.laenge
  have hw := hI.wait
  refine hI.updW (o := .ladeS k)
    ⟨σ.w.next, σ.w.serv, wrapDec lw⟩ rfl rfl
    (by simp [h, Ort.ticket]) (fun hh => by simp [Ort.haelt] at hh) ?_ trivial rfl
    (fun hk => by simp [h, Ort.weckt] at hk)
  show wrapDec lw = _
  rw [wrapDec_eq]
  omega

/-- **FUTEX_WAIT blocks** only while the low 32 bits of the serving word equal the passed value. -/
theorem Inv.schlaeft {σ : Zustand N} (hI : Inv N σ) {t : Fin N} {k s0 : Nat} (h : σ.pc t = .futexW k s0)
    (e : σ.w.serv % 4294967296 = s0 % 4294967296) : Inv N (σ.mit t (.blockiert k s0)) := by
  have ho : OrtOK N σ.w (σ.pc t) := hI.ort t
  rw [h] at ho
  have hf : (fun u => (upd σ.pc t (.blockiert k s0) u).gezaehlt) = (fun u => (σ.pc u).gezaehlt) :=
    funext (upd_eq_of Ort.gezaehlt σ.pc t _ (by simp [h, Ort.gezaehlt]))
  refine hI.lokal σ.w (upd σ.pc t (.blockiert k s0)) rfl rfl
    (upd_eq_of Ort.ticket σ.pc t _ (by simp [h, Ort.ticket])) ?_ (by rw [hf]; exact hI.wait) ?_ ?_
  · intro u hu
    by_cases hut : u = t
    · simp [hut, upd_self, Ort.haelt] at hu
    · simp only [upd_ne σ.pc _ hut] at hu
      exact hI.haelt u hu
  · intro u
    by_cases hut : u = t
    · rw [hut, upd_self]
      exact ho
    · rw [upd_ne σ.pc _ hut]
      exact hI.ort u
  · intro u k' s0' hu
    by_cases hut : u = t
    · rw [hut, upd_self] at hu
      injection hu with h1 h2
      left
      rw [← h2]
      exact e
    · simp only [upd_ne σ.pc _ hut] at hu
      rcases hI.nolost u k' s0' hu with e' | ⟨g, hg⟩
      · exact Or.inl e'
      · right
        refine ⟨g, ?_⟩
        by_cases hgt : g = t
        · rw [hgt, h] at hg
          simp [Ort.weckt] at hg
        · rw [upd_ne σ.pc _ hgt]
          exact hg

/-- **No waiter to wake**: when the giver reads a zero waiter word, nobody is blocked. -/
theorem Inv.keinWarter {σ : Zustand N} (hI : Inv N σ) {t : Fin N} (h : σ.pc t = .gibW) (e : σ.w.wait = 0) :
    Inv N (σ.mit t .frei) := by
  have hf : (fun u => (upd σ.pc t .frei u).gezaehlt) = (fun u => (σ.pc u).gezaehlt) :=
    funext (upd_eq_of Ort.gezaehlt σ.pc t _ (by simp [h, Ort.gezaehlt]))
  refine hI.lokal σ.w (upd σ.pc t .frei) rfl rfl
    (upd_eq_of Ort.ticket σ.pc t _ (by simp [h, Ort.ticket])) ?_ (by rw [hf]; exact hI.wait) ?_ ?_
  · intro u hu
    by_cases hut : u = t
    · simp [hut, upd_self, Ort.haelt] at hu
    · simp only [upd_ne σ.pc _ hut] at hu
      exact hI.haelt u hu
  · intro u
    by_cases hut : u = t
    · rw [hut, upd_self]
      exact trivial
    · rw [upd_ne σ.pc _ hut]
      exact hI.ort u
  · intro u k s0 hu
    exfalso
    by_cases hut : u = t
    · rw [hut, upd_self] at hu
      cases hu
    · simp only [upd_ne σ.pc _ hut] at hu
      have hm : u ∈ σ.q := (hI.mem u).2 (by simp [hu, Ort.ticket])
      have hpos : 0 < σ.q.countP (fun u => (σ.pc u).gezaehlt) :=
        List.countP_pos_iff.2 ⟨u, hm, by simp [hu, Ort.gezaehlt]⟩
      rw [← hI.wait, e] at hpos
      exact Nat.lt_irrefl 0 hpos

end Gabbro.Stage0.Senke.Faeden
