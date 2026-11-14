/-
  File:      stage0/Stage0/Senke/Sperre/Faeden/InvLauf.lean
  Subject:   The invariant across the give path of the emitted lock (`cas` on `serving`, FUTEX_WAKE of all
             waiters), then `Inv.schritt` (every step of every thread keeps the invariant, for at most
             2147483647 threads, the count the emitted WAKE passes) and `Inv.lauf` (along every run from a state
             that meets it, in particular from `start`).
-/
module
public import Stage0.Senke.Sperre.Faeden.InvSchritt
@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

variable {N : Nat}

/-- **The give**: the holder heads the queue; `serving + 1` serves the next ticket and the holder becomes a
    pending waker. -/
theorem Inv.gibt {σ : Zustand N} (hI : Inv N σ) {t : Fin N} {k ls : Nat} (h : σ.pc t = .gibC k ls) :
    Inv N ⟨⟨σ.w.next, σ.w.serv + 1, σ.w.wait⟩, upd σ.pc t .gibW, σ.q.tail⟩ := by
  have hhead : σ.q.head? = some t := hI.haelt t (by simp [h, Ort.haelt])
  obtain ⟨r, hr⟩ := List.head?_eq_some_iff.1 hhead
  have hn := hI.nodup
  rw [hr] at hn
  have htr : t ∉ r := (List.nodup_cons.1 hn).1
  have hqt : σ.q.tail = r := by rw [hr, List.tail_cons]
  refine ⟨?_, fun u => ?_, fun i u hi => ?_, ?_, fun u hu => ?_, ?_, fun u => ?_, fun u k' s0' hu => ?_⟩
  · show σ.q.tail.Nodup
    rw [hqt]
    exact (List.nodup_cons.1 hn).2
  · show u ∈ σ.q.tail ↔ (upd σ.pc t .gibW u).ticket.isSome = true
    rw [hqt]
    by_cases hut : u = t
    · rw [hut, upd_self]
      exact ⟨fun hm => absurd hm htr, fun hh => by simp [Ort.ticket] at hh⟩
    · rw [upd_ne σ.pc _ hut, ← hI.mem u, hr]
      exact ⟨List.mem_cons_of_mem t, fun hm => (List.mem_cons.1 hm).resolve_left hut⟩
  · show (upd σ.pc t .gibW u).ticket = some (σ.w.serv + 1 + i)
    rw [hqt] at hi
    have hi' : σ.q[i + 1]? = some u := by
      rw [hr, List.getElem?_cons_succ]
      exact hi
    have hut : u ≠ t := fun hut => htr (by rw [← hut]; exact List.mem_iff_getElem?.2 ⟨i, hi⟩)
    rw [upd_ne σ.pc _ hut, hI.tk (i + 1) u hi']
    exact congrArg some (by omega)
  · show σ.w.next = σ.w.serv + 1 + σ.q.tail.length
    have h1 := hI.next
    have h2 : σ.q.tail.length + 1 = σ.q.length := by rw [hr, List.tail_cons, List.length_cons]
    omega
  · show σ.q.tail.head? = some u
    exfalso
    by_cases hut : u = t
    · simp [hut, upd_self, Ort.haelt] at hu
    · simp only [upd_ne σ.pc _ hut] at hu
      have hh := hI.haelt u hu
      rw [hhead] at hh
      exact hut (Option.some.inj hh).symm
  · show σ.w.wait = σ.q.tail.countP (fun u => (upd σ.pc t .gibW u).gezaehlt)
    have h1 : r.countP (fun u => (upd σ.pc t .gibW u).gezaehlt) = r.countP (fun u => (σ.pc u).gezaehlt) :=
      List.countP_congr (fun x hx => by rw [upd_ne σ.pc _ (fun e : x = t => htr (e ▸ hx))])
    have h2 : σ.q.countP (fun u => (σ.pc u).gezaehlt) = r.countP (fun u => (σ.pc u).gezaehlt) := by
      rw [hr, List.countP_cons]
      simp [h, Ort.gezaehlt]
    rw [hqt, h1, hI.wait, h2]
  · show OrtOK N ⟨σ.w.next, σ.w.serv + 1, σ.w.wait⟩ (upd σ.pc t .gibW u)
    by_cases hut : u = t
    · rw [hut, upd_self]
      exact trivial
    · rw [upd_ne σ.pc _ hut]
      have hnh : (σ.pc u).haelt = false := by
        cases hh : (σ.pc u).haelt
        · rfl
        · exact absurd (Option.some.inj ((hI.haelt u hh).symm.trans hhead)) hut
      exact OrtOK.succ rfl _ hnh (hI.ort u)
  · right
    refine ⟨t, ?_⟩
    show (upd σ.pc t .gibW t).weckt = true
    simp [upd_self, Ort.weckt]

theorem geweckt_ticket (o : Ort) : o.geweckt.ticket = o.ticket := by cases o <;> rfl
theorem geweckt_haelt (o : Ort) : o.geweckt.haelt = o.haelt := by cases o <;> rfl
theorem geweckt_gezaehlt (o : Ort) : o.geweckt.gezaehlt = o.gezaehlt := by cases o <;> rfl
theorem geweckt_schlaeft (o : Ort) : o.geweckt.schlaeft = false := by cases o <;> rfl
theorem geweckt_ok {w : Wort} (o : Ort) (ho : OrtOK N w o) : OrtOK N w o.geweckt := by
  cases o <;> exact ho

/-- **FUTEX_WAKE of all waiters**: nobody stays blocked. -/
theorem Inv.weckt {σ : Zustand N} (hI : Inv N σ) {t : Fin N} (h : σ.pc t = .weck) :
    Inv N ⟨σ.w, upd (wecke σ.pc) t .frei, σ.q⟩ := by
  have hT : ∀ u, (upd (wecke σ.pc) t .frei u).ticket = (σ.pc u).ticket := by
    intro u
    by_cases hut : u = t
    · simp [hut, upd_self, h, Ort.ticket]
    · rw [upd_ne _ _ hut, wecke_apply, geweckt_ticket]
  have hf : (fun u => (upd (wecke σ.pc) t .frei u).gezaehlt) = (fun u => (σ.pc u).gezaehlt) := by
    funext u
    by_cases hut : u = t
    · simp [hut, upd_self, h, Ort.gezaehlt]
    · rw [upd_ne _ _ hut, wecke_apply, geweckt_gezaehlt]
  refine hI.lokal σ.w (upd (wecke σ.pc) t .frei) rfl rfl hT ?_ (by rw [hf]; exact hI.wait) ?_ ?_
  · intro u hu
    by_cases hut : u = t
    · simp [hut, upd_self, Ort.haelt] at hu
    · rw [upd_ne _ _ hut, wecke_apply, geweckt_haelt] at hu
      exact hI.haelt u hu
  · intro u
    by_cases hut : u = t
    · rw [hut, upd_self]
      exact trivial
    · rw [upd_ne _ _ hut, wecke_apply]
      exact geweckt_ok _ (hI.ort u)
  · intro u k s0 hu
    exfalso
    by_cases hut : u = t
    · rw [hut, upd_self] at hu
      cases hu
    · rw [upd_ne _ _ hut, wecke_apply] at hu
      have hs := geweckt_schlaeft (σ.pc u)
      rw [hu] at hs
      simp [Ort.schlaeft] at hs

/-- The loaded words of a waiting thread fit at its next place. -/
theorem Inv.ort_an {σ : Zustand N} (hI : Inv N σ) {t : Fin N} {o : Ort} (h : σ.pc t = o) :
    OrtOK N σ.w o := by
  rw [← h]
  exact hI.ort t

/-- **Every step keeps the invariant.** -/
theorem Inv.schritt (hN : N ≤ 2147483647) {σ σ' : Zustand N} {t : Fin N} (hI : Inv N σ)
    (hs : Schritt σ t σ') : Inv N σ' := by
  cases hs with
  | @beginnt h => exact hI.still (o := .ladeN) h rfl rfl rfl rfl rfl trivial
  | @ruht h => exact hI
  | @liestN h => exact hI.still (o := .casN (σ.w.next % 18446744073709551616)) h rfl rfl rfl rfl rfl trivial
  | @zieht l h e => exact hI.zieht h
  | @verfehlt l h e => exact hI.still (o := .ladeN) h rfl rfl rfl rfl rfl trivial
  | @tritt k h e => exact hI.tritt_inv hN h e
  | @wartet k h e => exact hI.wartet h e
  | @liestInc k s0 h =>
    exact hI.still (o := .incC k s0 σ.w.wait) h rfl rfl rfl rfl rfl (hI.ort_an h :)
  | @erhoeht k s0 lw h e => exact hI.erhoeht hN h e
  | @erhoehtNicht k s0 lw h e => exact hI.still (o := .incL k s0) h rfl rfl rfl rfl rfl (hI.ort_an h :)
  | @schlaeft k s0 h e => exact hI.schlaeft h e
  | @kehrtZurueck k s0 h e => exact hI.still (o := .decL k s0) h rfl rfl rfl rfl rfl (hI.ort_an h :)
  | @scheinbar k s0 h => exact hI.still (o := .decL k s0) h rfl rfl rfl rfl rfl (hI.ort_an h :)
  | @liestDec k s0 h =>
    exact hI.still (o := .decC k s0 σ.w.wait) h rfl rfl rfl rfl rfl (hI.ort_an h :)
  | @senkt k s0 lw h e => exact hI.senkt hN h e
  | @senktNicht k s0 lw h e => exact hI.still (o := .decL k s0) h rfl rfl rfl rfl rfl (hI.ort_an h :)
  | @arbeitet k h => exact hI
  | @verlaesst k h => exact hI.still (o := .gibL k) h rfl rfl rfl rfl rfl trivial
  | @liestGib k h =>
    exact hI.still (o := .gibC k (σ.w.serv % 18446744073709551616)) h rfl rfl rfl rfl rfl
      (show σ.w.serv % 18446744073709551616 = σ.w.serv % 18446744073709551616 from rfl)
  | @gibt k ls h e => exact hI.gibt h
  | @gibtNicht k ls h e =>
    have ho := hI.ort_an h
    exact absurd (show ls = σ.w.serv % 18446744073709551616 from ho).symm e
  | @keinWarter h e => exact hI.keinWarter h e
  | @warter h e => exact hI.still (o := .weck) h rfl rfl rfl rfl rfl trivial
  | @weckt h => exact hI.weckt h

/-- **The invariant along a run.** -/
theorem Inv.lauf (hN : N ≤ 2147483647) (R : Lauf N) (h0 : Inv N (R.z 0)) : ∀ n, Inv N (R.z n)
  | 0 => h0
  | n + 1 => by
    have ih := Inv.lauf hN R h0 n
    cases hk : R.akt n with
    | none =>
      rw [R.stotter n hk]
      exact ih
    | some t => exact ih.schritt hN (R.schritt n t hk)

end Gabbro.Stage0.Senke.Faeden
