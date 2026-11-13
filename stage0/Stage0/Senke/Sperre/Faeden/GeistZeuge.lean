/-
  File:      stage0/Stage0/Senke/Sperre/Faeden/GeistZeuge.lean
  Subject:   THE WITNESS RUN (Faeden/Zeuge.lean: two threads, thread 1 blocked in FUTEX_WAIT and woken) AS A RUN OF THE
             MODEL'S TICKET LOCK. Read at its own steps (`Fenster.id`), it is a run of the abstract lock at G
             granularity (`zeuge_absLauf`), so the queue facts of `FifoLauf` hold along it (`zeuge_fifo`), with a
             queue that really changes (`zeuge_schlange`); and it carries a ghost run of the model's `Tkt` in which
             thread 0 holds at step 4, thread 1 owns an outstanding ticket while it is blocked at step 11, and
             thread 1 holds at step 19 (`zeuge_tkt`). The G half of the coupling (`GSicht`) is not witnessed here.
-/
module
public import Stage0.Senke.Sperre.Faeden.Zeuge
public import Stage0.Senke.Sperre.Faeden.Fenster
@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden.Zeuge

open Gabbro.Stage0.Senke.Faeden
open Gabbro.Code (Conf)
open Gabbro.Code.Lower (Tkt)

/-- The witness run at each of its steps, threads by number. -/
def zbei : Nat → Abs Nat := zeuge.bei (fun n => n)

/-- Its scheduler, threads by number. -/
def zakt : Nat → Option Nat := fun n => (zeuge.akt n).map Fin.val

theorem zeuge_absLauf : AbsLauf zakt zbei := zeuge.absLauf (by decide) zeuge_inv (Fenster.id zeuge)

/-- **The `FifoLauf` facts along the witness**: each once, first come first served, only the head takes. -/
theorem zeuge_fifo : (∀ n, (zbei n).queue.Nodup) ∧
    (∀ n, (zbei n).queue.filter (fun u => decide (u ∈ (zbei (n + 1)).queue)) <+: (zbei (n + 1)).queue) ∧
    ∀ n u, zakt n = some u → u ∈ (zbei n).queue → (zbei (n + 1)).holder = some u →
      (zbei n).queue.head? = some u :=
  ⟨zeuge_absLauf.eindeutig, zeuge_absLauf.ordnung, fun _ _ hk hu hh => zeuge_absLauf.kopf hk hu hh⟩

/-- The queue along the witness is not trivial: thread 0 draws, thread 1 waits behind the holder 0, then holds. -/
theorem zeuge_schlange : zbei 3 = ⟨none, [0]⟩ ∧ zbei 11 = ⟨some 0, [1]⟩ ∧ zbei 19 = ⟨some 1, []⟩ := by
  simp [zbei, Lauf.bei, Abs.karte, zeuge, zz, zs, z19, z18, z17, z16, z15, z14,
    z13, z12, z11, z10, z9, z8, z7, z6, z5, z4, z3, z2, z1, z0,
    start, Zustand.mit, upd, wecke, Ort.geweckt, Ort.haelt, bild, bildAus]

/-- **The witness carries the model's ghost**: thread 0 holds at step 4; at step 11, blocked in FUTEX_WAIT, thread 1
    owns an outstanding ticket behind the holder 0; at step 19 thread 1 holds. -/
theorem zeuge_tkt [Conf] : ∃ gh : Nat → Tkt, (∀ n, Passt (gh n) (zbei n)) ∧
    (∀ n, Nach (zakt n) (gh n) (gh (n + 1))) ∧ tHalter (gh 4) = some 0 ∧ 1 ∈ tWarte (gh 11) ∧
    tHalter (gh 11) = some 0 ∧ tHalter (gh 19) = some 1 := by
  obtain ⟨gh, hP, hT⟩ := zeuge.tkt (by decide) zeuge_inv (Fenster.id zeuge)
  have h4 : (zbei 4).holder = some 0 := by
    simp [zbei, Lauf.bei, Abs.karte, zeuge, zz, zs, z4, z3, z2, z1, z0,
      start, Zustand.mit, upd, bild, bildAus, Ort.haelt]
  have h11 : zbei 11 = ⟨some 0, [1]⟩ := zeuge_schlange.2.1
  have h19 : zbei 19 = ⟨some 1, []⟩ := zeuge_schlange.2.2
  have p4 : Passt (gh 4) (zbei 4) := hP 4
  have p11 : Passt (gh 11) (zbei 11) := hP 11
  have p19 : Passt (gh 19) (zbei 19) := hP 19
  refine ⟨gh, hP, hT, ?_, ?_, ?_, ?_⟩
  · exact p4.halter.symm.trans h4
  · have e := p11.warte
    rw [h11] at e
    rw [← e]
    exact List.mem_singleton_self 1
  · exact p11.halter.symm.trans (congrArg Abs.holder h11)
  · exact p19.halter.symm.trans (congrArg Abs.holder h19)

end Gabbro.Stage0.Senke.Faeden.Zeuge
