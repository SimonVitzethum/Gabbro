/-
  File:      stage0/Stage0/Senke/Sperre/Faeden/Zeuge.lean
  Subject:   THE WITNESS of the cross-thread lock theorem: two threads contend for the emitted lock. Thread 0 draws
             ticket 0 and enters; thread 1 draws ticket 1, finds it not served, counts itself in the waiter word
             and BLOCKS in FUTEX_WAIT (step 11); thread 0 gives (`cas` on `serving`), reads a nonzero waiter word and
             makes the FUTEX_WAKE of all waiters, which WAKES thread 1 (step 16); thread 1 uncounts itself, finds
             ticket 1 served and enters (step 19). Then both threads keep stepping in place for ever (thread 0
             outside, thread 1 in the guarded body), so the run is weakly fair and has no spurious return: every
             premise of `Lauf.leben` holds on it (`zeuge_leben_satz`). The abstract ticket lock along the run
             (`zeuge_bild`) is the model run: draw 0, enter 0, draw 1, give 0, enter 1, with thread 1 in the queue
             while it is blocked. Run observations use simplification of the explicit states.
-/
module
public import Stage0.Senke.Sperre.Faeden.Leben
@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden.Zeuge

open Gabbro.Stage0.Senke.Faeden

/-! ## The states -/

def z0 : Zustand 2 := start 2
def z1 : Zustand 2 := z0.mit 0 .ladeN
def z2 : Zustand 2 := z1.mit 0 (.casN (z1.w.next % 18446744073709551616))
def z3 : Zustand 2 := ⟨⟨z2.w.next + 1, z2.w.serv, z2.w.wait⟩, upd z2.pc 0 (.ladeS z2.w.next), z2.q ++ [0]⟩
def z4 : Zustand 2 := z3.mit 0 (.drin 0)
def z5 : Zustand 2 := z4.mit 1 .ladeN
def z6 : Zustand 2 := z5.mit 1 (.casN (z5.w.next % 18446744073709551616))
def z7 : Zustand 2 := ⟨⟨z6.w.next + 1, z6.w.serv, z6.w.wait⟩, upd z6.pc 1 (.ladeS z6.w.next), z6.q ++ [1]⟩
def z8 : Zustand 2 := z7.mit 1 (.incL 1 z7.w.serv)
def z9 : Zustand 2 := z8.mit 1 (.incC 1 z7.w.serv z8.w.wait)
def z10 : Zustand 2 :=
  ⟨⟨z9.w.next, z9.w.serv, (z8.w.wait + 1) % 18446744073709551616⟩, upd z9.pc 1 (.futexW 1 z7.w.serv), z9.q⟩
def z11 : Zustand 2 := z10.mit 1 (.blockiert 1 z7.w.serv)
def z12 : Zustand 2 := z11.mit 0 (.gibL 0)
def z13 : Zustand 2 := z12.mit 0 (.gibC 0 (z12.w.serv % 18446744073709551616))
def z14 : Zustand 2 := ⟨⟨z13.w.next, z13.w.serv + 1, z13.w.wait⟩, upd z13.pc 0 .gibW, z13.q.tail⟩
def z15 : Zustand 2 := z14.mit 0 .weck
def z16 : Zustand 2 := ⟨z15.w, upd (wecke z15.pc) 0 .frei, z15.q⟩
def z17 : Zustand 2 := z16.mit 1 (.decC 1 z7.w.serv z16.w.wait)
def z18 : Zustand 2 :=
  ⟨⟨z17.w.next, z17.w.serv, wrapDec z16.w.wait⟩,
    upd z17.pc 1 (.ladeS 1), z17.q⟩
def z19 : Zustand 2 := z18.mit 1 (.drin 1)

/-! ## The steps -/

theorem s0 : Schritt z0 0 z1 := Schritt.beginnt (by decide)
theorem s1 : Schritt z1 0 z2 := Schritt.liestN (by decide)
theorem s2 : Schritt z2 0 z3 := Schritt.zieht (l := 0) (by decide) (by decide)
theorem s3 : Schritt z3 0 z4 := Schritt.tritt (k := 0) (by decide) (by decide)
theorem s4 : Schritt z4 1 z5 := Schritt.beginnt (by decide)
theorem s5 : Schritt z5 1 z6 := Schritt.liestN (by decide)
theorem s6 : Schritt z6 1 z7 := Schritt.zieht (l := 1) (by decide) (by decide)
theorem s7 : Schritt z7 1 z8 := Schritt.wartet (k := 1) (by decide) (by decide)
theorem s8 : Schritt z8 1 z9 := Schritt.liestInc (by decide)
theorem s9 : Schritt z9 1 z10 := Schritt.erhoeht (k := 1) (s0 := 0) (lw := 0) (by decide) (by decide)
/-- Thread 1 blocks in FUTEX_WAIT. -/
theorem s10 : Schritt z10 1 z11 := Schritt.schlaeft (k := 1) (s0 := 0) (by decide) (by decide)
theorem s11 : Schritt z11 0 z12 := Schritt.verlaesst (k := 0) (by decide)
theorem s12 : Schritt z12 0 z13 := Schritt.liestGib (k := 0) (by decide)
theorem s13 : Schritt z13 0 z14 := Schritt.gibt (k := 0) (ls := 0) (by decide) (by decide)
theorem s14 : Schritt z14 0 z15 := Schritt.warter (by decide) (by decide)
/-- Thread 0's FUTEX_WAKE wakes thread 1. -/
theorem s15 : Schritt z15 0 z16 := Schritt.weckt (by decide)
theorem s16 : Schritt z16 1 z17 := Schritt.liestDec (by decide)
theorem s17 : Schritt z17 1 z18 := Schritt.senkt (k := 1) (s0 := 0) (lw := 1) (by decide) (by decide)
theorem s18 : Schritt z18 1 z19 := Schritt.tritt (k := 1) (by decide) (by decide)

theorem s19 (t : Fin 2) : Schritt z19 t z19 :=
  match t with
  | ⟨0, _⟩ => Schritt.ruht rfl
  | ⟨1, _⟩ => Schritt.arbeitet (k := 1) rfl
  | ⟨n + 2, h⟩ => absurd h (by omega)

/-! ## The run -/

def zs : List (Zustand 2) := [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18]

def ts : List (Fin 2) := [0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1]

def zz (n : Nat) : Zustand 2 := if n < 19 then zs.getD n z19 else z19

def aa (n : Nat) : Option (Fin 2) :=
  if n < 19 then some (ts.getD n 0) else some ⟨n % 2, Nat.mod_lt n (by decide)⟩

theorem kette : ∀ n, n < 19 → Schritt (zz n) (ts.getD n 0) (zz (n + 1))
  | 0, _ => s0
  | 1, _ => s1
  | 2, _ => s2
  | 3, _ => s3
  | 4, _ => s4
  | 5, _ => s5
  | 6, _ => s6
  | 7, _ => s7
  | 8, _ => s8
  | 9, _ => s9
  | 10, _ => s10
  | 11, _ => s11
  | 12, _ => s12
  | 13, _ => s13
  | 14, _ => s14
  | 15, _ => s15
  | 16, _ => s16
  | 17, _ => s17
  | 18, _ => s18
  | n + 19, h => absurd h (by omega)

theorem zz_ende {n : Nat} (hn : ¬ n < 19) : zz n = z19 := by
  show (if n < 19 then zs.getD n z19 else z19) = z19
  rw [if_neg hn]

theorem schritte (n : Nat) (t : Fin 2) (h : aa n = some t) : Schritt (zz n) t (zz (n + 1)) := by
  by_cases hn : n < 19
  · unfold aa at h
    rw [if_pos hn] at h
    rw [← Option.some.inj h]
    exact kette n hn
  · unfold aa at h
    rw [if_neg hn] at h
    rw [zz_ende hn, zz_ende (n := n + 1) (by omega)]
    exact s19 t

/-- **The run**: the nineteen steps, then both threads step in place for ever. -/
def zeuge : Lauf 2 where
  z := zz
  akt := aa
  schritt := schritte
  stotter := fun n h => by
    unfold aa at h
    split at h <;> cases h

/-! ## What the run shows -/

theorem zeuge_inv : Inv 2 (zeuge.z 0) := Inv.start

/-- At step 11 thread 1 is blocked in FUTEX_WAIT with ticket 1 and serving value 0, and it waits at the lock. -/
theorem zeuge_blockiert : (zeuge.z 11).pc 1 = .blockiert 1 0 ∧ (1 : Fin 2) ∈ zeuge.warte 11 := by
  simp [Lauf.warte, zeuge, zz, zs, z19, z18, z17, z16, z15, z14,
    z13, z12, z11, z10, z9, z8, z7, z6, z5, z4, z3, z2, z1, z0,
    start, Zustand.mit, upd, wecke, Ort.geweckt, Ort.haelt, bild, bildAus]

/-- At step 16 the FUTEX_WAKE has woken it; at step 19 it holds the lock. -/
theorem zeuge_geweckt : (zeuge.z 16).pc 1 = .decL 1 0 ∧ (zeuge.z 19).pc 1 = .drin 1 := by
  simp [zeuge, zz, zs, z19, z18, z17, z16, z15, z14,
    z13, z12, z11, z10, z9, z8, z7, z6, z5, z4, z3, z2, z1, z0,
    start, Zustand.mit, upd, wecke, Ort.geweckt, Ort.haelt, bild, bildAus]

/-- **The abstract ticket lock along the run**: the model run of draw 0, enter 0, draw 1, give 0, enter 1. -/
theorem zeuge_bild : (List.range 20).map (fun n => bild (zeuge.z n)) =
    [⟨none, []⟩, ⟨none, []⟩, ⟨none, []⟩, ⟨none, [0]⟩, ⟨some 0, []⟩, ⟨some 0, []⟩, ⟨some 0, []⟩,
      ⟨some 0, [1]⟩, ⟨some 0, [1]⟩, ⟨some 0, [1]⟩, ⟨some 0, [1]⟩, ⟨some 0, [1]⟩, ⟨some 0, [1]⟩,
      ⟨some 0, [1]⟩, ⟨none, [1]⟩, ⟨none, [1]⟩, ⟨none, [1]⟩, ⟨none, [1]⟩, ⟨none, [1]⟩, ⟨some 1, []⟩] := by
  simp [List.range_succ, zeuge, zz, zs, z19, z18, z17, z16, z15, z14,
    z13, z12, z11, z10, z9, z8, z7, z6, z5, z4, z3, z2, z1, z0,
    start, Zustand.mit, upd, wecke, Ort.geweckt, Ort.haelt, bild, bildAus]

theorem zeuge_fair : zeuge.Fair := by
  intro t n _
  refine ⟨2 * (n + 19) + t.val, by omega, ?_⟩
  show aa (2 * (n + 19) + t.val) = some t
  have hn : ¬ (2 * (n + 19) + t.val < 19) := by omega
  unfold aa
  rw [if_neg hn]
  have ht := t.isLt
  exact congrArg some (Fin.ext (show (2 * (n + 19) + t.val) % 2 = t.val by omega))

theorem zeuge_scheinbar : zeuge.ScheinbarEndlich := by
  refine ⟨19, fun j hj v _ => ?_⟩
  show ((zz j).pc v).schlaeft = false
  rw [zz_ende (n := j) (by omega)]
  match v with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨k + 2, hk⟩ => exact absurd hk (by omega)

/-- **The premises of the liveness theorem hold jointly** on the witness run, for the blocked thread. -/
theorem zeuge_leben_satz :
    (∃ j, 11 ≤ j ∧ (zeuge.z j).pc 1 = .drin 1) ∨ ∃ u m, ∀ j, m ≤ j → ((zeuge.z j).pc u).haelt = true :=
  Lauf.leben (by decide) zeuge zeuge_inv zeuge_fair zeuge_scheinbar 11 1 1 ⟨by decide, by decide⟩

/-- Every scheduler step of the witness run is a stutter or one step of the abstract ticket lock. -/
theorem zeuge_abbild (n : Nat) :
    (zeuge.akt n = none ∧ bild (zeuge.z (n + 1)) = bild (zeuge.z n)) ∨
      ∃ t, zeuge.akt n = some t ∧ Opt (AbsSchritt t) (bild (zeuge.z n)) (bild (zeuge.z (n + 1))) :=
  Lauf.abbild (by decide) zeuge zeuge_inv n

end Gabbro.Stage0.Senke.Faeden.Zeuge
