/- Part 3 of 3 of `ZielOrt` (split by instrumente/teile/lean-teilen.py; the umbrella `ZielOrt.lean` imports all parts). -/
module
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt.T2
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 5. The finding: every candidate premise holds, the conclusion fails

    The program `gegP` over the reference declaration `refD`: the reference
    CONTRACTS (`einzahlen`: requires true, ensures `old(konto[0]) ≤
    konto[0]`; `lies`: requires true, ensures `result = konto[0]`), both
    functions holding the lock by signature; the bodies:
    `einzahlen` = `lies(); konto[0] := 100; return`,
    `lies` = `let x = konto[0]; return x`.
    Both are correct sequentially (`gegP_koerperGut`). -/

/-- `lies`: bind `konto[0]`, then return the bound value. -/
def gegRumpfLies : Endblock refD (vertragVon refD refLies) false []
    (Signatur.anfang refD (refD.signatur refLies)) :=
  .bind (.slot () () refIdxBodyLies refDarfBodyLies)
    (.ret (.val (.var .here)) (by rfl))

/-- `einzahlen`: call `lies`, write the cap, return. -/
def gegRumpfEin :
    Endblock refD (vertragVon refD refEin) false [.int 0 10] [Res.held (D := refD) ()] :=
  .cons (.call (V := vertragVon refD refEin) refLies refArgsLies refHpLiesAt rfl)
    (.cons refWriteStAt (.ret .empty (by rfl)))

/-- The counterexample program: reference contracts, the two bodies above. -/
def gegP : Programm refD where
  invariante := fun i => nomatch i
  requires
    | true => refReqEin
    | false => refReqLies
  ensures
    | true => refEnsEin
    | false => refEnsLies
  rumpf
    | true => refEin_start ▸ gegRumpfEin
    | false => refLies_start ▸ gegRumpfLies

/-- Every thread starts in `einzahlen 7`. -/
def gegInit : Faden → Σ f : refD.Fn, Env refD (refD.params f) :=
  fun _ => ⟨refEin, refRho7⟩

/-- The member list of `refD`'s functions, complete. -/
def refFs : List refD.Fn := [refEin, refLies]

theorem refFs_voll : ∀ g : refD.Fn, g ∈ refFs := by
  intro g
  cases g
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_self

theorem gegP_fragment : programmImFragment gegP refFs = true := by decide

theorem gegP_fuss : fussOrtB gegP refFs = true := by decide

theorem gegP_schreiber : schreiberHaeltB gegP refFs = true := by decide

theorem gegP_start : StartGut gegP refSp0 gegInit := fun _ => rfl

/-- `lies` is correct sequentially: the bound value IS `konto[0]` of the
    entry world, and reading keeps the slots, so `result = konto[0]` holds
    at the return world. It makes no call. -/
theorem gegP_koerper_lies : KoerperGut gegP refO 0 refLies := by
  intro R _ _ σ ρ _
  have hr : gegP.rumpf refLies = gegRumpfLies := rfl
  refine ⟨?_, ?_⟩
  · intro σ' v hrun
    rw [hr] at hrun
    simp only [gegRumpfLies, execEnd, EndAusgang.schrumpf] at hrun
    cases hrun
    exact (decide_eq_true_eq).mpr rfl
  · intro g hrun
    rw [hr] at hrun
    simp only [gegRumpfLies, execEnd, EndAusgang.schrumpf] at hrun
    cases hrun

/-- `einzahlen` is correct sequentially: whatever the contract-respecting
    handler answers for `lies`, the body then writes the cap `100`, the top
    of the field's range, so `old(konto[0]) ≤ konto[0]` holds at the return
    world; its one call meets `requires lies` (which is `true`). -/
theorem gegP_koerper_ein : KoerperGut gegP refO 0 refEin := by
  intro R _ hOV σ ρ _
  have hr : gegP.rumpf refEin = gegRumpfEin := rfl
  have htor : ∀ (σ1 : World refD) (ρ1 : Env refD (refD.params refLies)),
      torRuf gegP R refLies σ1 ρ1 = R refLies σ1 ρ1 := fun _ _ => if_pos rfl
  refine ⟨?_, ?_⟩
  · intro σ' v hrun
    rw [hr] at hrun
    simp only [gegRumpfEin, execEnd, execStmt] at hrun
    split at hrun
    · rename_i σa ρa heq
      split at heq
      · cases heq
        simp only [refWriteStAt, refWriteSt, execStmt] at hrun
        cases hrun
        have hOld : (σ.slots () 0 ()).n ≤ 100 := (σ.slots () 0 ()).le_hi
        show decide ((σ.slots () 0 ()).n ≤ 100) = true
        exact decide_eq_true_eq.mpr hOld
      · exact Fin.elim0 ‹_›
      · cases heq
      · cases heq
    all_goals first
      | (rename_i heq
         (split at heq <;> first | cases heq | exact Fin.elim0 ‹_›)
         done)
      | cases hrun
  · intro g hrun
    rw [hr] at hrun
    simp only [gegRumpfEin, execEnd, execStmt] at hrun
    simp only [htor] at hrun
    split at hrun
    · rename_i σa ρa heq
      split at heq
      · cases heq
        simp only [refWriteStAt, refWriteSt, execStmt] at hrun
        cases hrun
      · exact Fin.elim0 ‹_›
      · cases heq
      · cases heq
    all_goals first
      | (rename_i heq
         (split at heq <;> first | cases heq | exact Fin.elim0 ‹_›)
         done)
      | cases hrun
      | skip
    rename_i heq
    split at heq
    · cases heq
    · exact Fin.elim0 ‹_›
    · rename_i e' hRv
      cases heq
      exact hOV _ _ _ _ hRv g rfl
    · cases heq

/-- `HeldGenau` at the one-lock holdings, from the held set. -/
theorem heldGenau_ref {s : List (Ereignis refD)} (h : offen s = [()]) :
    HeldGenau [Res.held (D := refD) ()] (offen s) := by
  rw [h]
  intro L
  cases L
  exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩

theorem nicht_in_nil (L : refD.Lock) : L ∉ ([] : List refD.Lock) := fun h => nomatch h

/-- The start thread state of `gegInit` (every thread): `einzahlen 7`,
    HOLDING the lock (the repaired start). -/
def gegZ0 : RufFadenG refD :=
  ⟨[], ⟨refEin, refRho7, refSp0.welt [],
    ⟨false, refD.params refEin, Signatur.anfang refD (refD.signatur refEin), refRho7,
     .ende (gegP.rumpf refEin)⟩⟩, startSpur refEin,
     [RufEreignisF.eintritt refEin refRho7 (refSp0.welt [])]⟩

theorem gegM0_faden (t : Faden) : (RufStartG gegP refSp0 gegInit).faeden t = gegZ0 := by rfl

theorem offen_gegZ0 : offen gegZ0.spur = [()] := by rfl

/-- The rest of `einzahlen` after its call. -/
def gegRestEin : Endblock refD (vertragVon refD refEin) false [.int 0 10]
    (nach refD refLies [Res.held (D := refD) ()]) :=
  .cons refWriteStAt (.ret .empty (by rfl))

/-- Reachability composes. -/
theorem rufErreichbarG_trans {P : Programm D} {O : Orakel D} {passes : Nat}
    {M0 M1 M2 : RufMaschineG D} (h1 : RufErreichbarG P O passes M0 M1)
    (h2 : RufErreichbarG P O passes M1 M2) : RufErreichbarG P O passes M0 M2 := by
  induction h2 with
  | start => exact h1
  | schritt M M' f _ hs ih => exact RufErreichbarG.schritt M M' f ih hs

/-- `ensures lies` is `result = konto[0]`: false when the result is 0 and
    the return world has `konto[0] = 100`. -/
theorem ens_lies_falsch (s0 s1 : World refD) (rho : Env refD (refD.params refLies))
    (v : ErgVal refD (refD.erg refLies)) (hv : (show Zahl 0 100 from v).n = 0)
    (hs : (s1.slots () 0 ()).n = 100) : ¬ EnsAmRueck gegP refLies s0 s1 rho v := by
  intro hE
  have h : decide ((show Zahl 0 100 from v).n = (s1.slots () 0 ()).n) = true := hE
  rw [hv, hs] at h
  exact absurd h (by decide)

/-! ### 5a. The old counterexample is gone

    The run of the finding passed a machine `M4` in which thread 0's head
    frame (`lies`) names the lock in its static holdings while thread 0
    does not hold it -- reached by the bare `gibt`. On the repaired G no
    reachable machine has such a frame, for ANY program and start
    assignment (`rufG_haelt_statisch`); and every step that releases a lock
    releases one the head names (`offen_schrittG`). -/

/-- **The counterexample's pivot is unreachable.** On every machine of
    the repaired G reachable from ANY start, no thread has a frame (head or
    suspended) whose static holdings name a lock the thread does not hold.
    In particular the machine `M4` of the finding -- thread 0 inside
    `lies` with `Res.held ()` in its holdings and `() ∉ offen` -- is not
    reachable from the start machine of `gegP`. -/
theorem ziel_ort_gegenbeispiel_verschwindet :
    ∀ M : RufMaschineG refD,
      RufErreichbarG gegP refO 0 (RufStartG gegP refSp0 gegInit) M →
      ¬ ((M.faeden 0).kopf.f = refLies ∧
        Res.held (D := refD) () ∈ (M.faeden 0).kopf.rest.2.2.1 ∧
        (() : refD.Lock) ∉ offen (M.faeden 0).spur) := by
  intro M hr ⟨_, hmem, hnot⟩
  exact hnot (rufG_haelt_statisch refO_gut refSp0 gegInit hr 0 _ List.mem_cons_self () hmem)

/-! ### 5b. The start fact is needed

    With every thread starting in `einzahlen` -- which holds the lock by
    signature -- the start machine gives EVERY thread the lock: `gegInit`
    violates `StartExklusiv`. Then the interference is back, without any
    bare step: thread 0 enters `lies` and reads `konto[0] = 0`, thread 1
    (which also "holds" the lock) enters `lies`, returns and writes 100,
    thread 0 returns 0 in a world with `konto[0] = 100`. So the start fact
    is not decoration: dropping it makes `ziel_ort` false. -/

/-- **The run without an exclusive start.** Eight steps of the repaired G
    from the start machine of `gegP` under `gegInit`; thread 0's log ends
    with a return of `lies` whose `ensures` is false. -/
theorem geg_lauf : ∃ M : RufMaschineG refD,
    RufErreichbarG gegP refO 0 (RufStartG gegP refSp0 gegInit) M ∧
    ∃ (rho : Env refD (refD.params refLies)) (v : ErgVal refD (refD.erg refLies))
      (s0 s1 : World refD),
      RufEreignisF.rueck refLies rho v s0 s1 ∈ (M.faeden 0).log ∧
      ¬ EnsAmRueck gegP refLies s0 s1 rho v := by
  -- thread 0: call `lies`, bind `konto[0]`
  have h0 := gegM0_faden (0 : Faden)
  obtain ⟨M2, s2, hZ2⟩ := w_rufEnde (P := gegP) (O := refO) (passes := 0) h0 refLies
    refArgsLies refHpLiesAt rfl gegRestEin refRho7 rfl (heldGenau_ref offen_gegZ0).heldIn
  have hoff2 : offen (M2.faeden 0).spur = [()] := by
    rw [hZ2.1]
    exact ((Erw.lese _ _ _).offen).trans offen_gegZ0
  obtain ⟨M3, s3, hZ3⟩ := w_endeBind (P := gegP) (O := refO) (passes := 0) hZ2.1 _ _ _ rfl
    (heldGenau_ref (by first | exact hoff2 | (rw [hZ2.1] at hoff2; exact hoff2))).heldIn
  have hoff3 : offen (M3.faeden 0).spur = [()] := by
    rw [hZ3.1]
    exact ((Erw.lese _ _ _).offen).trans hoff2
  have hfremd3 : ∀ t : Faden, t ≠ 0 → M3.faeden t = gegZ0 := by
    intro t ht
    rw [rufSchrittG_fremd s3 t ht, rufSchrittG_fremd s2 t ht, gegM0_faden]
  have hr3 : RufErreichbarG gegP refO 0 (RufStartG gegP refSp0 gegInit) M3 :=
    .schritt _ _ _ (.schritt _ _ _ .start s2) s3
  -- thread 1: call `lies`, bind, return, write 100
  have h13 : M3.faeden 1 = gegZ0 := hfremd3 1 (by decide)
  obtain ⟨M4, s4, hZ4⟩ := w_rufEnde (P := gegP) (O := refO) (passes := 0) h13 refLies
    refArgsLies refHpLiesAt rfl gegRestEin refRho7 rfl (heldGenau_ref offen_gegZ0).heldIn
  have hoff4 : offen (M4.faeden 1).spur = [()] := by
    rw [hZ4.1]
    refine ((Erw.lese _ _ _).offen).trans ?_
    show offen (M3.faeden 1).spur = [()]
    rw [h13]; rfl
  obtain ⟨M5, s5, hZ5⟩ := w_endeBind (P := gegP) (O := refO) (passes := 0) hZ4.1 _ _ _ rfl
    (heldGenau_ref (by first | exact hoff4 | (rw [hZ4.1] at hoff4; exact hoff4))).heldIn
  have hoff5 : offen (M5.faeden 1).spur = [()] := by
    rw [hZ5.1]
    exact ((Erw.lese _ _ _).offen).trans hoff4
  obtain ⟨M6, s6, hG6⟩ := w_rueckP (P := gegP) (O := refO) (passes := 0) hZ5.1 _ [] rfl
    (PopArt.wie rfl) _ _ _ rfl (heldGenau_ref (by first | exact hoff5 | (rw [hZ5.1] at hoff5; exact hoff5))).heldIn
  have hoff6 : offen (M6.faeden 1).spur = [()] := by
    rw [hG6.1]
    exact ((Erw.lese _ _ _).offen).trans hoff5
  obtain ⟨M7, s7, hZ7⟩ := w_blatt (P := gegP) (O := refO) (passes := 0) hG6.1 refWriteStAt
    (.ret .empty (by rfl)) refRho7 rfl rfl
    (heldGenau_ref (by first | exact hoff6 | (rw [hG6.1] at hoff6; exact hoff6))).heldIn _ _ rfl
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  -- thread 0 again: return the stale value
  have hfremd7 : ∀ t : Faden, t ≠ 1 → M7.faeden t = M3.faeden t := by
    intro t ht
    rw [rufSchrittG_fremd s7 t ht, rufSchrittG_fremd s6 t ht, rufSchrittG_fremd s5 t ht,
      rufSchrittG_fremd s4 t ht]
  have h7_0 : M7.faeden 0 = _ := (hfremd7 0 (by decide)).trans hZ3.1
  obtain ⟨M8, s8, hG8⟩ := w_rueckP (P := gegP) (O := refO) (passes := 0) h7_0 _ [] rfl
    (PopArt.wie rfl) _ _ _ rfl (heldGenau_ref (by first | exact hoff3 | (rw [hZ3.1] at hoff3; exact hoff3))).heldIn
  have hr8 : RufErreichbarG gegP refO 0 (RufStartG gegP refSp0 gegInit) M8 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ hr3 s4) s5)
      s6) s7) s8
  refine ⟨M8, hr8, _, _, _, _, by rw [hG8.1]; exact List.mem_cons_self, ?_⟩
  refine ens_lies_falsch _ _ _ _ ?_ ?_
  · show (M2.speicher.slots () 0 ()).n = 0
    rw [hZ2.2]
    rfl
  · show (M7.speicher.slots () 0 ()).n = 100
    rw [hZ7.2]
    rfl

end Gabbro.Grammatik
