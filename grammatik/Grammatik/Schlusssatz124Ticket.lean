/-
  File:      Grammatik/Schlusssatz124Ticket.lean
  Subject:   STAGE (b) FOR `beispiele/124` WITH THE RUNTIME'S TICKET LOCK
             INLINED (plan `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §7.6
             item 3): `schlusssatz_124_ticket` -- the conclusion of
             `schlusssatz_124`, read in the C memory, on every configuration
             the emitted C reaches when `L_nimm`/`L_gib` are the four
             instructions of `CTicket.lean` and no longer a premise; and
             `ticket_zeuge_124`, a 23-step run in which the two threads
             CONTEND for the lock and the FIFO order of the tickets decides.

  WHAT DISAPPEARS FROM THE PREMISES. `schlusssatz_124` carries
  `LaufzeitC c124 [2,3] st0 K0 LP`, whose second field is
      sperre : ∀ t op h h', LP t op h h' → sperrAbstrakt t op h h'
  -- "the runtime's lock primitive behaves as `sperrAbstrakt`". Here the lock
  is the implementation, not a parameter, and that field is discharged by
  `ticketLP_sperrAbstrakt` / `schrittT_proj`. What REMAINS a premise is
  `FadenStartC` (thread creation at the declared roots: still the runtime's),
  the `forever` budget, and -- for the statement about the REAL machine --
  DRF-SC. Nothing is weakened: `schlusssatz_124` stands as it is, and this is
  its instance at the lock the runtime has.
-/
import Grammatik.CTicket
import Grammatik.Schlusssatz124

namespace Gabbro.Grammatik

namespace K124

open Zielsatz

/-! ## 1. The closing theorem with the lock implementation in place -/

/-- **THE CONCLUSION OF STAGE (b) WITH THE RUNTIME'S TICKET LOCK.** For every
    root assignment the runtime may choose, on EVERY configuration the emitted
    C reaches with `L_nimm`/`L_gib` executed instruction by instruction:
    1. two threads are never inside the lock together (mutual exclusion,
       PROVED from the two counters, not assumed);
    2. while nobody is inside it, `konto_speicher.slots[0].stand ==
       konto_speicher.slots[1].stand` in the C memory (the leg `sperrInv` of
       the goal theorem);
    3. once the `hauptA` thread has returned, `privA_speicher.slots[0].stand
       == 7` (the leg `startEnde`).
    The lock primitive is no longer a premise of any of it. -/
theorem schlusssatz_124_ticket (passes : Nat) (w : Faden → Option Nat) (hw : Wurzeln w)
    (T : KonfT) (hT : ErreichbarT c124 (startT c124 w st0) T) :
    (∀ t u, (0 : Nat) ∈ T.z.haelt t → (0 : Nat) ∈ T.z.haelt u → t = u) ∧
    ((∀ u, (0 : Nat) ∉ T.z.haelt u) → T.k.st.mem (.tab 0) 0 = T.k.st.mem (.tab 0) 4) ∧
    (∀ t, w t = some 2 → T.k.faeden t = .aus → T.k.st.mem (.tab 1) 0 = .int 7) := by
  obtain ⟨hE, hI, hA⟩ := erreichbarT_erreichbarC (startT_inv c124 w st0) (startT_abs c124 w st0) hT
  obtain ⟨hinv, hende⟩ :=
    schlusssatz_124_c passes w hw sperrAbstrakt (fun _ _ _ _ h => h) T.k hE
  exact ⟨fun t u ht hu => ticket_ausschluss hI ht hu, fun hf => hinv (abs_frei hA hf), hende⟩

/-! ## 2. The witness: two threads contending, and the ticket order -/

/-- Thread `1` (`hauptB`) draws the first ticket, thread `0` (`hauptA`) the
    second; the lock is FREE at that moment and thread `0` still cannot take
    it. -/
theorem ticket_zeuge_124 :
    ∃ (ks : Nat → KonfT) (ts : Nat → Faden) (ls : Nat → Etikett),
      LaufT c124 (startT c124 wAB st0) ks ts ls 23 ∧
      -- both threads stand at `L_nimm();`; thread 1 drew ticket 0, thread 0 ticket 1
      (ks 10).z.zieht 1 = some (0, 0) ∧ (ks 10).z.zieht 0 = some (0, 1) ∧
      -- the lock is FREE -- and thread 0 STILL cannot take it: only the ticket
      -- `now` serves may enter, which `sperrAbstrakt` does not say
      (ks 10).k.halter 0 = none ∧ (∀ u, (0 : Nat) ∉ (ks 10).z.haelt u) ∧
      (∀ (ℓ : Etikett) (T' : KonfT), SchrittT c124 (ks 10) 0 ℓ T' →
        T'.k = (ks 10).k ∧ ℓ = .still) ∧
      (∃ h', sperrAbstrakt 0 (.nimm 0) (ks 10).k.halter h') ∧
      -- FIFO: the earlier ticket acquires first
      ts 11 = 1 ∧ ls 11 = .sperre (.nimm 0) ∧ ts 15 = 0 ∧ ls 15 = .sperre (.nimm 0) ∧
      -- while thread 1 is inside, thread 0 spins and nothing of it moves
      (ks 12).z.haelt 1 = [0] ∧ (ks 12).z.haelt 0 = [] ∧
      (∀ (ℓ : Etikett) (T' : KonfT), SchrittT c124 (ks 12) 0 ℓ T' →
        T'.k = (ks 12).k ∧ ℓ = .still) ∧
      -- the end: both returned, nobody inside the lock, and the two legs of
      -- the goal theorem read in the C memory (`schlusssatz_124_ticket`)
      (ks 23).k.faeden 0 = .aus ∧ (ks 23).k.faeden 1 = .aus ∧
      (∀ u, (0 : Nat) ∉ (ks 23).z.haelt u) ∧
      (ks 23).k.st.mem (.tab 0) 0 = (ks 23).k.st.mem (.tab 0) 4 ∧
      (ks 23).k.st.mem (.tab 1) 0 = .int 7 ∧ st0.mem (.tab 1) 0 = .int 0 := by
  -- the C blocks, from related states: thread 1's `setze(70)` runs BEFORE
  -- thread 0's `setze(30)` here (the other order is the witness of
  -- `schlusssatz_124_zeuge`)
  obtain ⟨st1, hx1, hc1, -⟩ := cStore_lauf 2 (CallAt c124.L c124.orc keinXR c124.Pr 1) keinXR
    KTab.privA 0 (by decide) (.lit 7) 7 ρ0 (fun _ => rfl) (by decide) _ st0 corrW_st0 []
    ⟨7, by decide, by decide⟩ rfl
  obtain ⟨st2, hx2, hc2, -⟩ := cStore_lauf 2 (CallAt c124.L c124.orc keinXR c124.Pr 1) keinXR
    KTab.privA 1 (by decide) (.lit 7) 7 ρ0 (fun _ => rfl) (by decide) _ st1 hc1 []
    ⟨7, by decide, by decide⟩ rfl
  obtain ⟨st3, hx3, hc3, -⟩ := cStore_lauf 2 (CallAt c124.L c124.orc keinXR c124.Pr 1) keinXR
    KTab.privB 0 (by decide) (.lit 5) 5 ρ0 (fun _ => rfl) (by decide) _ st2 hc2 []
    ⟨5, by decide, by decide⟩ rfl
  obtain ⟨st4, hx4, hc4⟩ := cSetze_lauf 70 (by decide) _ st3 hc3 ρ0 [] []
    ⟨70, by decide, by decide⟩ rfl
  obtain ⟨st5, hx5, hc5⟩ := cSetze_lauf 30 (by decide) _ st4 hc4 ρ0 [] []
    ⟨30, by decide, by decide⟩ rfl
  have hx6 := cPruefe_lauf _ st5 hc5 ρ0
  -- the run
  have l0 : LaufT c124 (startT c124 wAB st0) (fun _ => startT c124 wAB st0) (fun _ => 0)
      (fun _ => .still) 0 := ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  have l1 := laufT_snoc l0 (SchrittT.rein _ 0 _ _ rfl (SchrittC.teile _ 0 cA0 cRestA1 [] ρ0 rfl))
  have l2 := laufT_snoc l1 (SchrittT.rein _ 0 _ _ rfl
    (SchrittC.block _ 0 cA0 [cRestA1] ρ0 st1 ρ0 rfl rfl hx1))
  have l3 := laufT_snoc l2 (SchrittT.rein _ 0 _ _ rfl (SchrittC.teile _ 0 cA1 cRestA2 [] ρ0 rfl))
  have l4 := laufT_snoc l3 (SchrittT.rein _ 0 _ _ rfl
    (SchrittC.block _ 0 cA1 [cRestA2] ρ0 st2 ρ0 rfl rfl hx2))
  have l5 := laufT_snoc l4 (SchrittT.rein _ 0 _ _ rfl (SchrittC.teile _ 0 cNimm cRestA3 [] ρ0 rfl))
  have l6 := laufT_snoc l5 (SchrittT.rein _ 1 _ _ rfl (SchrittC.teile _ 1 cB0 cRestB1 [] ρ0 rfl))
  have l7 := laufT_snoc l6 (SchrittT.rein _ 1 _ _ rfl
    (SchrittC.block _ 1 cB0 [cRestB1] ρ0 st3 ρ0 rfl rfl hx3))
  have l8 := laufT_snoc l7 (SchrittT.rein _ 1 _ _ rfl (SchrittC.teile _ 1 cNimm cRestB2 [] ρ0 rfl))
  -- thread 1 draws ticket 0, thread 0 ticket 1
  have l9 := laufT_snoc l8 (SchrittT.zieht _ 1 0 [cRestB2] ρ0 0 rfl rfl rfl)
  have l10 := laufT_snoc l9 (SchrittT.zieht _ 0 0 [cRestA3] ρ0 0 rfl rfl rfl)
  -- thread 0 spins: `now` is 0, its ticket is 1
  have l11 := laufT_snoc l10 (SchrittT.dreht _ 0 0 1 rfl (fun h => Nat.noConfusion h))
  -- thread 1's ticket is served
  have l12 := laufT_snoc l11 (SchrittT.tritt _ 1 0 [cRestB2] ρ0 0 0 rfl rfl rfl rfl)
  have l13 := laufT_snoc l12 (SchrittT.rein _ 1 _ _ rfl (SchrittC.teile _ 1 cSetzeB cGib [] ρ0 rfl))
  have l14 := laufT_snoc l13 (SchrittT.rein _ 1 _ _ rfl
    (SchrittC.block _ 1 cSetzeB [cGib] ρ0 st4 ρ0 rfl rfl hx4))
  -- thread 1 releases; `now` becomes 1, which is thread 0's ticket
  have l15 := laufT_snoc l14 (SchrittT.gibt _ 1 1 [] ρ0 0 rfl rfl List.mem_cons_self)
  have l16 := laufT_snoc l15 (SchrittT.tritt _ 0 0 [cRestA3] ρ0 0 1 rfl rfl rfl rfl)
  have l17 := laufT_snoc l16 (SchrittT.rein _ 0 _ _ rfl
    (SchrittC.teile _ 0 cSetzeA cRestA4 [] ρ0 rfl))
  have l18 := laufT_snoc l17 (SchrittT.rein _ 0 _ _ rfl
    (SchrittC.block _ 0 cSetzeA [cRestA4] ρ0 st5 ρ0 rfl rfl hx5))
  have l19 := laufT_snoc l18 (SchrittT.rein _ 0 _ _ rfl (SchrittC.teile _ 0 cGib cPruefe [] ρ0 rfl))
  have l20 := laufT_snoc l19 (SchrittT.gibt _ 0 1 [cPruefe] ρ0 0 rfl rfl List.mem_cons_self)
  have l21 := laufT_snoc l20 (SchrittT.rein _ 1 _ _ rfl (SchrittC.ende _ 1 ρ0 rfl))
  have l22 := laufT_snoc l21 (SchrittT.rein _ 0 _ _ rfl
    (SchrittC.block _ 0 cPruefe [] ρ0 _ ρ0 rfl rfl hx6))
  have l23 := laufT_snoc l22 (SchrittT.rein _ 0 _ _ rfl (SchrittC.ende _ 0 ρ0 rfl))
  -- "nobody stands inside the lock" is read off the abstraction, which the
  -- projection keeps in step with the two counters
  have hA10 := (erreichbarT_erreichbarC (startT_inv c124 wAB st0) (startT_abs c124 wAB st0)
    (laufT_erreichbar l23 10 (by omega))).2.2
  have hA23 := (erreichbarT_erreichbarC (startT_inv c124 wAB st0) (startT_abs c124 wAB st0)
    (laufT_erreichbar l23 23 (Nat.le_refl 23))).2.2
  refine ⟨_, _, _, l23, rfl, rfl, rfl, ?_,
    spinnt_nur rfl (fun h => Nat.noConfusion h) (fun K hK => absurd hK List.not_mem_nil),
    ⟨_, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl,
    spinnt_nur rfl (fun h => Nat.noConfusion h) (fun K hK => absurd hK List.not_mem_nil),
    rfl, rfl, ?_, ?_, ?_, rfl⟩
  · intro u hu
    have h1 : (none : Option Faden) = some u := (hA10 0 u).mpr hu
    cases h1
  · intro u hu
    have h1 : (none : Option Faden) = some u := (hA23 0 u).mpr hu
    cases h1
  · refine (schlusssatz_124_ticket 0 wAB wAB_wurzeln _
      (laufT_erreichbar l23 23 (Nat.le_refl 23))).2.1 (fun u hu => ?_)
    have h1 : (none : Option Faden) = some u := (hA23 0 u).mpr hu
    cases h1
  · exact (schlusssatz_124_ticket 0 wAB wAB_wurzeln _
      (laufT_erreichbar l23 23 (Nat.le_refl 23))).2.2 0 rfl rfl

end K124

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.K124.schlusssatz_124_ticket
#print axioms Gabbro.Grammatik.K124.ticket_zeuge_124
