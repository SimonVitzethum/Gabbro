/-
  File:      Grammatik/RufLogikZeuge.lean
  Subject:   **WITNESSES** for the handler congruence and its two consumers,
             on the two chains of the corpus -- non-degenerate, on programs
             that do work.

  1. `tiefe_zeuge_104` -- on the 104 chain (`einzahlen(k, 0, 7)` from the zero
     state, which moves the slot `0 -> 100`): at depth `0` the call IS the
     `abstieg` residue, at depth `2` it returns and moves the slot, and from
     depth `2` upward it is the SAME outcome at every depth. So both
     disjuncts of `rufAt_tiefer` are inhabited on one program, and
     `rufAt_stabil_ab` is applied to an outcome that is not `ok` by accident.

  2. `nurAbstieg_zeuge_104` -- clause 4e(ii) on the LOCKED chain, and this is
     the witness the frame theorem was built for. 104 declares the lock `M`
     and both its functions `requires Held(M)`, so
     `Signatur.anfang D4 (D4.signatur ein4)` names `Res.held m4` -- and the
     world the chain's own witness runs from holds NOTHING
     (`heldB_faellt_104`). At that world `rufAt_gut` (Satz.lean) says
     nothing at all, and `rufAt_treu` (RahmenTreu.lean) gives the frame
     anyway. Non-degenerate three times over: the entry world fails `HeldB`;
     the run RETURNS and moves the slot `0 -> 100`; and the frame is read on
     the function that may NOT write (`lies`, `D4.schreibt lies4 t4 = false`)
     at a world whose slot is `100`, so "the frame holds" forbids something
     that could have happened.

  3. `nurAbstieg_zeuge_108` -- the same clause on the lock-free chain, where
     it was already unconditional before the frame theorem. Kept as the
     control: 108's own call RETURNS (`kette_108_zeuge`), so the statement is
     not about an empty set of runs.
-/
import Grammatik.Kette104Satz
import Grammatik.Kette108

namespace Gabbro.Grammatik.Kette104

/-- **WITNESS for `rufAt_tiefer` / `rufAt_stabil_ab` on the 104 chain.** -/
theorem tiefe_zeuge_104 :
    rufAt P4 O4 0 0 ein4 (sp4.welt []) rho7 = .logik (.abstieg ein4) ∧
    (∃ σ' : World D4, rufAt P4 O4 0 2 ein4 (sp4.welt []) rho7 = .ok σ' () ∧
      ((sp4.welt []).slots t4 0 f4).n = 0 ∧ (σ'.slots t4 0 f4).n = 100) ∧
    (∀ k : Nat, rufAt P4 O4 0 (2 + k) ein4 (sp4.welt []) rho7 =
      rufAt P4 O4 0 2 ein4 (sp4.welt []) rho7) := by
  have hR : rufAt P4 O4 0 2 ein4 (sp4.welt []) rho7 = .ok _ () := rfl
  refine ⟨rfl, ⟨_, hR, rfl, rfl⟩, ?_⟩
  exact rufAt_stabil_ab P4 O4 0 2 ein4 (sp4.welt []) rho7 (fun g h => by rw [hR] at h; cases h)

/-- Gabbro's arguments of `lies(k, 0)`. -/
def rhoL : Env D4 (D4.params lies4) :=
  .cons () (.cons ⟨0, by decide, by decide⟩ .nil)

/-- The world `einzahlen(k, 0, 7)` leaves behind, from the zero state: its
    slot `0` stands at `100` and it holds no lock. -/
def wEin : World D4 :=
  match rufAt P4 O4 0 2 ein4 (sp4.welt []) rho7 with
  | .ok σ' _ => σ'
  | _ => sp4.welt []

/-- **THE PREMISE OF `rufAt_gut` FAILS AT THE CHAIN'S OWN ENTRY WORLD.**
    104's functions `requires Held(M)`, so the static resource context of
    the entry names `Res.held m4`; the zero world holds no lock. Everything
    `Satz.lean` proves about a call is silent here -- and clause 4e(ii)
    below is not. -/
theorem heldB_faellt_104 :
    ¬ HeldB (D4.signatur ein4).boden (Signatur.anfang D4 (D4.signatur ein4))
        (sp4.welt []).haelt := by
  intro h
  have hm : Res.held (D := D4) m4 ∈ Signatur.anfang D4 (D4.signatur ein4) := by decide
  exact absurd (h.1 m4 hm) (by decide)

/-- **WITNESS for clause 4e(ii) of `schlusssatz` on the LOCKED chain 104.**
    No call of 104's program ends in a `logik` outcome other than an
    `abstieg`, at any depth, any budget, any world and any arguments meeting
    the callee's `requires` -- with NO hypothesis about the frame, which is
    the point: the frame comes from `rufAt_rahmenTreu`, and the chain's own
    entry world does not meet `HeldB` (`heldB_faellt_104`), so `rufAt_gut`
    cannot supply it. -/
theorem nurAbstieg_zeuge_104 :
    (∀ (passes n : Nat) (f : D4.Fn) (σ : World D4) (ρG : Env D4 (D4.params f)) (e : Logik D4),
      ReqAmEintritt P4 f σ ρG → rufAt P4 O4 passes n f σ ρG = .logik e →
        ∃ h : D4.Fn, e = .abstieg h) ∧
    (∀ n : Nat, RufRahmenTreu P4 (rufAt P4 O4 0 n)) ∧
    ¬ HeldB (D4.signatur ein4).boden (Signatur.anfang D4 (D4.signatur ein4))
        (sp4.welt []).haelt ∧
    (rufAt P4 O4 0 2 ein4 (sp4.welt []) rho7 = .ok wEin () ∧
      (wEin.slots t4 0 f4).n = 100 ∧
      D4.schreibt lies4 t4 = false ∧
      ∃ (σ'' : World D4) (v : ErgVal D4 (D4.erg lies4)),
        rufAt P4 O4 0 1 lies4 wEin rhoL = .ok σ'' v ∧
        Rahmen (D4.schreibt lies4) (D4.gschreibt lies4) wEin σ'' ∧
        offen σ''.spur = offen wEin.spur ∧
        (σ''.slots t4 0 f4).n = 100) := by
  have hL : rufAt P4 O4 0 1 lies4 wEin rhoL = .ok _ _ := rfl
  have hframe : ∀ n : Nat, RufRahmenTreu P4 (rufAt P4 O4 0 n) :=
    rufAt_rahmenTreu P4 O4 0 (gutO_treuO hw4.1)
  refine ⟨?_, hframe, heldB_faellt_104, rfl, rfl, rfl, _, _, hL, ?_, ?_, rfl⟩
  · exact (schlusssatz kette_104 O4 hw4 tvOrc tvXR tvXR_funktional
      (fun f => CallAt EL4.lay tvOrc tvXR (kProg zert104) 2 (fnNr f)) (fun _ => 2)
      (fun _ _ _ _ _ h => h) (speicherR E4.sp0) init4 start4).2.2.2.2.2.2.2.1.2
  · exact (hframe 1 lies4 wEin rhoL _ _ hL).1
  · exact (hframe 1 lies4 wEin rhoL _ _ hL).2

#print axioms Gabbro.Grammatik.Kette104.tiefe_zeuge_104
#print axioms Gabbro.Grammatik.Kette104.heldB_faellt_104
#print axioms Gabbro.Grammatik.Kette104.nurAbstieg_zeuge_104

end Gabbro.Grammatik.Kette104

namespace Gabbro.Grammatik.Kette108

/-- **WITNESS for `rufAt_nurAbstieg` / clause 4e(ii) on 108**, the lock-free
    control: no call of 108's program ends in a `logik` outcome other than an
    `abstieg`, at any depth, at any entry meeting the callee's `requires`.
    Non-degenerate: 108's own call returns (`kette_108_zeuge`). -/
theorem nurAbstieg_zeuge_108 :
    (∀ (passes n : Nat) (f : D8.Fn) (σ : World D8) (ρG : Env D8 (D8.params f)) (e : Logik D8),
      ReqAmEintritt P8 f σ ρG → rufAt P8 O8 passes n f σ ρG = .logik e →
        ∃ h : D8.Fn, e = .abstieg h) ∧
    (∃ (σ' : World D8) (v : ErgVal D8 (D8.erg a8)),
      rufAt P8 O8 0 1 a8 (sp8.welt []) .nil = .ok σ' v) := by
  refine ⟨?_, ?_⟩
  · exact (schlusssatz kette_108 O8 hw8 tvOrc tvXR tvXR_funktional
      (fun f => CallAt EL8.lay tvOrc tvXR (kProg zert108) 1 (fnNr f)) (fun _ => 1)
      (fun _ _ _ _ _ h => h) (speicherR E8.sp0) init8 start8).2.2.2.2.2.2.2.1.2
  · exact ⟨_, _, rfl⟩

#print axioms Gabbro.Grammatik.Kette108.nurAbstieg_zeuge_108

end Gabbro.Grammatik.Kette108
