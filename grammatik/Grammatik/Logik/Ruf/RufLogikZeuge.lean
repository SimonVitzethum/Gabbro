/-
  File:      Grammatik/RufLogikZeuge.lean
  Subject:   **WITNESSES** for the handler congruence and its two consumers, on the two
              corpus units `104` and `108` -- non-degenerate, on programs that do work.

  1. `tiefe_zeuge_104` -- on unit 104 (`einzahlen(k, 0, 7)` from the zero state, which moves
     the slot `0 -> 100`): at depth `0` the call IS the `abstieg` residue, at depth `2` it
     returns and moves the slot, and from depth `2` upward it is the SAME outcome at every
     depth. So both disjuncts of `rufAt_tiefer` are inhabited on one program, and
     `rufAt_stabil_ab` is applied to an outcome that is not `ok` by accident.

  2. `nurAbstieg_zeuge_104` -- `rufAt_nurAbstieg` on the LOCKED unit. 104 declares the lock
     `M` and both its functions `requires Held(M)`, so `Signatur.anfang D4 (D4.signatur ein4)`
     names `Res.held m4` -- and the world the witness runs from holds NOTHING
     (`heldB_faellt_104`). At that world the generic frame theorem is honestly silent:
     `rufAt_treu` (RahmenTreu.lean) gives the frame only where the entry discipline
     holds, and part 4 carries that discipline as a premise (the gap closed here, not
     by luck). The witness states the discharge over disciplined entries, the generic
     frame half `RufRahmenTreu` (discharged by `scopes4`), the non-vacuity of the
     premise, and the concrete runs (the slot moves `0 -> 100`, `lies` returns it).

  3. `nurAbstieg_zeuge_108` -- the same on the lock-free unit, where the discipline
     premise is discharged by the empty held set. Kept as the control: 108's own call
     RETURNS, so the statement is not about an empty set of runs.

  (The closing theorem of the deleted C correspondence chain supplied `rufAt_nurAbstieg`'s
  premise "no `locks` block" through the correspondence certificate; here it is decided on the
  parsed bodies. Tag `archiv/c-emitter-2026-10-17` holds the chain.)
-/
module
public import Grammatik.Korpus.Programme.Einheit104
public import Grammatik.Korpus.Programme.Einheit108
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section


namespace Gabbro.Grammatik.Einheit104

open Gabbro.Grammatik Zielsatz

/-- **WITNESS for `rufAt_tiefer` / `rufAt_stabil_ab` on unit 104.** -/
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

/-- **THE PREMISE OF THE FRAME THEOREM FAILS AT THE UNIT'S OWN ENTRY WORLD.**
    104's functions `requires Held(M)`, so the static resource context of
    the entry names `Res.held m4`; the zero world holds no lock. -/
theorem heldB_faellt_104 :
    ¬ HeldB (D4.signatur ein4).boden (Signatur.anfang D4 (D4.signatur ein4))
        (sp4.welt []).haelt := by
  intro h
  have hm : Res.held (D := D4) m4 ∈ Signatur.anfang D4 (D4.signatur ein4) := by decide
  exact absurd (h.1 m4 hm) (by decide)

/-- **The scope discipline holds on 104**: neither body unwinds a scope
    (both end in plain returns), so the static check computes to true. -/
theorem scopes4 : ScopesOkProg P4 := by
  intro f
  rcases fn_zwei f with e | e <;> subst e
  · rw [rumpf_ein4]
    rfl
  · rw [rumpf_lies4]
    rfl

/-- **WITNESS for `rufAt_nurAbstieg` on the LOCKED unit 104.**
    No call of 104's program ends in a `logik` outcome other than an `abstieg`, at any depth,
    any budget, any world meeting the callee's entry discipline and any arguments meeting
    the callee's `requires` -- with NO hypothesis about the frame beyond the discipline,
    which `rufAt_treu` turns into the frame. The entry discipline is a real restriction
    (`heldB_faellt_104`); the runs below show the statement is about real work. -/
theorem nurAbstieg_zeuge_104 :
    (∀ (passes n : Nat) (f : D4.Fn) (σ : World D4) (ρG : Env D4 (D4.params f)) (e : Logik D4),
      HeldB (D4.signatur f).boden (Signatur.anfang D4 (D4.signatur f)) σ.haelt →
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
        (σ''.slots t4 0 f4).n = 100) := by
  have hL : rufAt P4 O4 0 1 lies4 wEin rhoL = .ok _ _ := rfl
  have hframe : ∀ n : Nat, RufRahmenTreu P4 (rufAt P4 O4 0 n) :=
    rufAt_rahmenTreu P4 O4 0 (gutO_treuO hw4.1) scopes4
  refine ⟨?_, hframe, heldB_faellt_104, rfl, rfl, rfl, _, _, hL, rfl⟩
  · intro passes n f σ ρG e hh hq hl
    obtain ⟨U, hU⟩ : ∃ U : Umwelt D4, HavocOk E4.S U :=
      ⟨_, havocOk_misch_lokal nutzer4.logik.2.1 (fun _ _ => E4.sp0)
        (fun L _ => nutzer4.start.sperren L)⟩
    have hlocks : ∀ g : D4.Fn, (P4.rumpf g).ohneLocks = true := by
      intro g
      rcases fn_zwei g with e | e <;> subst e
      · rw [rumpf_ein4]; rfl
      · rw [rumpf_lies4]; rfl
    exact rufAt_nurAbstieg P4 O4 passes E4.Q E4.S U (gutO_treuO hw4.1) hw4.2.1 hw4.2.2 hU
      hlocks (fun g => (nutzer4.logik.1 passes g).1) (fun g => (nutzer4.logik.1 passes g).2.1)
      scopes4 n f σ ρG e hh hq hl

#print axioms Gabbro.Grammatik.Einheit104.tiefe_zeuge_104
#print axioms Gabbro.Grammatik.Einheit104.heldB_faellt_104
#print axioms Gabbro.Grammatik.Einheit104.nurAbstieg_zeuge_104

end Gabbro.Grammatik.Einheit104

namespace Gabbro.Grammatik.Einheit108

open Gabbro.Grammatik Zielsatz

/-- **The scope discipline holds on 108**: no body unwinds a scope. -/
theorem scopes8 : ScopesOkProg P8 := by
  intro f
  rcases fn_zwei f with e | e <;> subst e
  · rw [rumpf_a8]; rfl
  · rw [rumpf_c8]; rfl

/-- **WITNESS for `rufAt_nurAbstieg` on 108**, the lock-free control: no call of 108's program
    ends in a `logik` outcome other than an `abstieg`, at any depth, at any entry meeting
    the callee's discipline and `requires`. Non-degenerate: 108's own call returns. -/
theorem nurAbstieg_zeuge_108 :
    (∀ (passes n : Nat) (f : D8.Fn) (σ : World D8) (ρG : Env D8 (D8.params f)) (e : Logik D8),
      HeldB (D8.signatur f).boden (Signatur.anfang D8 (D8.signatur f)) σ.haelt →
      ReqAmEintritt P8 f σ ρG → rufAt P8 O8 passes n f σ ρG = .logik e →
        ∃ h : D8.Fn, e = .abstieg h) ∧
    (∃ (σ' : World D8) (v : ErgVal D8 (D8.erg a8)),
      rufAt P8 O8 0 1 a8 (sp8.welt []) .nil = .ok σ' v) := by
  refine ⟨?_, ?_⟩
  · intro passes n f σ ρG e hh hq hl
    obtain ⟨U, hU⟩ : ∃ U : Umwelt D8, HavocOk E8.S U :=
      ⟨_, havocOk_misch_lokal nutzer8.logik.2.1 (fun _ _ => E8.sp0)
        (fun L _ => nutzer8.start.sperren L)⟩
    have hlocks : ∀ g : D8.Fn, (P8.rumpf g).ohneLocks = true := by
      intro g
      rcases fn_zwei g with e | e <;> subst e
      · rw [rumpf_a8]; rfl
      · rw [rumpf_c8]; rfl
    exact rufAt_nurAbstieg P8 O8 passes E8.Q E8.S U (gutO_treuO hw8.1) hw8.2.1 hw8.2.2 hU
      hlocks (fun g => (nutzer8.logik.1 passes g).1) (fun g => (nutzer8.logik.1 passes g).2.1)
      scopes8 n f σ ρG e hh hq hl
  · exact ⟨_, _, rfl⟩

#print axioms Gabbro.Grammatik.Einheit108.nurAbstieg_zeuge_108

end Gabbro.Grammatik.Einheit108
