/-
  Audit 46, probe F3: `kette_aus_deckung` forwards its premise (rule 4a).

  Claim (pattern a, filed as high severity for the N-thread reading): the
  N-thread theorem `kette_aus_deckung` (KetteMehrfadenC.lean:879-895) concludes
  `∃ J, J.welten = M.welten ∧ J.l = M.lauf ∧ J.schrittFaden = tr ∧ ...` from
  `hDeck : KettenSpurDeckung ...`, whose definiens at `(M, pc, tr)` is
  `∃ Jx, Jx.welten = Mx.welten ∧ Jx.l = Mx.lauf ∧ Jx.schrittFaden = trx ∧
   Jx.faeden = mem ∧ Jx.code = code ∧ ...`. Its proof is one application
  (`obtain ... := hDeck M pc tr hReach htr`), discarding only the trailing
  membership leg. The conclusion is the premise instantiated -- a forwarding.

  Demonstrated below WITHOUT re-proving anything about chains: the exact
  logical shape -- from `∀ x, ∃ y, P x y` conclude `∃ y, P a y` by application.
  The audit point is structural: all five kept legs travel argument-for-argument
  from the witness `Jx` to the goal. The file docstring is HONEST about this
  ("the N-thread conclusion follows by direct application", line 873), so this
  is (a) disclosed, exactly the case the premise-probe calls FORWARDED
  (only the restated premise feeds the conclusion; cf. MUSE-REPORT-23 F6, where
  the same honesty still earned a row).

  Contrast: `kette_zwei_aus_lauf` genuinely DERIVES the equations by induction
  (worlds/run/trace by construction at each level) -- not challenged here.
-/
import Grammatik.KetteMehrfadenC

namespace Gabbro.Grammatik

open Gabbro.Grammatik

variable {D : Deklaration}

/-- The forwarding shape of `kette_aus_deckung`: the conclusion is the premise
    applied at the end machine, with one carried leg dropped. Every binder is
    read by the goal. -/
theorem audit46_forwarding_shape
    (J : Type) (Welten : J → List (World D)) (Lauf : J → Lauf D)
    (Schritte : J → List Faden) (codeJ : J → Faden → D.Fn)
    (M : GenMaschine D) (tr : List Faden) (mem : List Faden) (code : Faden → D.Fn)
    (Jx2mem : J → List Faden → Prop)
    (hDeck : ∀ (Mx : GenMaschine D) (trx : List Faden),
      ∃ Jx : J, Welten Jx = Mx.welten ∧ Lauf Jx = Mx.lauf ∧ Schritte Jx = trx ∧
        Jx2mem Jx mem ∧ codeJ Jx = code) :
    ∃ Jx : J, Welten Jx = M.welten ∧ Lauf Jx = M.lauf ∧ Schritte Jx = tr ∧
      Jx2mem Jx mem ∧ codeJ Jx = code := by
  obtain ⟨Jx, hJxw, hJxl, hJxsf, hJxf, hJxcode⟩ := hDeck M tr
  exact ⟨Jx, hJxw, hJxl, hJxsf, hJxf, hJxcode⟩

#check @Gabbro.Grammatik.kette_aus_deckung

/-
CUTS:
- The shape theorem above is the forwarding skeleton, not a copy of the file
  proof: it pins the argument-for-argument travel on a minimal signature.
- `htr : PCSpur ...` and `hReach : PCReach ...` are load-bearing only as the
  two arguments that TYPE the `hDeck` application; no frame, witness, routing,
  or member arithmetic is consumed -- the file docstring says so itself.
- Whether `KettenSpurDeckung` is DISCHARGEABLE in general (the booked N-thread
  induction) is out of scope; the finding is that `kette_aus_deckung` itself
  derives nothing beyond restating it.
-/
#print axioms Gabbro.Grammatik.audit46_forwarding_shape
