/-
  File:      Grammatik/X86/AufrufOpt.lean
  Subject:   CALL-LOG OBLIGATIONS FOR SOURCE INLINING (lane 310, wave-A follow-up).

  Selective inlining (IR-VALIDIERUNG.md §3.4) removes a physical call but must
  NOT drop the logged call, its contracts or the `FolgeG` order leg: the
  certificate carries a GHOST-EVENT reconstruction -- the inlined execution
  re-emits the callee entry/return pair (identity, actual arguments, actual
  result/reason, entry/return worlds) in source call-log order. This file
  states that obligation over the REAL source model (machine-G call logs
  `RufEreignisF`, `rufAt`, `RufSchrittG`; order `FolgeLog`/`FolgeG`) and proves
  the generic reconstruction lemmas. No new source syntax, no Spec change,
  no fake IR: every event below is a `RufEreignisF` with actual values.
-/
import Grammatik.RufMaschineG
import Grammatik.Folge

namespace Gabbro.Grammatik.X86

variable {D : Deklaration}

/-- A ghost answer of an inlined call: the value case or the reason channel. -/
inductive GeistAntwort (D : Deklaration) (g : D.Fn) where
  | ok (v : ErgVal D (D.erg g)) (s1 : World D)
  | grund (r : Fin (D.gruende g)) (s1 : World D)

/-- The ghost pair of one inlined call, newest first: return over entry. -/
def geistPaar (g : D.Fn) (rho : Env D (D.params g)) (s0 : World D) :
    GeistAntwort D g → List (RufEreignisF D)
  | .ok v s1 =>
    [RufEreignisF.rueck g rho v s0 s1, RufEreignisF.eintritt g rho s0]
  | .grund r s1 =>
    [RufEreignisF.grund g rho r s0 s1, RufEreignisF.eintritt g rho s0]

/-- The ghost pair has exactly two events. -/
theorem geistPaar_laenge (g : D.Fn) (rho : Env D (D.params g)) (s0 : World D)
    (a : GeistAntwort D g) : (geistPaar g rho s0 a).length = 2 := by
  cases a <;> rfl

/- CUTS:
  - Ghost-pair order (`FolgeLog`) preservation: stated next (`geistRekon_folge`).
  - Every-`RufSchrittG`-step log classification: open (`rufSchrittG_logSchritt`).
  - `rufAt` contract-duty extraction (entry `requires`): open.
  - Joint non-degenerate source/table-write witness: open.
-/

#print axioms geistPaar_laenge

end Gabbro.Grammatik.X86
