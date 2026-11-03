/- C16 close-out (3): the machine-indexed evidence fold over GX.

    The fold reads the completed cycle off the machine's per-thread call log:
    a probe push, then the probe's normal pop with the report's verdict, then a
    gate push and its normal return -- unrelated calls preserve it (`torPush`/`zyklusPop`/`checkZyklus`
    skip every other event). Where the cycle is complete the fold yields exactly
    `replayEintrag c r g`; elsewhere it yields nothing: a push, a foreign pop,
    an error-channel return, a missing gate or a mismatched verdict synthesizes
    no completed report.

    G and GX share the thread-log type (`RufFadenG.log : List (RufEreignisF D)`),
    so the fold consults only the log and never the presented memory: the G and
    the GX fold of one thread agree by construction (`falteGX_log`), and the
    folded entry satisfies the goal leg `CheckTreueG` through the discharge
    (`falte_treu`). The deep ghost-history transport (samples at their pushes
    through the C08/C09 shared history) stays the lead's build step; this file
    fixes what that transport must yield at the log. -/
module

public import Grammatik.Kern.Syntax.Satz.Pruefung
public import Grammatik.Kern.Syntax.Satz.PruefungAbschluss
public import Grammatik.Kern.Syntax.Satz.PruefungReplay
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Herkunft
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Export
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T1
public import Grammatik.Zielsatz.Kern.Spec.Teil4

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Falte

variable [DecidableEq D.Fn]

/-- Match the selected gate activation's normal return, counting nested frames.
    An error return leaves the Duty pending; a later unrelated normal return
    cannot turn that failed activation into a successful consumption. -/
def torAbschluss (g : D.Fn) : Nat → List (RufEreignisF D) → Bool
  | _, [] => false
  | depth, .eintritt _ _ _ :: rest => torAbschluss g (depth + 1) rest
  | 0, .rueck f _ _ _ _ :: _ => decide (f = g)
  | 0, .why _ _ _ _ _ :: _ => false
  | depth + 1, .rueck _ _ _ _ _ :: rest => torAbschluss g depth rest
  | depth + 1, .why _ _ _ _ _ :: rest => torAbschluss g depth rest

/-- An admitted gate activation completes normally. Merely entering a gate,
    or returning through its foreign error channel, consumes no report. -/
def torPush (g : D.Fn) : List (RufEreignisF D) → Bool
  | [] => false
  | .eintritt f _ _ :: rest =>
    (decide (f = g) && torAbschluss g 0 rest) || torPush g rest
  | _ :: rest => torPush g rest

/-- A foreign gate's error channel never completes its activation. -/
theorem torAbschluss_fehler (g : D.Fn) (rho : Env D (D.params g))
    (reason : Fin (D.gruende g)) (s0 s1 : World D)
    (rest : List (RufEreignisF D)) :
    torAbschluss g 0 (.why g rho reason s0 s1 :: rest) = false := rfl

/-- The probe pops with the report's verdict and a gate push follows: the
    report a caller receives is the one the callee produced, consumed once. -/
def zyklusPop (c : CheckDecl D) (r : CheckReport) (g : D.Fn) :
    List (RufEreignisF D) → Bool
  | [] => false
  | ev :: rest =>
    (decide (rueckUrteil c ev = some r.urteil) && torPush g rest) ||
      zyklusPop c r g rest

/-- The completed cycle in the log: the probe pushes, then pops with the
    report's verdict, then a gate pushes. -/
def checkZyklus (c : CheckDecl D) (r : CheckReport) (g : D.Fn) :
    List (RufEreignisF D) → Bool
  | [] => false
  | .eintritt f _ _ :: rest =>
    (decide (f = c.probe) && zyklusPop c r g rest) || checkZyklus c r g rest
  | _ :: rest => checkZyklus c r g rest

/-- The machine-indexed fold: the consumed evidence entry where the log shows
    the completed cycle, nothing elsewhere. -/
def falteEvidenz (c : CheckDecl D) (r : CheckReport) (g : D.Fn)
    (log : List (RufEreignisF D)) : Option (CheckEvidenz D) :=
  if checkZyklus c r g log then some (replayEintrag c r g) else none

/-- The fold over a GX machine's thread: the same log, the same entry. -/
def falteGX (M : RufMaschineG D) (t : Faden) (c : CheckDecl D)
    (r : CheckReport) (g : D.Fn) : Option (CheckEvidenz D) :=
  falteEvidenz c r g (M.faeden t).log

/-- The GX fold reads only the thread log: G and GX agree by construction,
    whatever the presented memory answered in between. -/
theorem falteGX_log (M : RufMaschineG D) (t : Faden) (c : CheckDecl D)
    (r : CheckReport) (g : D.Fn) :
    falteGX M t c r g = falteEvidenz c r g (M.faeden t).log := rfl

/-- The empty log folds to nothing: no cycle, no evidence. -/
theorem falte_leer (c : CheckDecl D) (r : CheckReport) (g : D.Fn) :
    falteEvidenz c r g [] = none := rfl

/-- The completed cycle folds to the replayed entry. -/
theorem falte_zyklus (c : CheckDecl D) (r : CheckReport) (g : D.Fn)
    (log : List (RufEreignisF D)) (h : checkZyklus c r g log = true) :
    falteEvidenz c r g log = some (replayEintrag c r g) := by
  unfold falteEvidenz
  rw [h]

/-- The folded entry satisfies the goal leg through the discharge. -/
theorem falte_treu {P : Programm D} {c : CheckDecl D} {r : CheckReport}
    {g : D.Fn} (h : CheckEntladung P c r g) (log : List (RufEreignisF D))
    (hz : checkZyklus c r g log = true) :
    ∃ e, falteEvidenz c r g log = some e ∧
      Zielsatz.CheckTreueG P [c] [e] :=
  ⟨_, falte_zyklus c r g log hz, Parser.Uebersetze.treue_aus_entladung h⟩

end Falte

section FixtureFalte

/-! ## Fixture: the completed negative cycle folds, nothing else does -/

/-- The completed negative cycle folds to the consumed entry. -/
theorem falte_fixture_vollstaendig (rho : Env pruefD (pruefD.params true))
    (rho' : Env pruefD (pruefD.params true))
    (rho'' : Env pruefD (pruefD.params false))
    (s0 s1 : World pruefD) :
    falteEvidenz pruefC1 messBerichtFalsch false
      [.eintritt true rho s0, .rueck true rho' false s0 s1,
        .eintritt false rho'' s1, .rueck false rho'' () s1 s1] =
      some (replayEintrag pruefC1 messBerichtFalsch false) := rfl

/-- Without the gate push nothing folds: a completed report with no admitted
    consumer discharges nothing. -/
theorem falte_ohne_tor (rho : Env pruefD (pruefD.params true))
    (rho' : Env pruefD (pruefD.params true)) (s0 s1 : World pruefD) :
    falteEvidenz pruefC1 messBerichtFalsch false
      [.eintritt true rho s0, .rueck true rho' false s0 s1] = none := rfl

/-- A mismatched verdict folds nothing: the gate receives what the probe
    produced, never a neighboring report. -/
theorem falte_falsches_urteil (rho : Env pruefD (pruefD.params true))
    (rho' : Env pruefD (pruefD.params true))
    (rho'' : Env pruefD (pruefD.params false)) (s0 s1 : World pruefD) :
    falteEvidenz pruefC1 messBerichtFalsch false
      [.eintritt true rho s0, .rueck true rho' true s0 s1,
        .eintritt false rho'' s1, .rueck false rho'' () s1 s1] = none := rfl

/-- A foreign pop folds nothing: another function's answer is not this
    check's report. -/
theorem falte_fremd_pop (rho : Env pruefD (pruefD.params true))
    (rho' : Env pruefD (pruefD.params false))
    (rho'' : Env pruefD (pruefD.params false)) (s0 s1 : World pruefD) :
    falteEvidenz pruefC1 messBerichtFalsch false
      [.eintritt true rho s0, .rueck false rho' () s0 s1,
        .eintritt false rho'' s1, .rueck false rho'' () s1 s1] = none := rfl

/-- The folded negative entry is the consumed one of the goal leg. -/
theorem falte_eintrag_fixture (rho : Env pruefD (pruefD.params true))
    (rho' : Env pruefD (pruefD.params true))
    (rho'' : Env pruefD (pruefD.params false)) (s0 s1 : World pruefD) :
    ∃ e, falteEvidenz pruefC1 messBerichtFalsch false
        [.eintritt true rho s0, .rueck true rho' false s0 s1,
          .eintritt false rho'' s1, .rueck false rho'' () s1 s1] = some e ∧
        Zielsatz.CheckTreueG pruefP [pruefC1] [e] :=
  falte_treu entladung_falsch_zeuge
    [.eintritt true rho s0, .rueck true rho' false s0 s1,
      .eintritt false rho'' s1, .rueck false rho'' () s1 s1] rfl

end FixtureFalte

end Gabbro.Grammatik
