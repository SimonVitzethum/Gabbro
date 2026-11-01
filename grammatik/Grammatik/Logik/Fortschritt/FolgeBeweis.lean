/-
  File:      Grammatik/FolgeBeweis.lean
  Subject:   THE ORDER OF EFFECTS IS CARRIED BY MACHINE G (OFFEN O1, Opus agent G,
             2026-09-26): `folgeG_erreichbar`.

  For every order specification `Φ` a program passes (`FolgeOk`, Folge.lean), every reachable
  machine of G has, in every thread's call log, every entry of a `ruf` function and every
  return of an `ende` function DIRECTLY behind a return of a `vor` function, and a finished
  thread whose start function is an `ende` function ended directly behind one.

  THE INVARIANT (`FolgeInvG`), per thread:
  * the head frame's residue passes the check with the armed bit read off the log
    (`Armiert`: the newest log event is a return of a `vor` function);
  * every suspended caller's residue passes it with the bit `vor g` of the callee `g` above it
    (`FolgeStapel`): that is the bit the caller resumes with when `g` pops;
  * the log is ordered (`FolgeLog`).
  Every rule of G keeps it (`folgeInvG_schritt`): a head-local step logs nothing and moves the
  residue along the checked text (a leaf keeps the bit, an unfold starts a sub-block unarmed,
  which the check allows since it is monotone in the bit, `fB_mono`); a push logs the entry
  of a callee, which the residue demanded armed if the callee is ordered, and suspends the
  caller at the bit `vor g`; a pop logs the return of the head function, which the residue
  demanded armed if it is ordered, and resumes the caller at exactly the bit its suspended
  residue was checked at.
-/
module

public import Grammatik.Logik.Fortschritt.FolgeBeweis.Teil1
public import Grammatik.Logik.Fortschritt.FolgeBeweis.Teil2
