/-
  File:      Grammatik/Speichermodell/MaschineW.lean
  Subject:   MACHINE W -- machine G over the WEAK memory of `Sicht.lean` (Opus agent B,
             2026-09-26). Definitions, and `w_aus_g`: every run of G is a run of W.

  WHAT W IS. A state of W is a state `g` of machine G plus the weak memory: a HISTORY of
  messages per carrier (tables and globals, plain and `atomic` alike), a VIEW per thread and a
  view per lock. One step of thread `u`:
  * the thread is PRESENTED a memory `σ`: at every carrier its step READS (a recorded read
    event, `LiestG`), `σ` holds the value of SOME message of that carrier at or above `u`'s
    view (`Lesbar` -- not necessarily the newest: that is the weakness); at every carrier it
    does not read, `σ` is G's memory;
  * machine G takes the step on the presented memory (`RufSchrittG` from `mitSpeicher W.g σ`);
  * every carrier the step WRITES (`SchreibG`: a write event or a changed value) gets a new
    message at a FRESH timestamp strictly above the thread's view (`Frisch`), carrying the new
    value and -- for a release write of a `release`/`acquire`/`seq` atomic -- the thread's view;
    G's memory takes the written carriers from the step and keeps every other one;
  * views: a read raises the view to the message (an acquire read joins the message's view,
    `beitrag`), a lock the step TAKES joins the lock's view (`locksicht`), a write sets the
    view to its timestamp, a lock the step RELEASES joins the thread's final view.
  Plain carriers are modelled like relaxed atomics. For a race-free program that is an
  over-approximation of C11 (a race-free plain read reads the happens-before-latest write,
  which the views keep readable); for a racy one C11 is undefined anyway. The order of an
  atomic is the argument `ord` (the source declaration's; the exporter does not carry it, so
  every theorem about W quantifies over all of them, `relaxed` everywhere included).

  WHY THE WEAK CHOICE SITS AT THE RECORDED READS. What a step of G reads is what it records
  (`OrteInvG`, `schritt_ev`: every read event is a footprint carrier of the acting function);
  race freedom (`RennfreiBis`) is stated over the same records. A step that depended on a
  carrier without recording it would already escape the race leg of G. So "the thread sees an
  old value exactly where it reads" is the reading G already makes for the recorded reads.
  NOT for the unrecorded ones (corrected after the Spec-diff verdict of 2026-09-26, F1): the
  answers of foreign code and axioms (`Orakel.wirkt`), register reads (`O.regLies`) and the
  visibility of `awaits` (`O.sichtbar`) read memory without recording it, and at every carrier
  a step does not record W presents G's memory -- the last executed write. So W makes these
  reads sequentially consistent. That the foreign side, the device and the `awaits` hand-off
  see that memory is a NAMED ASSUMPTION of the reading (assumption (5) in Zielsatz/Spec.lean),
  the part of the old "the hardware is DRF-SC" the DRF theorem does not discharge.

  GRANULARITY. A step of W is one coarse step of G: nothing interleaves inside it, every read
  of the step is checked against the pre-step view, and a release message carries the view
  before the step's own writes. The last two make W weaker than C11 (safe); the first is the
  reading "G is the meaning of the C". "W over-approximates RC11" holds at G's step
  granularity, jointly with that reading, not on its own.

  PROVED HERE: `w_aus_g` -- every machine G reaches is the G-part of a machine W reaches (W
  admits every SC behaviour: always write above everything and read the newest). The other
  direction for accepted programs is the DRF theorem, `Speichermodell/DRF.lean`.
-/
module

public import Grammatik.Speichermodell.Maschine.MaschineW.Teil1
public import Grammatik.Speichermodell.Maschine.MaschineW.Teil2
