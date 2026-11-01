/-
  File:      Grammatik/RennfreiVoll.lean
  Subject:   DATA-RACE FREEDOM ON THE CALL MACHINE G, FULL FORM -- reads
             included, any distance, the release/acquire pair named by run
             index.

  `RennfreiG.lean` covers adjacent double writes (`rennfrei_g_nah`). Here:

  * An ACCESS of a step to a carrier `c` is a recorded access event on the
    acting thread's trace delta (`zugriffe`, read or write: every read of the
    semantics goes through `World.lese`, which records `zugriff t false Λ h`
    for every carrier of the read footprint; every write records its event)
    or a change of `c` in shared memory.
  * One trace invariant over every reachable machine (`SpurInv`): every
    thread trace is consistent (`Konsistent`) and every access event on it is
    good (`Ereignis.gut`: it carries its carrier's guards in its static `Λ`,
    and that `Λ`'s locks are held). It holds at the start and every step
    keeps it (`schritt_delta`, one case analysis over the 70 step rules).
  * From it: the acting thread holds every lock guard of every carrier its
    step accesses, before the step and after it (`zugriff_haelt`).
  * The ordering lemma over run indices (`sperre_ordnet`): two different
    threads holding one lock at steps `i < j` -- the first releases it at
    some step `r`, the second acquires it at some step `a`, with
    `i < r < a < j`, both steps recorded as `gibt L` / `nimmt L` events.
  * The theorem `rennfrei_g_voll` and the race notion `DatenRasse` (two
    accesses by different threads, at least one a write, NOT ordered by a
    release/acquire of a guard) with `keine_datenrasse_g`.
-/
module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll.Teil1
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll.Teil2
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll.Teil3
