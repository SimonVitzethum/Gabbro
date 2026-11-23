/-
  File:      Grammatik/Zielsatz/Ideal/Prototyp/Root.lean
  Subject:   The PROTOTYPE of step S7 of `dokumente/PERFECT-MODEL.md` §8 (refinement of the implementation by the
             ideal meaning `I`) on a two-thread fragment with locks, atomics, an interrupt handler, a device
             register and a DMA buffer. The theorem is `Prototyp.s7_prototyp`, its premise is satisfiable
             (`Prototyp.disc_erfuellbar`).

  | Module        | Content                                                                         |
  |---------------|---------------------------------------------------------------------------------|
  | `Syntax`      | the fragment: units, plain operations, protections, execution against answers   |
  | `Atomics`     | RC11 `rlx`/`sc` as a promise-free view model; determinacy and enabledness       |
  | `Impl`        | the implementation machine: fine-grained units, preemption, device, DMA         |
  | `Ideal`       | `I`: one step per unit; `I.Bestimmt`, `I.Fortschritt`                           |
  | `Discipline`  | the premise `Disc`, frames, the replay of one unit                              |
  | `Sim`         | the refinement relation `R`, disjointness of running units                      |
  | `StepEnter`, `StepOuter`, `StepCommit`, `StepEnd` | the cases of the step theorem               |
  | `Step`        | the step theorem, `Rest`, the stutter potential                                 |
  | `Run`         | finite runs, ONE ideal run per infinite run, answers, bounded stutter           |
  | `Satz`        | the theorem of the prototype                                                    |
  | `Erfuellbar`  | the premise is satisfiable by a program with every form                         |
-/
module

public import Grammatik.Zielsatz.Ideal.Prototyp.Erfuellbar
