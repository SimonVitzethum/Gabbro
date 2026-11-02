/-
  File:      Grammatik/Korpus59.lean
  Subject:   THE G PROGRAM OF `beispiele/0059-eintritt-nimmt-maskierte-sperre.gab`,
             with the bodies of the source, and every premise group of the goal
             theorem on it.

  The source: two modules. `takt`: table `Takte` (count 64, `u64` field
  `stand`), lock `TAKT` (rank 0, `masks irqs`), leaf `zaehle` (`requires Held`,
  one slot write of `1`), distributor `takt_verteiler` (`locks TAKT` around
  `zaehle(0)`), one `entry` dispatching to it. `ruf`: table `Auftraege`
  (count 16), lock `RING` (rank 0, no mask), leaf `bearbeite`, distributor
  `ruf_verteiler`, one `entry`. Every form has a G counterpart: index params
  are `Ty.index (count)`, `requires Held` is the signature-held set, `locks`
  blocks and direct calls are `Stmt`, `masks irqs` is `D.maskiert`, the entry
  dispatch roots are the declared starts, `costs`/`reads` are ignored form.

  ONE DOCUMENTED ANNOTATION-WEAKENING: every function of the source carries
  `deadline <= … arch x86_64 falsifier …`, and the exporter refuses exactly
  that in `check_fn` (`crates/gabbro-check/src/lean_g.rs`):
  `refuse("LG001", format!("function {} carries a form with no G counterpart",
  f.name))` when `d.deadline.is_some() || … || d.arch.is_some() || …`. Timing
  promises have no `Expr` form, so the model drops `deadline`/`arch`/
  `falsifier` and keeps bodies, Held sets, locks, starts and `costs`-free
  effects. No lock invariant is declared in the source, so the family is
  trivially true (owed nowhere).
-/
module

public import Grammatik.Korpus.Programme.Korpus59.Teil1
public import Grammatik.Korpus.Programme.Korpus59.Teil1a
public import Grammatik.Korpus.Programme.Korpus59.Teil2
