/-
  File:      Grammatik/SchablonenModul.lean
  Part of:   Gabbro -- the generator-template library (T5 of
             dokumente/PLAN-TRANSLATION-VALIDATION.md): the runtime of a `module` unit
             (a loadable kernel module) as GENERATED text (C-free lane, C2, 2026-09-30).

  Rows of `crates/gabbro-check/src/schablonen.rs`:

  * `arena.modul` -- the arena runtime the module driver writes (`treiber.rs::KMOD_ARENA`):
    each dynamic arena's storage is a static pool of the manifest's provision `V`, the span is
    `min(max * elem, V)`, the committed floor must fit it (else the LOAD is refused), a `grow`
    past the ceiling is a fail-stop the load function reads back, a `grow` past the span
    answers `false` with `committed` unchanged.
  * `modul.lebenslauf` -- the loader's two entry points the driver writes
    (`treiber.rs::erzeuge_kmod`): load = every arena bound, every lock initialised, the unit's
    init, the fail-stop read back, one thread per root; unload = every root awaited, then the
    unit's exit.

  * `faden.modul` -- the roots as kernel threads (C2 slice 3, 2026-10-01): one join word per
    root, 1 before the start, 0 from the wrapper after the root returned (or from the driver
    after a failed start); the wait re-reads it and sleeps through the binding.
    `faden_modul_warte_korrekt`: a wait that returns saw the root's whole run, or a start that
    failed and no step of the root; `faden_modul_ohne_eins`, `faden_modul_null_zuerst`: the two
    orders it rests on are not decoration.

  All are ABSTRACT CORES like `arena.dyn` and `faden.laufzeit` (SchablonenArena.lean,
  SchablonenFaden.lean): machine G has the arena as a table of `max` slots (ArenaDyn.lean) and
  the declared starts as threads (premise (d) of the goal, Zielsatz/Spec.lean). What is proved
  here is the mechanics the templates add:

  * `arena_modul_inv_reserve`, `arena_modul_inv_grow`: the invariant `committed <= max` and
    `committed * elem <= span <= V` is established by a successful reservation and kept by
    every `grow` -- so every slot the unit can reach lies inside its pool
    (`arena_modul_slot_im_lager`), which is the memory-safety half of the template;
  * `arena_modul_kein_ueberlauf`: no `uint64_t` product of the C wraps (`max`, `elem` are
    32-bit, and the span product is formed only below the ceiling);
  * `arena_modul_monoton`: the committed prefix only grows, and a refused `grow` changes
    nothing;
  * `laden_erfolg`, `laden_init_erst_nach_bindung`, `laden_ruft_kein_exit`,
    `laden_verweigert_wartet`, `entladen_wartet_vor_exit`: the load runs the unit's init only
    after every arena is bound and every lock initialised, never calls the unit's exit, starts
    roots only after an init that answered 0 with no fail-stop, and on a refusal waits for
    every root it started; the unload waits for every root before the exit.

  NOT proved: that the program's binding keeps its contract (a lock operation takes and gives
  the lock, a thread start runs the root and a failed start completes at once) -- the program's
  own declarations, user logic, premise (c).

  No `sorry`, no `native_decide`, no new axiom; each theorem has a witness instantiating ALL
  its premises jointly.
-/
module

public import Grammatik.Bausteine.Schablonen.SchablonenModul.Teil1
public import Grammatik.Bausteine.Schablonen.SchablonenModul.Teil2
