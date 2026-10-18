/-
  File:     Grammatik/Zeugnis.lean
  Subject:  The certificate side of the S4/V5 witness pair (Lean side only).

  SOURCE SENTENCES
    dokumente/PLAN-UMSETZUNG.md §1.3 -- the derivation printed as Lean; Lean
      accepting the print is the statement that the program is a sentence of
      the grammar. A `Zeugnis` the Rust side gets wrong is a Lean error at the
      line of the constructor.
    dokumente/PLAN-SICHERHEIT.md S4 (`checker_agrees` witness pairs per unit)
      + dokumente/PLAN-VERIFIKATION.md §3/V5 -- `gabbro lean` writes, per unit,
      `theorem checker_agrees : ... := by decide`; disagreement fails LOUDLY.
    messung/ZIEL-BEWERTUNG-2026-09-10.md, "S4 scope" -- the W16 seam fails loudly
      per routine per run instead of silently.

  WHAT STANDS HERE
    `CertExpr` -- the printed certificate format: derivation terms as PLAIN DATA
      (ranges as numbers, side conditions NOT as proofs). This is what the Rust
      printer writes; it carries no evidence by itself.
    `certRange` -- the range table (M104/M102), recomputed on the Lean side.
    `GueltigAbleitung c lo hi` -- the validity predicate: the printed claim
      `(lo, hi)` is EXACTLY what the table recomputes. A forged or mismatched
      print is not "rejected with a message"; it is PROVABLY invalid
      (`¬ GueltigAbleitung ...`, closed by `decide` below), and no acceptance
      proof can be built from it -- failure by construction, not by diagnostic.
    `zeugnis_sound` -- soundness: a valid certificate IMPLIES the judgment,
      i.e. elaborates to a real `Expr` term (an accepted derivation). This is
      the direction this file owns.

  TRUST BASE (explicit)
    The Rust printer (`gabbro lean` / `gabbro-ableitung`, PLAN-UMSETZUNG.md §1.3)
    is TRUST BASE here and stays trust base: this file proves
    valid-print-implies-judgment, NOT printer-prints-what-checker-derived.
    A printer that prints a different derivation than the one it checked is
    outside this file -- exactly as §1.3 books it (the print, not the printer,
    is what Lean checks).

  CUTS (shrunk, not faked -- each booked cut is a constructor this file does NOT cover)
    CUT-1 signed division and remainder (`sdiv`/`srem`): COVERED below
      (certificate rows, validity side conditions, soundness cases, probes).
    CUT-2 bitwise and shifts (`band`/`bor`/`bxor`/`shl`/`shr`, width proofs):
      COVERED below (same shape as CUT-1).
    CUT-3 floats, options, sums, grounds, quantifiers, `reaches`: COVERED below
      (constructors, range arms, validity defs with Decidable instances, and
      soundness as `cut3_sound`; the quantifier arms take the body as an
      explicit hypothesis -- the body elaboration is the remaining booked
      piece, named as `Cut3Body`).
    CUT-4 variables and carrier accesses: COVERED below for the int fragment --
      name reads (`var`, de Bruijn index against `Γ`), global reads (`glob`,
      type from `D.gtyp`, guard `gdarf` recomputed), place reads (`slot`,
      index shape `0 .. count - 1` plus field type plus guard `darf`
      recomputed). Each with certRange arms, `GueltigAbleitung` side
      conditions, soundness cases, pos/neg decide probes.
      REMAINDER, half covered: `ptrOf`/`fnref` are COVERED below (design plus
      soundness as `cut4_sound`); `durch` is covered conditional on the
      pointer it names (`Cut4Ptr` -- the pointer term is the remaining booked
      piece). Still booked: `altGlob`/`altSlot` (post-entry values,
      not reads of the live world).
    CUT-5 resource contexts: COVERED below for straight-line int blocks --
      `bind` (context extension by the recomputed range), nullary `call`
      (`params = []`, `gruende = 0` recomputed), `ret`/`retWert` (result shape
      plus the linear balance `Λ.Perm V.ende` recomputed). Each with validity
      side conditions, soundness cases, pos/neg decide probes.
      REMAINDER, COVERED below (design plus soundness as `block5_sound`,
      conditional on the argument lists): calls with arguments
      (`callArgs`/`callInd`/`bindCall`) recompute the argument-count shape and
      `gruende = 0`, and a call's `RufPasst` travels AS PROOF in the
      certificate. It quantifies over the arbitrary carrier types (`∀ t`,
      `∀ g`, `∀ L`), so no range table can recompute it the way `certRange`
      recomputes `darf`; carrying it is the honest shrink, and the day
      `Tab`/`Glob` enumerate, the arm can check it instead. Each argument's
      elaboration travels as an explicit hypothesis (`Block5Args`) -- the
      remaining booked piece; the `bindCallElse` error branch stays booked.
    The int fragment stands as it was: every `CertExpr` certificate elaborates
    to an `Expr` of `int` type (reads) or a `Block` over int bindings
    (statements). Beyond it, `cut3_sound`/`cut4_sound`/`block5_sound` cover
    floats, options, sums, grounds, `reaches`, pointers, function references,
    and calls with arguments -- conditional on the three named supplies
    (`Cut3Body`, `Cut4Ptr`, `Block5Args`). Still booked: `altGlob`/`altSlot`,
    the `bindCallElse` error branch, and the three supplies themselves.

  CHECK
    cd grammatik && lake env lean Grammatik/Zeugnis.lean
    Finished proofs only: the build log carries no unfinished-proof warning,
    and `#print axioms zeugnis_sound` / `#print axioms block_sound` at the end
    name every axiom the soundness proofs rest on.
-/

import Grammatik.Korpus.Zeugnis.Zeugnis.T1
import Grammatik.Korpus.Zeugnis.Zeugnis.T2
import Grammatik.Korpus.Zeugnis.Zeugnis.T3
import Grammatik.Korpus.Zeugnis.Zeugnis.T4
