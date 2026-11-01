/-
  Gabbro -- **what this grammar covers, and what it hands to the person.**

  `Body.lean` says what a Gabbro program MEANS. This file says something else, about the
  channel that sits on top of it: *for every form of the language that can put an obligation
  in front of a person, who answers for it.*

  The sentence `PLAN.md` serves is

  > a person who wants to verify a Gabbro program formally proves their own logic, and
  > nothing else.

  Read as a slogan that is unfalsifiable. Read as a proposition it is section 6 of this
  file: `Form` enumerates the obligation-generating forms the grammar admits, `classify`
  gives each of them exactly one verdict, and `the_sentence` says that every form which is
  NOT the person's own logic is carried, carried by the automation, assumed by a name, or
  refused with a tag.

  ## What is proved here, and what is NOT

  **NOT proved: "the tactic closes it".** Tactic success is a property of a RUN, not a
  theorem, and a file that claimed otherwise would be worse than no file. The verdict
  `Verdict.carriedByTactic` exists for exactly the forms whose obligations `gabbro_auto`
  closes on the corpus and for which no general theorem stands here; `Discharges` is
  `False` for them, on purpose, so that moving a form into `carried` without a lemma
  breaks `carried_discharges` instead of passing quietly.

  **Proved: the plumbing rows of `PLAN.md` section 1, as general lemmas.** Every form the
  classifier calls `carried` has a proposition below it that is quantified over an
  ARBITRARY program of that shape -- an arbitrary environment, an arbitrary typing, an
  arbitrary body -- and a proof. Where the general form is false without a side condition,
  the side condition is a PREMISE and there is a theorem saying the premise cannot be
  dropped (section 5.9).

  ## The trap this file is inside

  `Form` and `Reason` are HAND-WRITTEN mirrors of `crates/gabbro-check/src/parse.rs` and
  `crates/gabbro-check/src/lean.rs`. A mirror that drifts still typechecks, and then the
  theorem is about a language that is not Gabbro. That is the `W7`/`W16` class: two
  registers over one thing, one of them read by a guard. The guard is
  `instrumente/pruefe-deckung.py`, and what it does NOT check is written in its own header.
-/
module

public import Gabbro.Coverage.Teil1
public import Gabbro.Coverage.Teil2
public import Gabbro.Coverage.Teil3
public import Gabbro.Coverage.Teil4
