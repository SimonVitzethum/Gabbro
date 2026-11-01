/-
  Gabbro -- program COMPOSITION: from checked bodies to `UmgebungOK` and `SchleifenOK`.

  `Sicherheit.lean` books this file as its step 2: `(U1)` and `(U2)` are the same safety
  theorem one level down -- for the callee's body and for the loop's iteration -- and
  closing them from `Runs`/`RunsLoop` plus `pruefeBlock_sicher` is the program theorem.
  That closure stands here, and nowhere else.

  WHAT IS PROVED (0 `sorry`, 0 `admit`, 0 new axioms; `import Mathlib` arrives only
  transitively through `Sicherheit.Anweisung`, this file uses no Mathlib lemma):
    * `ergebnis_of_geprueft` -- the bridge both halves walk over: a checked body that
      does not stop at own logic ends in `Ergebnis` (directly from `pruefeBlock_sicher`).
    * `schleifen_ok_of_runsloop` / `schleifen_ok_of_runsloop_in` -- a registered loop
      whose body is checked, whose environment runs its passes (`RunsLoop` /
      `RunsLoopIn`), and whose passes stop at no own logic, keeps world and scope:
      the `SchleifenOK` conjunct, by induction over the `iterate` index list, in the
      shape of `Body.looprule_of_body` (`_in`).
    * `umgebung_ok_of_runs_azyklisch` -- acyclic routines: topological induction over an
      explicit rank. Each duty may assume the contracts of the callees it names
      (`ruftAuf`); the induction discharges them in rank order through
      `Body.contract_of_duty` (the step `Coverage` books as `contractFromDuty`).
    * `vertrag_zyklus_of_pflichten` -- cyclic routines: `Coverage.recursion_cycle_carried`
      applied as stated, so the duty shape here IS the Coverage shape (`ContractBelowM`
      over the `decreases` measure, one induction for cycles of every size).
    * `umgebung_ok_of_runs` -- the cyclic corollary: cycle contracts with the canonical
      pre/post (`Welt` in, `Welt` plus the signature's answer out) fold to `UmgebungOK`.
    * `umgebung_ok_of_vertrag` -- the shared fold both composition theorems end in.
    * Section 5 closes the S2 cuts (C1-C4) per unit and to minimal form:
      `wfu_eintritt_of_argumente` (C1 call-site half),
      `pflicht_of_geprueft_oder_fehlend` with `nachpost_of_antwortpasst`,
      `nachpost_none_of_kein_ergebnis`, `pflicht_scheitert_ohne_wert` (C1 duty half
      and C2 missing-return failure), `vertrag_blatt_of_pflicht` (C3 rank discharged
      for leaves), `umgebung_ok_kette_of_vertraege` (C3/C4 SCC-at-a-time composition),
      `umgebung_ok_of_runs_zyklus_min` (C4 foreign narrowed to called names),
      `umgebung_antwort_of_vertrag` / `umgebung_ok_of_antwort` (D split to minimal
      passthrough). Residuals are exact and stand in the C-cuts below.

  ASSUMED (as premises of the theorems, never as axioms):
    (F) Foreign bodies (`extern`, `asm`, `entrust`) stay hypotheses: `Fremd` marks the
        names with no body in the list, `hFremd` is their `UmgebungOK` conjuncts taken
        as a premise. Minimal form (§5): the fold queries only declared foreigners
        (`P.sig g = some S` rides along); cycle duties assume foreign posts only for
        the names the body calls (`ruftAuf r.body g`). A foreign body is refused by
        the emitter (`foreign-body`) for the same reason it is assumed here: there is
        no body to run a duty over.
    (D) `DivergenzOK` (no declared callee diverges -- `Sicherheit`'s U5). Minimal form
        (§5): it is a pure passthrough -- `umgebung_antwort_of_vertrag` derives world
        plus answer without it, and `umgebung_ok_of_antwort` adds exactly this
        conjunct. It is used nowhere else in the fold.

  CUTS -- places where the file shrinks instead of faking, booked here and not in a
  commit message:
    (C1) CLOSED per unit (§5). Discharging a duty from a checked body needs
         `WFU (paramUmgebung S.params)` at entry, which only call sites provide
         (`argumente_sicher`); `wfu_eintritt_of_argumente` names exactly that
         call-site half, and `pflicht_of_geprueft_oder_fehlend` keeps the entry `WFU`
         as an explicit duty premise. Exact residual: the entry `WFU` (provided per
         call by the caller, never invented here) and the person's `¬ LogikB`.
    (C2) CLOSED (§5). A body that falls off the end (`running`, `finalValue = none`)
         against a declared result (`S.ergebnis = some`) meets no duty:
         `pflicht_scheitert_ohne_wert` proves `¬ Nach` from `finalValue = none`, so
         the duty fails rather than a value being invented. `NachPost` without a
         declared result holds of `none` (`nachpost_none_of_kein_ergebnis`); a
         missing `return` stays loud as the right disjunct of
         `pflicht_of_geprueft_oder_fehlend`.
    (C3) NARROWED (§5): leaves need no rank (`vertrag_blatt_of_pflicht` discharges
         `hsort` entirely when every callee is foreign), and discharged contract
         sets compose rank-free (`umgebung_ok_kette_of_vertraege`). Exact residual:
         the rank over routines with defined callees in one acyclic group, which the
         emitter instantiates per unit in the checker's call-graph order
         (`Body.lean` section 5.1 tells the same story for
         `contract_of_duty`/`looprule_of_body`). No call-graph datatype stands in
         the model, so sortedness stays a premise, not a computation.
    (C4) NARROWED (§5): a cycle member's duty assumes foreign posts only for the
         names its body calls (`umgebung_ok_of_runs_zyklus_min` -- the ambient
         `∀ g, Fremd g → …` weakened to `∀ g, ruftAuf r.body g → Fremd g → …`),
         and SCCs compose supply-at-a-time through the shared fold
         (`umgebung_ok_kette_of_vertraege`). Exact residual: bounded intra-cycle
         contracts (`ContractBelowM` over `decreases`) plus foreign posts of called
         names; a call to a defined outside-cycle routine enters as foreign for
         that invocation (SCC condensation is the emitter's order, as in C3).
    (C5) Only `RunsLoop`/`RunsLoopIn` are closed; the counted `RunsLoopN` variant is
         not (its pass premise carries the ghost counter -- a second induction that
         would shadow `looprule_passes_aux` instead of reusing an idea).
    (C6) The loop theorems take `UmgebungOK`/`SchleifenOK` as premises for the nested
         constructs of the body -- the same shape as `pruefe_sicher` itself, which
         concludes `Ergebnis` under those hypotheses. Same-id nesting is excluded by
         emitter-fresh loop ids.
    (C7) The loop variable is fresh in the registered scope (`such ΔS v = none`); the
         emitter guarantees it, the induction needs it (`wfu_bindLocal_frisch`).
    (C8) Wiring into `Gabbro.lean` is a follow-up: this file is checked standalone
         (`lake env lean`) and must not edit outside itself.

  LAYERING -- how the pieces meet: `umgebung_ok_of_runs*` discharge (U1) from duties;
  `schleifen_ok_of_runsloop*` reduce (U2) to per-pass no-logic duties under (U1)/(U2)
  for nested constructs (C6); `exec_sicher` consumes both. The person's own logic is
  never discharged here: it is the `¬ LogikB` / duty premises, in the open, per unit.
-/
module

public import Gabbro.KompositionBeweis.Teil1
public import Gabbro.KompositionBeweis.Teil2
