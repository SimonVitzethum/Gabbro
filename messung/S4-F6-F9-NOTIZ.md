# S4 note: F6 tail-return reason gap and F9 shapeless-answer conflation

Status: note only. No model change. Verification commands are listed in
section 4 and were not run.

## 1. F6: tail return drops the reason channel

Checker site: `programmlogik/Gabbro/Sicherheit/Anweisung.lean:368`,
the `.retCall` arm of `pruefe`:

```
| some S => if S.gruende = [] && antwortGestaltPasst erg S.ergebnis then some Δ else none
```

A tail call in return position (`return f(args);`) is accepted only when
the callee declares an empty reason list. Any callee with a declared
`or R` channel is rejected at this position, unconditionally.

Premise site: `Anweisung.lean:520-525`, `UmgebungOK`. The environment
premise allows a callee to answer either with a value of its declared
result shape or with a reason drawn from its declared reason list, for
both the shaped-result case and the no-result case:

- result shape present: answer is some value with that shape, or a
  declared reason;
- result shape absent: answer is no value at all, or a declared reason.

So the premise states a reason channel that the checker arm at line 368
does not accept: the checker requires the channel to be empty, while the
premise gives meaning to a non-empty one. The same empty-list demand
appears in the neighboring plain-call arm (`:329`) and the bind-call arm
(`:335`), but this note scopes F6 to the tail-return arm, where the
consequence is sharpest: a well-formed callee answer (a declared reason)
has no accepted path through a tail return.

Fix direction: thread caller reasons. The checker should propagate the
callee reason list into the caller context instead of demanding it be
empty — either by requiring the caller signature to declare the same
reasons, or by requiring reason-arm coverage at the return site. The
shape-compatibility check (`antwortGestaltPasst`, `:262-265`) stays as
the value half; the missing half is the reason half.

## 2. F9: one encoding for no value and value without shape

Signature site: `Anweisung.lean:182-189`, structure `Signatur`. The field
`ergebnis : Option Shape` carries `none` with the documented meaning "no
answer". Binding site: `Anweisung.lean:331-336`, the `.bindCall` arm of
`pruefe`: when `S.ergebnis` is `none`, the arm rejects — there is nothing
to bind.

Conflation: "returns no value" and "returns a value that carries no
shape" share the single encoding `none`. A shapeless answer (a value the
shape judgment does not classify, such as an opaque handle) cannot be
told apart from absence, so the binding rule can only reject the whole
class. The checker therefore refuses answers the premise side could, in
principle, carry as present-but-unshaped values.

Fix direction: split the result field. Presence of an answer and shape
of the answer should be separate: one flag for whether the callee
returns at all, plus an independent optional shape. The binding rule
then has three distinct cases — absent (nothing to bind, reject),
present with shape (bind with that shape), present without shape (bind
as opaque or reject by an explicit rule, not by accident of encoding).

## 3. Summary

| finding | checker site | premise site | fix direction | instances |
|---|---|---|---|---|
| F6 tail return drops reason channel | Anweisung.lean:368 | Anweisung.lean:520-525 | thread caller reasons | 48 |
| F9 shapeless answer conflated with no value | Anweisung.lean:331-336, Signatur:186-187 | Anweisung.lean:520-525 | split result field | 21 |

Instance counts are carried over from the S4 census in
`dokumente/PLAN-SICHERHEIT.md` and were not recounted for this note.

## 4. Verification (listed, not run)

The following commands would check the cited lines and confirm the model
still elaborates after any future fix. They were not run for this note;
no build was performed.

```
grep -n "retCall" programmlogik/Gabbro/Sicherheit/Anweisung.lean
sed -n '366,369p;519,526p' programmlogik/Gabbro/Sicherheit/Anweisung.lean
sed -n '181,190p;331,337p' programmlogik/Gabbro/Sicherheit/Anweisung.lean
cd programmlogik && lake env lean Gabbro/Sicherheit/Anweisung.lean
```
