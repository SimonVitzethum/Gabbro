# C2 witness pairs: expected outcomes

Each probe in this directory exhibits one named C form (the `c2Paare` row in
`grammatik/Grammatik/Erhaltung.lean` §4b). The pair is the probe plus the
outcome below; the test `c2_witness_pairs_run_clean_and_emit_their_form` in
`crates/gabbro-check/tests/korpus.rs` measures both halves.

Measured 2026-09-11 against the unchanged checker: `gabbro pruefe` reports
0 errors over every probe, and `gabbro emit` writes the named fragment with
0 refusals.

| Probe | C form | `pruefe` | Emission carries |
|---|---|---|---|
| `c2-01-zuweisung.gab` | `zuweisung` | 0 errors | `= 41` |
| `c2-02-wenn.gab` | `wenn` | 0 errors | `else` |
| `c2-03-ruf.gab` | `ruf` | 0 errors | `gib()` |
| `c2-04-rueckgabe.gab` | `rueckgabe` | 0 errors | `return` |
| `c2-05-literal.gab` | `literal` | 0 errors | `8` |

The Lean side recomputes the form half (`zeugenPaarGueltig` over `ruledB`);
this file and the test above carry the execution half. The C meaning itself
stays cut (Erhaltung.lean C2): a green pair links the probe to the tabled
form, it does not prove what the C fragment means.
