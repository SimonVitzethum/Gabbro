# Simplicity without losing a guarantee -- plan

*Written 2026-09-14. The folder owner: "maximum simplicity is an important goal too, but the goal
must be reached; no guarantee is given up for simplicity." External review: most of the writing
burden does not carry a guarantee. It only answers who states the guarantee. As long as
everything derived is checked exactly like everything written, the guarantee does not change.*

## 0. The measure

A simplification is accepted when **the ceremony count goes down** (`gabbro zeremonie`, the
burden per rule with its reason) **and the pass register stays constant** (`saetze.rs` /
`messung/PASSREGISTER.md`: every guarantee, with the code that enforces it). Both numbers are
booked before and after each step. A step that lowers the first and moves the second is
refused, whatever it saves.

## 1. The levers, ordered by leverage

1. **Derive instead of demand, and turn the meaning of the clause around.**
   - `effects` and `costs` are about 767 of roughly 980 clause sites in the corpus. The checker
     already computes both: the effect hull, and `kosten.rs`.
   - Today `costs <= 32 ops` means "tell me what it costs". Afterwards it means "hold me to 32":
     a written bound is ENFORCED, tighter than the computed one.
   - An omitted clause means "whatever it is, and it stands in the register". The derived value
     is checked like a written one.
   - This is less work, and the clause becomes more useful.
2. **Defaults with a named escape**, after Rust's lifetime elision: a small, fixed, documented
   set of rules that fill in the normal case, not general inference. Candidates are the rank
   order, the phase, and `pure` on spec functions. Only the deviation is written. Every rule
   has a sentence in the register.
3. **Explicitness as a VIEW, not a storage format.**
   - `gabbro fmt --explicit` writes out every derived clause, for review, for the certifier and
     for the unfamiliar reader.
   - `gabbro fmt --elide` removes everything derivable, for writing.
   - Both run the same checker on the same program; there is no second language.
4. **Refusals that ship the fix.** The 386 diagnostics say what to write, as a
   machine-applicable edit (like `rustc --fix`). The guarantee is unchanged. This is worth even
   more to machine authors, which learn at once from an applicable correction.
5. **Contextual keywords.** In `70-kernel-namen.gab`, 212 of 221 vocabulary words could serve
   as no identifier anywhere, which is pure grammar friction. A word becomes a keyword only
   where the grammar expects one, as Rust did with `union` and `dyn`. This is parsing only,
   with zero semantics.
6. **The Lean side: better handed-over goals and more tactics** (normalisation, `gabbro_simp`,
   `gabbro_wf`). Every tactic produces a kernel-checked proof, so the lines per obligation fall
   and the guarantee is untouched.

## 2. What cannot be made lighter (each would cost a guarantee)

- **Deriving `ensures`.** What a function SHOULD do cannot be inferred. A tool that guesses the
  postcondition guesses the specification, and the proof then proves nothing. It stays by
  hand; it is 63 sites in the whole corpus.
- **Turning refusals into warnings.** That gives up a class; it does not simplify.
- **Uncounted exits.** `extern fn` with a named assumption is fine because it is counted. An
  `unsafe` that disappears in a diff would not be.

## 3. Order

- **Lanes 184, 187 and 188 run in parallel:** 184 is derivation with the enforced-bound
  semantics, 187 is fix-its, 188 is contextual keywords.
- **Then** defaults (lever 2, needs the rule set designed first) and `fmt --explicit/--elide`
  (lever 3, needs 184).
- **Tactics** follow the goal theorem.
- **Before and after each lane:** both numbers of §0 are booked.
