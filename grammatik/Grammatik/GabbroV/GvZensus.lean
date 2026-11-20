/-
  File:      Grammatik/GabbroV/GvZensus.lean
  Subject:   GabbroV bridge: continue-on-refusal census over the corpus
             (agent 02, GabbroV-lead task V-02).

  `elabU` stops at the first refusal (`Except` short-circuits), so the
  tallies only ever named one blocker per file. This module re-runs the
  pipeline in COLLECT mode instead: token streams split into top-level
  items (depth-tracked splitter, sound on balanced streams), each item
  parsed separately, then tables, locks, heads, bodies (per statement),
  contracts (per predicate), returns and entries elaborated item by
  item, collecting every refusal with its stage, construct and message.
  Parse failures that unbalance the stream fall back to first-error
  plus a token scan. The `#eval` census at the end prints, per
  construct, in how many files it appears and in how many it is the
  ONLY blocker, with the ranked flip list. `Parser/` untouched.
-/
module

public import Grammatik.GabbroV.GvZensus.Teil1
public import Grammatik.GabbroV.GvZensus.Teil2
