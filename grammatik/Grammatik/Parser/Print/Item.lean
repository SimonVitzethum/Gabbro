/-
  File:      Grammatik/Parser/Print/Item.lean
  Subject:   Track P: the token printer of items -- the inverse of `parseItemTief` on every item kind
             (`module`, `use`, `fn` with its clauses and bodies, `const`, `type`, `static`, `table`, `lock`,
             `concurrent`, `entry`, `device`, `format`, `arena`, `reason`, `state`, `atomic`, `syscall`,
             `target`, `assume`, `axiom`, `check`, `group`, `rcu`, `accumulates`, `walk`, `boot`, `entrust`,
             `profile`, `translator`, the `when TESTBUILD` gate).

  `druckItem` is total on the 35 item kinds. Like the statement printer it is measured, not proved:
  `Cover/Census` runs the round trip over every leaf item of the corpus (`ri=`); the expression leaves ride
  `druckToks`, whose `gut` shapes have the round-trip theorem.
-/
module

public import Grammatik.Parser.Print.Item.Teil1
public import Grammatik.Parser.Print.Item.Teil2
