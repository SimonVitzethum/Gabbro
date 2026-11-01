/-
  File:      Grammatik/Logik/Terminierung/Ausgang.lean
  Subject:   THE EXIT CONDITION OF A `forever` LOOP (2026-10-23): when a loop of class `umgebung` or `bedingt` ends.

  Whether a `forever` loop ever ends is the program's question (undecidable in general). What the model fixes is
  HOW it can end -- exactly:
  * `foreverLauf_ok`, `foreverLauf_zurueck`, `foreverLauf_why`: the loop completes only through a pass that ends in
    `leave`, and returns only through a pass that returns -- the condition C of class `bedingt`;
  * `foreverLauf_nur_umwelt`: a loop none of whose passes leaves or returns ends only at a logic or hardware stop --
    in particular at its `progress` assumption when the passes the environment grants are spent;
  * `ohneAus_execStmt` (syntax to semantics): a statement whose finding (`befS`, Klasse.lean) holds no exit -- no
    `leave` of the loop around it, no `return` inside a `forever` pass -- never yields one;
  * `forever_umgebung`: a `forever` loop whose body holds no exit (the loops of class `umgebung`) ends only at a
    logic or hardware stop: never normally, never by returning.
-/
module

public import Grammatik.Logik.Terminierung.Ausgang.Teil1
public import Grammatik.Logik.Terminierung.Ausgang.Teil2
