/-
  File:      Grammatik/Logik/Vertraege/ObjektRahmen.lean
  Subject:   **THE FRAME OVER OBJECTS AT THE MODEL'S CALL** -- `own`/separation slice 2b,
             the run half of `Objekte.lean`.

  THE ENCODING (no change to machine G). A pointer to ONE object of table `t` is a pair of
  parameters G already has: the capability `ptr n rw` with `D.tabNr n = some t` and an
  index `index (D.count t)`. `ObjPar` names such a pair: `idx` (the index parameter),
  `cap` (the capability), both counted from the BOTTOM of the context (`Var.unten`), so a
  position stays the same under every `let` a body pushes; `rw` is the right of the
  capability (`own` travels as read-write, `lean_g.rs::param_ty`). In an environment `ρ`
  the pair names the object `⟨tab, value of idx⟩` (`ObjPar.obj`). The identity is a VALUE
  the caller chooses -- which the type alone could not say (slice 2's obstruction 1).

  THE DECLARED FRAME OVER THE WRITABLE PARAMETERS, AT OBJECT GRANULARITY. A body keeps the
  object discipline (`oS`/`oB`/`oE`, a syntactic check over the WHOLE grammar) when:
    * every slot store (`assignSlot`, `assignDurch`, `uebergang`) indexes with a writable
      object parameter's own index variable, at that parameter's table (`SchreibOk`);
    * no assignment overwrites such an index variable (`VarFrei`);
    * every call hands each writable object parameter of the callee a writable object
      parameter of its own, at the same table (`ObjRufOk`) -- the frame is inherited;
    * no axiom it calls writes a table (`KeinTabAx`); indirect calls and multi-slot byte
      stores (`schreibBytes`) are not admitted (stated, not hidden: `False` there).
  `ProgObjOk` asks it of every body of a program, with the pairs faithful to the
  signature (`ObjParTreu`: the capability and the index have the declared types).

  WHAT IS PROVED (generic: every declaration, every program, every world, every depth):
    * `stmt_obj` .. `grund_obj` -- the induction over the whole grammar: a run changes no
      slot outside the objects of the writable parameters (`SlotRahmen (WVon ..)`), and
      the index variables keep their values.
    * `rufAt_obj` -- the model's own call `rufAt` keeps that frame at every depth, under
      the hardware's frame premise `TreuO` only (H1, as `rufAt_treu`).
    * **`obj_ruf_rahmen`** -- THE FRAME AT A SEPARATED CALL: if the call frame is
      `ObjGetrennt` (the argument-to-object map injective on the pairs with a writable
      side), every run leaves every field of the object of every READ-ONLY object
      parameter unchanged -- also when it lies in the very table the call writes.
    * `umsicht_behaelt` -- the borrow rule in the model: a function whose body answers one
      of its object parameters' index (`return k;`, a re-view at one table) answers the
      SAME object it was handed; `objGetrennt_nicht_bei_einem` (`Objekte.lean`) then says
      the re-view and its source are not separated.
-/

import Grammatik.Logik.Vertraege.ObjektRahmen.T1
import Grammatik.Logik.Vertraege.ObjektRahmen.T2
import Grammatik.Logik.Vertraege.ObjektRahmen.T3
