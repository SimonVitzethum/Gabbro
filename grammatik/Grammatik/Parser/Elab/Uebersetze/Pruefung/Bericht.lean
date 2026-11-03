/- C16 items 9/10/12 on the front end: the elaborated record keeps the declared
   identity, both verdicts elaborate to the same generated shape, and the Duty
   threads through the probe and its gate wrapper.

   The decider runs by kernel evaluation (`rfl`): the `uCheck` record preserves
   the name, the claim and the counterprobe while deriving the generated
   producer and Duty names from the check name (item 9); the false-verdict probe
   elaborates to its generated producer exactly like the true one (item 12);
   and the elaborated unit carries the Duty in the probe's `nimmt`/`gibt` and
   in the wrapper's `nimmt` (items 10/12). The kernel side of the identity,
   the completed reports and the discharge lives in
   `Kern/Syntax/Satz/PruefungAbschluss.lean`. -/
module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Proben

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- The false-verdict probe: the same check with a `can_fail` body returning
    `false` -- a completed measurement with a negative verdict, never a
    missing run. -/
def probenCheckFalsch : SCheck :=
  { probenCheck with canFail := .block [] (some (.ret (some .fls))) }

/-- The identity is preserved: the elaborated record keeps the name, the claim
    and the counterprobe, and derives the generated producer and Duty names
    from the check name. -/
example : (uCheck [] [] ["g"] ["p"] probenCheck).map
    (fun c => (c.name, c.claim, c.sonde, c.probe, c.duty)) =
    .ok ("p", "c", none, "p#probe", "p#duty") := rfl

/-- The counterprobe identity travels with the record. -/
def probenCheckSonde : SCheck :=
  { probenCheck with sonde := some ("ext", "assert x") }

example : (uCheck [] [] ["g"] ["p"] probenCheckSonde).map (·.sonde) =
    .ok (some ("ext", "assert x")) := rfl

/-- The floors elaborate to the retained predicates. -/
example : (uCheck [] [] ["g"] ["p"] { probenCheck with boden := [.tru, .fls] }).map
    (·.boeden) = .ok [.tru, .fls] := rfl

/-- The false-verdict probe elaborates to its generated producer, exactly like
    the true one. -/
example : (uProbeFns [] [] [] [] [] [] [] [] [] [] [] [] [] [] 0 ["g"] [probenCheckFalsch]).map
    (List.map (·.name)) = .ok ["p#probe"] := rfl

/-- The elaborated unit carries the Duty: the probe threads it (`nimmt` and
    `gibt`), the gate wrapper consumes it once. -/
example : (elabU [probenFn, .checkT probenCheck]).map
    (fun u => u.fns.map fun f => (f.name, f.nimmt, f.gibt)) =
    .ok [("g", [], []), ("p#probe", ["p#duty"], ["p#duty"]),
      ("p#tor#g", ["p#duty"], [])] := rfl

/-- The false-verdict check elaborates to the same generated shape: the Duty
    threads through `false` returns too. -/
example : (elabU [probenFn, .checkT probenCheckFalsch]).map (fun u => u.fns.map (·.name)) =
    .ok ["g", "p#probe", "p#tor#g"] := rfl

/-- A `bool` gate derives its Duty-consuming wrapper forwarding the answer:
    the wrapper binds the gate call and returns it. -/
example : uTorHuelle "p#duty" [{ torGate with resBool := true }] "p" "g" =
    .ok { name := "p#tor#g", params := [], kinds := [], res := none, resBool := true,
      held := [], puts := [], gputs := [], nimmt := ["p#duty"], gives := [], needs := [],
      body := [.bindCall "ans" "g" []], ret := .bool (.var "ans") } := rfl

end Gabbro.Grammatik.Parser.Uebersetze
