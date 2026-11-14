module

public import Grammatik.Niedrig.Bytes.Erreichbar

@[expose] public section

namespace Gabbro.Grammatik.Niedrig.Bytes.GrantsZeuge

/-- One carrier of eight bytes, initially at generation zero. -/
def cap0 : ByteCap :=
  { traeger := 0
    lo := 0
    hi := 8
    rechte := Perm.beide }

def grant0 : Grant :=
  { cap := cap0
    generation := 0 }

def table0 : GrantTable :=
  { generation := fun _ => 0
    loans := [] }

/-- The lent half-open range is [2, 5), weakened to write-only permission. -/
def lent : ByteCap :=
  { cap0 with
    lo := 2
    hi := 5
    rechte := Perm.schreibe }

def loan0 : Loan :=
  { cap := lent
    lender := grant0
    id := 7 }

def loaned : GrantTable := { table0 with loans := [loan0] }

def state1 : ByteState :=
  zustandNach leererZustand (gebrauchSchreib table0 grant0 3 11 leererZustand)

def state2 : ByteState :=
  zustandNach state1 (gebrauchSchreib loaned loan0.grant 3 99 state1 (Option.some 7))

def grant1 : Grant := { grant0 with generation := 1 }

/-- Observe the actual write through a read, not by equating state functions. -/
theorem write_zeuge :
    (gebrauchSchreib table0 grant0 3 11 leererZustand).bind
      (fun s => gebrauchLies table0 grant0 3 s) = Except.ok 11 := rfl

theorem lend_zeuge :
    (leihe table0 grant0 lent 7).map (fun t => (t.generation 0, t.loans)) =
      Except.ok (0, [loan0]) := rfl

theorem lenderWriteRefused_zeuge :
    gebrauchSchreib loaned grant0 3 12 state1 = Except.error leiheAktiv := rfl

theorem lenderReadRefused_zeuge :
    gebrauchLies loaned grant0 3 state1 = Except.error leiheAktiv := rfl

theorem loanWriteReturnRead_zeuge :
    (gebrauchSchreib loaned loan0.grant 3 99 state1 (Option.some 7)).bind (fun s =>
      (gibZurueck loaned 7).bind (fun t => gebrauchLies t grant0 3 s)) =
      Except.ok 99 := rfl

theorem return_zeuge :
    (gibZurueck loaned 7).map (fun t => (t.generation 0, t.loans)) =
      Except.ok (0, []) := rfl

theorem lenderAfterReturn_zeuge :
    (gibZurueck loaned 7).bind (fun t => gebrauchLies t grant0 3 state2) =
      Except.ok 99 := rfl

theorem revoke_zeuge :
    (widerrufe table0 0).map (fun t => (t.generation 0, t.generation 1)) =
      Except.ok (1, 0) := rfl

theorem oldReadRefused_zeuge :
    (widerrufe table0 0).bind (fun t => gebrauchLies t grant0 3 state2) =
      Except.error veraltet := rfl

theorem oldWriteRefused_zeuge :
    (widerrufe table0 0).bind (fun t =>
      (gebrauchSchreib t grant0 3 17 state2).map (fun s => s.wert 0 3)) =
      Except.error veraltet := rfl

theorem newGrant_zeuge :
    (widerrufe table0 0).bind (fun t => gebrauchLies t grant1 3 state2) =
      Except.ok 99 := rfl

theorem revokeWithLoanRefused_zeuge :
    widerrufe loaned 0 = Except.error leiheAktiv := rfl

/-- Same-range reborrowing has a distinct identity, even with identical grants. -/
theorem nested_zeuge :
    (leihe loaned loan0.grant lent 8 (Option.some 7)).map (fun t => t.loans.length) =
      Except.ok 2 := rfl

theorem outerReturnRefused_zeuge :
    (leihe loaned loan0.grant lent 8 (Option.some 7)).bind (fun t =>
      (gibZurueck t 7).map (fun u => u.loans.length)) =
      Except.error leiheReihenfolge := rfl

theorem suspendedBorrowerRefused_zeuge :
    (leihe loaned loan0.grant lent 8 (Option.some 7)).bind (fun t =>
      (gebrauchSchreib t loan0.grant 3 12 state1 (Option.some 7)).map
        (fun s => s.wert 0 3)) =
      Except.error leiheAktiv := rfl

theorem readSharing_zeuge :
    (leihe table0 grant0 { lent with rechte := Perm.lese } 10).bind (fun t =>
      (leihe t grant0 { lent with rechte := Perm.lese } 11).map
        (fun u => u.loans.length)) = Except.ok 2 := rfl

theorem state1Reachable_zeuge : Erreichbar state1 :=
  gebrauchSchreibErhaelt Erreichbar.leer

theorem state2Reachable_zeuge : Erreichbar state2 :=
  gebrauchSchreibErhaelt state1Reachable_zeuge

theorem provenance_zeuge : 99 < 256 ∧ Schreibspur state2 0 3 99 :=
  grantGelesenGeschrieben state2Reachable_zeuge (show
    gebrauchLies table0 grant0 3 state2 = Except.ok 99 from rfl)

#print axioms loanWriteReturnRead_zeuge
#print axioms provenance_zeuge

end Gabbro.Grammatik.Niedrig.Bytes.GrantsZeuge
