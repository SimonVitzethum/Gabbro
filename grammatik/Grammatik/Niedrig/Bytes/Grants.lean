module

public import Grammatik.Niedrig.Bytes.BytesSaetze

@[expose] public section

namespace Gabbro.Grammatik.Niedrig.Bytes

/-- A byte capability stamped with its carrier's generation. This layer
    neither creates initial authority nor changes machine G. -/
structure Grant where
  cap : ByteCap
  generation : Nat
  deriving DecidableEq

/-- A scoped loan, saving the lender's exact grant. Identifiers distinguish
    access scopes even when lender and borrower have identical byte ranges. -/
structure Loan where
  cap : ByteCap
  lender : Grant
  id : Nat
  deriving DecidableEq

/-- A borrower inherits the saved generation, never a freshly minted one. -/
def Loan.grant (l : Loan) : Grant :=
  { cap := l.cap
    generation := l.lender.generation }

/-- Generations and a LIFO escrow stack, innermost first. Like the owner
    ledger's `borrow`/`returnBorrow`, reborrowing suspends the outer accessor.
    The later refinement lemma `byteLoans_ownerEscrow` must identify the
    exclusive stack of each independently owned byte span with
    `ArenaOwnership.Cell.loans` (splitting disjoint spans into separate owner
    resources), map loan identifiers to activation frames, and commute lend/return with
    `OwnerState.borrow`/`OwnerState.returnBorrow`. Shared read loans require
    the corresponding read-share refinement; they are not exclusive owners.
    Identifiers are scope identities, not addresses or fresh authority. -/
structure GrantTable where
  generation : Nat → Nat
  loans : List Loan

/-- Liveness is precisely equality with the carrier's current generation. -/
def live (table : GrantTable) (g : Grant) : Prop :=
  g.generation = table.generation g.cap.traeger

instance (table : GrantTable) (g : Grant) : Decidable (live table g) :=
  inferInstanceAs (Decidable (_ = _))

def veraltet : String := "grant-stale"
def leiheAktiv : String := "grant-loan-active"
def leiheUnbekannt : String := "grant-loan-unknown"
def leihePasstNicht : String := "grant-loan-mismatch"
def leiheKennungBelegt : String := "grant-loan-id-in-use"
def leiheBereich : String := "grant-loan-range"
def leiheRechte : String := "grant-loan-rights"
def leiheReihenfolge : String := "grant-loan-return-order"

/-- Two nonempty half-open ranges intersect on the same carrier. -/
def ueberlappt (a b : ByteCap) : Bool :=
  decide (a.traeger = b.traeger ∧ a.lo < a.hi ∧ b.lo < b.hi ∧
    a.lo < b.hi ∧ b.lo < a.hi)

/-- Read/read sharing is allowed; any overlapping writer is exclusive. -/
def konflikt (a b : ByteCap) : Bool :=
  ueberlappt a b && (darfSchreiben a.rechte || darfSchreiben b.rechte)

/-- Check newer escrows until the requested scope is found. `Option.none` denotes
    the lender outside all loans; `Option.some id` must match a saved loan exactly.
    Ancestors below that scope do not block its access; descendants do.
    Carrier/range checks also block aliases obtained by narrowing a grant. -/
def pruefeLeihen : List Loan → Grant → Option Nat → ByteCap → Except String Unit
  | [], _, Option.none, _ => Except.ok ()
  | [], _, Option.some _, _ => Except.error leiheUnbekannt
  | l :: rest, g, scope, wanted =>
      if scope = Option.some l.id then
        if g.cap = l.cap ∧ g.generation = l.lender.generation then
          Except.ok ()
        else Except.error leihePasstNicht
      else if konflikt l.cap wanted = true then Except.error leiheAktiv
      else pruefeLeihen rest g scope wanted

/-- An access checks one byte with precisely the requested right. -/
def punkt (c : ByteCap) (i : Nat) (p : Perm) : ByteCap :=
  { traeger := c.traeger
    lo := i
    hi := i + 1
    rechte := p }

/-- Staleness is checked before looking at either loans or byte state.
    The optional final argument selects a borrower scope. -/
def gebrauchLies (table : GrantTable) (g : Grant) (i : Nat) (s : ByteState)
    (scope : Option Nat := Option.none) : Except String Nat :=
  if live table g then
    match pruefeLeihen table.loans g scope (punkt g.cap i Perm.lese) with
    | Except.error e => Except.error e
    | Except.ok _ => readByte g.cap i s
  else Except.error veraltet

/-- Grant-checked write, with the same scope and refusal order as reading. -/
def gebrauchSchreib (table : GrantTable) (g : Grant) (i v : Nat) (s : ByteState)
    (scope : Option Nat := Option.none) : Except String ByteState :=
  if live table g then
    match pruefeLeihen table.loans g scope (punkt g.cap i Perm.schreibe) with
    | Except.error e => Except.error e
    | Except.ok _ => writeByte g.cap i v s
  else Except.error veraltet

/-- Refusals commit no byte-state change. -/
def zustandNach (s : ByteState) : Except String ByteState → ByteState
  | Except.error _ => s
  | Except.ok next => next

/-- Revoke only at quiescence: every outstanding loan on the carrier blocks
    revocation, including shared read loans. -/
def widerrufe (table : GrantTable) (carrier : Nat) : Except String GrantTable :=
  if table.loans.any (fun l => decide (l.cap.traeger = carrier)) = true then
    Except.error leiheAktiv
  else Except.ok
    { table with
      generation := fun t =>
        if t = carrier then table.generation t + 1 else table.generation t }

/-- Lend a well-formed sub-range with at most the lender's rights. Reborrow
    uses the same scope check as access; active identifiers cannot be reused.
    No byte state is accepted or returned by this metadata operation. -/
def leihe (table : GrantTable) (g : Grant) (c : ByteCap) (id : Nat)
    (scope : Option Nat := Option.none) : Except String GrantTable :=
  if live table g then
    if c.traeger = g.cap.traeger ∧ g.cap.lo ≤ c.lo ∧
        c.lo ≤ c.hi ∧ c.hi ≤ g.cap.hi then
      if schwaecher c.rechte g.cap.rechte = true then
        if table.loans.any (fun l => decide (l.id = id)) = true then
          Except.error leiheKennungBelegt
        else
          match pruefeLeihen table.loans g scope c with
          | Except.error e => Except.error e
          | Except.ok _ => Except.ok
              { table with
                loans := { cap := c
                           lender := g
                           id := id } :: table.loans }
      else Except.error leiheRechte
    else Except.error leiheBereich
  else Except.error veraltet

/-- Return only the innermost escrow. Outer returns are refused even when
    the outer loan concerns another carrier. No byte contents are rolled back. -/
def gibZurueck (table : GrantTable) (id : Nat) : Except String GrantTable :=
  match table.loans with
  | [] => Except.error leiheUnbekannt
  | l :: rest =>
      if id = l.id then Except.ok { table with loans := rest }
      else Except.error leiheReihenfolge

end Gabbro.Grammatik.Niedrig.Bytes
