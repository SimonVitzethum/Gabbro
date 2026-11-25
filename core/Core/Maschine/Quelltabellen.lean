module

public import Core.Maschine.Kontext
public import Core.Katalog.Aussen

@[expose] public section

namespace Gabbro.Core.Maschine

/-- **The finite domain declaration** of a unit: the domain count, the finite assignment tables
    for contexts, memory objects and device objects, and the declared channels.
    Pure data; lookup below is total with default domain `0`. The unit carries its table in
    `Einheit.domaenen` (`Core/Maschine/Start.lean`); the checker row (`Core/Annahme/Lokal.lean`)
    decides exactly this table. -/
structure DomaenenTabelle where
  domaenen : Nat
  kontexte : List (Kontext × Nat)
  objekte : List (Nat × Nat)
  geraete : List (Katalog.Objekt × Nat)
  kanaele : List (Nat × Nat)

/-- Total lookup of a context's domain: the table entry, or `0` when unlisted. -/
def tabKontext (tab : DomaenenTabelle) (c : Kontext) : Nat :=
  ((tab.kontexte.find? (fun e => decide (e.1 = c))).map (fun e => e.2)).getD 0

/-- Total lookup of a memory object's domain: the table entry, or `0` when unlisted. -/
def tabObjekt (tab : DomaenenTabelle) (n : Nat) : Nat :=
  ((tab.objekte.find? (fun e => decide (e.1 = n))).map (fun e => e.2)).getD 0

/-- Total lookup of a device object's domain: the table entry, or `0` when unlisted. -/
def tabGeraet (tab : DomaenenTabelle) (o : Katalog.Objekt) : Nat :=
  ((tab.geraete.find? (fun e => decide (e.1 = o))).map (fun e => e.2)).getD 0

/-- **The static checker line for tables**: a positive domain count, every table entry
    inside the declared domains, every channel between declared domains. -/
def pruefeDomaenenTab (tab : DomaenenTabelle) : Bool :=
  decide (0 < tab.domaenen) &&
    tab.kontexte.all (fun e => decide (e.2 < tab.domaenen)) &&
    tab.objekte.all (fun e => decide (e.2 < tab.domaenen)) &&
    tab.geraete.all (fun e => decide (e.2 < tab.domaenen)) &&
    tab.kanaele.all (fun k => decide (k.1 < tab.domaenen) && decide (k.2 < tab.domaenen))

/-- **Table coherence**: the exact finite condition the checker decides — a positive
    domain count with every table entry and every channel endpoint in scope. -/
def tabKohaerent (tab : DomaenenTabelle) : Prop :=
  0 < tab.domaenen ∧
    (∀ e ∈ tab.kontexte, e.2 < tab.domaenen) ∧
    (∀ e ∈ tab.objekte, e.2 < tab.domaenen) ∧
    (∀ e ∈ tab.geraete, e.2 < tab.domaenen) ∧
    (∀ k ∈ tab.kanaele, k.1 < tab.domaenen ∧ k.2 < tab.domaenen)

/-- The single-domain table: everything unlisted, hence owned by domain `0`. -/
def eineTabelle : DomaenenTabelle where
  domaenen := 1
  kontexte := []
  objekte := []
  geraete := []
  kanaele := []

/-- The empty-domain table: no domain to assign to. -/
def leereTabelle : DomaenenTabelle where
  domaenen := 0
  kontexte := []
  objekte := []
  geraete := []
  kanaele := []

/-- The single-domain table passes the line. -/
theorem eineTabelle_akzeptiert : pruefeDomaenenTab eineTabelle = true := rfl

/-- The single-domain table is coherent. -/
theorem eineTabelle_kohaerent : tabKohaerent eineTabelle :=
  ⟨Nat.zero_lt_one, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim⟩

/-- The line refuses the empty-domain table. -/
theorem leereTabelle_verweigert : pruefeDomaenenTab leereTabelle = false := rfl

/-- Partial operations for which an unhandled use requires a generated guard. -/
inductive PartielleOperation where
  | division
  | modulo
  | index
  | shift
  | konvertierung
  | entpacken
  | ganzzahlBereich
  | teilfolge
  deriving DecidableEq, Repr

/-- The inputs required to check one use. Integer narrowing uses the exact
    result relative to the lower bound and the cardinality of the declared range. -/
def Operanden : PartielleOperation → Type
  | .division => Nat × Nat
  | .modulo => Nat × Nat
  | .index => Nat × Nat
  | .shift => Nat × Nat
  | .konvertierung => Nat × Nat
  | .entpacken => Nat
  | .ganzzahlBereich => Int × Nat
  | .teilfolge => Int × Int × Nat


/-- Translate the declared inclusive range to a zero-based interval. An empty
    range has cardinality zero and admits no value. -/
def ganzzahlBereichOperanden (wert lo hi : Int) : Operanden .ganzzahlBereich :=
  (wert - lo, (hi + 1 - lo).toNat)

/-- Written predicates, kept in source order as elaboration combines fragments. -/
structure Quellklauseln (S : Type) where
  voraus : List (S → Prop)
  sicher : List (S → Prop)
  invariant : List (S → Prop)

def Quellklauseln.leer : Quellklauseln S := ⟨[], [], []⟩

def Quellklauseln.anhaengen (a b : Quellklauseln S) : Quellklauseln S :=
  ⟨a.voraus ++ b.voraus, a.sicher ++ b.sicher, a.invariant ++ b.invariant⟩

/-- Data produced by elaboration. Guards are indexed by pre-state and have no
    dependency on the existence of a successor or on implementation execution. -/
structure Quelltabellen (S : Type) where
  klauseln : Quellklauseln S
  guard : S → (op : PartielleOperation) → Operanden op → Prop

def Quelltabellen.leer : Quelltabellen S := ⟨.leer, fun _ _ _ => False⟩

end Gabbro.Core.Maschine
