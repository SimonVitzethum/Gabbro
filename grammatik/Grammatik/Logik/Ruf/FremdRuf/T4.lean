/- Part 4 of `FremdRuf` (C08 foundation): boundary records, the live-grant
   inventory and the provider transition judgment.

   A boundary record is ghost specification data for one foreign step: the item,
   its actual entry/exit memories, the raw answer, the decoded success and the
   declared grant/release identity. The deterministic fold of those records is the
   live-grant inventory (a success grant inserts, a declared release removes).
   `ProviderOk`/`ProviderRealisiert` is the provider clause of `ForeignPflicht`:
   every record is tied to the actual binding (`O.wirkt`), failure introduces no
   grant and meets the declared failure frame, success is fresh and disjoint, and
   releases hit live grants. Release against the ownership ledger and reuse with no
   outstanding borrow stay open (the ledger lives with the arenas); the byte-level
   region membership and the injective physical mapping compose later with
   `Adressen/Bereich` and IR-06 (C12 spaces are a prerequisite). -/
module

public import Grammatik.Kern.Syntax.Syntax.Teil2
public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Kern.Syntax.Satz

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- A granted extent: table identity, byte base, length, alignment and rights. -/
structure Konzession (D : Deklaration) where
  tab : D.Tab
  basis : Int
  laenge : Nat
  ausrichtung : Nat := 1
  schreibrecht : Bool := true

/-- The key of a grant: table and byte base. Freshness forbids reissue while live. -/
def Konzession.schluessel (k : Konzession D) : D.Tab × Int := (k.tab, k.basis)

/-- Two concessions overlap: same table with intersecting byte ranges. -/
def Konzession.ueberschneidet (j k : Konzession D) : Prop :=
  j.tab = k.tab ∧ j.basis < k.basis + (k.laenge : Int) ∧ k.basis < j.basis + (j.laenge : Int)

/-- A boundary record (C08): one foreign step with its actual entry/exit memories,
    raw answer, decoded success and declared grant/release identity. Erased from
    emitted code, not a second executable heap. -/
structure BoundaryRecord (D : Deklaration) where
  ax : D.Ax
  args : Env D (D.aparams ax)
  eingabe : World D
  ausgabe : World D
  roh : Int
  erfolg : Bool
  konzession : Option (Konzession D) := none
  freigabe : Option (D.Tab × Int) := none

/-- One record folded into the inventory: a declared release removes, a success
    grant inserts, anything else keeps the inventory. -/
def grantSchritt (inv : List (Konzession D)) (r : BoundaryRecord D) : List (Konzession D) :=
  match r.freigabe with
  | some key => inv.filter (fun k => !decide (k.schluessel = key))
  | none =>
    match r.erfolg, r.konzession with
    | true, some k => inv ++ [k]
    | _, _ => inv

/-- The fold, chronological: the head record first. -/
def GrantInventoryAux (inv : List (Konzession D)) : List (BoundaryRecord D) → List (Konzession D)
  | [] => inv
  | r :: rest => GrantInventoryAux (grantSchritt inv r) rest

/-- `GrantInventory` is the deterministic fold of the boundary records. -/
def GrantInventory (H : List (BoundaryRecord D)) : List (Konzession D) :=
  GrantInventoryAux [] H

theorem grantInventory_nil : GrantInventory (D := D) [] = [] := rfl

theorem grantInventoryAux_anhang (inv : List (Konzession D)) (H L : List (BoundaryRecord D)) :
    GrantInventoryAux inv (H ++ L) = GrantInventoryAux (GrantInventoryAux inv H) L := by
  induction H generalizing inv with
  | nil => rfl
  | cons r rest ih =>
    simp only [List.cons_append, GrantInventoryAux]
    exact ih _

theorem grantInventory_anhang (H : List (BoundaryRecord D)) (r : BoundaryRecord D) :
    GrantInventory (H ++ [r]) = grantSchritt (GrantInventory H) r :=
  grantInventoryAux_anhang [] H [r]

/-- The meaning of a boundary clause (C08): a Prop over the entry live-grant
    inventory, the exit world and the success grant. Pre-clauses hold at the call;
    output clauses apply only to success. Input clauses demand an open provider
    table; output lengths and freshness/disjointness are exact; release demands a
    live grant of the table (whose base and ledger check strengthen later). -/
def klauselGilt (a : D.Ax) (σ0 : World D) (ρ : Env D (D.aparams a))
    (vor : List (Konzession D)) (σ1 : World D) (grant : Option (Konzession D)) :
    BoundaryClause D (D.asignatur a) → Prop
  | .eingabe _ _ t _ _ _ _ => D.offen t = true
  | .ausgabe _ t _ _ m len =>
    ∀ k, grant = some k → k.tab = t ∧ k.laenge = (eval σ0 len σ0 ρ).n.toNat
  | .frisch _ t _ _ =>
    ∀ k, grant = some k → k.tab = t ∧ k ∉ vor ∧ ∀ j ∈ vor, ¬ j.ueberschneidet k
  | .freigabe _ _ t _ _ => ∃ b : Int, (t, b) ∈ vor.map Konzession.schluessel

/-- The provider transition judgment (C08): `ProviderOk O inv H` says the history `H`
    realizes the live-grant inventory `inv` against the actual binding `O`. Every
    record answers through `O.wirkt`; failure introduces no grant and meets the
    declared failure frame; success is positive, aligned, fresh and disjoint;
    release removes a live grant and introduces none. -/
inductive ProviderOk (O : Orakel D) :
    List (Konzession D) → List (BoundaryRecord D) → Prop where
  | nil : ProviderOk O [] []
  | erfolg {inv : List (Konzession D)} {H : List (BoundaryRecord D)} (h : ProviderOk O inv H)
      (r : BoundaryRecord D)
      (link : O.wirkt r.ax r.eingabe r.args = (r.ausgabe, r.roh))
      (frame : Rahmen (D.aschreibt r.ax) (D.agschreibt r.ax) r.eingabe r.ausgabe)
      (ok : r.erfolg = true) (k : Konzession D) (hk : r.konzession = some k)
      (pos : 0 < k.laenge) (align : 0 < k.ausrichtung)
      (frisch : ∀ j ∈ inv, ¬ j.ueberschneidet k)
      (frei : r.freigabe = none) :
      ProviderOk O (inv ++ [k]) (H ++ [r])
  | fehler {inv : List (Konzession D)} {H : List (BoundaryRecord D)} (h : ProviderOk O inv H)
      (r : BoundaryRecord D)
      (link : O.wirkt r.ax r.eingabe r.args = (r.ausgabe, r.roh))
      (frame : Rahmen (D.aschreibt r.ax) (D.agschreibt r.ax) r.eingabe r.ausgabe)
      (ok : r.erfolg = false) (nogrant : r.konzession = none) (frei : r.freigabe = none) :
      ProviderOk O inv (H ++ [r])
  | freigabe {inv : List (Konzession D)} {H : List (BoundaryRecord D)} (h : ProviderOk O inv H)
      (r : BoundaryRecord D)
      (link : O.wirkt r.ax r.eingabe r.args = (r.ausgabe, r.roh))
      (frame : Rahmen (D.aschreibt r.ax) (D.agschreibt r.ax) r.eingabe r.ausgabe)
      (key : D.Tab × Int) (hk : r.freigabe = some key) (nogrant : r.konzession = none)
      (live : ∃ k ∈ inv, k.schluessel = key) :
      ProviderOk O (inv.filter (fun k => !decide (k.schluessel = key))) (H ++ [r])

theorem grantSchritt_erfolg (inv : List (Konzession D)) (r : BoundaryRecord D) (k : Konzession D)
    (frei : r.freigabe = none) (ok : r.erfolg = true) (hk : r.konzession = some k) :
    grantSchritt inv r = inv ++ [k] := by
  simp only [grantSchritt, frei, ok, hk]

theorem grantSchritt_fehler (inv : List (Konzession D)) (r : BoundaryRecord D)
    (frei : r.freigabe = none) (ok : r.erfolg = false) (nogrant : r.konzession = none) :
    grantSchritt inv r = inv := by
  simp only [grantSchritt, frei, ok, nogrant]

theorem grantSchritt_freigabe (inv : List (Konzession D)) (r : BoundaryRecord D)
    (key : D.Tab × Int) (hk : r.freigabe = some key) :
    grantSchritt inv r = inv.filter (fun k => !decide (k.schluessel = key)) := by
  simp only [grantSchritt, hk]

/-- The judgment agrees with the deterministic fold. (Induction hypotheses come after ALL
    fields of a constructor.) -/
theorem providerOk_inventar {O : Orakel D} {inv : List (Konzession D)}
    {H : List (BoundaryRecord D)} (h : ProviderOk O inv H) : inv = GrantInventory H := by
  induction h with
  | nil => rfl
  | erfolg h r link frame ok k hk pos align frisch frei ih =>
    rw [grantInventory_anhang, ← ih, grantSchritt_erfolg _ r k frei ok hk]
  | fehler h r link frame ok nogrant frei ih =>
    rw [grantInventory_anhang, ← ih, grantSchritt_fehler _ r frei ok nogrant]
  | freigabe h r link frame key hk nogrant live ih =>
    rw [grantInventory_anhang, ← ih, grantSchritt_freigabe _ r key hk]

/-- The provider clause: some inventory realizes the history against `O`. -/
def ProviderRealisiert (O : Orakel D) (H : List (BoundaryRecord D)) : Prop :=
  ∃ inv, ProviderOk O inv H

theorem providerRealisiert_nil (O : Orakel D) : ProviderRealisiert O [] :=
  ⟨[], .nil⟩

end Gabbro.Grammatik
