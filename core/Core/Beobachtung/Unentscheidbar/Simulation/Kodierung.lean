module

public import Core.Beobachtung.Unentscheidbar.Modell
public import Mathlib.Logic.Encodable.Basic
import Mathlib.Basic.Countable.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.Tactic.DeriveCountable

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Katalog

noncomputable section

instance : Countable UInt32 :=
  (show Function.Injective (fun x : UInt32 => x.toNat) from
    fun a b h => UInt32.toNat_inj.mp h).countable

deriving instance Countable for Char

instance : Encodable Char := Encodable.ofCountable _

instance : Countable Identifier := by
  dsimp only [Identifier]
  infer_instance

deriving instance Countable for Arith
deriving instance Countable for Compare
deriving instance Countable for LowLevel.AddressSpace
deriving instance Countable for PtrRecht
deriving instance Countable for CarrierAccess
deriving instance Countable for CarrierEffect
deriving instance Countable for Ty
deriving instance Countable for DienstAbi
deriving instance Countable for FirmwareZeile
deriving instance Countable for WrittenType, WrittenTypes
deriving instance Countable for RegionInitializer
deriving instance Countable for Rufstelle

instance : Encodable Arith := Encodable.ofCountable _
instance : Encodable Compare := Encodable.ofCountable _
instance : Encodable LowLevel.AddressSpace := Encodable.ofCountable _
instance : Encodable PtrRecht := Encodable.ofCountable _
instance : Encodable CarrierAccess := Encodable.ofCountable _
instance : Encodable CarrierEffect := Encodable.ofCountable _
instance : Encodable (Ty .value) := Encodable.ofCountable _
instance : Encodable DienstAbi := Encodable.ofCountable _
instance : Encodable FirmwareZeile := Encodable.ofCountable _
instance : Encodable WrittenType := Encodable.ofCountable _
instance : Encodable WrittenTypes := Encodable.ofCountable _
instance : Encodable RegionInitializer := Encodable.ofCountable _
instance : Encodable Rufstelle := Encodable.ofCountable _
instance : Encodable Identifier := Encodable.ofCountable _

/-- A first-order code: a constructor tag and Encodable numbers of its data
    fields. Proof fields are irrelevant and omitted. -/
abbrev FlatBefehl := Nat × List Nat

def zuFlat : Befehl → FlatBefehl
  | .literal z v => (0, [z, v])
  | .binaer op l => (1, [Encodable.encode op, l])
  | .binden n s => (2, [Encodable.encode n, s])
  | .wahrheitswert z w => (3, [z, Encodable.encode w])
  | .lesen z i => (4, [z, i])
  | .negativ z m => (5, [z, m])
  | .negieren z => (6, [z])
  | .verneinen z => (7, [z])
  | .teilen l => (8, [l])
  | .vergleichen op l => (9, [Encodable.encode op, l])
  | .springeWenn q b d => (10, [q, Encodable.encode b, d])
  | .zuweisen q i t => (11, [q, i, Encodable.encode t])
  | .zurueck q t => (12, [q, Encodable.encode t])
  | .springe d => (13, [d])
  | .blockEnde c => (14, [c])
  | .bindeWert q t g => (15, [q, Encodable.encode t, Encodable.encode g])
  | .definiere n ps r g s m calls eff => (16, [Encodable.encode n,
      Encodable.encode ps, Encodable.encode r, g, s, Encodable.encode m,
      Encodable.encode calls, Encodable.encode eff])
  | .rufe n args bind => (17, [Encodable.encode n, Encodable.encode args,
      Encodable.encode bind])
  | .rueckVoid => (18, [])
  | .pruefeMass q => (19, [q])
  | .setzePasszahl q d => (20, [q, d])
  | .whileTest q e h => (21, [q, e, Encodable.encode h])
  | .forAnfang u o i s sh miss => (22, [u, o, Encodable.encode i, s,
      Encodable.encode sh, Encodable.encode miss])
  | .forTest e h => (23, [e, Encodable.encode h])
  | .forNaechster b i => (24, [b, Encodable.encode i])
  | .zurueckSprung d => (25, [d])
  | .starte n => (26, [Encodable.encode n])
  | .ende => (27, [])
  | .baueArray z e c => (28, [z, Encodable.encode e, c])
  | .liesArray b e c => (29, [b, Encodable.encode e, c])
  | .baueTupel z ts => (30, [z, Encodable.encode ts])
  | .liesTupelfeld b ts i => (31, [b, Encodable.encode ts, i.val, ts.length])
  | .bindeTupel q ts b => (32, [q, Encodable.encode ts, Encodable.encode b])
  | .definiereRecord n ls ts => (33, [Encodable.encode n,
      Encodable.encode ls, Encodable.encode ts])
  | .baueRecord z n ls ts ss => (34, [z, Encodable.encode n,
      Encodable.encode ls, Encodable.encode ts, Encodable.encode ss])
  | .liesRecordFeld b n ls ts i => (35, [b, Encodable.encode n,
      Encodable.encode ls, Encodable.encode ts, i.val, ts.length])
  | .setzeRecordFeld s il n ls ts i => (36, [s, il, Encodable.encode n,
      Encodable.encode ls, Encodable.encode ts, i.val, ts.length])
  | .definiereVariante n ls cs => (37, [Encodable.encode n,
      Encodable.encode ls, Encodable.encode cs])
  | .baueVariante z n ls cs i => (38, [z, Encodable.encode n,
      Encodable.encode ls, Encodable.encode cs, i.val, cs.length])
  | .waehleVariante s n ls cs br => (39, [s, Encodable.encode n,
      Encodable.encode ls, Encodable.encode cs, Encodable.encode br])
  | .textLiteral z d => (40, [z, Encodable.encode d])
  | .textConcat b a c => (41, [b, a, c])
  | .textIndex b c => (42, [b, c])
  | .substring b c => (43, [b, c])
  | .textLength b c => (44, [b, c])
  | .definiereTraeger c ls layout e => (45, [c, Encodable.encode ls,
      Encodable.encode layout, Encodable.encode e])
  | .optionIstBesetzt z c => (46, [z, c])
  | .definiereEffektgruppe eff => (47, [Encodable.encode eff])
  | .waehleUmgebung n abi row => (48, [Encodable.encode n,
      Encodable.encode abi, Encodable.encode row])
  | .bindeRegion r init => (49, [r, Encodable.encode init])

def finVonCode {α : Type} (xs : List α) (i len : Nat) : Option (Fin xs.length) :=
  if hlen : xs.length = len then
    if hi : i < len then some ⟨i, by simpa only [hlen] using hi⟩ else none
  else none

def vonFlat : FlatBefehl → Option Befehl
  | (0, [z, v]) => some (.literal z v)
  | (1, [op, l]) => (Encodable.decode op : Option Arith).map (fun o => .binaer o l)
  | (2, [n, s]) => (Encodable.decode n : Option Identifier).map (fun x => .binden x s)
  | (3, [z, w]) => (Encodable.decode w : Option Bool).map (fun x => .wahrheitswert z x)
  | (4, [z, i]) => some (.lesen z i)
  | (5, [z, m]) => some (.negativ z m)
  | (6, [z]) => some (.negieren z)
  | (7, [z]) => some (.verneinen z)
  | (8, [l]) => some (.teilen l)
  | (9, [op, l]) => (Encodable.decode op : Option Compare).map (fun o => .vergleichen o l)
  | (10, [q, b, d]) => (Encodable.decode b : Option Bool).map (fun x => .springeWenn q x d)
  | (11, [q, i, t]) => (Encodable.decode t : Option (Ty .value)).map (fun x => .zuweisen q i x)
  | (12, [q, t]) => (Encodable.decode t : Option (Ty .value)).map (fun x => .zurueck q x)
  | (13, [d]) => some (.springe d)
  | (14, [c]) => some (.blockEnde c)
  | (15, [q, t, g]) => do
      let ty : Ty .value ← Encodable.decode t
      let g' : Bool ← Encodable.decode g
      some (.bindeWert q ty g')
  | (16, [n, ps, r, g, s, m, calls, eff]) => do
      let name : Identifier ← Encodable.decode n
      let params : List (Ty .value) ← Encodable.decode ps
      let result : Option (Ty .value) ← Encodable.decode r
      let measure : Bool ← Encodable.decode m
      let ruft : List Rufstelle ← Encodable.decode calls
      let effects : Option (List CarrierEffect) ← Encodable.decode eff
      some (.definiere name params result g s measure ruft effects)
  | (17, [n, args, bind]) => do
      let name : Identifier ← Encodable.decode n
      let args' : List (Ty .value) ← Encodable.decode args
      let b : Option (Ty .value) ← Encodable.decode bind
      some (.rufe name args' b)
  | (18, []) => some .rueckVoid
  | (19, [q]) => some (.pruefeMass q)
  | (20, [q, d]) => some (.setzePasszahl q d)
  | (21, [q, e, h]) => (Encodable.decode h : Option Identifier).map (fun x => .whileTest q e x)
  | (22, [u, o, i, s, sh, miss]) => do
      let index : Ty .value ← Encodable.decode i
      let shadowed : Bool ← Encodable.decode sh
      let missing : Bool ← Encodable.decode miss
      some (.forAnfang u o index s shadowed missing)
  | (23, [e, h]) => (Encodable.decode h : Option Identifier).map (fun x => .forTest e x)
  | (24, [b, i]) => (Encodable.decode i : Option (Ty .value)).map (fun x => .forNaechster b x)
  | (25, [d]) => some (.zurueckSprung d)
  | (26, [n]) => (Encodable.decode n : Option Identifier).map (fun x => .starte x)
  | (27, []) => some .ende
  | (28, [z, e, c]) => (Encodable.decode e : Option (Ty .value)).map (fun x => .baueArray z x c)
  | (29, [b, e, c]) => (Encodable.decode e : Option (Ty .value)).map (fun x => .liesArray b x c)
  | (30, [z, ts]) => (Encodable.decode ts : Option (List (Ty .value))).map (fun x => .baueTupel z x)
  | (31, [b, ts, i, len]) => do
      let x : List (Ty .value) ← Encodable.decode ts
      let idx ← finVonCode x i len
      some (.liesTupelfeld b x idx)
  | (32, [q, ts, b]) => do
      let ts' ← Encodable.decode ts
      let bind : List Bool ← Encodable.decode b
      some (.bindeTupel q ts' bind)
  | (33, [n, ls, ts]) => do
      let name : List Char ← Encodable.decode n
      let labels : List Identifier ← Encodable.decode ls
      let types ← Encodable.decode ts
      some (.definiereRecord name labels types)
  | (34, [z, n, ls, ts, ss]) => do
      let name : List Char ← Encodable.decode n
      let labels : List Identifier ← Encodable.decode ls
      let types ← Encodable.decode ts
      let sources : List Nat ← Encodable.decode ss
      some (.baueRecord z name labels types sources)
  | (35, [b, n, ls, ts, i, len]) => do
      let name : List Char ← Encodable.decode n
      let labels : List Identifier ← Encodable.decode ls
      let types : List (Ty .value) ← Encodable.decode ts
      let idx ← finVonCode types i len
      some (.liesRecordFeld b name labels types idx)
  | (36, [s, il, n, ls, ts, i, len]) => do
      let name : List Char ← Encodable.decode n
      let labels : List Identifier ← Encodable.decode ls
      let types : List (Ty .value) ← Encodable.decode ts
      let idx ← finVonCode types i len
      some (.setzeRecordFeld s il name labels types idx)
  | (37, [n, ls, cs]) => do
      let name : List Char ← Encodable.decode n
      let labels : List Identifier ← Encodable.decode ls
      let cases' : List (Option (Ty .value)) ← Encodable.decode cs
      some (.definiereVariante name labels cases')
  | (38, [z, n, ls, cs, i, len]) => do
      let name : List Char ← Encodable.decode n
      let labels : List Identifier ← Encodable.decode ls
      let cases' : List (Option (Ty .value)) ← Encodable.decode cs
      let idx ← finVonCode cases' i len
      some (.baueVariante z name labels cases' idx)
  | (39, [s, n, ls, cs, br]) => do
      let name : List Char ← Encodable.decode n
      let labels : List Identifier ← Encodable.decode ls
      let cases' : List (Option (Ty .value)) ← Encodable.decode cs
      let branches : List (Nat × Bool) ← Encodable.decode br
      some (.waehleVariante s name labels cases' branches)
  | (40, [z, d]) => (Encodable.decode d : Option (List Char)).map (fun x => .textLiteral z x)
  | (41, [b, a, c]) => some (.textConcat b a c)
  | (42, [b, c]) => some (.textIndex b c)
  | (43, [b, c]) => some (.substring b c)
  | (44, [b, c]) => some (.textLength b c)
  | (45, [c, ls, layout, e]) => do
      let labels : List (List Char) ← Encodable.decode ls
      let layout' : Ty .value ← Encodable.decode layout
      let exported : Bool ← Encodable.decode e
      some (.definiereTraeger c labels layout' exported)
  | (46, [z, c]) => some (.optionIstBesetzt z c)
  | (47, [eff]) => (Encodable.decode eff : Option (List CarrierEffect)).map (fun x => .definiereEffektgruppe x)
  | (48, [n, abi, row]) => do
      let name : Identifier ← Encodable.decode n
      let a : DienstAbi ← Encodable.decode abi
      let r : FirmwareZeile ← Encodable.decode row
      some (.waehleUmgebung name a r)
  | (49, [r, init]) => (Encodable.decode init : Option RegionInitializer).map (fun x => .bindeRegion r x)
  | _ => none

theorem finVonCode_zuFlat {α : Type} (xs : List α) (i : Fin xs.length) :
    finVonCode xs i.val xs.length = some i := by
  simp only [finVonCode, ↓reduceDIte]
  rw [dif_pos i.isLt]

def vonFlat_zuFlat : (b : Befehl) → vonFlat (zuFlat b) = some b
  | .literal z v => by simp only [zuFlat, vonFlat]
  | .binaer op l => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .binden n s => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .wahrheitswert z w => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .lesen z i => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .negativ z m => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .negieren z => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .verneinen z => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .teilen l => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .vergleichen op l => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .springeWenn q b d => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .zuweisen q i t => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .zurueck q t => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .springe d => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .blockEnde c => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .bindeWert q t g => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .definiere n ps r g s m calls eff => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .rufe n args bind => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .rueckVoid => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .pruefeMass q => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .setzePasszahl q d => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .whileTest q e h => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .forAnfang u o i s sh miss => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .forTest e h => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .forNaechster b i => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .zurueckSprung d => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .starte n => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .ende => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .baueArray z e c => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .liesArray b e c => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .baueTupel z ts => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .liesTupelfeld b ts i => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind, finVonCode_zuFlat]
  | .bindeTupel q ts b => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .definiereRecord n ls ts => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .baueRecord z n ls ts ss => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .liesRecordFeld b n ls ts i => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind, finVonCode_zuFlat]
  | .setzeRecordFeld s il n ls ts i => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind, finVonCode_zuFlat]
  | .definiereVariante n ls cs => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .baueVariante z n ls cs i => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind, finVonCode_zuFlat]
  | .waehleVariante s n ls cs br => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .textLiteral z d => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .textConcat b a c => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .textIndex b c => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .substring b c => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .textLength b c => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .definiereTraeger c ls layout e => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .optionIstBesetzt z c => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .definiereEffektgruppe eff => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .waehleUmgebung n abi row => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]
  | .bindeRegion r init => by
      simp only [zuFlat, vonFlat, Encodable.encodek, Option.map_some, Option.bind_eq_bind]

instance : Encodable Befehl :=
  Encodable.ofLeftInjection zuFlat vonFlat vonFlat_zuFlat

end

/-- The Godel numbering of a command program is the Encodable numbering of the
    first-order syntax. No predicate ever inspects a micro-recursive code here. -/
noncomputable def kodiere (p : List Befehl) : ℕ :=
  Encodable.encode p

/-- Decoding is the Encodable inverse; the left inverse is `Encodable.encodek`. -/
noncomputable def dekodiere (n : ℕ) : Option (List Befehl) :=
  Encodable.decode n

theorem dekodiere_links (p : List Befehl) : dekodiere (kodiere p) = some p := by
  exact Encodable.encodek p

/-- The canonical start frame places the input as an exact integer in slot zero.
    All bound maps keep their default `none`, so the frame is open. -/
def startVon (n : ℕ) : Rahmen :=
  { pc := 0
    temp := fun slot => if slot = 0 then some ⟨.int (n : Int) (n : Int), Zahl.literal (n : Int)⟩ else none
    lokale := []
    rueckgabe := none }

theorem start_offen (n : ℕ) : OffenesFragment (startVon n) := by
  intro slot
  rfl

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation
