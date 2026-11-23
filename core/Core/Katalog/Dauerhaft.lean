module
public import Core.Katalog.Seiten

@[expose] public section

namespace Gabbro.Core.Katalog

/-- A write is identified by its issue order within one persistence domain. -/
structure PersistSchreib where
  index : Nat
  addr : Nat
  wert : UInt8
  deriving DecidableEq, Repr

structure PersistZustand where
  /-- Newest first. Superseded writes may have already reached the medium. -/
  fluechtig : List PersistSchreib
  eingereiht : List PersistSchreib
  dauerhaft : Nat → UInt8
  /-- Greatest persisted write per byte, to prevent a later drain from rolling the byte back. -/
  letzter : Nat → Option Nat
  next : Nat

def PersistZustand.leer (image : Nat → UInt8) : PersistZustand :=
  ⟨[], [], image, fun _ => none, 0⟩

inductive PersistEreignis where
  | write (addr : Nat) (value : UInt8)
  | flush (range : Strecke)
  | durable (write : PersistSchreib)
  | discard (write : PersistSchreib)
  | fence
  | crash
  deriving DecidableEq, Repr

/-- A byte can reach the medium after a flush, in any order between bytes. A fence returns only
    after the pending history drains. A crash can be taken from every state and loses pending work. -/
inductive persistenz (region : Strecke) :
    PersistZustand → PersistEreignis → PersistZustand → Prop where
  | write {s addr value} (within : region.drin addr) :
      persistenz region s (.write addr value)
        { s with fluechtig := ⟨s.next, addr, value⟩ :: s.fluechtig, next := s.next + 1 }
  | flush {s range} (within : region.enthaelt range) :
      persistenz region s (.flush range)
        { s with
          fluechtig := s.fluechtig.filter (fun w => !(range.von ≤ w.addr && w.addr < range.bis))
          eingereiht := s.fluechtig.filter (fun w => range.von ≤ w.addr && w.addr < range.bis) ++
            s.eingereiht }
  | durable {s w} (queued : w ∈ s.eingereiht)
      (fresh : ∀ i, s.letzter w.addr = some i → i < w.index) :
      persistenz region s (.durable w)
        { s with
          dauerhaft := fun a => if a = w.addr then w.wert else s.dauerhaft a
          letzter := fun a => if a = w.addr then some w.index else s.letzter a
          eingereiht := s.eingereiht.erase w }
  | superseded {s w i} (queued : w ∈ s.eingereiht)
      (persisted : s.letzter w.addr = some i) (old : w.index ≤ i) :
      persistenz region s (.discard w) { s with eingereiht := s.eingereiht.erase w }
  | fence {s} (drained : s.eingereiht = []) : persistenz region s .fence s
  | crash (s) :
      persistenz region s .crash { s with fluechtig := [], eingereiht := [] }

theorem absturz_immer (r : Strecke) (s : PersistZustand) :
    ∃ t, persistenz r s .crash t ∧ t.dauerhaft = s.dauerhaft :=
  ⟨_, .crash s, rfl⟩

end Gabbro.Core.Katalog
