/-
  File:      Grammatik/X86/LockedOps.lean
  Subject:   LOCK-prefixed single-op RMW (XADD shape) and MFENCE as machine
             definitions over the canonical TSO target state.

  Lane 339 (plan A5): new target forms with per-event access records and
  full-barrier order facts. Reuses the canonical `TSOZustand`/`TSOSchritt`
  vocabulary, `read64`/`write64`, `Fuss` and `zugriff`; it adds NO new
  evaluator for the existing 14 `Befehl` forms and claims NO W/GX
  refinement (the bridge owns it) and NO cycle bound (shape cost only).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.TSO
import Grammatik.X86.Zugriffe

namespace Gabbro.Grammatik.X86

/-- Locked target forms: one single-op read-modify-write (XADD shape with
    an explicit word delta) and one full fence. No other LOCK form exists. -/
inductive SperrBefehl where
  | xadd64 (addr : Adresse) (delta : Wort)
  | mfence
  deriving DecidableEq, Repr

/-- Per-event access record of one locked step: the acting core, the read
    and written byte footprints, the observed old and installed new word
    (exactly for the RMW form), and the shape tags. -/
structure LockEreignis where
  kern : Nat
  lesen : List Adresse
  schreiben : List Adresse
  gelesen : Option Wort
  geschrieben : Option Wort
  istRmw : Bool
  istZaun : Bool
  deriving DecidableEq, Repr

/-- Declared alignment guard of the locked word form: the byte address is
    8-divisible. Ordinary unaligned accesses stay allowed; only the LOCK
    form demands this, as its selected profile contract. -/
def ausgerichtet8 (a : Adresse) : Bool :=
  decide (a.toNat % 8 = 0)

end Gabbro.Grammatik.X86
