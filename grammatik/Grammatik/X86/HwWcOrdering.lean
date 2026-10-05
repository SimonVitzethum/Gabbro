/-
  File:      Grammatik/X86/HwWcOrdering.lean
  Subject:   WC eviction order and CLFLUSHOPT/CLWB on the lifted WC machine.

  Lane 1301: follow-up of lane 1287 (`HwMemTypesWC.lean`): its CUTS leave
  OPEN cross-core WC same-line eviction order, WC read ordering, and
  CLFLUSHOPT/CLWB. This file lifts the accepted 1287 machine
  (`HwWcMaschine1287`) unchanged -- never copied -- and adds: WC buffer
  eviction as a nondeterministic oldest-first drain step, a same-core WC
  read observation after a WC store, CLFLUSHOPT (weakly ordered, ordered
  by SFENCE/MFENCE) and CLWB (no invalidation requirement).

  Manual provenance (official Intel SDM 325462-093US, September 2026,
  local `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`):
  - CLFLUSHOPT entry: `NFx 66 0F AE /7`, ordered wrt fences, locked
    RMW and older writes to the line; NOT ordered wrt other
    CLFLUSHOPT/CLFLUSH/CLWB or younger writes; SFENCE orders it;
    byte-load faults (execute-only allowed); #UD without the CPUID bit.
  - CLWB entry: `66 0F AE /6`, same fence/older-write ordering, same
    non-ordering, writes back and MAY retain the line (no invalidation);
    byte-load faults; #UD without the CPUID bit.
  - Vol.1 12.8/WC buffer: separate from caches and store buffer, not
    snooped (no coherency); eviction protocol is implementation
    dependent; WC weakly ordered; buffer 2 may appear before buffer 1
    on the bus; partial writes possible.
  The memory-ordering chapter is NOT supplied in the clone: every
  ordering rule below is a NAMED assumption (`WcEvictOrdAnnahme1301`,
  `ClflushoptZaunAnnahme1301`, `ClwbKeepAnnahme1301`); silicon behaviour
  is never proved.
-/
import Grammatik.X86.HwMemTypesWC

namespace Gabbro.Grammatik.X86

namespace HwWcOrd1301

/-- Observable events on the lifted WC machine: a retired WC store, a
    spontaneous eviction drain, a same-core WC read observation, the two
    weakly ordered flushes (each carrying its stated CPUID bit), and a
    fence drain. The acting core rides the event wherever the effect is
    per-core, as in `HwEreignis` and `WcEreignis1287`. -/
inductive WcOrdEreignis1301 where
  | wcGepuffert : Nat → Adresse → Byte → WcOrdEreignis1301
  | evict : Nat → Adresse → Byte → WcOrdEreignis1301
  | wcGelesen : Nat → Adresse → Byte → WcOrdEreignis1301
  | clflushopt : Nat → Bool → Adresse → WcOrdEreignis1301
  | clwb : Nat → Bool → Adresse → WcOrdEreignis1301
  | zaun : Nat → WcOrdEreignis1301
  deriving DecidableEq, Repr

end HwWcOrd1301

end Gabbro.Grammatik.X86
