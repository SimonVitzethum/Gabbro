/-
  File:      Grammatik/X86/HwKapsteinZwei.lean
  Subject:   Capstone, second step: the families merged since the first union.

  Lane 1311: on top of the first union `HwVollSchritt` (lane 1149,
  `HwKapstein.lean`, reused unchanged), add one union arm per family
  merged since: `IntRotate`, `IntCarryForms`, `IntBitTest`,
  `IntBitScan`, `HwPaging`, `HwPagingLarge`, `HwTranslate`,
  `HwSegTlb`, `HwMemTypesWC`, `HwContextState`, `HwFpStoreDrain`,
  `HwPageFaultDelivery`, `Avx2State`, `Avx2Mem`, `Avx2Join`.
  Every accepted definition is reused unchanged (lifted, never
  redefined); no new machine, no new evaluator, no new adapter.
-/
import Grammatik.X86.HwKapstein
import Grammatik.X86.IntRotate
import Grammatik.X86.IntCarryForms
import Grammatik.X86.IntBitTest
import Grammatik.X86.IntBitScan
import Grammatik.X86.HwPaging
import Grammatik.X86.HwPagingLarge
import Grammatik.X86.HwTranslate
import Grammatik.X86.HwSegTlb
import Grammatik.X86.HwMemTypesWC
import Grammatik.X86.HwContextState
import Grammatik.X86.HwFpStoreDrain
import Grammatik.X86.HwPageFaultDelivery
import Grammatik.X86.Avx2State
import Grammatik.X86.Avx2Mem
import Grammatik.X86.Avx2Join

namespace Gabbro.Grammatik.X86

/-- Second-union events: the whole first union plus one tag per
    family merged since. -/
inductive Kap2Ereignis where
  | alt : KapEreignis → Kap2Ereignis
  | rot : Nat → RotDecodiert → Kap2Ereignis
  | carry : Nat → CarryInstr → Kap2Ereignis
  | bittest : Nat → BtDecodiert → Kap2Ereignis
  | bitscan : Nat → PopcntMerkmal → BsDecodiert → Kap2Ereignis
  | fpstore : Nat → FpStoreEreignis → Kap2Ereignis
  | pf : Nat → PfEreignis → Kap2Ereignis
  | ctx : Nat → CtxEreignis → Kap2Ereignis
  | wc : Nat → HwMemWC1287.WcZugriff1287 → Kap2Ereignis
  | avx2mem : Nat → Avx2MemEreignis → Kap2Ereignis
  | avx2tor : CpuMerkmal → Xcr0Bild → KontrollBild → Nat → ExtInstr → Kap2Ereignis
  | seiten : Nat → SeitenAnfrage → Kap2Ereignis
  | gross : Nat → SeitenAnfrage → Kap2Ereignis
  | uebersetz : Nat → SeitenAnfrage → Kap2Ereignis

end Gabbro.Grammatik.X86
