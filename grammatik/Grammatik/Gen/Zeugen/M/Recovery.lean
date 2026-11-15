/- Accepted recovery candidates; exact cell records follow the slot measurement. -/
module

import Grammatik.Gen.Druck.LeanZeuge

public import Grammatik.Gen.Zeugen.M.ScalarRead
public import Grammatik.Gen.Zeugen.Reset
public import Grammatik.Gen.Zeugen.M.F00_call
public import Grammatik.Gen.Zeugen.M.F01_chain
public import Grammatik.Gen.Zeugen.M.F02_foot
public import Grammatik.Gen.Zeugen.M.F03_reg
public import Grammatik.Gen.Zeugen.M.F04_nolock
public import Grammatik.Gen.Zeugen.M.F06_pool
public import Grammatik.Gen.Zeugen.M.F07_race
public import Grammatik.Gen.Zeugen.M.F08_answer
public import Grammatik.Gen.Zeugen.M.F09_mask
public import Grammatik.Gen.Zeugen.M.M16_13
public import Grammatik.Gen.Zeugen.M.M169_350
public import Grammatik.Gen.Zeugen.M.M103_803
public import Grammatik.Gen.Zeugen.M.M103_131

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen.Recovery

open Gabbro.Grammatik Gabbro.Grammatik.Gen

def fixtures : List Einsatz := [F00_call.e, F01_chain.e, F02_foot.e, F03_reg.e, F04_nolock.e, F06_pool.e, F07_race.e, F08_answer.e, F09_mask.e, M16_13.e, M169_350.e, M103_803.e, M103_131.e]

theorem checked : ∀ e ∈ fixtures, e.gueltig = true := by
  intro e member
  simp only [fixtures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact F00_call.e_gueltig
  · exact F01_chain.e_gueltig
  · exact F02_foot.e_gueltig
  · exact F03_reg.e_gueltig
  · exact F04_nolock.e_gueltig
  · exact F06_pool.e_gueltig
  · exact F07_race.e_gueltig
  · exact F08_answer.e_gueltig
  · exact F09_mask.e_gueltig
  · exact M16_13.e_gueltig
  · exact M169_350.e_gueltig
  · exact M103_803.e_gueltig
  · exact M103_131.e_gueltig

/-- The original Boolean-read and reset baselines are retained. -/
def baseline : List Einsatz := [ScalarRead.e, Reset.Good.e]

#eval ((baseline.flatMap Einsatz.zellen).eraseDups.map (·.lean))
#eval ((fixtures.flatMap Einsatz.zellen).eraseDups.map (·.lean))
#eval ((fixtures.flatMap Einsatz.zellen).eraseDups.filter
  (fun x => !(baseline.any (fun e => e.zellen.contains x)))).map (·.lean)

end Gabbro.Grammatik.Gen.Zeugen.Recovery
