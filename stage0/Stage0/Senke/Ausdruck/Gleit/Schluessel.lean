/- Signed integer keys for binary64 words; both zero encodings map to zero. -/
import Stage0.Senke.Ausdruck.Gleit.Ordnung

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gabbro.Grammatik.Gleitkomma Runner.IR

theorem floatMag_lt {a : GFloat} (ha : wf f64 a) : floatMag a < 2 ^ 63 := by
  have he : a.bexp ≤ 2047 := ha.1
  have hf : a.frac < 4503599627370496 := ha.2
  unfold floatMag
  omega

theorem float_bits {a : GFloat} :
    zuBits f64 a = (if a.sign then 2 ^ 63 else 0) + floatMag a := by
  change (if a.sign then 2 ^ 63 else 0) + a.bexp * 4503599627370496 + a.frac =
    (if a.sign then 2 ^ 63 else 0) + (a.bexp * 4503599627370496 + a.frac)
  omega

end Gabbro.Stage0.Senke
