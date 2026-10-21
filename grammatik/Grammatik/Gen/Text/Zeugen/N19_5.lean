/-
  File:      Grammatik/Gen/Text/Zeugen/N19_5.lean
  Subject:   The witness `N19_5` at the text level: its printed text reads back as a program with its cells and its
             verdict. Decided by the kernel (the text is never lexed: `ausText_druckB`).
-/
import Grammatik.Gen.Text.Pruefung
import Grammatik.Gen.Zeugen.N.N19_5

namespace Gabbro.Grammatik.Gen.Text.Zeugen.N19_5

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Gen.Zeugen.N19_5

theorem check : textCheck z P ws e.zellen e.gueltig = true := by decide +kernel

/-- **The text of the witness reads back as the witness**, up to cells and verdict. -/
theorem text : ∃ e', ausText (textVon z P ws) = .ok e' ∧ e'.zellen = e.zellen ∧ e'.gueltig = e.gueltig :=
  textCheck_sound z P ws e.zellen e.gueltig check

end Gabbro.Grammatik.Gen.Text.Zeugen.N19_5
