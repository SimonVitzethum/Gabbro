module

public import Grammatik.Korpus.Zeugnis.ZeugnisStmt2
public import Grammatik.Korpus.Referenz.ReferenzB
public import Grammatik.Korpus.Programme.Export108
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section



namespace Gabbro.Grammatik

/-! ## Contracts: one per result type (the place travels as paste data) -/

/-- Contract for result `none` over `refD`. -/
def VKorpus_none : Vertrag refD :=
  { schreibt := fun _ => false, gschreibt := fun _ => false,
    erg := none, gruende := 0, haelt := [], produziert := [] }

/-- Contract for result `some (.int 0 4294967295)` over `refD`. -/
def VKorpus_0_4294967295 : Vertrag refD :=
  { schreibt := fun _ => false, gschreibt := fun _ => false,
    erg := some (.int 0 4294967295), gruende := 0, haelt := [], produziert := [] }

/-- Contract for result `some (.int 0 18446744073709551615)` over `refD`. -/
def VKorpus_0_18446744073709551615 : Vertrag refD :=
  { schreibt := fun _ => false, gschreibt := fun _ => false,
    erg := some (.int 0 18446744073709551615), gruende := 0, haelt := [], produziert := [] }

/-- Contract for result `some (.int 0 255)` over `refD`. -/
def VKorpus_0_255 : Vertrag refD :=
  { schreibt := fun _ => false, gschreibt := fun _ => false,
    erg := some (.int 0 255), gruende := 0, haelt := [], produziert := [] }

/-- Contract for result `some (.int 0 65535)` over `refD`. -/
def VKorpus_0_65535 : Vertrag refD :=
  { schreibt := fun _ => false, gschreibt := fun _ => false,
    erg := some (.int 0 65535), gruende := 0, haelt := [], produziert := [] }

/-- Contract for result `some (.int 0 80)` over `refD`. -/
def VKorpus_0_80 : Vertrag refD :=
  { schreibt := fun _ => false, gschreibt := fun _ => false,
    erg := some (.int 0 80), gruende := 0, haelt := [], produziert := [] }

/-- Contract for result `some (.int 0 8191)` over `refD`. -/
def VKorpus_0_8191 : Vertrag refD :=
  { schreibt := fun _ => false, gschreibt := fun _ => false,
    erg := some (.int 0 8191), gruende := 0, haelt := [], produziert := [] }

/-- Contract for result `some (.int (-9223372036854775808) 9223372036854775807)` over `refD`. -/
def VKorpus_m9223372036854775808_9223372036854775807 : Vertrag refD :=
  { schreibt := fun _ => false, gschreibt := fun _ => false,
    erg := some (.int (-9223372036854775808) 9223372036854775807), gruende := 0, haelt := [], produziert := [] }

/-- Contract for result `some (.int 0 2000)` over `refD`. -/
def VKorpus_0_2000 : Vertrag refD :=
  { schreibt := fun _ => false, gschreibt := fun _ => false,
    erg := some (.int 0 2000), gruende := 0, haelt := [], produziert := [] }

/-- Verbatim printer output for `abnahme` (`beispiele/0006-annahmen.gab`). -/
def c06_annahmen_abnahme : CertEnd2 refD VKorpus_none := (.liftE .ret)

example : certEnd2Ok refD VKorpus_none false [] [] c06_annahmen_abnahme = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_none false [] [], True :=
  zeugnisStmt2_sound refD VKorpus_none false [] [] c06_annahmen_abnahme (by decide)

/-- Verbatim printer output for `freigabe` (`beispiele/0006-annahmen.gab`). -/
def c06_annahmen_freigabe : CertEnd2 refD VKorpus_none := (.liftE .ret)

example : certEnd2Ok refD VKorpus_none false [] [] c06_annahmen_freigabe = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_none false [] [], True :=
  zeugnisStmt2_sound refD VKorpus_none false [] [] c06_annahmen_freigabe (by decide)

/-- Verbatim printer output for `kernel` (`beispiele/0100-hardwareprofil.gab`). -/
def c100_hardwareprofil_kernel : CertEnd2 refD VKorpus_0_4294967295 := (.liftE (.retWert (.var 0) 0 4294967295))

example : certEnd2Ok refD VKorpus_0_4294967295 false [(.int 0 4294967295)] [] c100_hardwareprofil_kernel = true := by
  decide +kernel

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_0_4294967295 false [(.int 0 4294967295)] [], True :=
  zeugnisStmt2_sound refD VKorpus_0_4294967295 false [(.int 0 4294967295)] [] c100_hardwareprofil_kernel (by decide +kernel)

/-- Verbatim printer output for `filter` (`beispiele/0101-hardwareprofil-schluessel.gab`). -/
def c101_hardwareprofil_schluessel_filter : CertEnd2 refD VKorpus_0_4294967295 := (.liftE (.retWert (.var 0) 0 4294967295))

example : certEnd2Ok refD VKorpus_0_4294967295 false [(.int 0 4294967295)] [] c101_hardwareprofil_schluessel_filter = true := by
  decide +kernel

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_0_4294967295 false [(.int 0 4294967295)] [], True :=
  zeugnisStmt2_sound refD VKorpus_0_4294967295 false [(.int 0 4294967295)] [] c101_hardwareprofil_schluessel_filter (by decide +kernel)

/-- Verbatim printer output for `pa_aus_zahl` (`beispiele/0029-undurchsichtig.gab`). -/
def c29_undurchsichtig_pa_aus_zahl : CertEnd2 refD VKorpus_0_18446744073709551615 := (.liftE (.retWert (.var 0) 0 18446744073709551615))

example : certEnd2Ok refD VKorpus_0_18446744073709551615 false [(.int 0 18446744073709551615)] [] c29_undurchsichtig_pa_aus_zahl = true := by
  decide +kernel

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_0_18446744073709551615 false [(.int 0 18446744073709551615)] [], True :=
  zeugnisStmt2_sound refD VKorpus_0_18446744073709551615 false [(.int 0 18446744073709551615)] [] c29_undurchsichtig_pa_aus_zahl (by decide +kernel)

/-- Verbatim printer output for `pa_als_zahl` (`beispiele/0029-undurchsichtig.gab`). -/
def c29_undurchsichtig_pa_als_zahl : CertEnd2 refD VKorpus_0_18446744073709551615 := (.liftE (.retWert (.var 0) 0 18446744073709551615))

example : certEnd2Ok refD VKorpus_0_18446744073709551615 false [(.int 0 18446744073709551615)] [] c29_undurchsichtig_pa_als_zahl = true := by
  decide +kernel

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_0_18446744073709551615 false [(.int 0 18446744073709551615)] [], True :=
  zeugnisStmt2_sound refD VKorpus_0_18446744073709551615 false [(.int 0 18446744073709551615)] [] c29_undurchsichtig_pa_als_zahl (by decide +kernel)

/-- Verbatim printer output for `abnahme` (`beispiele/0043-gegenprobe.gab`). -/
def c43_gegenprobe_abnahme : CertEnd2 refD VKorpus_none := (.liftE .ret)

example : certEnd2Ok refD VKorpus_none false [] [] c43_gegenprobe_abnahme = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_none false [] [], True :=
  zeugnisStmt2_sound refD VKorpus_none false [] [] c43_gegenprobe_abnahme (by decide)

/-- Verbatim printer output for `freigabe` (`beispiele/0043-gegenprobe.gab`). -/
def c43_gegenprobe_freigabe : CertEnd2 refD VKorpus_none := (.liftE .ret)

example : certEnd2Ok refD VKorpus_none false [] [] c43_gegenprobe_freigabe = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_none false [] [], True :=
  zeugnisStmt2_sound refD VKorpus_none false [] [] c43_gegenprobe_freigabe (by decide)

/-- Verbatim printer output for `abnahme` (`beispiele/0052-baugatter.gab`). -/
def c52_baugatter_abnahme : CertEnd2 refD VKorpus_none := (.liftE .ret)

example : certEnd2Ok refD VKorpus_none false [] [] c52_baugatter_abnahme = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_none false [] [], True :=
  zeugnisStmt2_sound refD VKorpus_none false [] [] c52_baugatter_abnahme (by decide)

/-- Verbatim printer output for `freigabe` (`beispiele/0052-baugatter.gab`). -/
def c52_baugatter_freigabe : CertEnd2 refD VKorpus_none := (.liftE .ret)

example : certEnd2Ok refD VKorpus_none false [] [] c52_baugatter_freigabe = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_none false [] [], True :=
  zeugnisStmt2_sound refD VKorpus_none false [] [] c52_baugatter_freigabe (by decide)

/-- Verbatim printer output for `maske8` (`beispiele/0061-invertierung.gab`). -/
def c61_invertierung_maske8 : CertEnd2 refD VKorpus_0_255 := (.liftE (.retWert (.bxor 8 (.var 0) (.lit 255)) 0 255))

example : certEnd2Ok refD VKorpus_0_255 false [(.int 0 255)] [] c61_invertierung_maske8 = true := by
  decide +kernel

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_0_255 false [(.int 0 255)] [], True :=
  zeugnisStmt2_sound refD VKorpus_0_255 false [(.int 0 255)] [] c61_invertierung_maske8 (by decide +kernel)

/-- Verbatim printer output for `maske32` (`beispiele/0061-invertierung.gab`). -/
def c61_invertierung_maske32 : CertEnd2 refD VKorpus_0_4294967295 := (.liftE (.retWert (.bxor 32 (.var 0) (.lit 4294967295)) 0 4294967295))

example : certEnd2Ok refD VKorpus_0_4294967295 false [(.int 0 4294967295)] [] c61_invertierung_maske32 = true := by
  decide +kernel

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_0_4294967295 false [(.int 0 4294967295)] [], True :=
  zeugnisStmt2_sound refD VKorpus_0_4294967295 false [(.int 0 4294967295)] [] c61_invertierung_maske32 (by decide +kernel)

/-- Verbatim printer output for `loesche` (`beispiele/0061-invertierung.gab`). -/
def c61_invertierung_loesche : CertEnd2 refD VKorpus_0_65535 := (.liftE (.retWert (.band (.var 0) (.bxor 16 (.var 1) (.lit 65535))) 0 65535))

example : certEnd2Ok refD VKorpus_0_65535 false [(.int 0 65535), (.int 0 65535)] [] c61_invertierung_loesche = true := by
  decide +kernel

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_0_65535 false [(.int 0 65535), (.int 0 65535)] [], True :=
  zeugnisStmt2_sound refD VKorpus_0_65535 false [(.int 0 65535), (.int 0 65535)] [] c61_invertierung_loesche (by decide +kernel)

/-- Verbatim printer output for `verbreitert` (`beispiele/0061-invertierung.gab`). -/
def c61_invertierung_verbreitert : CertEnd2 refD VKorpus_0_4294967295 := (.liftE (.bind (.wide 0 4294967295 (.bxor 16 (.var 0) (.lit 65535))) 0 4294967295 (.retWert (.var 0) 0 4294967295)))

example : certEnd2Ok refD VKorpus_0_4294967295 false [(.int 0 65535)] [] c61_invertierung_verbreitert = true := by
  decide +kernel

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_0_4294967295 false [(.int 0 65535)] [], True :=
  zeugnisStmt2_sound refD VKorpus_0_4294967295 false [(.int 0 65535)] [] c61_invertierung_verbreitert (by decide +kernel)

/-- Verbatim printer output for `invertiere` (`beispiele/0062-grenzwort-im-ausdruck.gab`). -/
def c62_grenzwort_im_ausdruck_invertiere : CertEnd2 refD VKorpus_0_4294967295 := (.liftE (.retWert (.bxor 32 (.var 0) (.lit 4294967295)) 0 4294967295))

example : certEnd2Ok refD VKorpus_0_4294967295 false [(.int 0 4294967295)] [] c62_grenzwort_im_ausdruck_invertiere = true := by
  decide +kernel

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_0_4294967295 false [(.int 0 4294967295)] [], True :=
  zeugnisStmt2_sound refD VKorpus_0_4294967295 false [(.int 0 4294967295)] [] c62_grenzwort_im_ausdruck_invertiere (by decide +kernel)

/-- Verbatim printer output for `kombiniert` (`beispiele/0069-integer-conversion.gab`). -/
def c69_integer_conversion_kombiniert : CertEnd2 refD VKorpus_0_18446744073709551615 := (.liftE (.retWert (.wide 0 18446744073709551615 (.bor 32 (.var 0) (.var 1))) 0 18446744073709551615))

example : certEnd2Ok refD VKorpus_0_18446744073709551615 false [(.int 0 4294967295), (.int 0 4294967295)] [] c69_integer_conversion_kombiniert = true := by
  decide +kernel

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_0_18446744073709551615 false [(.int 0 4294967295), (.int 0 4294967295)] [], True :=
  zeugnisStmt2_sound refD VKorpus_0_18446744073709551615 false [(.int 0 4294967295), (.int 0 4294967295)] [] c69_integer_conversion_kombiniert (by decide +kernel)

end Gabbro.Grammatik
