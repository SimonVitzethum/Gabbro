module
public import Grammatik.Korpus.Zeugnis.ZeugnisKorpus.Teil1Basis
import all Grammatik.Korpus.Zeugnis.ZeugnisKorpus.Teil1Basis

public import Grammatik.Korpus.Zeugnis.ZeugnisStmt2
public import Grammatik.Korpus.Referenz.ReferenzB
public import Grammatik.Korpus.Programme.Export108

@[expose] public section



namespace Gabbro.Grammatik

/-- Verbatim printer output for `k3_namen` (`beispiele/0070-kernel-namen.gab`). -/
def c70_kernel_namen_k3_namen : CertEnd2 refD VKorpus_0_80 := (.liftE (.retWert (.add (.add (.add (.add (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.var 3)) (.var 4)) (.var 5)) (.var 6)) (.var 7)) 0 80))

example : certEnd2Ok refD VKorpus_0_80 false [(.int 0 10), (.int 0 10), (.int 0 10), (.int 0 10), (.int 0 10), (.int 0 10), (.int 0 10), (.int 0 10)] [] c70_kernel_namen_k3_namen = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_0_80 false [(.int 0 10), (.int 0 10), (.int 0 10), (.int 0 10), (.int 0 10), (.int 0 10), (.int 0 10), (.int 0 10)] [], True :=
  zeugnisStmt2_sound refD VKorpus_0_80 false [(.int 0 10), (.int 0 10), (.int 0 10), (.int 0 10), (.int 0 10), (.int 0 10), (.int 0 10), (.int 0 10)] [] c70_kernel_namen_k3_namen (by decide)

/-- Verbatim printer output for `eins` (`beispiele/0073-sugar-widths.gab`). -/
def c73_sugar_widths_eins : CertEnd2 refD VKorpus_0_255 := (.liftE (.retWert (.wide 0 255 (.var 0)) 0 255))

example : certEnd2Ok refD VKorpus_0_255 false [(.int 0 1)] [] c73_sugar_widths_eins = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_0_255 false [(.int 0 1)] [], True :=
  zeugnisStmt2_sound refD VKorpus_0_255 false [(.int 0 1)] [] c73_sugar_widths_eins (by decide)

/-- Verbatim printer output for `dreizehn` (`beispiele/0073-sugar-widths.gab`). -/
def c73_sugar_widths_dreizehn : CertEnd2 refD VKorpus_0_65535 := (.liftE (.retWert (.wide 0 65535 (.var 0)) 0 65535))

example : certEnd2Ok refD VKorpus_0_65535 false [(.int 0 8191)] [] c73_sugar_widths_dreizehn = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_0_65535 false [(.int 0 8191)] [], True :=
  zeugnisStmt2_sound refD VKorpus_0_65535 false [(.int 0 8191)] [] c73_sugar_widths_dreizehn (by decide)

/-- Verbatim printer output for `wandle` (`beispiele/0073-sugar-widths.gab`). -/
def c73_sugar_widths_wandle : CertEnd2 refD VKorpus_0_8191 := (.liftE (.retWert (.wide 0 8191 (.var 0)) 0 8191))

example : certEnd2Ok refD VKorpus_0_8191 false [(.int 0 100)] [] c73_sugar_widths_wandle = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_0_8191 false [(.int 0 100)] [], True :=
  zeugnisStmt2_sound refD VKorpus_0_8191 false [(.int 0 100)] [] c73_sugar_widths_wandle (by decide)

/-- Verbatim printer output for `grenze` (`beispiele/0073-sugar-widths.gab`). -/
def c73_sugar_widths_grenze : CertEnd2 refD VKorpus_0_18446744073709551615 := (.liftE (.retWert (.wide 0 18446744073709551615 (.lit 8191)) 0 18446744073709551615))

example : certEnd2Ok refD VKorpus_0_18446744073709551615 false [] [] c73_sugar_widths_grenze = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_0_18446744073709551615 false [] [], True :=
  zeugnisStmt2_sound refD VKorpus_0_18446744073709551615 false [] [] c73_sugar_widths_grenze (by decide)

/-- Verbatim printer output for `minus` (`beispiele/0073-sugar-widths.gab`). -/
def c73_sugar_widths_minus : CertEnd2 refD VKorpus_m9223372036854775808_9223372036854775807 := (.liftE (.retWert (.wide (-9223372036854775808) 9223372036854775807 (.var 0)) (-9223372036854775808) 9223372036854775807))

example : certEnd2Ok refD VKorpus_m9223372036854775808_9223372036854775807 false [(.int (-68719476736) 68719476735)] [] c73_sugar_widths_minus = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_m9223372036854775808_9223372036854775807 false [(.int (-68719476736) 68719476735)] [], True :=
  zeugnisStmt2_sound refD VKorpus_m9223372036854775808_9223372036854775807 false [(.int (-68719476736) 68719476735)] [] c73_sugar_widths_minus (by decide)

/-- Verbatim printer output for `voll` (`beispiele/0073-sugar-widths.gab`). -/
def c73_sugar_widths_voll : CertEnd2 refD VKorpus_0_18446744073709551615 := (.liftE (.retWert (.var 0) 0 18446744073709551615))

example : certEnd2Ok refD VKorpus_0_18446744073709551615 false [(.int 0 18446744073709551615)] [] c73_sugar_widths_voll = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_0_18446744073709551615 false [(.int 0 18446744073709551615)] [], True :=
  zeugnisStmt2_sound refD VKorpus_0_18446744073709551615 false [(.int 0 18446744073709551615)] [] c73_sugar_widths_voll (by decide)

/-- Verbatim printer output for `kernel` (`beispiele/0080-bibliothek-erklaert.gab`). -/
def c80_bibliothek_erklaert_kernel : CertEnd2 refD VKorpus_0_4294967295 := (.liftE (.retWert (.var 0) 0 4294967295))

example : certEnd2Ok refD VKorpus_0_4294967295 false [(.int 0 4294967295)] [] c80_bibliothek_erklaert_kernel = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_0_4294967295 false [(.int 0 4294967295)] [], True :=
  zeugnisStmt2_sound refD VKorpus_0_4294967295 false [(.int 0 4294967295)] [] c80_bibliothek_erklaert_kernel (by decide)

/-- Verbatim printer output for `quad` (`beispiele/0092-const-squares.gab`). -/
def c92_const_squares_quad : CertEnd2 refD VKorpus_0_4294967295 := (.liftE (.retWert (.wide 0 4294967295 (.mul (.var 0) (.var 0))) 0 4294967295))

example : certEnd2Ok refD VKorpus_0_4294967295 false [(.int 0 64)] [] c92_const_squares_quad = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_0_4294967295 false [(.int 0 64)] [], True :=
  zeugnisStmt2_sound refD VKorpus_0_4294967295 false [(.int 0 64)] [] c92_const_squares_quad (by decide)

/-- Verbatim printer output for `doppelt` (`beispiele/0093-const-scalars.gab`). -/
def c93_const_scalars_doppelt : CertEnd2 refD VKorpus_0_2000 := (.liftE (.retWert (.add (.var 0) (.var 0)) 0 2000))

example : certEnd2Ok refD VKorpus_0_2000 false [(.int 0 1000)] [] c93_const_scalars_doppelt = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_0_2000 false [(.int 0 1000)] [], True :=
  zeugnisStmt2_sound refD VKorpus_0_2000 false [(.int 0 1000)] [] c93_const_scalars_doppelt (by decide)

/-- Verbatim printer output for `einsetzen` (`beispiele/0094-uebersetzer-erklaert.gab`). -/
def c94_uebersetzer_erklaert_einsetzen : CertEnd2 refD VKorpus_0_4294967295 := (.liftE (.retWert (.var 0) 0 4294967295))

example : certEnd2Ok refD VKorpus_0_4294967295 false [(.int 0 4294967295)] [] c94_uebersetzer_erklaert_einsetzen = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_0_4294967295 false [(.int 0 4294967295)] [], True :=
  zeugnisStmt2_sound refD VKorpus_0_4294967295 false [(.int 0 4294967295)] [] c94_uebersetzer_erklaert_einsetzen (by decide)

/-- Verbatim printer output for `einsetzen` (`beispiele/0095-uebersetzer-vertrag.gab`). -/
def c95_uebersetzer_vertrag_einsetzen : CertEnd2 refD VKorpus_0_4294967295 := (.liftE (.retWert (.var 0) 0 4294967295))

example : certEnd2Ok refD VKorpus_0_4294967295 false [(.int 0 4294967295)] [] c95_uebersetzer_vertrag_einsetzen = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD VKorpus_0_4294967295 false [(.int 0 4294967295)] [], True :=
  zeugnisStmt2_sound refD VKorpus_0_4294967295 false [(.int 0 4294967295)] [] c95_uebersetzer_vertrag_einsetzen (by decide)

/-! ## 108 slot bodies over the real export -/

/-- Verbatim printer output for `read_a` (`beispiele/0108-disjoint-start-locks.gab`), constructors
    for the printed names. -/
def c108_read_a : CertEnd2 G108_disjoint_start_locks.gD (vertragVon G108_disjoint_start_locks.gD G108_disjoint_start_locks.g_read_a) := (.liftE (.retWert (.slot G108_disjoint_start_locks.GTab.T G108_disjoint_start_locks.GTFeld.v (.wide 0 3 (.lit 0))) 0 4294967295))

example : certEnd2Ok G108_disjoint_start_locks.gD (vertragVon G108_disjoint_start_locks.gD G108_disjoint_start_locks.g_read_a) false G108_disjoint_start_locks.gCtx_read_a G108_disjoint_start_locks.gL_read_a c108_read_a = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock G108_disjoint_start_locks.gD (vertragVon G108_disjoint_start_locks.gD G108_disjoint_start_locks.g_read_a) false G108_disjoint_start_locks.gCtx_read_a G108_disjoint_start_locks.gL_read_a, True :=
  zeugnisStmt2_sound G108_disjoint_start_locks.gD (vertragVon G108_disjoint_start_locks.gD G108_disjoint_start_locks.g_read_a) false G108_disjoint_start_locks.gCtx_read_a G108_disjoint_start_locks.gL_read_a c108_read_a (by decide)

/-- Verbatim printer output for `read_c` (`beispiele/0108-disjoint-start-locks.gab`), constructors
    for the printed names. -/
def c108_read_c : CertEnd2 G108_disjoint_start_locks.gD (vertragVon G108_disjoint_start_locks.gD G108_disjoint_start_locks.g_read_c) := (.liftE (.retWert (.slot G108_disjoint_start_locks.GTab.T G108_disjoint_start_locks.GTFeld.v (.wide 0 3 (.lit 1))) 0 4294967295))

example : certEnd2Ok G108_disjoint_start_locks.gD (vertragVon G108_disjoint_start_locks.gD G108_disjoint_start_locks.g_read_c) false G108_disjoint_start_locks.gCtx_read_c G108_disjoint_start_locks.gL_read_c c108_read_c = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock G108_disjoint_start_locks.gD (vertragVon G108_disjoint_start_locks.gD G108_disjoint_start_locks.g_read_c) false G108_disjoint_start_locks.gCtx_read_c G108_disjoint_start_locks.gL_read_c, True :=
  zeugnisStmt2_sound G108_disjoint_start_locks.gD (vertragVon G108_disjoint_start_locks.gD G108_disjoint_start_locks.g_read_c) false G108_disjoint_start_locks.gCtx_read_c G108_disjoint_start_locks.gL_read_c c108_read_c (by decide)

/-! ## Hand declaration for `0059-eintritt-nimmt-maskierte-sperre.gab` (no `lean-g` export) -/

inductive D59Tab where
| Takte
| Auftraege
  deriving DecidableEq

inductive D59FeldTakte where
  | stand
  deriving DecidableEq

inductive D59FeldAuftraege where
  | stand
  deriving DecidableEq

/-- Dummy signature: this declaration names no functions, but
    `sigNr` still needs a value (no call validity ever reads it). -/
def D59SigDummy : Signatur D59Tab Empty Empty Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

abbrev D59D : Deklaration where
  Tab := D59Tab
  decTab := inferInstance
  count := fun
  | .Takte => 64
  | .Auftraege => 16
  Feld := fun | .Takte => D59FeldTakte | .Auftraege => D59FeldAuftraege
  decFeld := fun | .Takte => inferInstance | .Auftraege => inferInstance
  typ := fun
  | .Takte, .stand => (.int 0 18446744073709551615)
  | .Auftraege, .stand => (.int 0 18446744073709551615)
  erlaubt := fun _ _ _ _ => false
  tabNr := fun
  | 0 => some D59Tab.Takte
  | 1 => some D59Tab.Auftraege
  | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Empty
  sig := fun e => nomatch e
  sigNr := fun _ => D59SigDummy
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t => by cases t <;> decide
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

end Gabbro.Grammatik
