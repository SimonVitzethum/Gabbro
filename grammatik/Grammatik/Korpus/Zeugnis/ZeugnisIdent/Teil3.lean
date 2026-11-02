module
public import Grammatik.Korpus.Zeugnis.ZeugnisIdent.Teil3Basis
import all Grammatik.Korpus.Zeugnis.ZeugnisIdent.Teil3Basis

public import Grammatik.Korpus.Zeugnis.Zeugnis
public import Grammatik.Korpus.Referenz.ReferenzB
public import Grammatik.Korpus.Zeugnis.ZeugnisIdent.Teil2

@[expose] public section

namespace Gabbro.Grammatik
/-- Witness for `print_elab_all` (rule 13): joint instantiation on the
    reference fixture -- a checked int expression (`refHundert`, the
    some-branch, round-tripping through `wide`/`lit`) and a checked bool
    expression (`refReqEin`, the none-branch) -- over the non-degenerate
    program (`einzahlen` writes `konto`, `refEin_schreibt`). -/
theorem print_elab_all_zeuge :
    (∃ (e : Expr refD [.int 0 10] [Res.held (D := refD) ()] (.int 0 100)),
      (match printInt e with
       | some c =>
         elabInt (D := refD) (Γ := [.int 0 10]) (Λ := [Res.held (D := refD) ()])
           c = some ⟨.int 0 100, e⟩
       | none => True) ∧
      (vertragVon refD refEin).schreibt () = true) ∧
    ∃ (e : Expr refD (refD.params refEin)
      (Signatur.anfang refD (refD.signatur refEin)) .bool),
      (match printInt e with
       | some c =>
         elabInt (D := refD) (Γ := refD.params refEin)
           (Λ := Signatur.anfang refD (refD.signatur refEin))
           c = some ⟨.bool, e⟩
       | none => True) := by
  refine ⟨⟨refHundert, ?_, refEin_schreibt ()⟩, ⟨refReqEin, ?_⟩⟩
  · exact print_elab refHundert
  · exact print_elab_all refReqEin

end Gabbro.Grammatik
