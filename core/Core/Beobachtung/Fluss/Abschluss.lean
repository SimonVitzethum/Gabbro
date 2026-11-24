module

public import Core.Beobachtung.Fluss.Lader
public import Core.Beobachtung.Fluss.Skalar
public import Core.Beobachtung.Fluss.Kontrollfluss
public import Core.Beobachtung.Fluss.AufrufSchleife
public import Core.Beobachtung.Fluss.Aggregat
public import Core.Beobachtung.Fluss.Text
public import Core.Beobachtung.Fluss.Variante
public import Core.Beobachtung.Fluss.Antwort
public import Core.Beobachtung.Fluss.Interrupt
public import Core.Beobachtung.Fluss.Absturz

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Annahme Katalog
open Ast.Semantik (Fragment)

structure FragmentNIBeweise : Prop where
  skalar : SkalarNIAussage
  kontrollfluss : KontrollflussNIAussage
  aufrufSchleife : AufrufSchleifeNIAussage
  aggregat : AggregatNIAussage
  text : TextNIAussage
  variante : VarianteNIAussage
  antwort : AntwortNIAussage
  interrupt : InterruptNIAussage
  absturz : AbsturzNIAussage

/-- Every accepted fragment has the two NI conclusions once its instruction and
    protocol proof packets are filled. The actual loader proof is shared. -/
theorem akzeptiertes_fragment_ni (beweise : FragmentNIBeweise)
    (p : Fragment) (plattform : Plattform) (h : Akzeptiert (p.einheit plattform)) :
    Nichtinterferent (p.einheit plattform) := by
  apply ni_akzeptierter_einheit (p.einheit plattform) h (fragment_lader_ni p plattform)
  · intro f quelle
    cases familie : f.familie with
    | skalar => exact beweise.skalar p plattform f familie quelle
    | kontrollfluss => exact beweise.kontrollfluss p plattform f familie quelle
    | aufrufSchleife => exact beweise.aufrufSchleife p plattform f familie quelle
    | aggregat => exact beweise.aggregat p plattform f familie quelle
    | text => exact beweise.text p plattform f familie quelle
    | variante => exact beweise.variante p plattform f familie quelle
  · intro h₁ h₂ ρ₁ ρ₂ v predictor t w spur tick protokoll praefix
    cases w with
    | kontext _ _ => exact False.elim protokoll
    | antwort a => exact (beweise.antwort p plattform h₁ ρ₁ v.links t a spur tick).elim
    | interrupt _ => exact beweise.interrupt p plattform v predictor t _ spur tick trivial praefix
    | absturz => exact beweise.absturz p plattform v predictor t _ spur tick trivial praefix

end Gabbro.Core.Beobachtung
