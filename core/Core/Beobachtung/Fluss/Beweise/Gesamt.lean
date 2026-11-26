module

public import Core.Beobachtung.Fluss.Abschluss
public import Core.Beobachtung.Fluss.AufrufSchleifeBeweis
public import Core.Beobachtung.Fluss.InterruptBeweis
public import Core.Beobachtung.Fluss.AbsturzBeweis
public import Core.Beobachtung.Fluss.Beweise.PauseBeweis

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Annahme Katalog Maschine
open Ast.Semantik (Fragment)

/-- All ten instruction-family and protocol proof packets are now proved: the six
    silent families, answers, interrupts, crashes and pauses (for frame-only fragments). -/
theorem fragmentNIBeweise : FragmentNIBeweise where
  skalar := skalarNI
  kontrollfluss := kontrollflussNI
  aufrufSchleife := aufrufSchleifeNI
  aggregat := aggregatNI
  text := textNI
  variante := varianteNI
  antwort := antwortNI
  interrupt := interruptNI
  absturz := absturzNI
  pause := pauseNI

/-- Every accepted source fragment is non-interferent, with no remaining open
    obligations: the packets above discharge all family and protocol duties and
    acceptance supplies the start rule. -/
theorem fragment_nichtinterferent (p : Fragment) (plattform : Plattform) (rein : ∀ b ∈ p.code, b.Privat) :
    Akzeptiert (p.einheit plattform) → Nichtinterferent (p.einheit plattform) :=
  akzeptiertes_fragment_ni fragmentNIBeweise p plattform rein

end Gabbro.Core.Beobachtung
