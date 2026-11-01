module

public import Grammatik.Speichermodell.Atomar.Atomar
public import Grammatik.Speichermodell.Maschine.Zeuge
public import Grammatik.Speichermodell.Atomar.AtomarZeuge.Teil1
import all Init.Data.Repr
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
open Speichermodell Zielsatz
variable {D : Deklaration}
namespace AtomarZeuge
open NIZeuge

/-- **THE REFUSAL: a plain payload read with no synchronisation.** `hauptA` writes the PLAIN
    table `tabA`, `zaehlA` reads it, no lock: `AkzeptiertA` refuses, at its footprint
    component -- the exemption covers atomic carriers only, never a plain one. -/
theorem nutzlast_ohne_erwerb_abgelehnt :
    AkzeptiertA nP SchwachZeuge.nS nFs [] nCs [NFn.hauptA, NFn.zaehlA] = false ∧
      fussWAB nP SchwachZeuge.nS nFs [NFn.hauptA, NFn.zaehlA] = false := by
  decide

/-- Non-degenerate: the payload is plain, written by one start and read by the other. -/
theorem nutzlast_echt :
    TraegerSchreibt (D := nD) NFn.hauptA (.inl NTab.tabA) = true ∧
      (.inl NTab.tabA : nD.Tab ⊕ nD.Glob) ∈ fussOrteG nP NFn.zaehlA ∧
      ¬ AtomarAusgenommen (D := nD) (.inl NTab.tabA) := by
  refine ⟨rfl, istIn_iff.mp (by decide), fun ⟨_, e, _⟩ => by cases e⟩

end AtomarZeuge

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.fussWAB_iff
#print axioms Gabbro.Grammatik.akzeptiertA_of_akzeptiert
#print axioms Gabbro.Grammatik.schwach_ist_gA_akzeptiert
#print axioms Gabbro.Grammatik.w_sprache_akzeptiertA
#print axioms Gabbro.Grammatik.AtomarZeuge.n1_sprache
#print axioms Gabbro.Grammatik.AtomarZeuge.n1_akzeptiertA
#print axioms Gabbro.Grammatik.AtomarZeuge.n1_ga
#print axioms Gabbro.Grammatik.AtomarZeuge.n1_nicht_sc_aber_ga
#print axioms Gabbro.Grammatik.AtomarZeuge.n1_schwachSC_falsch
#print axioms Gabbro.Grammatik.AtomarZeuge.faltung_abgelehnt
#print axioms Gabbro.Grammatik.AtomarZeuge.faltung_akzeptiertA
#print axioms Gabbro.Grammatik.AtomarZeuge.nutzlast_ohne_erwerb_abgelehnt
