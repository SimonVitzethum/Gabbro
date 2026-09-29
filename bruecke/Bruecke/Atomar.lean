import Bruecke.Simulation
import Grammatik.Zielsatz.BeweisAtomar

/-!
# S4 (atomic rely): `NutzerPflichtA` for a unit the parser elaborates

Premise (b) of the goal theorem carries the ATOMIC RELY: `NutzerPflichtA E` asks every body to
hold against every value a read of a shared atomic may return. The Lean parser's declaration has
`Glob := Empty` (no `UStmt` publishes, awaits or exchanges), so no shared atomic exists and no
such read does: `nutzerPflichtA_ohne_atomar` turns `NutzerPflicht` into `NutzerPflichtA`.
A unit WITH a shared atomic lies outside the bridge; the report writes down what its duty would
have to quantify.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

instance (u : UProg) : DecidableEq (declOf u).Fn := inferInstanceAs (DecidableEq (Fin u.fns.length))

/-- The parser's declaration has no atomic global. -/
theorem declOf_kein_atomar (u : UProg) : ∀ g : (declOf u).Glob, (declOf u).atomar g = false :=
  fun g => nomatch g

/-- **PREMISE (b) WITH THE ATOMIC RELY, FROM GABBROV.** -/
theorem bruecke_nutzerA {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : Stimmig u) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, ∃ body, zuBody u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (E : Zielsatz.Einheit (declOf u)) (hP : E.P = P) (hS : E.S = SperrInv.leer (declOf u))
    (hQ : E.Q = axWahr (declOf u)) : Zielsatz.NutzerPflichtA E :=
  Zielsatz.nutzerPflichtA_ohne_atomar (declOf_kein_atomar u)
    (bruecke_nutzer hlow S rk hR hZ E hP hS hQ)

#print axioms bruecke_nutzerA

end Gabbro.Bruecke
