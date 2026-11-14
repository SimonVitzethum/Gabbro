module

public import Grammatik.Logik.Vertraege.Pruefer.Unit
public import Grammatik.Zielsatz.Atomar.BeweisAtomar.Voll

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz

variable {D : Deklaration} [DecidableEq D.Fn]

/-- For the strengthened concrete checker, NutzerPflichtA is a theorem.
    The C08 call-site and binding obligations are separate from this predicate. -/
theorem nutzerPflicht_of_akzeptiert {E : Einheit D}
    (functions : Aufzaehlung D.Fn) (locks : Aufzaehlung D.Lock)
    {carriers : List (D.Tab ⊕ D.Glob)}
    (accepted : akzeptiertX_pruefer.akzeptiert E functions.1 locks.1 carriers = true) :
    NutzerPflichtA E :=
  nutzerPflicht_of_geprueft functions.2 locks.2 (Bool.and_eq_true.mp accepted).2

/-- Remove the independent NutzerPflichtA premise of GabbroZielVoll.
    The headline C08 theorem retains its software call-site and binding duties. -/
theorem gabbro_ziel_ohne_nutzerpflicht (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob))
    (accepted : akzeptiertX_pruefer.akzeptiert E fs.1 ls.1 cs.1 = true)
    (O : Orakel D) (hardware : HardwareAnnahmen O E.Q) (passes : Nat)
    (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f))
    (runtime : Laufzeit E sp init) (live : Faden → Bool) (state : FadenMaschine D.mitRuhe)
    (reached : FadenErreichbarX E.P.mitRuhe O.mitRuhe passes
      (GeteiltV (D := D) E.P E.ws) (FadenStart E.P.mitRuhe sp init live) state) :
    ZielFX E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
      (RufStartG E.P.mitRuhe sp init) (E.arenen.map (·.mitRuhe)) state :=
  gabbro_ziel_voll akzeptiertX_pruefer D E fs ls cs accepted
    (nutzerPflicht_of_akzeptiert fs ls accepted)
    O hardware passes sp init runtime live state reached

#print axioms nutzerPflicht_of_akzeptiert
#print axioms gabbro_ziel_ohne_nutzerpflicht

end Gabbro.Grammatik.Zielsatz
