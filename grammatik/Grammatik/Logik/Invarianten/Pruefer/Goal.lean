module

public import Grammatik.Logik.Invarianten.Pruefer.Duties
public import Grammatik.Zielsatz.Atomar.BeweisAtomar.Voll

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz

variable {D : Deklaration} [DecidableEq D.Fn]

/-- The concrete checker's final unit gate carries the complete invariant
    decision, including initial memory and optional lock reification. -/
theorem akzeptiertX_invarianten {E : Einheit D} {functions : List D.Fn} {locks : List D.Lock}
    {carriers : List (D.Tab ⊕ D.Glob)}
    (accepted : akzeptiertX_pruefer.akzeptiert E functions locks carriers = true) :
    InvariantenGeprueft E functions locks :=
  (invariantenGeprueftB_iff E functions locks {}).mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp accepted).1).2

/-- The complete goal, on a checker-admitted unit, without a user proof of
    any table/group/global invariant. Opaque semantic lock duties remain
    explicit in NutzerLogikA. No change is made to gabbro_ziel's statement. -/
theorem gabbro_ziel_gepruefte_invarianten (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob))
    (accepted : akzeptiertX_pruefer.akzeptiert E fs.1 ls.1 cs.1 = true) (logic : NutzerLogikA E)
    (O : Orakel D) (hardware : HardwareAnnahmen O E.Q) (passes : Nat)
    (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f))
    (runtime : Laufzeit E sp init) (live : Faden → Bool) (state : FadenMaschine D.mitRuhe)
    (reached : FadenErreichbarX E.P.mitRuhe O.mitRuhe passes
      (GeteiltV (D := D) E.P E.ws) (FadenStart E.P.mitRuhe sp init live) state) :
    ZielFX E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
      (RufStartG E.P.mitRuhe sp init) (E.arenen.map (·.mitRuhe)) state :=
  gabbro_ziel_voll akzeptiertX_pruefer D E fs ls cs accepted
    (nutzerPflichtA_of_geprueft fs.2 ls.2 (akzeptiertX_invarianten accepted) logic)
    O hardware passes sp init runtime live state reached

#print axioms invGut_of_geprueft
#print axioms gabbro_ziel_gepruefte_invarianten

end Gabbro.Grammatik.Zielsatz
