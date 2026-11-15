/- Concrete-checker goal witnesses on the bounded increment fixture.
   The atomic-read flag remains refused. No claim of shared-atomic
   acceptance is made by this separate, contract-bearing fixture. -/
module

public import Grammatik.Logik.Vertraege.Pruefer.Witness.Contracts
public import Grammatik.Zielsatz.Atomar.BeweisAtomar

@[expose] public section

namespace Gabbro.Grammatik.ConcreteGoalZeuge

open Gabbro.Grammatik Speichermodell Zielsatz
open Vertraege.Pruefer.Witness (declaration unit checker_accepted_zeuge
  nutzerPflicht_of_akzeptiert_zeuge)

abbrev fs : Aufzaehlung declaration.Fn :=
  ⟨[()], fun f => by cases f; exact List.mem_cons_self⟩

abbrev ls : Aufzaehlung declaration.Lock := ⟨[], fun lock => nomatch lock⟩

abbrev cs : Aufzaehlung (declaration.Tab ⊕ declaration.Glob) :=
  ⟨[.inl (), .inr false, .inr true], fun carrier => by
    rcases carrier with table | global
    · cases table; exact List.mem_cons_self
    · cases global <;> simp⟩

/-- No foreign item or register; visibility is constant. -/
def oracle : Orakel declaration where
  wirktL := fun item => nomatch item
  regLiesL := fun item => nomatch item
  regSchreib := fun item => nomatch item
  sichtbarL := fun _ _ => true

theorem hardware_zeuge [RootNativeFloat.Hardware] : HardwareAnnahmen oracle unit.Q :=
  ⟨(fun item => nomatch item),
    ⟨(fun item => nomatch item), fun _ _ _ _ => rfl⟩,
    (fun item => nomatch item), inferInstance⟩

abbrev sp : Speicher declaration.mitRuhe := speicherR unit.sp0
abbrev init := initRuhe unit.starts
abbrev initial : FadenMaschine declaration.mitRuhe :=
  FadenStart unit.P.mitRuhe sp init (fun _ => true)

/-- Both sides of the contract constrain values: 4 is admitted, 10 is
    refused, and only 5 (not 6) satisfies the postcondition at input 4. -/
theorem concrete_contract_zeuge :
    ReqAmEintritt unit.P () Vertraege.Pruefer.Witness.world
      Vertraege.Pruefer.Witness.arguments ∧
    ¬ ReqAmEintritt unit.P () Vertraege.Pruefer.Witness.world
      (.cons ⟨10, by decide, by decide⟩ .nil) ∧
    EnsAmRueck unit.P () Vertraege.Pruefer.Witness.world
      Vertraege.Pruefer.Witness.world Vertraege.Pruefer.Witness.arguments
      ⟨5, by decide, by decide⟩ ∧
    ¬ EnsAmRueck unit.P () Vertraege.Pruefer.Witness.world
      Vertraege.Pruefer.Witness.world Vertraege.Pruefer.Witness.arguments
      ⟨6, by decide, by decide⟩ := by
  constructor
  · decide
  constructor
  · decide
  constructor <;> decide

/-- All four premise groups hold jointly on a declared start with input 4.
    Its requires excludes 10 and its ensures demands result = input + 1. -/
theorem concrete_premises_zeuge [RootNativeFloat.Hardware] :
    akzeptiertX_pruefer.akzeptiert unit fs.1 ls.1 cs.1 = true ∧
    NutzerPflichtA unit ∧ HardwareAnnahmen oracle unit.Q ∧
    Laufzeit unit sp init ∧ unit.starts ≠ [] ∧
    FadenErreichbarX unit.P.mitRuhe oracle.mitRuhe 0
      (GeteiltV (D := declaration) unit.P unit.ws) initial initial :=
  ⟨checker_accepted_zeuge, nutzerPflicht_of_akzeptiert_zeuge,
    hardware_zeuge, laufzeit_voll unit, List.cons_ne_nil _ _, .start⟩

/-- Replacement for the refused flag's concrete-checker atomic goal application. -/
theorem incrementE_ziel_zeuge [RootNativeFloat.Hardware]
    (ord : declaration.mitRuhe.Glob → Ordnung) (passes : Nat) :
    ∀ W : RufMaschineW declaration.mitRuhe,
      RufErreichbarW unit.P.mitRuhe oracle.mitRuhe passes ord
        (RufStartW (RufStartG unit.P.mitRuhe sp init)) W →
      ZielAtomar unit.P.mitRuhe unit.S.mitRuhe oracle.mitRuhe passes ord
        (GeteiltV unit.P.mitRuhe (wsRuhe unit.ws))
        (RufStartG unit.P.mitRuhe sp init) W :=
  gabbro_ziel_atomar akzeptiertX_pruefer declaration unit fs ls cs
    checker_accepted_zeuge nutzerPflicht_of_akzeptiert_zeuge oracle hardware_zeuge
    passes ord sp init (laufzeit_voll unit)

/-- Full-summary goal application, with the complete concrete checker. -/
theorem incrementE_gabbro_zeuge [RootNativeFloat.Hardware]
    (passes : Nat) (live : Faden → Bool) (K : FadenMaschine declaration.mitRuhe)
    (reached : FadenErreichbarX unit.P.mitRuhe oracle.mitRuhe passes
      (GeteiltV (D := declaration) unit.P unit.ws)
      (FadenStart unit.P.mitRuhe sp init live) K) :
    ZielFX unit.P.mitRuhe unit.S.mitRuhe oracle.mitRuhe passes
      (GeteiltV (D := declaration) unit.P unit.ws)
      (RufStartG unit.P.mitRuhe sp init) [] K :=
  gabbro_ziel_voll akzeptiertX_pruefer declaration unit fs ls cs
    checker_accepted_zeuge nutzerPflicht_of_akzeptiert_zeuge oracle hardware_zeuge
    passes sp init (laufzeit_voll unit) live K reached

/-- The headline call-site goal has the same jointly satisfied premises. -/
theorem incrementE_gabbro_callSite_zeuge [RootNativeFloat.Hardware]
    (passes : Nat) (live : Faden → Bool) (K : FadenMaschine declaration.mitRuhe)
    (reached : FadenErreichbarX unit.P.mitRuhe oracle.mitRuhe passes
      (GeteiltV (D := declaration) unit.P unit.ws)
      (FadenStart unit.P.mitRuhe sp init live) K) :
    ZielFX unit.P.mitRuhe unit.S.mitRuhe oracle.mitRuhe passes
      (GeteiltV (D := declaration) unit.P unit.ws)
      (RufStartG unit.P.mitRuhe sp init) [] K := by
  have noSoftware : ∀ item : declaration.Ax,
      declaration.axHerkunft item ≠ some AxOrigin.software := fun item => nomatch item
  exact gabbro_ziel akzeptiertX_pruefer declaration unit fs ls cs
    checker_accepted_zeuge nutzerPflicht_of_akzeptiert_zeuge
    (callSitePflicht_ohne unit noSoftware) (postDeckt_ohne unit noSoftware) oracle
    (foreignVertrag_ohne unit oracle noSoftware) (hardwareAnnahmenHw_of hardware_zeuge)
    passes sp init (laufzeit_voll unit) live K reached

/-- Reachability is inhabited jointly with both thread-goal conclusions. -/
theorem concrete_goals_zeuge [RootNativeFloat.Hardware] :
    ZielFX unit.P.mitRuhe unit.S.mitRuhe oracle.mitRuhe 0
      (GeteiltV (D := declaration) unit.P unit.ws)
      (RufStartG unit.P.mitRuhe sp init) [] initial ∧
    ZielAtomar unit.P.mitRuhe unit.S.mitRuhe oracle.mitRuhe 0 (fun _ => .entspannt)
      (GeteiltV unit.P.mitRuhe (wsRuhe unit.ws))
      (RufStartG unit.P.mitRuhe sp init)
      (RufStartW (RufStartG unit.P.mitRuhe sp init)) :=
  ⟨incrementE_gabbro_zeuge 0 (fun _ => true) initial .start,
    incrementE_ziel_zeuge (fun _ => .entspannt) 0 _ .start⟩

#print axioms concrete_premises_zeuge
#print axioms incrementE_ziel_zeuge
#print axioms incrementE_gabbro_zeuge
#print axioms incrementE_gabbro_callSite_zeuge
#print axioms concrete_goals_zeuge

end Gabbro.Grammatik.ConcreteGoalZeuge
