module
public import Grammatik.Parser.Elab.UebersetzeAllg3.Rest2
public import Grammatik.Zielsatz.Atomar.BeweisTerminierung
@[expose] public section

namespace Gabbro.Grammatik.Parser.Measures
open Uebersetze UebersetzeAllg UebersetzeAllg2 Zielsatz

/-- The actual generic lowering endpoint validates the measure against the same program. -/
theorem lowerAllg_measures (u : UProg) (P : Programm (declOf u)) (fs : List (declOf u).Fn)
    (lowered : lowerAllg u = .ok (P, fs)) :
    ∃ exported, lowerMeasures u = .ok exported ∧ cycleLengths u P exported.mass = true := by
  cases hi : lowerInvs u (List.finRange u.invs.length) with
  | error error => simp only [lowerAllg, hi, reduceCtorEq] at lowered
  | ok value =>
    cases hf : lowerEach u (List.finRange u.fns.length) with
    | error error => simp only [lowerAllg, hi, hf, reduceCtorEq] at lowered
    | ok value =>
      exact checkedProgram_export u _ P fs (by simpa only [lowerAllg, hi, hf] using lowered)

/-- The generated user duty is the existing `MassPflicht`, for every pass grant and every function.
    This proposition is deliberately not discharged by the structural checker. -/
def Obligations (u : UProg) (E : Einheit (declOf u)) (exported : Export u) : Prop :=
  ∀ passes f, MassPflicht E.P passes E.Q E.S (GeteiltV E.P E.ws)
    exported.mass (zykS E.P (List.finRange u.fns.length)) f

/-- The original-source measure retains its value under the idle-root declaration embedding. -/
theorem lowerMeasures_idle_value (u : UProg) (exported : Export u)
    (f : (declOf u).Fn) (state : World (declOf u)) (env : Env (declOf u) ((declOf u).params f)) :
    exported.mass.mitRuhe.wert (some f) (worldR state) (envR env) =
      exported.mass.wert f state env := Mass.wert_mitRuhe exported.mass f state env

/-- Instantiate the existing termination theorem with the exported source measure. Its proof
    retains `massPflicht_mitRuhe` and cycle-length transfer inside `gabbro_ziel_terminierung`.
    No depth or stack bound is inferred for the compiler or its execution theorem. -/
theorem source_termination (u : UProg) (E : Einheit (declOf u)) (exported : Export u)
    (_origin : lowerMeasures u = .ok exported)
    (lengths : cycleLengths u E.P exported.mass = true) (duty : Obligations u E exported)
    (C : PrueferX) (ls : Aufzaehlung (declOf u).Lock)
    (cs : Aufzaehlung ((declOf u).Tab ⊕ (declOf u).Glob))
    (accepted : C.akzeptiert E (List.finRange u.fns.length) ls.1 cs.1 = true)
    (user : NutzerPflichtA E) (passes : Nat) (O : Orakel (declOf u))
    (hardware : HardwareAnnahmen O E.Q)
    (sp : Speicher (declOf u).mitRuhe)
    (init : Faden → Σ f : (declOf u).mitRuhe.Fn, Env (declOf u).mitRuhe ((declOf u).mitRuhe.params f))
    (runtime : Laufzeit E sp init) (alive : Faden → Bool)
    (run : FadenLaufX E.P.mitRuhe O.mitRuhe passes (GeteiltV E.P E.ws))
    (initial : run.K 0 = FadenStart E.P.mitRuhe sp init alive) (thread : Faden) :
    (∃ N, ∀ j, N ≤ j → run.akt j ≠ some thread) ∧
      ((∀ w, (init thread).1 = some w →
          klasse E.P (List.finRange u.fns.length) exported.mass.hat w = .endet) →
        ∀ j, ¬ HaltBenannt O.mitRuhe passes (run.K j).m .budget thread) := by
  exact gabbro_ziel_terminierung C (declOf u) E
    ⟨List.finRange u.fns.length, fun f => List.mem_finRange f⟩ ls cs accepted user passes
    exported.mass (duty passes) (cycleLengths_sound u E.P exported.mass lengths)
    O hardware sp init runtime alive run initial thread

end Gabbro.Grammatik.Parser.Measures
