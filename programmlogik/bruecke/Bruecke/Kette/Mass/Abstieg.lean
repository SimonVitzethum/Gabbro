module
public import Bruecke.Kette.Mass.Wert
public import Bruecke.Kette.Mass.Rang
@[expose] public section

/-!
# The measure of a unit, computed from its source

`massQuelle u` replaces a hand-chosen `MassU`: the value of an entry into `n` at `t` is the
pair (call-graph rank of `n`, value of `n`'s `decreases` clause at `t`), ordered
lexicographically by the canonical `lexLt` and well-founded by `lexLt_wf 2`. Nothing in it is
chosen by the person: the rank is `rangU`, the second component is `massTupel`, which is the
exported canonical `Mass.wert` at the bridge's entries (`massTupel_wert`).

Under this measure the duty `meetsUM` reduces to the source-level duty `meetsUQ`
(`meetsUM_of_meetsUQ`): the contract of a callee OFF the caller's cycle is assumed outright --
the rank carries that call --, the contract of a callee ON the cycle only where the callee's
`decreases` value lies below the caller's entry value. That second guard is exactly the test
of the canonical measure gate `massTor` (`unterQ_of_lexLt`). A function none of whose callees
lies on its cycle owes exactly its old duty `meetsU` (`meetsUQ_of_meetsU`).
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.Measures

/-- The source value of an entry into the function named `n` at `t`: its `decreases` clause
    on the entry binding (`0` without a clause). -/
def quellZahl (u : UProg) (n : String) (t : Gabbro.Body.State) : Nat :=
  match fnSuch u n with
  | some gf => (massTupel gf t.local').headD 0
  | none => 0

/-- **The measure of a unit, from its source**: rank first, then the `decreases` value. -/
noncomputable def massQuelle (u : UProg) : MassU where
  Wert := List Nat
  lt := lexLtN 2
  wf := lexLt_wf 2
  mass := fun n t => [rangU u n, quellZahl u n t]

variable {u : UProg}

theorem massQuelle_lt_rang {n m : String} {t t' : Gabbro.Body.State}
    (h : rangU u n < rangU u m) :
    (massQuelle u).lt ((massQuelle u).mass n t) ((massQuelle u).mass m t') := by
  show lexLtN 2 [rangU u n, quellZahl u n t] [rangU u m, quellZahl u m t']
  unfold lexLtN
  refine ⟨rfl, rfl, ?_⟩
  simp [lexLt, h]

theorem massQuelle_lt_wert {n m : String} {t t' : Gabbro.Body.State}
    (hr : rangU u n = rangU u m) (hw : quellZahl u n t < quellZahl u m t') :
    (massQuelle u).lt ((massQuelle u).mass n t) ((massQuelle u).mass m t') := by
  show lexLtN 2 [rangU u n, quellZahl u n t] [rangU u m, quellZahl u m t']
  unfold lexLtN
  refine ⟨rfl, rfl, ?_⟩
  rw [hr]
  simp [lexLt, hw]

/-- **Along a call edge the measure falls** wherever the callee lies off the caller's cycle,
    or its source value lies below the caller's. -/
theorem massQuelle_kante {f g : String} {gf : UFn} {s t : Gabbro.Body.State}
    (hf : fnSuch u f = some gf) (hg : g ∈ calleesOf gf)
    (h : ¬ ZyklusU u f g ∨ quellZahl u g t < quellZahl u f s) :
    (massQuelle u).lt ((massQuelle u).mass g t) ((massQuelle u).mass f s) := by
  rcases h with hz | hw
  · exact massQuelle_lt_rang (rangU_kante_lt hf hg hz)
  · rcases Nat.lt_or_eq_of_le (rangU_kante_le hf hg) with hr | hr
    · exact massQuelle_lt_rang hr
    · exact massQuelle_lt_wert hr hw

/-- The guard of a callee entry `t` of `g` from the entry `s` of `f`: `g` lies off `f`'s
    cycle, or its `decreases` value falls. -/
def unterQ (u : UProg) (f : UFn) (s : Gabbro.Body.State) (g : String)
    (t : Gabbro.Body.State) : Prop :=
  ¬ ZyklusU u f.name g ∨ quellZahl u g t < quellZahl u f.name s

/-- **The source-level duty**: the body meets the promise, assuming each callee's contract on
    the entries its guard `unterQ` admits. -/
def meetsUQ (u : UProg) (wf : Gabbro.Body.State → Prop) (f : UFn)
    (body : List Gabbro.Body.Stmt) : Prop :=
  ∀ (ρ : Gabbro.Body.Env) (s : Gabbro.Body.State), wf s →
    Gabbro.Body.eval s (preExpr f) = some (.bool true) →
    hypsM u wf ρ (unterQ u f s) (calleesOf f)
      (∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρ body s) = some s' ∧
        (postU u wf f s s' (Gabbro.Body.finalValue (Gabbro.Body.exec ρ body s))).getD False)

/-- Bounded hypotheses under a wider bound give those under a narrower one. -/
theorem hypsM_mono (wf : Gabbro.Body.State → Prop) (ρ : Gabbro.Body.Env)
    {unter unter' : String → Gabbro.Body.State → Prop} : ∀ (gs : List String) (c : Prop),
    (∀ g ∈ gs, ∀ t, unter' g t → unter g t) → hypsM u wf ρ unter' gs c → hypsM u wf ρ unter gs c
  | [], _, _, h => h
  | g :: gs, c, hle, h => by
      cases hgf : fnSuch u g with
      | none => simp only [hypsM, hgf] at h
      | some gf =>
        simp only [hypsM, hgf] at h ⊢
        intro hc hfr
        exact hypsM_mono wf ρ gs c (fun g' hm => hle g' (List.mem_cons_of_mem _ hm))
          (h (fun t ht => hc t ⟨hle g (List.mem_cons_self ..) t ht.1, ht.2⟩) hfr)

/-- **The source duty is a measure duty under the computed measure.** -/
theorem meetsUM_of_meetsUQ {wf : Gabbro.Body.State → Prop} {f : UFn}
    {body : List Gabbro.Body.Stmt} (hf : fnSuch u f.name = some f) (h : meetsUQ u wf f body) :
    meetsUM u wf (massQuelle u) f body := by
  intro ρ s hs hpre
  exact hypsM_mono (unter := fun g t => (massQuelle u).lt ((massQuelle u).mass g t)
      ((massQuelle u).mass f.name s)) (unter' := unterQ u f s) wf ρ (calleesOf f) _
    (fun g hg t ht => massQuelle_kante hf hg ht) (h ρ s hs hpre)

/-- **An acyclic duty is a source duty**: where no callee lies on the function's cycle, the old
    duty `meetsU` with full callee contracts is enough. -/
theorem meetsUQ_of_meetsU {wf : Gabbro.Body.State → Prop} {f : UFn}
    {body : List Gabbro.Body.Stmt} (hz : ∀ g ∈ calleesOf f, ¬ ZyklusU u f.name g)
    (h : meetsU u wf f body) : meetsUQ u wf f body := by
  intro ρ s hs hpre
  exact hypsM_of_hyps wf ρ (unterQ u f s) (calleesOf f) _ (fun g hg _ => Or.inl (hz g hg))
    (h ρ s hs hpre)

/-- **The duties of a unit under its computed measure**, from the source duties. -/
theorem massPflichtU_quelle {C : Fin u.fns.length → Prop}
    (hs : ∀ c : Fin u.fns.length, C c → fnSuch u (fnAt u c).name = some (fnAt u c))
    (hZ : ∀ c : Fin u.fns.length, C c → ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsUQ u (wfU u) (fnAt u c) body) : MassPflichtU u C (massQuelle u) := by
  intro c hc
  obtain ⟨body, hb, hm⟩ := hZ c hc
  exact ⟨body, hb, meetsUM_of_meetsUQ (hs c hc) hm⟩

/-- **The canonical gate admits what the source guard admits**: where `massTor` lets a call of
    `g` from an entry of `f` through (`lexLt` of the exported values), the callee entry is
    admitted by `unterQ` at the bridge's entry states. -/
theorem unterQ_of_lexLt (ex : Export u) {f g : Fin u.fns.length}
    (hNf : NamenEindeutig (fnAt u f)) (hNg : NamenEindeutig (fnAt u g))
    (hsf : fnSuch u (fnAt u f).name = some (fnAt u f))
    (hsg : fnSuch u (fnAt u g).name = some (fnAt u g))
    (σ σ' : World (declOf u)) (ρ : Env (declOf u) ((declOf u).params f))
    (ρ' : Env (declOf u) ((declOf u).params g))
    (h : lexLt (ex.mass.wert g σ' ρ') (ex.mass.wert f σ ρ) = true) :
    unterQ u (fnAt u f) (eintritt u f σ ρ) (fnAt u g).name (eintritt u g σ' ρ') := by
  refine Or.inr ?_
  simp only [quellZahl, hsf, hsg]
  exact massTupel_faellt ex hNf hNg σ σ' ρ ρ' h

end Gabbro.Bruecke
