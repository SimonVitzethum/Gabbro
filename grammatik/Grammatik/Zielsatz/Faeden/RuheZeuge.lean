/-
  File:      Grammatik/Zielsatz/RuheZeuge.lean
  Subject:   witnesses for the runtime's idle root (A4): the programs that
             had NO admissible start before have one on `P.mitRuhe`.

  * The export's idle start is admissible (`gP_mitRuhe_start`), while its
    old-memory contracts stay outside the strict checker fragment.
  * Probes B/C retain their admissible idle starts.
  * The original two-thread start remains admissible; the in-fragment
    replacement also witnesses strict acceptance after adding the idle root.
-/
module
public import Grammatik.Zielsatz.Faeden.Ruhe
public import Grammatik.Zielsatz.Kern.AkzeptiertZeuge
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik
@[expose] public section


namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

theorem eval_umΛ {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} (h : Λ = Λ') (e : Expr D Γ Λ τ)
    (σ₀ σ : World D) (ρ : Env D Γ) : eval σ₀ (Expr.umΛ h e) σ ρ = eval σ₀ e σ ρ := by
  subst h; rfl

/-- A `requires true` of `P` stays `true` on `P.mitRuhe`. -/
theorem req_mitRuhe_wahr (P : Programm D) (f : D.Fn) (hf : P.requires f = .tru)
    (σ : World D.mitRuhe) (ρ : Env D.mitRuhe (D.mitRuhe.params (some f))) :
    ReqAmEintritt P.mitRuhe (some f) σ ρ := by
  refine (congrArg wahr? (eval_umΛ (anfang_map (D.signatur f)) (ruE (P.requires f)) σ σ ρ)).trans ?_
  have e : ruE (P.requires f) = ruE (Expr.tru (D := D)) := by rw [hf]
  rw [e]
  rfl

/-- **The runtime's start, stated on `P`**: declared starts (each once) on
    threads `0 .. k-1` with their `requires` holding in `P` at the start
    memory, the idle root on every other thread, the lock invariants of `P`
    at the start memory -- an admissible start of `P.mitRuhe` from the
    translated memory. -/
theorem startZulaessig_mitRuhe_P [DecidableEq D.Fn] (P : Programm D) {S : SperrInv D}
    {fs ws : List D.Fn} (aktiv : List (Σ w : D.Fn, Env D (D.params w))) (sp : Speicher D)
    (hws : ∀ a ∈ aktiv, a.1 ∈ ws) (hnd : (aktiv.map (·.1)).Nodup)
    (hreq : ∀ a ∈ aktiv, ReqAmEintritt P a.1 (sp.welt []) a.2)
    (hS : ∀ L, S.inv L sp = true) :
    StartZulaessig P.mitRuhe S.mitRuhe (fsRuhe fs) (wsRuhe ws) (speicherR sp) (initRuhe aktiv) :=
  startZulaessig_mitRuhe P aktiv (speicherR sp) hws hnd
    (fun a ha => (req_mitRuhe_iff P a.1 (sp.welt []) a.2).mpr (hreq a ha))
    (fun L => by rw [speicherZ_speicherR]; exact hS L)

/-! ## 1. The export of `beispiele/104` -/

/-- A memory of the export: every balance `0`. -/
def x104Sp : Speicher x104D :=
  ⟨fun t _ f => match t, f with
    | .Konto, .stand => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

def x104IdleSources : Invarianten.Pruefer.LockSources x104S.mitRuhe := fun _ => some
  { resources := [], expression := .tru, correct := fun _ => rfl }

/-- Capability gap: outside the decidable fragment: translated old-memory postconditions. -/

theorem gP_mitRuhe_abgelehnt :
    Akzeptiert x104P.mitRuhe x104S.mitRuhe (fsRuhe x104Fs) x104Ls x104Cs (wsRuhe []) (sources := x104IdleSources) = false := by decide +kernel

/-- **An admissible start of `gP.mitRuhe`** -- the export itself has none
    (`gP_start_leer`). -/
theorem gP_mitRuhe_start :
    ∃ (sp : Speicher x104D.mitRuhe)
      (init : Faden → Σ f : x104D.mitRuhe.Fn, Env x104D.mitRuhe (x104D.mitRuhe.params f)),
      StartZulaessig x104P.mitRuhe x104S.mitRuhe (fsRuhe x104Fs) (wsRuhe []) sp init :=
  ⟨speicherR x104Sp, ruheInit _, startZulaessig_ruhe x104P _ (fun _ => rfl)⟩

/-! ## 2. Probes B and C -/

/-- **An admissible start of probe B on `zPB.mitRuhe`.** -/
theorem probeB_start :
    ∃ (sp : Speicher zD.mitRuhe)
      (init : Faden → Σ f : zD.mitRuhe.Fn, Env zD.mitRuhe (zD.mitRuhe.params f)),
      StartZulaessig zPB.mitRuhe zS.mitRuhe (fsRuhe zFs) (wsRuhe []) sp init :=
  ⟨speicherR zSp, ruheInit _, startZulaessig_ruhe zPB _ (fun _ => rfl)⟩

/-- **An admissible start of probe C on `zPC.mitRuhe`.** -/
theorem probeC_start :
    ∃ (sp : Speicher zD.mitRuhe)
      (init : Faden → Σ f : zD.mitRuhe.Fn, Env zD.mitRuhe (zD.mitRuhe.params f)),
      StartZulaessig zPC.mitRuhe zS.mitRuhe (fsRuhe zFs) (wsRuhe []) sp init :=
  ⟨speicherR zSp, ruheInit _, startZulaessig_ruhe zPC _ (fun _ => rfl)⟩

/-! ## 3. The two-thread fixture with its declared starts -/

def mFragmentIdleSources : Invarianten.Pruefer.LockSources mFragmentS.mitRuhe := fun _ => some
  { resources := [], expression := .tru, correct := fun _ => rfl }

/-- The replacement still witnesses admission after adding the runtime root. -/
theorem mFragment_mitRuhe_akzeptiert :
    Akzeptiert mFragment.mitRuhe mFragmentS.mitRuhe (fsRuhe mFs) [()] mCs
      (wsRuhe [mHauptA, mHauptB]) (sources := mFragmentIdleSources) = true := by
  decide +kernel

/-- **`hauptA` on thread 0, `hauptB` on thread 1, the root everywhere
    else, is admissible on `mP.mitRuhe`.** -/
theorem mP_mitRuhe_start :
    StartZulaessig mP.mitRuhe mSI.mitRuhe (fsRuhe mFs) (wsRuhe [mHauptA, mHauptB])
      (speicherR mSp) (initRuhe [⟨mHauptA, .nil⟩, ⟨mHauptB, .nil⟩]) := by
  refine startZulaessig_mitRuhe mP _ _ ?_ (by decide) ?_ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact req_mitRuhe_wahr mP mHauptA rfl _ _
    · exact req_mitRuhe_wahr mP mHauptB rfl _ _
  · intro L
    rw [speicherZ_speicherR]
    cases L
    decide

#print axioms Gabbro.Grammatik.startZulaessig_mitRuhe_P
#print axioms Gabbro.Grammatik.gP_mitRuhe_abgelehnt
#print axioms Gabbro.Grammatik.gP_mitRuhe_start
#print axioms Gabbro.Grammatik.probeB_start
#print axioms Gabbro.Grammatik.probeC_start
#print axioms Gabbro.Grammatik.mFragment_mitRuhe_akzeptiert
#print axioms Gabbro.Grammatik.mP_mitRuhe_start

end Gabbro.Grammatik
