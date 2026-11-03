/-
  File:      Grammatik/ZielOrtStart.lean
  Subject:   WHAT A START FUNCTION OWES AT ITS END (THEOREM-MAP §15.6, §16.2).

  Machine G logs a return only when a frame POPS (`rueck g rho v s0 s1`),
  and a thread's start frame has no caller: it never pops. So `InvAmOrtG`
  (every logged return meets its owed invariants) and the `ensures` half of
  `VertragAmOrtG` said nothing about a start function -- an invariant owed
  at the return of a thread's start function was never checked.

  **The decision.** The completion of a start function IS a machine state:
  the thread's stack is empty and its head stands at a `return` (one of the
  three shapes a pop would fire on: `ret`, `ret` before the rest of an end
  block, `ret` before the rest of a block). No rule of G applies there (the
  returns need a caller, `kein_schritt_ruhig` for the bare shape); the
  thread is finished and stays so. The statement is therefore a property of
  every reachable machine, not of a log entry, and it needs no change of G:

  * `StartEndeG P M`: for every thread whose stack is empty and whose head
    stands at a `return e`, the start function's `ensures` AND every
    invariant it owes hold at the world that return reads
    (`(M.weltVon t).lese Λ e.orte`, exactly the world a pop would log), with
    the value `e` evaluates to there.

  Because it holds on EVERY reachable machine, it holds at the moment the
  thread finishes and at every later moment: the carriers read are stable
  for the finished frame (signature-guarded -- the finished thread holds
  those locks for good --, protected by a lock the frame names, or local),
  and the replay invariant keeps them. A start function that never returns
  owes nothing here (the premise never fires); no `never`/`diverges`
  annotation is needed. The obligation is the existing one: `KoerperGutS`
  (ensures) and `InvGutS` (owed invariants) of the start function, the same
  per-function sequential triples every function owes.

  `ziel_ort_ende` (generic in the local carriers) and
  `ziel_ort_mehrfaden_ende` (thread-local carriers): the flagship's
  conclusion AND `StartEndeG`.

  Since 2026-09-14 (second round, THEOREM-MAP §18): the goal statements of
  §4 demand the obligations at EVERY `forever` budget and conclude on the
  machines of every budget (probe D, `Durchgaenge.lean`, `ProbeD.lean`;
  the per-budget statements are the lemmas `*_bei` of §3), and start
  functions declare no reasons (§2a: `StartOhneGrund`, `KeinStartGrundG`),
  `StartEndeG` covers both plain and completed scoped returns. Replay supplies
  `ScopedRueckGutG` at the release source; `ZielOrtStartSaved.lean` carries
  that guarantee with the saved pre-release world.
-/
module
public import Grammatik.Zielsatz.ZielOrt.Grundlage.Core.ZielOrtStartBasis
public import Grammatik.Zielsatz.ZielOrt.Grundlage.Core.ZielOrtStartScoped
public import Grammatik.Zielsatz.ZielOrt.Grundlage.Core.ZielOrtStartSaved
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtMehrfaden
public import Grammatik.Kern.Semantik.Evaluation.Durchgaenge
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtEinfaden
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}
theorem ziel_ort_ende_bei (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (lok : D.Tab ⊕ D.Glob → Bool) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussS P S lok f) (hLok : LokOk P O passes lok sp init)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hI : ∀ f : D.Fn, InvGutS P passes Q S f) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      ((VertragAmOrtG P M ∧ SperrInvG S M ∧ KeinLogikHaltG O passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M') ∧
      InvAmOrtG P M) ∧ StartEndeG P M := by
  intro M hr
  refine ⟨ziel_ort_sperre_invL P O passes Q S lok sp init hO hRL hQ hlok hS hFragS hFS hLok hK
    hStart hSstart hex hI M hr, ?_⟩
  have hZ := (zielInvS_erreichbarL P O passes Q S lok sp init hO hRL hQ hlok hS hFragS hFS
    hLok hK hStart hSstart hex M hr).1
  constructor
  · intro t _ l Γ Λ ρ r e hr' hk
    exact kopfS_ret hO hRL hQ hS hSstart hK hI hFS (hZ.1 t).1 hr' e hk
  · exact startScopedEndeG_erreichbar
      (ziel_ort_scoped_rueck_bei P O passes Q S lok sp init hO hRL hQ hlok hS hFragS hFS
        hLok hK hStart hSstart hex hI) hr

/-- `ziel_ort_mehrfaden_ende` at ONE budget (a lemma; §4 has the goal
    statement). -/
theorem ziel_ort_mehrfaden_ende_bei (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (K : Faden → D.Fn → Bool)
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussS P S (lokK P K) f)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hI : ∀ f : D.Fn, InvGutS P passes Q S f) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      ((VertragAmOrtG P M ∧ SperrInvG S M ∧ KeinLogikHaltG O passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M') ∧
      InvAmOrtG P M) ∧ StartEndeG P M :=
  ziel_ort_ende_bei P O passes Q S (lokK P K) sp init hO hRL hQ hlok hS
    (programmImFragmentS_ok P S hvoll hFrag hFuss) hFuss
    (lokOk_mehr hO hvoll sp init K hAbg hWurzel) hK hStart hSstart hex hI

/-- `ziel_ort_sperre_ende` at ONE budget (the footprint check
    `fussSperreB`; a lemma). -/
theorem ziel_ort_sperre_ende_bei (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussSperreB P S fs = true)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hI : ∀ f : D.Fn, InvGutS P passes Q S f) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      ((VertragAmOrtG P M ∧ SperrInvG S M ∧ KeinLogikHaltG O passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M') ∧
      InvAmOrtG P M) ∧ StartEndeG P M :=
  have hFS : ∀ f, FussS P S (freiB fs) f := fussSperreB_ok hvoll hFuss
  ziel_ort_ende_bei P O passes Q S (freiB fs) sp init hO hRL hQ hlok hS
    (programmImFragmentS_ok P S hvoll hFrag hFS) hFS (lokOk_frei hO hvoll sp init) hK hStart
    hSstart hex hI

/-! ## 4. THE GOAL STATEMENTS: over EVERY `forever` budget

The obligation (`KoerperGutS`, `InvGutS`) is demanded at every budget, the
conclusion holds on the machines of every budget. G re-arms the budget at
every loop entry, so every finite run is a run at some budget: the
conclusion covers every finite run, and no budget is chosen that could
empty the obligation of a `forever` loop (probe D, `Durchgaenge.lean`,
`ProbeD.lean`). -/

/-- **The flagship with the start functions' completion, generic in the
    local carriers, over every budget.** -/
theorem ziel_ort_ende (P : Programm D) (O : Orakel D) (Q : AxEns D)
    (S : SperrInv D) (lok : D.Tab ⊕ D.Glob → Bool) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussS P S lok f) (hLok : ∀ passes : Nat, LokOk P O passes lok sp init)
    (hK : ∀ (passes : Nat) (f : D.Fn), KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hI : ∀ (passes : Nat) (f : D.Fn), InvGutS P passes Q S f)
    (hGrund : StartOhneGrund init) :
    ∀ (passes : Nat) (M : RufMaschineG D), RufErreichbarG P O passes (RufStartG P sp init) M →
      ((VertragAmOrtG P M ∧ SperrInvG S M ∧ KeinLogikHaltG O passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M') ∧
      InvAmOrtG P M) ∧ StartEndeG P M ∧ KeinStartGrundG M :=
  fun passes M hr => (fun h => ⟨h.1, h.2, keinStartGrundG hGrund hr⟩) <|
    ziel_ort_ende_bei P O passes Q S lok sp init hO hRL hQ hlok hS hFragS hFS
    (hLok passes) (hK passes) hStart hSstart hex (hI passes) M hr

/-- **THE FLAGSHIP (2026-09-14, budget-quantified): several active threads
    with thread-local carriers, lock invariants, table invariants, and the
    start functions' completion, over EVERY `forever` budget.** The
    premises of `ziel_ort_mehrfaden` (obligations at every budget) and
    start functions without reasons (`StartOhneGrund`); the conclusion of
    `ziel_ort_mehrfaden` AND `StartEndeG` AND `KeinStartGrundG` (every
    completion of a start function is a value return, where `StartEndeG`
    checks it), on the machines of every budget. -/
theorem ziel_ort_mehrfaden_ende (P : Programm D) (O : Orakel D) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (K : Faden → D.Fn → Bool)
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussS P S (lokK P K) f)
    (hK : ∀ (passes : Nat) (f : D.Fn), KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hI : ∀ (passes : Nat) (f : D.Fn), InvGutS P passes Q S f)
    (hGrund : StartOhneGrund init) :
    ∀ (passes : Nat) (M : RufMaschineG D), RufErreichbarG P O passes (RufStartG P sp init) M →
      ((VertragAmOrtG P M ∧ SperrInvG S M ∧ KeinLogikHaltG O passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M') ∧
      InvAmOrtG P M) ∧ StartEndeG P M ∧ KeinStartGrundG M :=
  fun passes M hr => (fun h => ⟨h.1, h.2, keinStartGrundG hGrund hr⟩) <|
    ziel_ort_mehrfaden_ende_bei P O passes Q S fs sp init K hO hRL hQ hlok hS hvoll
    hFrag hAbg hWurzel hFuss (hK passes) hStart hSstart hex (hI passes) M hr

/-- **`ziel_ort_sperre_ende`, over every budget** (footprint check
    `fussSperreB`). -/
theorem ziel_ort_sperre_ende (P : Programm D) (O : Orakel D) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussSperreB P S fs = true)
    (hK : ∀ (passes : Nat) (f : D.Fn), KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hI : ∀ (passes : Nat) (f : D.Fn), InvGutS P passes Q S f)
    (hGrund : StartOhneGrund init) :
    ∀ (passes : Nat) (M : RufMaschineG D), RufErreichbarG P O passes (RufStartG P sp init) M →
      ((VertragAmOrtG P M ∧ SperrInvG S M ∧ KeinLogikHaltG O passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M') ∧
      InvAmOrtG P M) ∧ StartEndeG P M ∧ KeinStartGrundG M :=
  fun passes M hr => (fun h => ⟨h.1, h.2, keinStartGrundG hGrund hr⟩) <|
    ziel_ort_sperre_ende_bei P O passes Q S fs sp init hO hRL hQ hlok hS hvoll hFrag
    hFuss (hK passes) hStart hSstart hex (hI passes) M hr

/-- **One active thread, over every budget, with the start functions'
    completion** (`ziel_ort_einfaden` with `StartEndeG` and
    `KeinStartGrundG`): every thread but `0` idle, no footprint check, no
    exclusivity premise. The shape of every sequential corpus program
    (thread `0` the driver's call, the rest the runtime's idle roots). -/
theorem ziel_ort_einfaden_ende (P : Programm D) (O : Orakel D) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true)
    (hRuhe : ∀ u, u ≠ 0 → ruhig P (init u).1 = true)
    (hK : ∀ (passes : Nat) (f : D.Fn), KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true)
    (hI : ∀ (passes : Nat) (f : D.Fn), InvGutS P passes Q S f)
    (hGrund : StartOhneGrund init) :
    ∀ (passes : Nat) (M : RufMaschineG D), RufErreichbarG P O passes (RufStartG P sp init) M →
      ((VertragAmOrtG P M ∧ SperrInvG S M ∧ KeinLogikHaltG O passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M') ∧
      InvAmOrtG P M) ∧ StartEndeG P M ∧ KeinStartGrundG M :=
  fun passes M hr => (fun h => ⟨h.1, h.2, keinStartGrundG hGrund hr⟩) <|
    ziel_ort_ende_bei P O passes Q S (fun _ => true) sp init hO hRL hQ hlok hS
      (programmImFragmentS_ok P S hvoll hFrag (fussS_alle P S)) (fussS_alle P S)
      (lokOk_einfaden sp init hRuhe) (hK passes) hStart hSstart (startExklusiv_einfaden init hRuhe)
      (hI passes) M hr

#print axioms Gabbro.Grammatik.kopfS_ret
#print axioms Gabbro.Grammatik.ziel_ort_einfaden_ende
#print axioms Gabbro.Grammatik.wurzelFn_erreichbar
#print axioms Gabbro.Grammatik.keinStartGrundG
#print axioms Gabbro.Grammatik.ziel_ort_ende_bei
#print axioms Gabbro.Grammatik.ziel_ort_ende
#print axioms Gabbro.Grammatik.ziel_ort_mehrfaden_ende
#print axioms Gabbro.Grammatik.ziel_ort_sperre_ende

end Gabbro.Grammatik
