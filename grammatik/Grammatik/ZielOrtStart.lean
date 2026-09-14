/-
  File:      Grammatik/ZielOrtStart.lean
  Subject:   WHAT A START FUNCTION OWES AT ITS END (SATZKARTE §15.6, §16.2).

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
-/
import Grammatik.ZielOrtMehrfaden
import Grammatik.Durchgaenge
import Grammatik.ZielOrtEinfaden

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The predicate -/

/-- The residue stands at a `return e` a pop would fire on: `ret` as the
    end block, `ret` before the rest of an end block, or `ret` before the
    rest of a block. -/
def RetKopf {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : ErgExpr D Γ Λ V.erg) (r : GRest D V l Γ Λ) : Prop :=
  ∃ hperm : Λ.Perm V.ende,
    r = .ende (.ret e hperm) ∨ (∃ rest, r = .ende (.cons (.ret e hperm) rest)) ∨
    (∃ (Λ'' : List (Res D)) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ''),
      r = .dann (.cons (.ret e hperm) rest) k)

/-- **The start function's completion**: at every thread whose stack is
    empty and whose head stands at `return e`, the start function's
    `ensures` and every invariant it owes hold at the world the return
    reads, with the returned value. -/
def StartEndeG (P : Programm D) (M : RufMaschineG D) : Prop :=
  ∀ (t : Faden), (M.faeden t).stapel = [] →
    ∀ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ)
      (r : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ)
      (e : ErgExpr D Γ Λ (vertragVon D (M.faeden t).kopf.f).erg),
      (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, r⟩ → RetKopf e r →
      EnsAmRueck P (M.faeden t).kopf.f (M.faeden t).kopf.s0 ((M.weltVon t).lese Λ e.orte)
          (M.faeden t).kopf.rho (evalErg ((M.weltVon t).lese Λ e.orte) e
            ((M.weltVon t).lese Λ e.orte) ρ) ∧
        InvAmRueck P (M.faeden t).kopf.f ((M.weltVon t).lese Λ e.orte)

/-! ## 2. From the replay -/

section Ende

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool}

/-- **A replayed head at a `return` meets `ensures` and its owed
    invariants at the machine world** -- whether or not a caller waits. -/
theorem kopfS_ret (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f) (hI : ∀ f, InvGutS P passes Q S f)
    (hFS : ∀ f, FussS P S lok f) {G : RufRahmenG D} {W : World D}
    (hG : KopfS P O passes Q S lok G W) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D G.f) l Γ Λ} (hr : G.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (e : ErgExpr D Γ Λ (vertragVon D G.f).erg) (hk : RetKopf e r) :
    EnsAmRueck P G.f G.s0 (W.lese Λ e.orte) G.rho (evalErg (W.lese Λ e.orte) e (W.lese Λ e.orte) ρ) ∧
      InvAmRueck P G.f (W.lese Λ e.orte) := by
  obtain ⟨hperm, h | ⟨rest, h⟩ | ⟨Λ'', rest, k, h⟩⟩ := hk <;> subst h
  · have hok := kopfS_okS hG hr
    exact ⟨popS_ens hO hRL hQ hS hsp hK hG hr e (erg_stabil (hFS _) e hok.2)
        (ens_stabil (hFS _) hperm) (fun O' R U σ => semH_rueck S O' U passes R e hperm σ ρ),
      popS_inv hO hRL hQ hS hsp hI hG hr e (fun i hi hs => inv_stabil (hFS _) hperm hi hs)
        (fun O' R U σ => semH_rueck S O' U passes R e hperm σ ρ)⟩
  · have hok := okS_ende_cons (kopfS_okS hG hr)
    exact ⟨popS_ens hO hRL hQ hS hsp hK hG hr e (erg_stabil (hFS _) e hok.2.1)
        (ens_stabil (hFS _) hperm) (fun O' R U σ => semH_rueckCons S O' U passes R e hperm rest σ ρ),
      popS_inv hO hRL hQ hS hsp hI hG hr e (fun i hi hs => inv_stabil (hFS _) hperm hi hs)
        (fun O' R U σ => semH_rueckCons S O' U passes R e hperm rest σ ρ)⟩
  · have hok := okS_dann_cons (kopfS_okS hG hr)
    exact ⟨popS_ens hO hRL hQ hS hsp hK hG hr e (erg_stabil (hFS _) e hok.2.1)
        (ens_stabil (hFS _) hperm) (fun O' R U σ => semH_dannRet S O' U passes R e hperm rest k σ ρ),
      popS_inv hO hRL hQ hS hsp hI hG hr e (fun i hi hs => inv_stabil (hFS _) hperm hi hs)
        (fun O' R U σ => semH_dannRet S O' U passes R e hperm rest k σ ρ)⟩

end Ende

/-! ## 2a. A start function may not end in a reason

A reason return (`retGrund`) hands a failure to the CALLER, which the
typing forces to handle it (`bindCallElse` with its `else` block; a call
that ignores reasons needs `gruende = 0`). A thread's start frame has no
caller: a reason there is a failure nobody handles, no `ensures` is
claimed for it (`rufAt` checks neither `ensures` nor invariants at a
reason return), and `StartEndeG` said nothing (verdict
`URTEIL-MUSE-2026-09-14.md` §5: a start function with `ensures false`
whose body fails with a reason met every premise).

**The decision: start functions declare no reasons** (`StartOhneGrund`,
decidable per start). Then no start frame can stand at a reason return --
`retGrund` needs an element of `Fin (gruende f)` and the bottom frame of a
thread always runs its start function (`wurzelFn_erreichbar`) -- so every
completion of a start function is a VALUE return, where `StartEndeG`
checks `ensures` and the owed invariants (`keinStartGrundG`; with
`FertigG`: `fertig_wert`, `Verklemmung.lean`). The alternative -- let a
reason return of a start function check its owed invariants -- would
demand at a thread's root what `rufAt` does not demand of any other reason
return, and still leave its `ensures` unchecked. -/

/-- **The start functions declare no reasons.** -/
def StartOhneGrund (init : Faden → Σ f : D.Fn, Env D (D.params f)) : Prop :=
  ∀ t, D.gruende (init t).1 = 0

/-- The function of a thread's bottom frame. -/
def wurzelFn (z : RufFadenG D) : D.Fn := (z.stapel.getLast?.getD z.kopf).f

/-- No rule of G changes the function of the bottom frame. -/
theorem wurzelFn_schritt {P : Programm D} {O : Orakel D} {pa : Nat} {M M' : RufMaschineG D}
    {u : Faden} (hs : RufSchrittG P O pa M u M') : wurzelFn (M'.faeden u) = wurzelFn (M.faeden u) := by
  rcases schrittMerk hs with ⟨hst, hf, _⟩ | ⟨g, c', rho, s0, hst, hcf, _, _⟩ |
      ⟨caller, rst, hpop, hst, hf, _⟩
  · unfold wurzelFn; rw [hst]
    cases (M.faeden u).stapel.getLast? with
    | none => exact hf
    | some F => rfl
  · unfold wurzelFn; rw [hst, List.getLast?_cons]
    cases (M.faeden u).stapel.getLast? with
    | none => exact hcf
    | some F => rfl
  · unfold wurzelFn; rw [hst, hpop, List.getLast?_cons]
    cases rst.getLast? with
    | none => exact hf
    | some F => rfl

/-- **The bottom frame of every thread runs its start function**, on every
    reachable machine. -/
theorem wurzelFn_erreichbar {P : Programm D} {O : Orakel D} {pa : Nat} {sp : Speicher D}
    {init : Faden → Σ f : D.Fn, Env D (D.params f)} {M : RufMaschineG D}
    (hr : RufErreichbarG P O pa (RufStartG P sp init) M) : ∀ t, wurzelFn (M.faeden t) = (init t).1 := by
  induction hr with
  | start => intro t; rw [start_faden]; rfl
  | schritt M M' u _ hs ih =>
      intro t
      by_cases htu : t = u
      · subst htu
        rw [wurzelFn_schritt hs]
        exact ih t
      · rw [rufSchrittG_fremd hs t htu]
        exact ih t

/-- The residue stands at a reason return (`retGrund`) a pop would fire on:
    as the end block, before the rest of an end block, or before the rest
    of a block. -/
def GrundKopf {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ) : Prop :=
  ∃ (g : Fin V.gruende) (hperm : Λ.Perm V.ende),
    r = .ende (.retGrund g hperm) ∨ (∃ rest, r = .ende (.cons (.retGrund g hperm) rest)) ∨
    (∃ (Λ'' : List (Res D)) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ''),
      r = .dann (.cons (.retGrund g hperm) rest) k)

/-- **No start frame stands at a reason return.** -/
def KeinStartGrundG (M : RufMaschineG D) : Prop :=
  ∀ (t : Faden), (M.faeden t).stapel = [] →
    ∀ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ)
      (r : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ),
      (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, r⟩ → ¬ GrundKopf r

/-- **Start functions without reasons never end in one**, on every
    reachable machine. -/
theorem keinStartGrundG {P : Programm D} {O : Orakel D} {pa : Nat} {sp : Speicher D}
    {init : Faden → Σ f : D.Fn, Env D (D.params f)} (hG : StartOhneGrund init) {M : RufMaschineG D}
    (hr : RufErreichbarG P O pa (RufStartG P sp init) M) : KeinStartGrundG M := by
  intro t hst l Γ Λ ρ r _ ⟨g, _, _⟩
  have hw := wurzelFn_erreichbar hr t
  unfold wurzelFn at hw
  rw [hst] at hw
  have h0 : (vertragVon D (M.faeden t).kopf.f).gruende = 0 := by
    show D.gruende (M.faeden t).kopf.f = 0
    have e : (M.faeden t).kopf.f = (init t).1 := hw
    rw [e]
    exact hG t
  have hg : g.val < (vertragVon D (M.faeden t).kopf.f).gruende := g.2
  omega

/-! ## 3. The theorems at one budget (lemmas) -/

/-- **The flagship with the start functions' completion, generic in the
    local carriers, AT ONE `forever` BUDGET.** The conclusion of
    `ziel_ort_sperre_invL` AND `StartEndeG`: at every finished thread (empty
    stack, head at a `return`) the start function's `ensures` and owed
    invariants hold. A lemma: the goal statement is `ziel_ort_ende` (§4),
    over every budget. -/
theorem ziel_ort_ende_bei (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (lok : D.Tab ⊕ D.Glob → Bool) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
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
  refine ⟨ziel_ort_sperre_invL P O passes Q S lok sp init e0 hO hRL hQ hlok hS hFragS hFS hLok hK
    hStart hSstart hex hI M hr, ?_⟩
  have hZ := (zielInvS_erreichbarL P O passes Q S lok sp init e0 hO hRL hQ hlok hS hFragS hFS
    hLok hK hStart hSstart hex M hr).1
  intro t _ l Γ Λ ρ r e hr' hk
  exact kopfS_ret hO hRL hQ hS hSstart hK hI hFS (hZ.1 t).1 hr' e hk

/-- `ziel_ort_mehrfaden_ende` at ONE budget (a lemma; §4 has the goal
    statement). -/
theorem ziel_ort_mehrfaden_ende_bei (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
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
  ziel_ort_ende_bei P O passes Q S (lokK P K) sp init e0 hO hRL hQ hlok hS
    (programmImFragmentS_ok P S hvoll hFrag hFuss) hFuss
    (lokOk_mehr hO hvoll sp init K hAbg hWurzel) hK hStart hSstart hex hI

/-- `ziel_ort_sperre_ende` at ONE budget (the footprint check
    `fussSperreB`; a lemma). -/
theorem ziel_ort_sperre_ende_bei (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
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
  ziel_ort_ende_bei P O passes Q S (freiB fs) sp init e0 hO hRL hQ hlok hS
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
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
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
    ziel_ort_ende_bei P O passes Q S lok sp init e0 hO hRL hQ hlok hS hFragS hFS
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
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
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
    ziel_ort_mehrfaden_ende_bei P O passes Q S fs sp init e0 K hO hRL hQ hlok hS hvoll
    hFrag hAbg hWurzel hFuss (hK passes) hStart hSstart hex (hI passes) M hr

/-- **`ziel_ort_sperre_ende`, over every budget** (footprint check
    `fussSperreB`). -/
theorem ziel_ort_sperre_ende (P : Programm D) (O : Orakel D) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
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
    ziel_ort_sperre_ende_bei P O passes Q S fs sp init e0 hO hRL hQ hlok hS hvoll hFrag
    hFuss (hK passes) hStart hSstart hex (hI passes) M hr

#print axioms Gabbro.Grammatik.kopfS_ret
#print axioms Gabbro.Grammatik.wurzelFn_erreichbar
#print axioms Gabbro.Grammatik.keinStartGrundG
#print axioms Gabbro.Grammatik.ziel_ort_ende_bei
#print axioms Gabbro.Grammatik.ziel_ort_ende
#print axioms Gabbro.Grammatik.ziel_ort_mehrfaden_ende
#print axioms Gabbro.Grammatik.ziel_ort_sperre_ende

end Gabbro.Grammatik
