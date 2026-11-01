module

public import Grammatik.Zielsatz.Eigenschaften.NeverAsm
public import Grammatik.Logik.Ruf.Maschine.RufMaschineF
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz
public import Grammatik.Zielsatz.Eigenschaften.Divergenz.Teil1
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

namespace Gabbro.Grammatik.Zielsatz
open Gabbro.Grammatik

/-- Start slot value: `0`. -/
theorem divSp0_slot :
    divSp0.slots () 0 () = (⟨0, by decide, by decide⟩ :
      Wert divD (divD.typ () ())) := by rfl

/-- Thread start: thread 0 runs `lies`, thread 1 runs `schreib 7`. -/
def divInit : Faden → Σ f : divD.Fn, Env divD (divD.params f)
  | 0 => ⟨divLies, Env.nil⟩
  | _ => ⟨divSchreib, divRho7⟩

/-! ## 6. The witness run: lock, write, then the head stands at `forever` -/

/-- The start machine for the witness run. -/
def divM0F : RufMaschineF divD := RufStartF divP divSp0 divInit

/-- The lock is free at the start: every trace is empty. -/
theorem divFrei0F : RufFreiF divM0F 1 (()) := by
  intro g hne hmem
  have e : (divM0F.faeden g).spur = [] := rfl
  have hnil : offen (divM0F.faeden g).spur = [] := by rw [e]; rfl
  have h2 : (()) ∈ ([] : List divD.Lock) := hnil ▸ hmem
  exact (List.mem_nil_iff _).mp h2 |>.elim

/-- Thread 1 holds nothing yet. -/
theorem divSelf0F : (() : divD.Lock) ∉ offen (divM0F.faeden 1).spur := by
  intro hmem
  have e : (divM0F.faeden 1).spur = [] := rfl
  have hnil : offen (divM0F.faeden 1).spur = [] := by rw [e]; rfl
  have h2 : (()) ∈ ([] : List divD.Lock) := hnil ▸ hmem
  exact (List.mem_nil_iff _).mp h2 |>.elim

/-- Thread 1 holds nothing, so the rank side is vacuous. -/
theorem divRang0F (K : divD.Lock) (hK : K ∈ offen (divM0F.faeden 1).spur) :
    divD.rang K < divD.rang (()) := by
  have e : (divM0F.faeden 1).spur = [] := rfl
  have hnil : offen ([] : List (Ereignis divD)) = [] := rfl
  rw [e, hnil, List.mem_nil_iff] at hK
  exact absurd hK (by decide)

/-- Step A: thread 1 takes the lock. -/
def divM1F : RufMaschineF divD :=
  ⟨divM0F.speicher,
   rufUpdateF divM0F.faeden 1
     ⟨(divM0F.faeden 1).stapel, (divM0F.faeden 1).kopf,
      Ereignis.nimmt () (offen (divM0F.faeden 1).spur) :: (divM0F.faeden 1).spur,
      (divM0F.faeden 1).log⟩,
   divM0F.lauf ++ rufEigenF 1 [Ereignis.nimmt () (offen (divM0F.faeden 1).spur)],
   divM0F.start⟩

theorem divSchrittAF :
    RufSchrittF divP divO 0 divM0F 1 divM1F := by
  unfold divM1F
  exact RufSchrittF.nimmt divM0F 1 () divSelf0F (fun K hK => divRang0F K hK)
    divFrei0F

theorem divReachAF : RufErreichbarF divP divO 0 divM0F divM1F :=
  RufErreichbarF.schritt _ _ 1 RufErreichbarF.start divSchrittAF

/-- Thread 1 holds the lock exactly after step A. -/
theorem divM1Fhaelt :
    HeldGenau [Res.held (D := divD) ()]
      (offen (divM1F.faeden 1).spur) := by
  intro L
  have eL : L = () := by cases L <;> rfl
  have eH : offen (divM1F.faeden 1).spur = [()] := rfl
  rw [eH, eL]
  constructor
  · intro hL
    have heq : Res.held (D := divD) L = Res.held (D := divD) () :=
      (List.mem_singleton.mp hL)
    cases heq
    exact List.mem_singleton.mpr rfl
  · intro hL
    have heq : L = () :=
      (List.mem_singleton.mp (eH ▸ hL))
    cases heq
    exact List.mem_singleton.mpr rfl

/-- The evaluated index: `0`. -/
def divK0 : Int := 0

/-- The evaluated cap: `100` in range. -/
def divV100 : Wert divD (.int 0 100) := ⟨100, by decide, by decide⟩

/-- Step B: thread 1 fires the writing leaf `konto[0] := 100`. The head
    after the step stands at the diverging `forever`. -/
def divM2F : RufMaschineF divD :=
  ⟨(((divM1F.weltVon 1).lese [Res.held (D := divD) ()]
      (divIdx.orte ++ divHundert.orte)).schreibSlot () [Res.held (D := divD) ()]
      divK0 () divV100).speicher,
   rufUpdateF divM1F.faeden 1
     ⟨(divM1F.faeden 1).stapel,
      ⟨(divM1F.faeden 1).kopf.f, (divM1F.faeden 1).kopf.rho,
       (divM1F.faeden 1).kopf.s0,
       ⟨false, [.int 0 10], [Res.held (D := divD) ()], divRho7,
        .cons divSchleife (.ret .empty (by rfl))⟩⟩,
      (((divM1F.weltVon 1).lese [Res.held (D := divD) ()]
        (divIdx.orte ++ divHundert.orte)).schreibSlot () [Res.held (D := divD) ()]
        divK0 () divV100).spur,
      (divM1F.faeden 1).log⟩,
   divM1F.lauf ++ rufEigenF 1
     [Ereignis.zugriff () true [Res.held (D := divD) ()]
       (divM1F.weltVon 1).haelt],
   divM1F.start⟩

theorem divSchrittBF : RufSchrittF divP divO 0 divM1F 1 divM2F := by
  have hhead : (divM1F.faeden 1).kopf.rest =
      ⟨false, [.int 0 10], [Res.held (D := divD) ()], divRho7,
        .cons divWriteStAt
          (.cons divSchleife (.ret .empty (by rfl)))⟩ := rfl
  have hstep : (execStmt divO 0 keinRuf divWriteStAt
      (divM1F.weltVon 1) divRho7) =
      Ausgang.ok (D := divD) (V := vertragVon divD divSchreib)
        (((divM1F.weltVon 1).lese [Res.held (D := divD) ()]
          (divIdx.orte ++ divHundert.orte)).schreibSlot ()
          [Res.held (D := divD) ()] divK0 () divV100) divRho7 := rfl
  have hneu : (((divM1F.weltVon 1).lese [Res.held (D := divD) ()]
      (divIdx.orte ++ divHundert.orte)).schreibSlot () [Res.held (D := divD) ()]
      divK0 () divV100).spur =
      [Ereignis.zugriff () true [Res.held (D := divD) ()]
        (divM1F.weltVon 1).haelt] ++ (divM1F.faeden 1).spur := rfl
  have hkn : ∀ (L : divD.Lock) (h : List divD.Lock),
      Ereignis.nimmt L h ∉ [Ereignis.zugriff () true
        [Res.held (D := divD) ()] (divM1F.weltVon 1).haelt] := by
    intro L h hm
    simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at hm
  exact RufSchrittF.blatt divM1F 1 false [.int 0 10]
    [Res.held (D := divD) ()] [Res.held (D := divD) ()]
    divWriteStAt _ divRho7 rfl hhead divM1Fhaelt _ _ _ hstep hneu hkn

theorem divReachBF : RufErreichbarF divP divO 0 divM0F divM2F :=
  RufErreichbarF.schritt _ _ 1 divReachAF divSchrittBF

/-- `divM0F` IS the start machine. -/
theorem divM0F_start : divM0F = RufStartF divP divSp0 divInit := by rfl

/-- The witness run: lock, then the writing leaf -- reached from start. -/
theorem divB_erreicht :
    RufErreichbarF divP divO 0 (RufStartF divP divSp0 divInit) divM2F := by
  rw [← divM0F_start]
  exact divReachBF

/-- The final memory carries the written cap at `konto[0]`. -/
theorem divMB_slot : divM2F.speicher.slots () 0 () = divV100 := by
  have hhit := storeSlot_hit (D := divD)
    ((divM1F.weltVon 1).lese [Res.held (D := divD) ()]
      (divIdx.orte ++ divHundert.orte)) () divK0 () divV100
  have k0 : divK0 = (0 : Int) := rfl
  have hmem : divM2F.speicher.slots () 0 () =
      ((((divM1F.weltVon 1).lese [Res.held (D := divD) ()]
        (divIdx.orte ++ divHundert.orte)).storeSlot ()
        divK0 () divV100).slots () 0 ()) := rfl
  rw [k0] at hhit
  rw [hmem, k0]
  exact hhit

/-- Memory really moved: `konto[0]` reads `100`, the start reads `0`. -/
theorem divB_schreibt : divM2F.speicher.slots () 0 () ≠
    divSp0.slots () 0 () := by
  have h100 := divMB_slot
  have h0 : divSp0.slots () 0 () =
      (⟨0, by decide, by decide⟩ : Wert divD (divD.typ () ())) := rfl
  rw [h100, h0]
  intro hcon
  have hn : (divV100.n) = ((⟨0, by decide, by decide⟩ :
      Wert divD (divD.typ () ())).n) := congrArg Zahl.n hcon
  simp only [divV100, Int.reduceEq] at hn

/-- After step B the head stands at the diverging `forever`. -/
theorem divM2kopf : (divM2F.faeden 1).kopf.rest =
    ⟨false, [.int 0 10], [Res.held (D := divD) ()], divRho7,
      .cons divSchleife (.ret .empty (by rfl))⟩ := rfl

/-! ## 7. The joint witness: every premise together, nothing weakened -/

/-- The remaining body after the write diverges at every budget: the write
    runs, then the `forever` answers the named assumption. -/
theorem divRest_divergiert (n : Nat) (σ : World divD) (ρ : Env divD [.int 0 10]) :
    execEnd divO n keinRuf
      (.cons divSchleife (.ret .empty (by rfl)) :
        Endblock divD (vertragVon divD divSchreib) false [.int 0 10]
          [Res.held (D := divD) ()]) σ ρ =
      .hardware (.fortschritt ()) := by
  have hF : execStmt divO n keinRuf divSchleife σ ρ = .hardware (.fortschritt ()) :=
    forever_leer_divergiert divO n keinRuf () σ ρ
  simp only [execEnd, hF]

/-- Evidence bundle: the empty body cannot exit, at any oracle and budget. -/
theorem divNoExit (O : Orakel divD) (passes : Nat)
    (R : ∀ f : divD.Fn, World divD → Env divD (divD.params f) → RufAusgang f) :
    NoExit O passes R
      (.nil : Block divD (vertragVon divD divSchreib) true [.int 0 10]
        [Res.held (D := divD) ()] [Res.held (D := divD) ()]) :=
  fun _ _ => Or.inl ⟨_, _, rfl⟩

/-- Evidence bundle: `true` holds everywhere. -/
theorem divInvWahr :
    InvWahr (.tru : Expr divD [.int 0 10] [Res.held (D := divD) ()] .bool)
      [Res.held (D := divD) ()] :=
  fun _ _ => rfl

/-- **ZEUGE: `divergent_body_zeuge`.** All premises JOINTLY on the concrete
    non-degenerate program `divP`: a writer that writes `konto` then
    diverges in the accepted `forever` shape, a `-> never` axiom (the
    accepted `asm` shape), and a reached run that changes memory and stands
    at the `forever`. The same exit evidence proves the divergence
    (`forever_noexit_divergiert` applied to the witnessed `hNo`/`hInv`);
    the run shows it. The loop budget is `3`, not `0`: at budget `0`
    `foreverLauf` answers `hardware (fortschritt a)` by its first equation
    for EVERY loop (false guard, leavable body), so a budget-`0` conjunct
    would not depend on `hNo`/`hInv` at all. At `3` the guard is checked
    and the body run three times before the named exit (review G10).
    Nothing is weakened: the table is written
    (`divB_schreibt`), the run is reached (`divB_erreicht`), the axiom
    admits its site (`StelleOk`) and fits no answer (`AntwortLeer`). -/
theorem divergent_body_zeuge :
    ∃ (σ : World divD) (ρ : Env divD [.int 0 10]),
    ∃ (hNo : NoExit divO 3 keinRuf
          (.nil : Block divD (vertragVon divD divSchreib) true [.int 0 10]
            [Res.held (D := divD) ()] [Res.held (D := divD) ()]))
      (hInv : InvWahr (.tru : Expr divD [.int 0 10] [Res.held (D := divD) ()] .bool)
          [Res.held (D := divD) ()]),
      execStmt divO 3 keinRuf
          ((.forever () .tru .nil : Stmt divD (vertragVon divD divSchreib) false
            [.int 0 10] [Res.held (D := divD) ()] [Res.held (D := divD) ()])) σ ρ =
          .hardware (.fortschritt ()) ∧
      (∃ M : RufMaschineF divD,
        RufErreichbarF divP divO 0 (RufStartF divP divSp0 divInit) M ∧
        M.speicher.slots () 0 () ≠ divSp0.slots () 0 ()) ∧
      StelleOk divD (.inl ()) ∧ AntwortLeer divD (divD.aerg ()) := by
  obtain ⟨hNo, hInv⟩ : NoExit divO 3 keinRuf
      (.nil : Block divD (vertragVon divD divSchreib) true [.int 0 10]
        [Res.held (D := divD) ()] [Res.held (D := divD) ()]) ∧
      InvWahr (.tru : Expr divD [.int 0 10] [Res.held (D := divD) ()] .bool)
        [Res.held (D := divD) ()] :=
    ⟨divNoExit divO 3 keinRuf, divInvWahr⟩
  refine ⟨divSp0.welt [], divRho7, hNo, hInv, ?_, ?_, ?_, ?_⟩
  · exact forever_noexit_divergiert (l := false) divO 3 keinRuf () .tru .nil _ _
      hNo hInv
  · exact ⟨divM2F, divB_erreicht, divB_schreibt⟩
  · exact stelleOk_never_ax (D := divD) () divAx_never
  · exact asm_never_antwort_leer () divAx_never

/-! ## 8. The spin on machine G: a reached `.ewig` head, `KeinLogikHaltG` there

`divPS` is `divP` with `schreib` reduced to the bare spin and `lies` to
`return 0`, so that the G run needs no write step. Thread 0 runs `schreib`,
every other thread `lies`. Two G steps from the start (`endeEntf`,
`dannForever` at budget `1`) put thread 0 at the `.ewig` head; there the
WHOLE machine satisfies `KeinLogikHaltG` (thread 0 by `spin_prueft`, the
others at their start `return`, `ret_prueft`), and thread 0 takes its
next step (`ewig_wahr_schreitet`). The memory-changing run of this file
is the F-machine run of §6; this section is the G-machine witness that the
review asked for (G10 F3). -/

/-- `schreib` as a bare spin: `forever () invariant true {}`, then the
    unreachable `ret`. -/
def divRumpfSpin : Endblock divD (vertragVon divD divSchreib) false (divD.params divSchreib)
    (Signatur.anfang divD (divD.signatur divSchreib)) :=
  .cons (.forever () .tru .nil) (.ret .empty (by rfl))

/-- `lies` returns the constant `0` (no read, so no lock story). -/
def divRumpfNull : Endblock divD (vertragVon divD divLies) false (divD.params divLies)
    (Signatur.anfang divD (divD.signatur divLies)) :=
  .ret (.val (.widen (by decide) (by decide) (.lit 0))) (by rfl)

/-- The spin program (see the section header). -/
def divPS : Programm divD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf
    | true => divRumpfSpin
    | false => divRumpfNull

/-- Thread 0 spins, every other thread returns `0`. -/
def divInitS : Faden → Σ f : divD.Fn, Env divD (divD.params f)
  | 0 => ⟨divSchreib, divRho7⟩
  | _ => ⟨divLies, Env.nil⟩

/-- The start machine of the spin run. -/
def divS0 : RufMaschineG divD := RufStartG divPS divSp0 divInitS

/-- Thread 0 starts at the spin body. -/
theorem divS0_kopf : (divS0.faeden 0).kopf.rest =
    ⟨false, divD.params divSchreib, Signatur.anfang divD (divD.signatur divSchreib), divRho7,
      .ende (.cons (.forever () .tru .nil) (.ret .empty (by rfl)))⟩ := rfl

/-- The unreachable `ret` behind the spin. -/
abbrev divSpinRet : Endblock divD (vertragVon divD divSchreib) false (divD.params divSchreib)
    (Signatur.anfang divD (divD.signatur divSchreib)) := .ret .empty (by rfl)

/-- After `endeEntf`: the `forever` statement unfolded to a `dann` head. -/
def divS1 : RufMaschineG divD :=
  ⟨divS0.speicher, rufUpdateG divS0.faeden 0
    ⟨(divS0.faeden 0).stapel,
     ⟨(divS0.faeden 0).kopf.f, (divS0.faeden 0).kopf.rho, (divS0.faeden 0).kopf.s0,
      ⟨false, divD.params divSchreib, Signatur.anfang divD (divD.signatur divSchreib), divRho7,
       .dann (.cons (.forever () .tru .nil) .nil) (.ende divSpinRet)⟩⟩,
     (divS0.faeden 0).spur, (divS0.faeden 0).log⟩,
   divS0.lauf, divS0.start⟩

/-- The first G step: `endeEntf` unfolds the `forever` statement. -/
theorem divS01 : RufSchrittG divPS divO 1 divS0 0 divS1 :=
  RufSchrittG.endeEntf divS0 0 false _ _ _ (.forever () .tru .nil) divSpinRet divRho7 rfl divS0_kopf

/-- **Witness** (rule 13) for `ewig_wahr_schreitet` and `spin_prueft`: a
    REACHED G machine (two steps from `RufStartG`) whose thread 0 stands at
    `.ewig () 1 .tru .nil k`, where `KeinLogikHaltG` holds for every thread
    and thread 0 steps on. -/
theorem ewig_spin_zeuge :
    ∃ M, RufErreichbarG divPS divO 1 divS0 M ∧
      (∃ k, (M.faeden 0).kopf.rest = ⟨false, divD.params divSchreib,
        Signatur.anfang divD (divD.signatur divSchreib), divRho7,
        .ewig () 1 .tru .nil k⟩) ∧
      KeinLogikHaltG divO 1 M ∧ ∃ M', RufSchrittG divPS divO 1 M 0 M' := by
  have s2 := RufSchrittG.dannForever (P := divPS) (O := divO) (passes := 1) divS1 0 false _ _
    (Signatur.anfang divD (divD.signatur divSchreib)) _ () .tru .nil .nil (.ende divSpinRet) divRho7 rfl
  refine ⟨_, .schritt _ _ _ (.schritt _ _ _ .start divS01) s2, ⟨_, rfl⟩, ?_, ?_⟩
  · intro t
    by_cases ht : t = 0
    · subst ht
      exact spin_prueft ⟨_, _, _, _, _, _, _, Or.inl rfl⟩
    · match t, ht with
      | n + 1, _ => exact ret_prueft (e := .val (.widen (by decide) (by decide) (.lit 0))) (hΛ := by rfl) rfl
  · refine ewig_wahr_schreitet (n := 0) rfl rfl ?_
    intro L _
    show L ∈ offen (startSpur (D := divD) divSchreib)
    rw [offen_startSpur]
    exact List.mem_singleton_self _

/-! ## CUTS

  Proved (every premise used by its proof):
  * `foreverLauf_noexit` -- syntax-free fuel lemma: exit-free step + true
    guard gives `hardware (fortschritt a)` at every fuel.
  * `forever_noexit_divergiert`, `forever_noexit_kein_logik`,
    `forever_noexit_kein_zurueck` -- the `forever` divergence as declared,
    never `logik`, never a return.
  * `forever_leer_divergiert` -- the empty spin, no evidence premises.
  * `asm_never_antwort_leer`, `asm_never_kein_ok` -- the `-> never` axiom
    fits no answer and never continues.
  * `spin_prueft` -- a thread at any head of the empty true-invariant spin
    passes every clause of `PrueftG`; `ret_prueft` the same at a bare
    `return` head.
  * `ewig_wahr_schreitet` -- the `.ewig` head at budget `n + 1` takes its
    G step (one step).
  * `ewig_spin_zeuge` -- a reached G machine at the `.ewig` head with
    `KeinLogikHaltG` for every thread, and the step.
  * `bindAxiom_kein_blatt` -- discrimination only: a `bindAxiom` head is no
    leaf head (vacuous; renamed from `nieZurueck_blatt_frei`, review G10 F3).
  * `divRest_divergiert`, `divergent_body_zeuge` -- the joint witness on
    `divD`/`divP`: table written (`0 -> 100`), run reached, head at
    `forever`, axiom site admissible with empty answer class.

  NOT proved, named:
  * THAT a body's exits are absent / an invariant holds on a REAL program
    is writer's logic (`NoExit`/`InvWahr` are premises, proved here only for
    the witness shapes `.nil`/`.tru`).
  * No checker acceptance (`antwortenB`, lane 225's sentences) is claimed in
    Lean: the shapes are the model's, the acceptance is the checker's.
  * The spin facts are PER HEAD: `spin_prueft` does not show that a thread
    stays in `SpinKopf` along its steps (no inversion of `RufSchrittG`), and
    only the empty body with guard `.tru` is covered -- a `forever` with a
    real body or a real invariant is the writer's logic (`NoExit`/`InvWahr`)
    and meets `KeinLogikHaltG` through the general route, not through this
    file. `KeinLogikHaltG` is shown for ONE reached machine
    (`ewig_spin_zeuge`), not for every reachable one.
  * `divP` carries no `HeldGenau`/progress story: its run is on the F
    machine (contracts aside, as in `ReferenzB`); the G-machine witness is
    the reduced program `divPS` of §8, which writes nothing.
-/

#print axioms Gabbro.Grammatik.Zielsatz.foreverLauf_noexit
#print axioms Gabbro.Grammatik.Zielsatz.forever_noexit_divergiert
#print axioms Gabbro.Grammatik.Zielsatz.forever_noexit_kein_logik
#print axioms Gabbro.Grammatik.Zielsatz.forever_noexit_kein_zurueck
#print axioms Gabbro.Grammatik.Zielsatz.forever_leer_divergiert
#print axioms Gabbro.Grammatik.Zielsatz.asm_never_antwort_leer
#print axioms Gabbro.Grammatik.Zielsatz.asm_never_kein_ok
#print axioms Gabbro.Grammatik.Zielsatz.ewig_wahr_schreitet
#print axioms Gabbro.Grammatik.Zielsatz.bindAxiom_kein_blatt
#print axioms Gabbro.Grammatik.Zielsatz.spin_prueft
#print axioms Gabbro.Grammatik.Zielsatz.ret_prueft
#print axioms Gabbro.Grammatik.Zielsatz.ewig_spin_zeuge
#print axioms Gabbro.Grammatik.Zielsatz.divRest_divergiert
#print axioms Gabbro.Grammatik.Zielsatz.divergent_body_zeuge

end Gabbro.Grammatik.Zielsatz
