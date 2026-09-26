/-
  File:      Grammatik/CloneHandoff.lean
  Subject:   THE CHECKED CLONE HANDOFF, MODEL SIDE (lane O-1, K-1; fix lane F9).

  K-1 measured the gap: a `syscall` gate can declare the raw clone call,
  but "the child starts on the handed stack and must never return into the
  caller's frame" had no checked shape. The Rust half is the `stack` clause
  plus the `child` statement (`clone.rs`, N446-N452, and fix lane F3's
  N456/N457); this file is the model half. It is STANDALONE: `Spec.lean`,
  `Syntax.lean` and machine G are not touched, and `gabbro_ziel` is unchanged.

  * §1-§3 `CloneAbi` -- a `SysAbi` plus the handed-stack register, with
    well-formedness `CloneAbi.good`, its decider and a good/bad witness pair
    (O-1 commit `2244babf`, unchanged).
  * §4-§5 THE CHILD AS A THREAD (fix lane F9, review G11 F1). A clone
    machine is a machine-G state plus the set of live threads; a dormant slot
    sits at its child entry until a live parent spawns it, then steps by
    machine G's own rules. Laws: every clone run is a G run
    (`klonErreichbar_G`), a dormant slot is untouched
    (`klon_schlafend_unberuehrt`), a dormant child with no signature lock
    holds nothing and never blocks (`klon_kind_haelt_nichts`,
    `klon_frei_nur_lebende`: the model side of `N456`).
  * §6 `ChildNoReturn`/`CloneHandoff` -- now over threads that really start
    at a child entry.
  * §7 `klon_ziel` -- every leg of `Ziel` on every clone run, when the unit
    that lists the child entry as a declared start is accepted (the model
    side of `N457`: the child is judged like a start).
  * §8-§9 witnesses: `beispiele/124` with `hauptB` spawned by `hauptA`
    (`k124_klon_ziel`, all premise groups discharged), and a run on the
    machine-G witness program where the child sleeps through a parent step,
    is spawned, and takes three steps including a write (`kw_lauf`,
    `kw_nicht_degeneriert`, `kw_handoff`).

  WHY NOT IN THE GOAL. The O-1 branch (`cde18e25`) added `Laufzeit.klon` (d)
  and a premise `CloneAssume` (d2) to `GabbroZiel`. Review G11 F1 showed (d2)
  was vacuous: (d) kept every thread off the gate entries, so no thread the
  premise talks about existed. Fix lane F9 did NOT take that Spec diff (a
  decorative premise is worse than none) and puts the child in a model of
  its own instead; §7 is how the goal reaches it. See the CUTS at the end.
-/
import Grammatik.Syscall
import Grammatik.RufMaschineG
import Grammatik.Korpus124

namespace Gabbro.Grammatik

/-! ## 1. The handoff shape: `CloneAbi` -/

/-- `CloneAbi`: a `SysAbi` plus the handed-stack register named by the
    `stack` clause. The number, the map and the table stay in the user
    declaration (beispiele/155); only the SHAPE travels here. -/
structure CloneAbi where
  /-- The gate's machine side (number, input map, output register, clobbers). -/
  abi : SysAbi
  /-- The handed-stack register: the `stack` clause names it AS a stack. -/
  stack : SysReg
  deriving DecidableEq, Repr

/-- Well-formedness: the base map is well-formed, the handed register is
    bound in `regs in`, and it is neither the answer register nor scratch.
    The Rust side decides the same four (`N446` in `clone.rs`). -/
def CloneAbi.good (a : CloneAbi) : Prop :=
  a.abi.gut ∧ a.stack ∈ a.abi.ein.map Prod.fst ∧ a.stack ≠ a.abi.aus ∧
    a.stack ∉ a.abi.clobber

/-- Decision procedure for `CloneAbi.good`. -/
def cloneAbiGoodB (a : CloneAbi) : Bool :=
  sysAbiGutB a.abi && decide (a.stack ∈ a.abi.ein.map Prod.fst) &&
    decide (a.stack ≠ a.abi.aus) && !decide (a.stack ∈ a.abi.clobber)

/-- Soundness: a positive decision means well-formedness. -/
theorem cloneAbiGoodB_sound (a : CloneAbi) (h : cloneAbiGoodB a = true) :
    a.good := by
  unfold cloneAbiGoodB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hGut, hBound⟩, hOut⟩, hClob⟩ := h
  exact ⟨sysAbiGutB_sound a.abi hGut, of_decide_eq_true hBound,
    of_decide_eq_true hOut, by simpa using hClob⟩

/-! ## 2. The handoff legs at declaration level -/

instance : Decidable (CloneAbi.good a) :=
  inferInstanceAs (Decidable
    (a.abi.gut ∧ a.stack ∈ a.abi.ein.map Prod.fst ∧ a.stack ≠ a.abi.aus ∧
      a.stack ∉ a.abi.clobber))

/-- The handed register is bound: first projection of `good`. -/
theorem cloneStack_bound (a : CloneAbi) (h : a.good) :
    a.stack ∈ a.abi.ein.map Prod.fst := h.2.1

/-- The handed register is not the answer register: second projection. -/
theorem cloneStack_notOut (a : CloneAbi) (h : a.good) : a.stack ≠ a.abi.aus :=
  h.2.2.1

/-- The handed register is no scratch register: third projection. -/
theorem cloneStack_notClobber (a : CloneAbi) (h : a.good) :
    a.stack ∉ a.abi.clobber := h.2.2.2

/-! ## 3. Witnesses: one good gate, one bad gate -/

/-- The witness map: two parameters in `rdi`/`rsi`, answers in `rax`,
    clobbers `rcx`/`r11`. -/
def cloneWitnessAbi : SysAbi :=
  { nummer := 1000
    ein := [(.rdi, 0), (.rsi, 1)]
    aus := .rax
    clobber := [.rcx, .r11] }

/-- The witness gate: the map above, handing `rsi`. `1000` is NOT an OS
    number -- the shape is gate-agnostic (beispiele/155 carries a user
    number of its own); any number instantiates it, and this one is chosen
    to be no dispatched call the tree knows. -/
def cloneWitness : CloneAbi :=
  { abi := cloneWitnessAbi
    stack := .rsi }

/-- The witness is well-formed, by computation. -/
theorem cloneWitness_good : cloneWitness.good := by decide

/-- The decider agrees, by computation. -/
theorem cloneWitness_goodB : cloneAbiGoodB cloneWitness = true := by decide

/-- Soundness, jointly instantiated: the decider's `true` delivers `good`
    on the witness table. -/
theorem cloneWitness_sound : cloneWitness.good :=
  cloneAbiGoodB_sound cloneWitness cloneWitness_goodB

/-- The handed register of the witness is bound (first leg, exercised). -/
theorem cloneWitness_stackBound : cloneWitness.stack ∈ cloneWitness.abi.ein.map Prod.fst :=
  cloneStack_bound cloneWitness cloneWitness_good

/-- The planted defect, red direction: handing the ANSWER register (`rax`)
    is no handoff. -/
def cloneBadWitness : CloneAbi :=
  { abi := cloneWitness.abi, stack := .rax }

/-- The defect fails, by computation. -/
theorem cloneBadWitness_fails : ¬ cloneBadWitness.good := by decide

#print axioms Gabbro.Grammatik.cloneAbiGoodB_sound
#print axioms Gabbro.Grammatik.cloneStack_bound
#print axioms Gabbro.Grammatik.cloneStack_notOut
#print axioms Gabbro.Grammatik.cloneStack_notClobber
#print axioms Gabbro.Grammatik.cloneWitness_good
#print axioms Gabbro.Grammatik.cloneWitness_goodB
#print axioms Gabbro.Grammatik.cloneWitness_sound
#print axioms Gabbro.Grammatik.cloneWitness_stackBound
#print axioms Gabbro.Grammatik.cloneBadWitness_fails


/-! ## 4. The child as a thread: dormant slots and the spawn rule

  Fix lane F9 (review G11 F1). The O-1 branch put the run-level duty on a
  population that could not occur: under its (d) no thread ever started at a
  gate entry, so its (d2) was empty. Here the child IS a thread of machine G.
  A clone machine is a G machine plus the set of LIVE threads; a thread that
  is not live is a dormant child slot. It sits, unmoved, at the entry frame of
  its child function until a live thread (its parent) spawns it; from then on
  it steps by machine G's own rules, interleaved with the parent and every
  other live thread. No new G rule: the step relation of machine G is used
  unchanged, and the spawn only switches a slot on.

  WHAT THE SPAWN RULE OVER-APPROXIMATES. A spawn may fire at ANY point of a
  live parent's run, not only right after a stack-gate call (G has no event
  for an axiom call to key it to). Every real spawn time is therefore among
  the modelled ones, and so is every interleaving after it. What it does NOT
  capture: the child's arguments and entry world are fixed at the start
  machine (the real child gets the gate's answer, the handed values and the
  world at the gate), and each slot is spawned at most once (a gate that runs
  again would need a fresh slot; nothing here bounds how often).
-/

variable {D : Deklaration}

/-- A clone machine: a G machine and the live threads. `lebt t = false` is a
    dormant child slot. -/
structure KlonMaschine (D : Deklaration) where
  /-- The machine G state, every slot included. -/
  m : RufMaschineG D
  /-- Which threads are live. -/
  lebt : Faden → Bool

/-- One step of the clone machine: a LIVE thread takes a machine-G step, or a
    live thread spawns a dormant slot. The spawn changes nothing but liveness:
    the child starts in the frame it was placed in, with its OWN trace -- none
    of the parent's held locks travels with it (the model side of `N456`). -/
inductive KlonSchritt (P : Programm D) (O : Orakel D) (passes : Nat) :
    KlonMaschine D → KlonMaschine D → Prop where
  | lauf (K : KlonMaschine D) (f : Faden) (M' : RufMaschineG D)
      (hf : K.lebt f = true) (hs : RufSchrittG P O passes K.m f M') :
      KlonSchritt P O passes K ⟨M', K.lebt⟩
  | spawn (K : KlonMaschine D) (p c : Faden)
      (hp : K.lebt p = true) (hc : K.lebt c = false) :
      KlonSchritt P O passes K ⟨K.m, fun t => if t = c then true else K.lebt t⟩

/-- Reachable clone machines. -/
inductive KlonErreichbar (P : Programm D) (O : Orakel D) (passes : Nat)
    (K0 : KlonMaschine D) : KlonMaschine D → Prop where
  | start : KlonErreichbar P O passes K0 K0
  | schritt (K K' : KlonMaschine D) (h : KlonErreichbar P O passes K0 K)
      (hs : KlonSchritt P O passes K K') : KlonErreichbar P O passes K0 K'

/-- The start of the clone machine: machine G's start with the children
    placed at their entries, and the slots `lebt0` names dormant. -/
def KlonStart (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (lebt0 : Faden → Bool) :
    KlonMaschine D :=
  ⟨RufStartG P sp init, lebt0⟩

/-! ## 5. The laws of the clone machine -/

/-- **Every clone run is a machine-G run** from the start with the children
    placed at their entries: a spawn does not move the G state, and a live
    step is a G step. This is the bridge: whatever holds on every G run from
    that start holds on every clone run. -/
theorem klonErreichbar_G {P : Programm D} {O : Orakel D} {passes : Nat}
    {K0 K : KlonMaschine D} (h : KlonErreichbar P O passes K0 K) :
    RufErreichbarG P O passes K0.m K.m := by
  induction h with
  | start => exact RufErreichbarG.start
  | schritt K K' _ hs ih =>
      cases hs with
      | lauf f M' _ hs' => exact RufErreichbarG.schritt _ _ f ih hs'
      | spawn => exact ih

/-- **A dormant slot is untouched**: on every clone run from the start, a
    thread that is still dormant is exactly its start-machine state -- its
    entry frame, its start trace, its entry log. -/
theorem klon_schlafend_unberuehrt {P : Programm D} {O : Orakel D} {passes : Nat}
    {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    {lebt0 : Faden → Bool} {K : KlonMaschine D}
    (h : KlonErreichbar P O passes (KlonStart P sp init lebt0) K) (t : Faden)
    (ht : K.lebt t = false) : K.m.faeden t = (RufStartG P sp init).faeden t := by
  induction h with
  | start => rfl
  | schritt K K' _ hs ih =>
      cases hs with
      | lauf f M' hf hs' =>
          have hne : t ≠ f := by
            intro e; subst e; simp_all
          rw [rufSchrittG_passt_anders P O passes K.m M' f t hne hs']
          exact ih ht
      | spawn p c hp hc =>
          by_cases e : t = c
          · subst e; simp at ht
          · simp only [e] at ht
            exact ih ht

/-- Liveness only grows: a thread live once stays live. -/
theorem klon_lebt_bleibt {P : Programm D} {O : Orakel D} {passes : Nat}
    {K0 K : KlonMaschine D} (h : KlonErreichbar P O passes K0 K) (t : Faden)
    (ht : K0.lebt t = true) : K.lebt t = true := by
  induction h with
  | start => exact ht
  | schritt K K' _ hs ih =>
      cases hs with
      | lauf => exact ih
      | spawn p c _ _ =>
          show (if t = c then true else K.lebt t) = true
          split <;> simp_all

/-- **A dormant child holds no lock** (the model side of `N456`): if the
    child function holds nothing by signature, then as long as the slot is
    dormant its held set is empty -- whatever its parent holds. So at the
    spawn the child starts with an EMPTY held set, not the parent's. -/
theorem klon_kind_haelt_nichts {P : Programm D} {O : Orakel D} {passes : Nat}
    {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    {lebt0 : Faden → Bool} {K : KlonMaschine D}
    (h : KlonErreichbar P O passes (KlonStart P sp init lebt0) K) (t : Faden)
    (ht : K.lebt t = false) (hsig : D.haelt (init t).1 = []) (L : D.Lock) :
    L ∉ offen (K.m.faeden t).spur := by
  rw [klon_schlafend_unberuehrt h t ht]
  have hsp : ((RufStartG P sp init).faeden t).spur = startSpur (init t).1 := by
    simp only [RufStartG]
  rw [hsp, offen_startSpur, hsig]
  simp

/-- **A dormant child never blocks** a lock: the scheduler side condition
    `RufFreiG` for any thread reads the live threads only. -/
theorem klon_frei_nur_lebende {P : Programm D} {O : Orakel D} {passes : Nat}
    {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    {lebt0 : Faden → Bool} {K : KlonMaschine D}
    (h : KlonErreichbar P O passes (KlonStart P sp init lebt0) K)
    (hsig : ∀ t, K.lebt t = false → D.haelt (init t).1 = [])
    (f : Faden) (L : D.Lock) :
    RufFreiG K.m f L ↔ ∀ g, g ≠ f → K.lebt g = true → L ∉ offen (K.m.faeden g).spur := by
  constructor
  · intro hfr g hg _
    exact hfr g hg
  · intro hl g hg
    cases hlg : K.lebt g with
    | true => exact hl g hg hlg
    | false => exact klon_kind_haelt_nichts h g hlg (hsig g hlg) L

/-! ## 6. The handoff on a run with a child -/

/-- The log holds a return of `e`: the G reading of "returns". A `grund`
    (reason return) is no value return into the caller frame. -/
def isEntryReturn (D : Deklaration) (e : D.Fn) : RufEreignisF D → Prop
  | .rueck f _ _ _ _ => f = e
  | .eintritt _ _ _ => False
  | .grund _ _ _ _ _ => False

/-- A child thread never returns from its entry: no `.rueck entry` in its
    log. Returns of SUBFUNCTIONS inside the child are fine -- only the
    ENTRY's return would land in the caller's frame. -/
def ChildNoReturn (D : Deklaration) (M : RufMaschineG D) (child : Faden)
    (entry : D.Fn) : Prop :=
  ∀ ev ∈ (M.faeden child).log, ¬ isEntryReturn D entry ev

/-- The handoff on one machine pair: every thread the start machine places
    at a child entry never logs its entry's return. Unlike the O-1 branch,
    the clone machine DOES place threads at child entries (the dormant
    slots), so this is a statement about real threads. -/
def CloneHandoff (D : Deklaration) (entries : List D.Fn)
    (M0 M : RufMaschineG D) : Prop :=
  ∀ (t : Faden) (e : D.Fn), e ∈ entries →
    (M0.faeden t).kopf.f = e → ChildNoReturn D M t e

/-- No entries, no duty. -/
theorem cloneHandoff_empty (M0 M : RufMaschineG D) :
    CloneHandoff D [] M0 M := by
  intro t e he _
  exact absurd he (by simp)

/-- A dormant child has logged nothing but its entry: the handoff holds at
    every dormant slot of every clone run, for every entry list. -/
theorem cloneHandoff_schlafend {P : Programm D} {O : Orakel D} {passes : Nat}
    {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    {lebt0 : Faden → Bool} {K : KlonMaschine D}
    (h : KlonErreichbar P O passes (KlonStart P sp init lebt0) K) (t : Faden)
    (ht : K.lebt t = false) (e : D.Fn) : ChildNoReturn D K.m t e := by
  intro ev hev hret
  rw [klon_schlafend_unberuehrt h t ht] at hev
  have hlog : ev = RufEreignisF.eintritt (init t).1 (init t).2 (sp.welt []) := by
    simpa [RufStartG] using hev
  rw [hlog] at hret
  simp [isEntryReturn] at hret

/-! ## 7. The goal theorem on clone runs -/

/-- **Every leg of `Ziel` on every clone run** -- provided the unit that
    lists each child entry as a DECLARED START is accepted and meets (b), (c)
    and (d). The child is then judged by the checker like any start (race
    freedom over the starts, `Getrennt`/`SchreibGetrennt`, the lock order,
    contracts, time); Rust's `N457` is the checker's local approximation of
    exactly that ("the region is judged like a pool routine"). The start
    machine of the clone run is machine G's start from the runtime `init`;
    which slots are dormant (`lebt0`) is free. -/
theorem klon_ziel (C : Zielsatz.Pruefer) (D : Deklaration) [DecidableEq D.Fn]
    (E : Zielsatz.Einheit D) (fs : Zielsatz.Aufzaehlung D.Fn)
    (ls : Zielsatz.Aufzaehlung D.Lock) (cs : Zielsatz.Aufzaehlung (D.Tab ⊕ D.Glob))
    (hC : C.akzeptiert E fs.1 ls.1 cs.1 = true) (hN : Zielsatz.NutzerPflicht E)
    (O : Orakel D) (hH : Zielsatz.HardwareAnnahmen O E.Q) (passes : Nat)
    (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f))
    (hL : Zielsatz.Laufzeit E sp init) (lebt0 : Faden → Bool)
    (K : KlonMaschine D.mitRuhe)
    (hK : KlonErreichbar E.P.mitRuhe O.mitRuhe passes
      (KlonStart E.P.mitRuhe sp init lebt0) K) :
    Zielsatz.Ziel E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes
      (RufStartG E.P.mitRuhe sp init) K.m :=
  Zielsatz.gabbro_ziel_g C D E fs ls cs hC hN O hH passes sp init hL K.m
    (klonErreichbar_G hK)

#print axioms Gabbro.Grammatik.klonErreichbar_G
#print axioms Gabbro.Grammatik.klon_schlafend_unberuehrt
#print axioms Gabbro.Grammatik.klon_lebt_bleibt
#print axioms Gabbro.Grammatik.klon_kind_haelt_nichts
#print axioms Gabbro.Grammatik.klon_frei_nur_lebende
#print axioms Gabbro.Grammatik.cloneHandoff_empty
#print axioms Gabbro.Grammatik.cloneHandoff_schlafend
#print axioms Gabbro.Grammatik.klon_ziel


/-! ## 8. Witness of the bridge: `beispiele/124` with `hauptB` as the child

  The accepted unit `kE` (Korpus124.lean) declares the starts `hauptA` and
  `hauptB`. The runtime places them on threads 0 and 1 (`initRuhe`). Here
  thread 1 is a DORMANT child: `hauptB` does not run until `hauptA` spawns it.
  `hauptB` holds no lock by signature, the declaration has a lock (`L`, which
  `hauptA` and `hauptB` both take inside `locks L`), so the empty held set at
  the spawn is a fact about a lock that exists. -/

/-- Thread 1 is dormant at the start, every other thread is live. -/
def k124Lebt0 : Faden → Bool := fun t => t != 1

/-- The clone start of `beispiele/124`: the runtime start, `hauptB` dormant. -/
def k124K0 : KlonMaschine K124.kD.mitRuhe :=
  KlonStart K124.kE.P.mitRuhe (speicherR K124.kE.sp0) (initRuhe K124.kE.starts) k124Lebt0

/-- The dormant slot is the child `hauptB`, and it holds nothing by signature. -/
theorem k124_kind : (initRuhe K124.kE.starts 1).1 = some K124.kHauptB ∧
    K124.kD.mitRuhe.haelt (initRuhe K124.kE.starts 1).1 = [] ∧
    K124.kD.mitRuhe.haelt (initRuhe K124.kE.starts 0).1 = [] ∧
    k124K0.lebt 1 = false ∧ k124K0.lebt 0 = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The state right after `hauptA` spawns `hauptB`. -/
def k124K1 : KlonMaschine K124.kD.mitRuhe :=
  ⟨k124K0.m, fun t => if t = 1 then true else k124K0.lebt t⟩

/-- The spawn is a clone step: live parent 0, dormant child 1. -/
theorem k124_spawn (O : Orakel K124.kD.mitRuhe) (passes : Nat) :
    KlonErreichbar K124.kE.P.mitRuhe O passes k124K0 k124K1 :=
  KlonErreichbar.schritt _ _ KlonErreichbar.start (KlonSchritt.spawn _ 0 1 rfl rfl)

/-- Before the spawn the child holds no lock (`klon_kind_haelt_nichts`,
    instantiated on every clone run of 124 while slot 1 sleeps). -/
theorem k124_kind_haelt_nichts (O : Orakel K124.kD.mitRuhe) (passes : Nat)
    (K : KlonMaschine K124.kD.mitRuhe)
    (hK : KlonErreichbar K124.kE.P.mitRuhe O passes k124K0 K)
    (ht : K.lebt 1 = false) (L : K124.kD.mitRuhe.Lock) :
    L ∉ offen (K.m.faeden 1).spur :=
  klon_kind_haelt_nichts hK 1 ht k124_kind.2.1 L

/-- **The bridge on `beispiele/124`**: every clone run in which `hauptA`
    spawns `hauptB` satisfies every leg of `Ziel` -- `klon_ziel` with the
    concrete checker and every premise group discharged. -/
theorem k124_klon_ziel (O : Orakel K124.kD)
    (hO : Zielsatz.HardwareAnnahmen O K124.kE.Q) (passes : Nat)
    (K : KlonMaschine K124.kD.mitRuhe)
    (hK : KlonErreichbar K124.kE.P.mitRuhe O.mitRuhe passes k124K0 K) :
    Zielsatz.Ziel K124.kE.P.mitRuhe K124.kE.S.mitRuhe O.mitRuhe passes
      (RufStartG K124.kE.P.mitRuhe (speicherR K124.kE.sp0) (initRuhe K124.kE.starts)) K.m :=
  klon_ziel akzeptiert_pruefer K124.kD K124.kE ⟨K124.kFs, K124.kFs_voll⟩
    ⟨[()], K124.kLocks_voll⟩ ⟨K124.kCs, K124.kCs_voll⟩ K124.kE_akzeptiert
    K124.kE_nutzerPflicht O hO passes _ _ (laufzeit_initRuhe K124.kE)
    k124Lebt0 K hK

/-- Joint instantiation: the machine right after the spawn, on the oracle of
    124, meets `Ziel` -- the child is live there. -/
theorem k124_klon_ziel_spawn (passes : Nat) :
    k124K1.lebt 1 = true ∧
    Zielsatz.Ziel K124.kE.P.mitRuhe K124.kE.S.mitRuhe K124.kO.mitRuhe passes
      (RufStartG K124.kE.P.mitRuhe (speicherR K124.kE.sp0) (initRuhe K124.kE.starts))
      k124K1.m :=
  ⟨rfl, k124_klon_ziel K124.kO K124.kO_hw passes k124K1 (k124_spawn _ passes)⟩

#print axioms Gabbro.Grammatik.k124_kind
#print axioms Gabbro.Grammatik.k124_spawn
#print axioms Gabbro.Grammatik.k124_kind_haelt_nichts
#print axioms Gabbro.Grammatik.k124_klon_ziel
#print axioms Gabbro.Grammatik.k124_klon_ziel_spawn


/-! ## 9. Witness of a run: the child is spawned, then steps and writes

  Over the machine-G witness program `gP` (RufMaschineG.lean §7): thread 0 is
  the parent (`false`, the caller: it calls `true`), thread 1 is the child at
  the entry `true` (the `if` whose taken branch writes slot 0 := 2), dormant
  at the start. The run: the parent takes its call step while the child
  sleeps; the parent spawns the child; the child unfolds its `if`, takes the
  branch and WRITES -- three child steps interleaved after a parent step. -/

/-- The start assignment: the child entry `true` on thread 1, the caller on
    every other thread. -/
def klonInitW : Faden → Σ f : rufDF.Fn, Env rufDF (rufDF.params f) :=
  fun t => if t = 1 then ⟨rufIncF, rufRhoF⟩ else ⟨rufCallerF, rhoCallerF⟩

/-- Only thread 1 is dormant. -/
def klonLebtW : Faden → Bool := fun t => t != 1

/-- The start machine. -/
def kwM0 : RufMaschineG rufDF := RufStartG gP spF klonInitW

theorem kwM0_kopf0 :
    (kwM0.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufCallerF,
     Signatur.anfang rufDF (rufDF.signatur rufCallerF),
     rhoCallerF, .ende rufCallerRumpfF⟩ := rfl

theorem kwM0_kopf1 :
    (kwM0.faeden 1).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF),
     rufRhoF, .ende (.cons iteG restF)⟩ := rfl

/-- The parent after its call step (thread 0), the child untouched. -/
def kwM1 : RufMaschineG rufDF :=
  ⟨kwM0.speicher,
   rufUpdateG kwM0.faeden 0
     ⟨callerFrameG :: (kwM0.faeden 0).stapel,
      ⟨rufIncF, rufRhoF, kwM0.weltVon 0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF),
        rufRhoF, .ende (gP.rumpf rufIncF)⟩⟩,
      (kwM0.weltVon 0).spur,
      (RufEreignisF.eintritt rufIncF rufRhoF (kwM0.weltVon 0)) ::
        (kwM0.faeden 0).log⟩,
   kwM0.lauf ++ rufEigenG 0 [],
   kwM0.start⟩

theorem kwSchritt1 : RufSchrittG gP rufOF 0 kwM0 0 kwM1 := by
  have hhead : (kwM0.faeden 0).kopf.rest =
      ⟨false, rufDF.params rufCallerF, [],
       rhoCallerF,
       .ende (.cons (.call rufIncF rufArgsF rufHpF rfl)
         ((rufDF_params rufCallerF).symm ▸
           (.ret (.wert ((.weiter (by decide) (by decide) (.var .hier) :
             Expr rufDF (rufDF.params rufIncF) [] (.int 0 6)))) (by decide)) :
           Endblock rufDF (vertragVon rufDF rufCallerF) false
             (rufDF.params rufIncF) (nach rufDF rufIncF [])))⟩ := by
    rw [kwM0_kopf0]
    rfl
  have hΛ : HeldIn ([] : List (Res rufDF)) (offen (kwM0.faeden 0).spur) :=
    (heldLeerF _).heldIn
  have hs0 : kwM0.weltVon 0 =
      (kwM0.weltVon 0).lese [] (Args.orte rufArgsF) := by
    rw [argsOrteF]
    rfl
  have hrho : rufRhoF = evalArgs (kwM0.weltVon 0) rufArgsF
      (kwM0.weltVon 0) rhoCallerF := by
    have hw : kwM0.weltVon 0 = spF.welt [] := rfl
    rw [hw]
    rfl
  have hneu : (kwM0.weltVon 0).spur = [] ++ (kwM0.faeden 0).spur := rfl
  exact RufSchrittG.ruf kwM0 0 false (rufDF.params rufCallerF) [] rufIncF
    rufArgsF rufHpF rfl _ rhoCallerF hhead hΛ _ hs0 _ hrho _ hneu

/-- The child after unfolding its `if` (thread 1). -/
def kwM2 : RufMaschineG rufDF :=
  ⟨kwM1.speicher,
   rufUpdateG kwM1.faeden 1
     ⟨(kwM1.faeden 1).stapel,
      ⟨(kwM1.faeden 1).kopf.f, (kwM1.faeden 1).kopf.rho, (kwM1.faeden 1).kopf.s0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
        .dann (.cons iteG .nil) (.ende restF)⟩⟩,
      (kwM1.faeden 1).spur, (kwM1.faeden 1).log⟩,
   kwM1.lauf, kwM1.start⟩

theorem kwSchritt2 : RufSchrittG gP rufOF 0 kwM1 1 kwM2 :=
  RufSchrittG.endeEntf kwM1 1 false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    iteG restF rufRhoF iteG_entf rfl

/-- The child after taking the branch. -/
def kwM3 : RufMaschineG rufDF :=
  ⟨kwM2.speicher,
   rufUpdateG kwM2.faeden 1
     ⟨(kwM2.faeden 1).stapel,
      ⟨(kwM2.faeden 1).kopf.f, (kwM2.faeden 1).kopf.rho, (kwM2.faeden 1).kopf.s0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
        .dann (.cons leafSF .nil) (.dann .nil (.ende restF))⟩⟩,
      (kwM2.weltVon 1).spur, (kwM2.faeden 1).log⟩,
   kwM2.lauf ++ rufEigenG 1 [],
   kwM2.start⟩

theorem kwSchritt3 : RufSchrittG gP rufOF 0 kwM2 1 kwM3 := by
  have hhead : (kwM2.faeden 1).kopf.rest =
      ⟨false, rufDF.params rufIncF,
       Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
       .dann (.cons (.ite cG thenG elseG) .nil) (.ende restF)⟩ := rfl
  have hs₁ : kwM2.weltVon 1 =
      (kwM2.weltVon 1).lese
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) cG.orte := by
    rw [cG_orte]
    rfl
  have hw : wahr? (eval (kwM2.weltVon 1) cG (kwM2.weltVon 1) rufRhoF) = true :=
    rfl
  have hneu : (kwM2.weltVon 1).spur = [] ++ (kwM2.faeden 1).spur := rfl
  exact RufSchrittG.dannIteWahr kwM2 1 false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    cG thenG elseG .nil (.ende restF) rufRhoF hhead _ hs₁ hw _ hneu (heldGenau_rufDF _ _)

/-- The child after its WRITE: memory moved to `outWF`. -/
def kwM4 : RufMaschineG rufDF :=
  ⟨outWF.speicher,
   rufUpdateG kwM3.faeden 1
     ⟨(kwM3.faeden 1).stapel,
      ⟨(kwM3.faeden 1).kopf.f, (kwM3.faeden 1).kopf.rho, (kwM3.faeden 1).kopf.s0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
        .dann .nil (.dann .nil (.ende restF))⟩⟩,
      outWF.spur, (kwM3.faeden 1).log⟩,
   kwM3.lauf ++ rufEigenG 1 outWF.spur,
   kwM3.start⟩

theorem kwM3_welt : kwM3.weltVon 1 = spF.welt [] := rfl

theorem kwSchritt4 : RufSchrittG gP rufOF 0 kwM3 1 kwM4 := by
  have hhead : (kwM3.faeden 1).kopf.rest =
      ⟨false, rufDF.params rufIncF,
       Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
       .dann (.cons leafSF .nil) (.dann .nil (.ende restF))⟩ := rfl
  have hΛ : HeldIn (Signatur.anfang rufDF (rufDF.signatur rufIncF))
      (offen (kwM3.faeden 1).spur) :=
    (heldLeerF _).heldIn
  have hstep : (execStmt rufOF 0 (R := keinRuf)
      (V := vertragVon rufDF (kwM3.faeden 1).kopf.f)
      leafSF (kwM3.weltVon 1) rufRhoF) =
      Ausgang.ok (D := rufDF) (V := vertragVon rufDF (kwM3.faeden 1).kopf.f)
        outWF rufRhoF := by
    rw [kwM3_welt]
    exact leafSF_ok
  have hneu : outWF.spur = outWF.spur ++ (kwM3.faeden 1).spur := by
    have hspur : (kwM3.faeden 1).spur = [] := rfl
    rw [hspur, List.append_nil]
  have hkein : ∀ (L : rufDF.Lock) (h : List rufDF.Lock),
      Ereignis.nimmt L h ∉ (outWF.spur : List (Ereignis rufDF)) := by
    intro L h _
    exact nomatch L
  exact RufSchrittG.dannBlatt kwM3 1 false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    leafSF .nil (.dann .nil (.ende restF)) rufRhoF leafSF_blatt hhead hΛ
    outWF rufRhoF outWF.spur hstep hneu hkein

/-- The clone states of the run. -/
def kwK0 : KlonMaschine rufDF := KlonStart gP spF klonInitW klonLebtW
def kwK1 : KlonMaschine rufDF := ⟨kwM1, klonLebtW⟩
def kwLebtAlle : Faden → Bool := fun t => if t = 1 then true else klonLebtW t
def kwK2 : KlonMaschine rufDF := ⟨kwM1, kwLebtAlle⟩
def kwK3 : KlonMaschine rufDF := ⟨kwM2, kwLebtAlle⟩
def kwK4 : KlonMaschine rufDF := ⟨kwM3, kwLebtAlle⟩
def kwK5 : KlonMaschine rufDF := ⟨kwM4, kwLebtAlle⟩

/-- **The run**: parent call (child asleep), spawn, three child steps. -/
theorem kw_lauf : KlonErreichbar gP rufOF 0 kwK0 kwK5 := by
  have r1 : KlonErreichbar gP rufOF 0 kwK0 kwK1 :=
    .schritt _ _ .start (KlonSchritt.lauf kwK0 0 kwM1 rfl kwSchritt1)
  have r2 : KlonErreichbar gP rufOF 0 kwK0 kwK2 :=
    .schritt _ _ r1 (KlonSchritt.spawn kwK1 0 1 rfl rfl)
  have r3 : KlonErreichbar gP rufOF 0 kwK0 kwK3 :=
    .schritt _ _ r2 (KlonSchritt.lauf kwK2 1 kwM2 rfl kwSchritt2)
  have r4 : KlonErreichbar gP rufOF 0 kwK0 kwK4 :=
    .schritt _ _ r3 (KlonSchritt.lauf kwK3 1 kwM3 rfl kwSchritt3)
  exact .schritt _ _ r4 (KlonSchritt.lauf kwK4 1 kwM4 rfl kwSchritt4)

/-- **The run is not degenerate.** The child slot starts dormant at the entry
    `true` and ends live; while it slept the parent stepped (it is inside its
    call, one frame deep); the child's own trace carries the write event and
    memory slot 0 moved from 0 to 2 -- a write by the child, not by the
    parent (the parent's trace is still empty). -/
theorem kw_nicht_degeneriert :
    kwK0.lebt 1 = false ∧ kwK5.lebt 1 = true ∧
    (kwM0.faeden 1).kopf.f = rufIncF ∧
    (kwM4.faeden 0).stapel.length = 1 ∧ (kwM4.faeden 0).kopf.f = rufIncF ∧
    (kwM4.faeden 1).spur = outWF.spur ∧ outWF.spur ≠ [] ∧
    (kwM4.faeden 0).spur = [] ∧
    kwM4.speicher.slots () 0 () = (⟨2, by decide, by decide⟩ : Wert rufDF (.int 0 5)) ∧
    kwM0.speicher.slots () 0 () = (⟨0, by decide, by decide⟩ : Wert rufDF (.int 0 5)) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
  intro h
  have : outWF.spur.length = 0 := by rw [h]; rfl
  simp [outWF, World.schreibSlot, World.lese, World.merke] at this

/-- The handoff holds on this run for the entry `true`, and it is not empty:
    thread 1 starts AT the entry (`kw_nicht_degeneriert`) and has stepped. -/
theorem kw_handoff : CloneHandoff rufDF [rufIncF] kwM0 kwM4 := by
  intro t e he ht ev hev hret
  simp only [List.mem_singleton] at he
  subst he
  by_cases h1 : t = 1
  · subst h1
    have hlog : (kwM4.faeden 1).log = [RufEreignisF.eintritt rufIncF rufRhoF (spF.welt [])] := rfl
    rw [hlog] at hev
    simp only [List.mem_singleton] at hev
    subst hev
    simp [isEntryReturn] at hret
  · exfalso
    have h0 : (kwM0.faeden t).kopf.f = rufCallerF := by
      simp [kwM0, RufStartG, klonInitW, h1]
    rw [h0] at ht
    exact absurd ht (by decide)

#print axioms Gabbro.Grammatik.kwSchritt1
#print axioms Gabbro.Grammatik.kwSchritt2
#print axioms Gabbro.Grammatik.kwSchritt3
#print axioms Gabbro.Grammatik.kwSchritt4
#print axioms Gabbro.Grammatik.kw_lauf
#print axioms Gabbro.Grammatik.kw_nicht_degeneriert
#print axioms Gabbro.Grammatik.kw_handoff

/- CUTS: what is not proved or not modelled (SATZKARTE §39, OFFEN O21).
   UPDATE 2026-09-26 (Opus agent A): `GabbroZiel` now runs over the THREAD machine
   (FadenMaschine.lean), of which this clone machine is a special case (`klon_als_faden`,
   Zielsatz/FaedenZeuge.lean): a clone spawn is a `kind` step, and the run-time root is listed
   in `Einheit.gestartet` (judged as a pool routine) instead of as a declared start. The first
   cut below is therefore history; the argument/entry-world cut and the stack cut stand, and
   the one-spawn-per-slot cut is gone (the unit may place any number of slots at a root).
   - (history) `GabbroZiel` has no child: its thread population is fixed at the start
     (`Laufzeit.start`: root or a declared start). A spawned child reaches
     `Ziel` only through `klon_ziel`, i.e. when the unit lists the child
     entry as a DECLARED START and that unit is accepted. The exporter
     refuses `child` (`LG004`), so no exported unit is in that shape yet, and
     nothing checks that Rust's `N457` (the region judged like a pool routine)
     implies the Lean checker accepts the unit with the child as a start --
     the correspondence is stated, not proved.
   - The spawn over-approximates the time (any point of a live parent's run)
     but NOT the data: the child's arguments and its entry world `s0` are
     fixed at the start machine; the real child gets the gate's answer, the
     handed values and the world at the gate. So the child's entry world
     (what `old`-style contract reads of its entry frame see) is the start
     world, and the `requires` of the child entry is (b)'s start duty at the
     START world, not at the spawn world.
   - One spawn per slot: a gate that runs repeatedly spawns unboundedly many
     children; the model has finitely many dormant slots, each spawned once
     (Rust's `N457` is fail-safe for exactly this reason).
   - `ChildNoReturn` is shown on dormant slots (`cloneHandoff_schlafend`)
     and on the witness run (`kw_handoff`), not on every run: an entry that
     calls itself recursively logs a `rueck` of the entry inside the child.
     The C-level half -- the stub never executes `ret` on the handed stack,
     the child is entered BY JUMP at the region (PLAN-SYSCALL) -- is the
     lowering's duty (lane 258, `C185` until then) and translation
     validation's, not this file's.
   - The handed STACK has no G counterpart (G is address-free).
-/

end Gabbro.Grammatik
