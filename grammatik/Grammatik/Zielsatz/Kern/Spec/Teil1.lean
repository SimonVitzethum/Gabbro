module
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
public import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll
public import Grammatik.Logik.Fortschritt.KostenG
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuhe
public import Grammatik.Logik.Vertraege.AntwortOrte
public import Grammatik.Speichermodell.Maschine.MaschineW
public import Grammatik.Nebenlaeufigkeit.Allgemein.FadenMaschine
public import Grammatik.Speichermodell.Maschine.GXMaschine
public import Grammatik.Logik.Fortschritt.Folge
public import Grammatik.Logik.Ruf.Maschine.BudgetMonoton
public import Grammatik.Logik.Fortschritt.PlanLauf
public import Grammatik.Logik.Fortschritt.Warten
public import Grammatik.Speichermodell.Adressen.Layout
public import Grammatik.Logik.Terminierung.LaufGX
public import Grammatik.Bausteine.Arena.Ownership.Ruhe.Lift
public import Grammatik.Bausteine.Arena.Ownership.Machine.Reach
public import Grammatik.Logik.Ruf.Schnittstellen.Vertrag
public import Grammatik.Bausteine.Arena.ArenaStaticReset
public import Grammatik.Zielsatz.Kern.Akzeptiert.Bibliothek
public import Grammatik.Bausteine.Kernzelle.Zulassung
@[expose] public section
namespace Gabbro.Grammatik.Zielsatz
open Gabbro.Grammatik
variable {D : Deklaration}
/-- A complete enumeration: every element is in the list. -/
def Aufzaehlung (α : Type) : Type := {l : List α // ∀ a, a ∈ l}
/-! ## The program the user wrote -/
/-- **The program as ONE declaration** (2026-09-15, verdict P2): the code with its contracts
    (`P`: bodies, `requires`, `ensures`, table invariants) AND what the source declares about
    its run, which before were free parameters of the statement:
    * `S` -- the lock invariants (`lock L protects { … } invariant I`);
    * `Q` -- the axioms' declared `ensures` (the content of the hardware assumption);
    * `starts` -- the declared thread starts with their arguments (`concurrent { … }`,
      `entry`/`boot` dispatch roots);
    * `sp0` -- the declared initial memory (every table and global initializer);
    * `gestartet` (NEW 2026-09-26, Opus agent A, OFFEN O21/O22) -- the roots of threads the
      program creates AT RUN TIME: every root of a hosted `start { f, g };` and every
      `child { … }` region (lifted to a function), with its arguments (`N458`: a root takes
      none, so the exporter writes `.nil`). A root here runs on any number of threads (a `start`
      in a loop, in two starters, in a pool routine), so the checker judges it as a POOL
      routine: it enters `ws` TWICE (`Einheit.ws`). Default `[]`: a unit that creates no thread
      at run time is the unit of before.
    * `arenen` (NEW 2026-10-24, review branch `review/besitz-spec`) -- the unit's arenas, each with
      the ownership interface of every function (`ArenaIface`: which parameter is handed which
      allocation, which result returns one). Default `[]`: a unit without an arena is the unit of
      before.
    * `akku` (NEW 2026-11-02, C15) -- the unit's per-core accumulators (`AccumulatorDecl`:
      core count, width, signedness, range, operator, private cells and locks, core-query and
      generated update/reduction functions). Default `[]`: a unit without an accumulator is
      the unit of before (the elaborator expands admitted `accT` declarations to guarded
      storage but refuses every use, so every elaborated unit still has `akku = []`; the
      storage is inert).
    The exporter's output is exactly one such value; a different `starts` (say `[]`) is a
    DIFFERENT program, whose run the statement then describes (`laufzeit_nur_erklaert`). -/
structure Einheit (D : Deklaration) where
  P : Programm D
  S : SperrInv D
  Q : AxEns D
  starts : List (Σ w : D.Fn, Env D (D.params w))
  sp0 : Speicher D
  gestartet : List (Σ w : D.Fn, Env D (D.params w)) := []
  arenen : List (ArenaOwnership.Body.ArenaIface D) := []
  akku : List (Kernzelle.AccumulatorDecl D) := []
/-- The thread roots the checker judges: the declared starts, and every run-time root TWICE
    (since 2026-09-26): a root the program may spawn is a pool routine (`Mehrfach`), so `einzeln`
    demands it pool-safe (the model side of `N462`/`N457`), `Getrennt` pairs it with itself and
    `Laufzeit.einmal` lets it run on any number of threads. For `gestartet = []` this is the list
    of before (`ws_ohne_gestartet`). -/
def Einheit.ws (E : Einheit D) : List D.Fn := (E.starts ++ E.gestartet ++ E.gestartet).map (·.1)
/-- **`w` is declared at least twice** (fix lane F10, 2026-09-22): two start OCCURRENCES of one
    routine, `concurrent { w, w }` -- a symmetric worker pool. The one notion of "twice" in
    this file: the checker's `einzeln` (pool safety), its thread-locality `Getrennt` (two
    occurrences are two threads) and the runtime's `Laufzeit.einmal` all read it. -/
def Mehrfach {α : Type} (ws : List α) (w : α) : Prop := List.Sublist [w, w] ws
/-! ## (a) What the checker decides -/
section Pruefer

variable [DecidableEq D.Fn]

/-- Carrier `c` is thread-local among the declared starts `ws`: no start reaches `c` in a
    footprint while a DIFFERENT start OCCURRENCE can write it (`GetrenntK` over the starts).
    Since fix lane F10 (2026-09-22) a routine declared twice (`Mehrfach`) is two threads, so
    it is paired with ITSELF too: its footprint carriers must not be written by its own graph
    unless a signature lock or a lock invariant covers them (`FussS`). On a repetition-free
    `ws` this is the old condition word for word (`Mehrfach` never holds there). -/
def Getrennt (P : Programm D) (fs ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Prop :=
  ∀ w₁ ∈ ws, ∀ w₂ ∈ ws, (w₁ ≠ w₂ ∨ Mehrfach ws w₁) → ∀ f g, reachB P fs w₁ f = true →
    c ∈ fussOrteG P f → reachB P fs w₂ g = true → TraegerSchreibt g c = false

noncomputable def lokW (P : Programm D) (fs ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Bool :=
  @decide (Getrennt P fs ws c) (Classical.propDecidable _)

/-- Carrier `c` is WRITE-separated among the declared starts `ws`: if one start's call graph
    may write `c`, no DIFFERENT start's graph may write it or have it in a footprint. -/
def SchreibGetrennt (P : Programm D) (fs ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Prop :=
  ∀ w₁ ∈ ws, ∀ w₂ ∈ ws, w₁ ≠ w₂ → ∀ g, reachB P fs w₁ g = true → TraegerSchreibt g c = true →
    ∀ h, reachB P fs w₂ h = true → TraegerSchreibt h c = false ∧ c ∉ fussOrteG P h

/-- **Pool-safe**: routine `w` may run on any number of threads. It starts
    like any admitted start (no signature-held lock, no reasons), and every
    carrier some function of the thread graph `K` may write is guarded by a
    lock or atomic. Reads need nothing for the RACE leg: with no unguarded
    writer, two threads reading one carrier do not race; the footprint leg
    (a carrier read in a footprint that the other instance may write) is
    `Getrennt`'s, which pairs a routine declared twice with itself. (Lane
    245: the model side of the narrowed `N304`.) -/
def PoolSicher (D : Deklaration) (K : D.Fn → Bool) (w : D.Fn) : Prop :=
  D.haelt w = [] ∧ D.gruende w = 0 ∧
    ∀ f, K f = true → ∀ c, TraegerSchreibt f c = true →
      (∃ L, Bewacht c L) ∨ AtomarAusgenommen c

/-- **Pool-safe at its computed graph**: `PoolSicher` with the thread
    graph `reachB P fs w`. -/
def PoolSicherW (P : Programm D) (fs : List D.Fn) (w : D.Fn) : Prop :=
  PoolSicher D (reachB P fs w) w

/-- **Duplicates allowed iff pool-safe**: every routine declared at least
    twice is pool-safe at its computed graph. `ws.Nodup` implies it
    vacuously (`einzelnPool_of_nodup`, PoolSym.lean); the symmetric pair
    `[w, w]` satisfies it exactly for pool-safe `w` (`einzelnPool_paar`).
    The checker's `N304` decides it for same-routine pairs. Since fix lane
    F10 (2026-09-22) this is the field `einzeln` of `AkzeptiertSpec`. -/
def EinzelnPool (P : Programm D) (fs : List D.Fn) (ws : List D.Fn) : Prop :=
  ∀ w, Mehrfach ws w → PoolSicherW P fs w

-- BEGIN handler discipline (Opus agent H, 2026-09-26, OFFEN O19) --
/-- The feature set "every call, every signature, and ONLY locks declared `masks irqs`": a body
    admitted by it takes no lock that leaves interrupts on. -/
def NurMaskiert (D : Deklaration) : Merkmal D :=
  ⟨fun _ => true, fun _ => true, fun L => D.maskiert L⟩

/-- **The masking discipline of an interrupt handler** (the Rust `H102`, `kontexte.rs`): every
    function of the call graph of a root `w` the program declares entered by hardware
    (`P.unterbricht w`, `entry … via idt`) takes only locks declared `masks irqs`. -/
def MaskenDisziplin [DecidableEq D.Fn] (P : Programm D) (fs : List D.Fn) : Prop :=
  ∀ w, P.unterbricht w = true → ∀ f, reachB P fs w f = true → mE (NurMaskiert D) (P.rumpf f) = true
-- END handler discipline --

/-- **What `Akzeptiert` must establish** (the Props of its components): fragment; closed call
    graphs; every footprint carrier signature-guarded, lock-protected or thread-local; lock
    floors; protected carriers guarded by their lock; declared starts hold no lock by
    signature and have no reasons, and a start declared twice is pool-safe (`EinzelnPool`,
    since fix lane F10 -- before: pairwise distinct, `ws.Nodup`); every carrier without a guard
    lock that is not `atomic` is write-separated among the declared starts (the counterpart
    of the checker's `H013`; publish payloads INCLUDED since 2026-09-15, verdict P3); no body
    calls an axiom or reads a register at a declared answer type without a value, except an
    axiom whose result is `never` (`antworten`, since 2026-09-15, W1); every function an
    interrupt handler's call graph reaches takes only locks declared `masks irqs` (`masken`,
    since 2026-09-26, Opus agent H: the Rust `H102`); every declared static array admits
    zero (`reset`, since C18: no `fnptr`/`ref`/`ptr` zero, no floats); accumulator admission is required (C15). -/
structure AkzeptiertSpec (P : Programm D) (S : SperrInv D) (fs ws : List D.Fn)\n    (A : List (Kernzelle.AccumulatorDecl D)) : Prop where
  frag : programmImFragmentG P fs = true
  abg : ∀ w, AbgK P fs (reachB P fs w)
  fuss : ∀ f, FussS P S (lokW P fs ws) f
  stufen : StufenM P
  sperrOrte : ∀ L c, c ∈ S.orte L → Bewacht c L
  wurzeln : ∀ w ∈ ws, D.haelt w = [] ∧ D.gruende w = 0
  einzeln : EinzelnPool P fs ws
  renn : ∀ c, (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c → SchreibGetrennt P fs ws c
  antworten : ∀ f, ∀ x ∈ (P.rumpf f).ants, StelleOk D x
  -- the handler discipline `H102` (Opus agent H, 2026-09-26, OFFEN O19)
  masken : MaskenDisziplin P fs
  -- checked static-array reset admission (C18): every declared static array admits zero
  reset : ∀ (g : D.Glob) (elem : Ty) (len : Nat), D.gtyp g = .arr elem len → ZeroAdmitting elem
  -- the C02 library binding (generated programs are ordinary; the content is source-level)
  bibliothek : LibraryAdmission P := trivial
  -- the accumulator admission (C15, 2026-11-02)
  akku : Kernzelle.AccumulatorAdmission P fs A

/-- **The accumulator admission added to the checker's facts**: the facts of `AkzeptiertSpec`
    that do not read the accumulators hold for every accumulator list. -/
theorem AkzeptiertSpec.mitAkku {P : Programm D} {S : SperrInv D} {fs ws : List D.Fn}
    {A A' : List (Kernzelle.AccumulatorDecl D)} (h : AkzeptiertSpec P S fs ws A)
    (ha : Kernzelle.AccumulatorAdmission P fs A') : AkzeptiertSpec P S fs ws A' :=
  { h with akku := ha }

end Pruefer

/-- **The checker interface.** `akzeptiert E fs ls cs` is the Bool the Rust checker computes
    on the program `E` (member lists of functions, locks, carriers); `korrekt` is its
    soundness, the one link between the Bool and what the statement uses. -/
structure Pruefer where
  akzeptiert : ∀ {D : Deklaration} [DecidableEq D.Fn],
    Einheit D → List D.Fn → List D.Lock → List (D.Tab ⊕ D.Glob) → Bool
  korrekt : ∀ {D : Deklaration} [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    akzeptiert E fs.1 ls.1 cs.1 = true → AkzeptiertSpec E.P E.S fs.1 E.ws E.akku

/-! ## (b) What the user proves -/

/-- Owed invariants at a REASON exit (the twin of `InvGutS`; SYNTAX.md: "owes `I` at every
    `return`"). -/
def InvGutGrund (P : Programm D) (passes : Nat) (Q : AxEns D) (S : SperrInv D) (f : D.Fn) :
    Prop :=
  ∀ O' : Orakel D, RahmenO O' → RegLokal O' → AxVertragO Q O' → ∀ U : Umwelt D, HavocOk S U →
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
      RespektiertRahmen P R → OhneVorbedingung R →
      ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ →
        ∀ (σ' : World D) (r : Fin (D.gruende f)),
          execEndH (V := vertragVon D f) S O' U passes R (P.rumpf f) σ ρ = EndAusgang.why σ' r →
            InvAmRueck P f σ'

/-- A lock invariant reads only its protected carriers (second half of `SperrInvOk`). -/
def SperrInvLokal (S : SperrInv D) : Prop :=
  ∀ L (s s' : Speicher D), (∀ c ∈ S.orte L, TraegerGleich s s' c) → S.inv L s = S.inv L s'

/-- **The logic of the bodies**: per function and at EVERY `forever` budget the body triple
    with caller duty and no `logik` outcome, owed invariants at value AND reason exits; the
    lock invariants and declared axiom ensures the user wrote read only their carriers.
    (Until 2026-09-14 this was all of `NutzerPflicht`.)
    Since C06 the interface refinement `PtrVerfeinert` is an explicit conjunct:
    every admitted target refines its pointer interface, contravariant
    requires and covariant normal ensures over arbitrary entry/current worlds. -/
def LogikPflicht (P : Programm D) (S : SperrInv D) (Q : AxEns D) : Prop :=
  (∀ (passes : Nat) (f : D.Fn),
    KoerperGutS P passes Q S f ∧ InvGutS P passes Q S f ∧ InvGutGrund P passes Q S f) ∧
  SperrInvLokal S ∧ AxEnsLokal Q ∧ PtrVerfeinert P

/-- **The start obligation** (NEW 2026-09-15, verdict P1): at the program's DECLARED initial
    memory every lock invariant holds, and every declared start's `requires` holds with its
    declared arguments. Before, these two were conditions on the quantified start
    (`StartZulaessig.sperren`/`.req`) that belonged to no premise group: an unsatisfiable
    family (`invariant false`) emptied both the body obligations (`HavocOk` had no member) and
    the conclusion (no start was admissible). Now such a family refutes (b)
    (`probeA_falsch_inv_nicht`, Zielsatz/Proben.lean). -/
structure StartPflicht (E : Einheit D) : Prop where
  sperren : ∀ L, E.S.inv L E.sp0 = true
  req : ∀ a ∈ E.starts ++ E.gestartet, ReqAmEintritt E.P a.1 (E.sp0.welt []) a.2

/-- **The user's own logic**: the bodies' logic and the start obligation, both over the
    program `E` -- nothing the prover picks. -/
structure NutzerPflicht (E : Einheit D) : Prop where
  logik : LogikPflicht E.P E.S E.Q
  start : StartPflicht E

/-! ## (c) What the hardware is assumed to do -/

def HardwareAnnahmen (O : Orakel D) (Q : AxEns D) : Prop :=
  GutO O ∧ RegLokal O ∧ AxVertragO Q O

/-! ## (d) What the runtime is assumed to do (A4) -/

/-- **Assumption A4, the loader and the runtime's thread creation.** The machine runs
    `E.P.mitRuhe` (the program with the runtime's idle root `none`, MitRuhe.lean) from
    * `lader` -- the loader establishes the program's DECLARED initial memory `E.sp0`;
    * `start` -- every thread runs the idle root or ONE declared start with its DECLARED
      arguments;
    * `einmal` -- a declared start runs on two threads only if the program declares it at
      least twice (`Mehrfach`, a worker pool; fix lane F10, 2026-09-22 -- before: never).
    The runtime starts EXACTLY the declared starts, each on its own thread, the root on every
    other thread (`initRuhe E.starts`); that start meets this predicate whenever the checker
    accepts (`laufzeit_initRuhe`, Zielsatz/Proben.lean), and so does every assignment running
    only some of the declared starts. -/
structure Laufzeit (E : Einheit D) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)) : Prop where
  lader : sp = speicherR E.sp0
  start : ∀ t, init t = ⟨none, .nil⟩ ∨ ∃ a ∈ E.starts ++ E.gestartet, init t = ⟨some a.1, envR a.2⟩
  einmal : ∀ t u, t ≠ u → (init t).1 = (init u).1 →
    (init t).1 = none ∨ ∃ w, (init t).1 = some w ∧ Mehrfach E.ws w

/-! ## The start the proof works with (derived from (b) and (d), not a premise) -/

section Start

variable [DecidableEq D.Fn]

/-- An idle start: no signature lock, no reasons, every function it reaches has an empty
    footprint and writes nothing. Any number of threads may run it. -/
def Ruhig (P : Programm D) (fs : List D.Fn) (w : D.Fn) : Prop :=
  D.haelt w = [] ∧ D.gruende w = 0 ∧ ∀ f, reachB P fs w f = true →
    fussOrteG P f = [] ∧ ∀ c, TraegerSchreibt f c = false

/-- **Admissible starts** (the proof's notion; NOT a premise of `GabbroZiel` since
    2026-09-15): every thread runs a declared start or an idle one; a start on two threads is
    idle or declared twice (`Mehrfach`, since fix lane F10); the start functions' `requires`
    and every lock invariant hold at the start memory.
    `startZulaessig_aus` (Zielsatz/Beweis.lean) derives it from (b) and (d). -/
structure StartZulaessig (P : Programm D) (S : SperrInv D) (fs ws : List D.Fn)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) : Prop where
  wurzel : ∀ t, (init t).1 ∈ ws ∨ Ruhig P fs (init t).1
  einmal : ∀ t u, t ≠ u → (init t).1 = (init u).1 → Ruhig P fs (init t).1 ∨ Mehrfach ws (init t).1
  req : StartGut P sp init
  sperren : ∀ L, S.inv L sp = true

end Start

/-! ## The legs of the goal -/

/-- **Data-race freedom on every run from `M0` to `M`**: two accesses by different threads to
    ONE carrier, one a write, the carrier not `atomic`, are ordered through a guard lock
    (release by the first, acquire by the second). Unguarded carriers included: there such a
    pair must not exist. Publish payloads included (2026-09-15, verdict P3). -/
def RennfreiBis (P : Programm D) (O : Orakel D) (passes : Nat) (M0 M : RufMaschineG D) : Prop :=
  ∀ (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat),
    LaufG P O passes M0 ms fs n → ms n = M →
    ∀ (i j : Nat) (c : D.Tab ⊕ D.Glob), i < j → j < n → fs i ≠ fs j →
      ZugriffG (ms i) (ms (i + 1)) (fs i) c → ZugriffG (ms j) (ms (j + 1)) (fs j) c →
      (SchreibG (ms i) (ms (i + 1)) (fs i) c ∨ SchreibG (ms j) (ms (j + 1)) (fs j) c) →
      ¬ AtomarAusgenommen c →
      ∃ L, Bewacht c L ∧ GeordnetG ms fs L i j

/-- At every logged REASON return, every invariant the function owes holds. -/
def InvAmGrundG (P : Programm D) (M : RufMaschineG D) : Prop :=
  ∀ (t : Faden) (ev : RufEreignisF D), ev ∈ (M.faeden t).log →
    ∀ (g : D.Fn) (rho : Env D (D.params g)) (r : Fin (D.gruende g)) (s0 s1 : World D),
      ev = RufEreignisF.why g rho r s0 s1 → InvAmRueck P g s1

/-- **The kinds of named stop** (2026-09-15, verdicts F1 and F3, finding G1). Each is a place
    where G has no rule for a thread and the statement reports it instead of claiming more:
    * `hardware` -- a hardware assumption of (c) fails at the head: an axiom (foreign code)
      answered outside its (answerable) type, a register (a device) outside its type or
      against the promise its declaration makes;
    * `nieZurueck` -- the head calls an axiom whose declared result is `never`: the call does
      not return;
    * `flagge` -- a WAIT for a publication: the head is `awaits g` and `g` is not visible;
    * `budget` -- the `forever` budget is spent: G's finite stand-in for a loop the program runs
      without end (not final: the leg `budgetUnecht`).
    An out-of-range float is NOT a stop any more: it is `Logik.bereich`, excluded by the
    user's obligation, and no reachable machine stands at one (verdict F1). -/
inductive HaltArt where
  | hardware
  | flagge
  | budget
  /-- The head is a call of an axiom whose DECLARED result is `never` -- the call does not
      return. That is the declaration's promise (the lowering marks the call `noreturn`), and
      the code after the call is unreachable in the binary as in G; the
      obligation (b) still covers everything before the call. NEW 2026-09-15 (round-5
      finding G1): before, this stop was filed as `hardware`, as if the machine had answered
      outside a type that has no inside. NARROWED 2026-09-15 (round-6 finding W1): every
      other empty answer type (`.why 0`, an empty range, a sum without a value, a pointer
      type no function has, at an axiom or a register) is refused by the checker
      (`AkzeptiertSpec.antworten`), because there the compiled call returns. -/
  | nieZurueck

/-- The first layer of the head block is a named stop of kind `k` at the world `σ`: the
    failing side conditions of `dannBlatt` (a leaf's hardware outcome), `dannBindAxiom`,
    `dannRegLies*` (`hardware` for an answerable type, since G1), an axiom `-> never`
    (`nieZurueck`, since W1 the only empty type the checker admits) and `dannAwaits`
    (`flagge`). -/
def KopfHalt (O : Orakel D) (passes : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (σ : World D) (ρ : Env D Γ) : HaltArt → Block D V l Γ Λ Λ' → Prop
  | .hardware, .cons s _ => s.istBlatt = true ∧ ∃ h, execStmt O passes keinRuf s σ ρ = .hardware h
  | .hardware, .bindAxiom a args .. =>
      (axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).2 = none ∧
      ¬ AntwortLeer D (D.aerg a)
  | .hardware, .regRead r .. =>
      (∀ v, einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) = some v → D.rzusage r v = false) ∧
      ¬ AntwortLeer D (some (D.rtyp r))
  | .hardware, .regReadElse r .. =>
      einpassen (D := D) O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) = none ∧
      ¬ AntwortLeer D (some (D.rtyp r))
  | .nieZurueck, .bindAxiom a .. => D.aerg a = some .never
  | .hardware, .bindAxiomElse a args .. =>
      (axiomAntwortSonst O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).2 = none
  | .flagge, .awaits g .. => O.sichtbar g (σ.fragt (.inr (.inr g))) = false
  | _, _ => False

/-- A residue at a named stop of kind `k`: a spent `forever` budget (`budget`), a leaf's
    hardware outcome at the end block's head (`hardware`), or its head block's first layer. -/
def RestHalt (O : Orakel D) (passes : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (σ : World D) (ρ : Env D Γ) : HaltArt → GRest D V l Γ Λ → Prop
  | .budget, .ewig _ 0 _ _ _ => True
  | .hardware, .ende (.cons s _) =>
      s.istBlatt = true ∧ ∃ h, execStmt O passes keinRuf s σ ρ = .hardware h
  | .hardware, @GRest.ende _ _ _ _ Λ (.bindAxiom a args ..) =>
      (axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).2 = none ∧
      ¬ AntwortLeer D (D.aerg a)
  | .nieZurueck, .ende (.bindAxiom a ..) => D.aerg a = some .never
  | .hardware, @GRest.ende _ _ _ _ Λ (.bindAxiomElse a args ..) =>
      (axiomAntwortSonst O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).2 = none
  | k, .dann b _ => KopfHalt O passes σ ρ k b
  | _, _ => False

/-- Thread `t` stands at a named stop of kind `k`. -/
def HaltBenannt (O : Orakel D) (passes : Nat) (M : RufMaschineG D) (k : HaltArt) (t : Faden) :
    Prop :=
  ∃ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ)
    (r : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ),
    (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, r⟩ ∧ RestHalt O passes (M.weltVon t) ρ k r

/-- **Every stop is named**: each thread is finished, waits for a lock another thread holds,
    waits for a publication, has spent its `forever` budget, stands at a hardware stop, stands
    at a call that does not return (an axiom `-> never`: G1, narrowed by W1), or can step. Nothing else: no thread ever stands at a failing `logik` check (`keinLogikHalt`) or
    at a float result outside its range. -/
def FortschrittG (P : Programm D) (O : Orakel D) (passes : Nat) (M : RufMaschineG D) : Prop :=
  ∀ t, FertigG M t ∨ WartetG M t ∨ HaltBenannt O passes M .flagge t ∨
    HaltBenannt O passes M .budget t ∨ HaltBenannt O passes M .hardware t ∨
    HaltBenannt O passes M .nieZurueck t ∨ ∃ M', RufSchrittG P O passes M t M'

/-- **No named stop inside a critical section**, of any kind (`HaltArt`): devices and axioms answer, `awaits`
    payloads become visible, the `forever` budget is not spent while a lock is held. A named assumption of the
    waiting bound (`GabbroZielWarten`). -/
def HardwareImAbschnitt {P : Programm D} {O : Orakel D} {passes : Nat} (R : PlanLauf P O passes) : Prop :=
  ∀ n u L, L ∈ offen ((R.M n).faeden u).spur → ∀ k, ¬ HaltBenannt O passes (R.M n) k u

/-- Thread `t` stands at `locks L` while thread `u` holds `L`. -/
def WartetAuf (M : RufMaschineG D) (t u : Faden) (L : D.Lock) : Prop :=
  AnSperre M t L ∧ L ∈ offen (M.faeden u).spur

/-- **No wait cycle** (verdict F2): there are no threads `t₀, …, tₙ₊₁` with `tₙ₊₁ = t₀` where
    each `tᵢ` stands at a lock that `tᵢ₊₁` holds -- whatever the OTHER threads do. (The global
    `keineVerklemmung` only rules out that EVERY unfinished thread waits.) -/
def KeinWarteZyklus (M : RufMaschineG D) : Prop :=
  ∀ (n : Nat) (ts : Nat → Faden) (Ls : Nat → D.Lock),
    (∀ i, i ≤ n → WartetAuf M (ts i) (ts (i + 1)) (Ls i)) → ts (n + 1) ≠ ts 0

/-- **The schedule of ONE core with interrupt handlers** (fix lane F11, 2026-09-22, OFFEN
    O19): the two hardware facts about `cli`/`sti` and about preemption, as conditions on a
    G run. `kern t` is the core thread `t` runs on, `H g` says `g` is an interrupt handler (in
    the leg of `Ziel`: `HandlerVon`, the roots the program declares `via idt`, since Opus agent
    H 2026-09-26).
    * ENTRY ONLY WHEN UNMASKED: a handler takes its FIRST step only where no OTHER thread of
      its core holds a lock declared `masks irqs` (`D.maskiert`). That is what masking IS:
      while such a lock is held, interrupts are off on that core, so the handler is not
      entered there.
    * RUN TO COMPLETION: from that first step until the handler is finished, no other thread
      of its core steps. That is what preemption IS on one core: the handler displaces the
      thread it interrupted, and that thread continues only afterwards.
    The run-side twin of `MaskenOrdnung` (Unterbrechung.lean), which says the same over the
    event log `Lauf`; here over the machine-G run, so that `AnSperre` can be read. -/
def KernPlan (kern : Faden → Nat) (H : Faden → Prop) (ms : Nat → RufMaschineG D)
    (fs : Nat → Faden) (n : Nat) : Prop :=
  (∀ i, i < n → H (fs i) → (∀ k, k < i → fs k ≠ fs i) →
      ∀ (f : Faden) (L : D.Lock), f ≠ fs i → kern f = kern (fs i) →
        L ∈ offen ((ms i).faeden f).spur → D.maskiert L = false) ∧
  (∀ (g : Faden) (i j k : Nat), H g → fs i = g → (∀ r, r < i → fs r ≠ g) →
      i ≤ k → k < j → j ≤ n → ¬ FertigG (ms j) g → kern (fs k) = kern g → fs k = g)

-- BEGIN handler leg (Opus agent H, 2026-09-26, OFFEN O19) --
/-- **Thread `t` is an interrupt handler of the program** (Opus agent H, 2026-09-26): its root --
    the function it started with at `M0` -- is one the program declares entered by hardware
    (`P.unterbricht`, the exported `entry … via idt`). Read off the unit, not chosen by the
    prover; the runtime's idle root is never one (`Programm.mitRuhe`). -/
def HandlerVon (P : Programm D) (M0 : RufMaschineG D) (t : Faden) : Prop :=
  P.unterbricht (M0.faeden t).kopf.f = true

/-- **No same-core interrupt deadlock** (fix lane F11, 2026-09-22; CONTENTFUL since Opus agent H,
    2026-09-26, OFFEN O19). For EVERY core assignment `kern` and every run from `M0` to `M` that
    the core hardware admits (`KernPlan`: masking and preemption as named hardware facts), a
    thread whose root the program declares an interrupt handler (`HandlerVon`) NEVER stands at a
    lock that another thread of its own core holds -- the deadlock `H102` refuses in Rust.

    Unlike the leg of F11 (`KernHaltG`, now in Zielsatz/Masken.lean), nothing of the program side
    is a hypothesis here: WHICH threads are handlers comes from the unit (`P.unterbricht`), and
    the masking discipline from (a) (`AkzeptiertSpec.masken`). The leg is FALSE for programs the
    discipline refuses (`kernHaltE_verletzt`, Zielsatz/MaskenZeuge.lean: a handler entering at an
    unmasked lock its core's thread holds), so it is not a theorem about every program: it is
    carried by (a). The one premise left inside is the hardware schedule `KernPlan`, named in the
    header. -/
def KernHaltE (P : Programm D) (O : Orakel D) (passes : Nat) (M0 M : RufMaschineG D) : Prop :=
  ∀ (kern : Faden → Nat) (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat),
    LaufG P O passes M0 ms fs n → ms n = M → KernPlan kern (HandlerVon P M0) ms fs n →
    ∀ (g f : Faden) (L : D.Lock), HandlerVon P M0 g → f ≠ g → kern f = kern g →
      AnSperre M g L → L ∉ offen ((M.faeden f).spur)
-- END handler leg --

/-- **Time**: a frame entered at `M`, of a function whose calls nest at most `n` deep, takes
    at most `kostenTief P passes (n + 1) g` own steps on every run while it is active. -/
def ZeitAb (P : Programm D) (O : Orakel D) (passes : Nat) (M : RufMaschineG D) : Prop :=
  ∀ (f : Faden) (g : D.Fn) (n : Nat) (rho : Env D (D.params g)) (s0 : World D) (k : Nat),
    rufTief P (n + 1) g = true → Eintritt P f g rho s0 k M →
    ∀ (M2 : RufMaschineG D) (run : SegLauf P O passes M M2), aktivVor f k run →
      segZaehle run f ≤ kostenTief P passes (n + 1) g

end Gabbro.Grammatik.Zielsatz
