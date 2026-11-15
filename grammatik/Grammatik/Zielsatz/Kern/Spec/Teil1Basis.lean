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
public import Grammatik.Logik.Vertraege.Locations.AntwortOrte
public import Grammatik.Speichermodell.Maschine.MaschineW
public import Grammatik.Nebenlaeufigkeit.Allgemein.Threads.FadenMaschine
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
public import NativeFloat.Hardware
public import Grammatik.Bausteine.Arena.ArenaStaticReset
public import Grammatik.Zielsatz.Kern.Akzeptiert.Bibliothek
public import Grammatik.Bausteine.Kernzelle.Zulassung
public import Grammatik.Kern.Syntax.Satz.Pruefung
public import Grammatik.Zielsatz.Kern.Akzeptiert.CheckDecide
public import Grammatik.Logik.Ruf.FremdRuf.T4
public import Grammatik.Zielsatz.Kern.Schnittstellen

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
  /-- The unit's declared checks (C16): kernel descriptors of every `check` item,
      elaborated by the exporter (`UCheck.probe` names the generated producer).
      Default `[]`: a unit without a check is the unit of before. -/
  pruefungen : List (CheckDecl D) := []
  /-- The source-declared initial grant inventory (C08): the external world's live
      grants at the start, proved by `GrantsStart`, not assumed empty. Default `[]`:
      a unit with no provider is the unit of before. -/
  grants0 : List (BoundaryRecord D) := []
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
structure AkzeptiertSpec (P : Programm D) (S : SperrInv D) (fs ws : List D.Fn)
    (A : List (Kernzelle.AccumulatorDecl D)) : Prop where
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
  -- the interface resolution (C08): every referenced foreign item agrees with its
  -- canonical signature (decided by `schnittstellenB`, exactly by `schnittstellenB_iff`)
  schnittstellen : SchnittstellenOk P fs
  -- checked static-array reset admission (C18): every declared static array admits zero
  reset : ∀ (g : D.Glob) (elem : Ty) (len : Nat), D.gtyp g = .arr elem len → ZeroAdmitting elem
  -- the C02 library binding (generated programs are ordinary; the content is source-level)
  bibliothek : LibraryAdmission P := trivial
  -- the accumulator admission (C15, 2026-11-02)
  akku : Kernzelle.AccumulatorAdmission P fs A
  -- C16: a Prop stores the admitted list existentially, never as a data projection.
  -- The concrete checker still checks E.pruefungen; this interface forgets its identity.
  pruef : ∃ checks : List (CheckDecl D), CheckAdmission P fs checks
/-- **The accumulator admission added to the checker's facts**: the facts of `AkzeptiertSpec`
    that do not read the accumulators hold for every accumulator list. -/
theorem AkzeptiertSpec.mitAkku {P : Programm D} {S : SperrInv D} {fs ws : List D.Fn}
    {A A' : List (Kernzelle.AccumulatorDecl D)} (h : AkzeptiertSpec P S fs ws A)
    (ha : Kernzelle.AccumulatorAdmission P fs A') : AkzeptiertSpec P S fs ws A' :=
  { h with akku := ha }
end Pruefer
/-- **The checker interface.** `akzeptiert E fs ls cs` is the Bool the Rust checker computes
    on the program `E` (member lists of functions, locks, carriers); `korrekt` is its
    soundness under the supplied ISA-neutral CPU contract; the Bool itself
    takes no hardware certificate. -/
structure Pruefer where
  akzeptiert : ∀ {D : Deklaration} [DecidableEq D.Fn],
    Einheit D → List D.Fn → List D.Lock → List (D.Tab ⊕ D.Glob) → Bool
  korrekt : ∀ {D : Deklaration} [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob))
    (hardware : RootNativeFloat.Hardware),
    akzeptiert E fs.1 ls.1 cs.1 = true → AkzeptiertSpec E.P E.S fs.1 E.ws E.akku
end Gabbro.Grammatik.Zielsatz
