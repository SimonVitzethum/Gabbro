module

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
public import Grammatik.Logik.Fortschritt.Halten.Pruefung
public import Grammatik.Speichermodell.Adressen.Layout
public import Grammatik.Logik.Terminierung.LaufGX
public import Grammatik.Bausteine.Arena.Ownership.Ruhe.Lift
public import Grammatik.Bausteine.Arena.Ownership.Machine.Reach
public import Grammatik.Zielsatz.Kern.Spec.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz
open Gabbro.Grammatik
variable {D : Deklaration}

/-- **THE STATEMENT OF BEFORE** (verbatim `GabbroZiel` until Opus lane O25c, 2026-09-26): the
    checker of before, (b) without the rely, `ZielF` over the thread machine over G. It is proved
    directly (`gabbro_ziel_sc`) and, on every unit without an arena, a COROLLARY of `GabbroZiel`
    (`gabbro_ziel_sc_aus`), kept as a name because the corpus theorems
    and the earlier embeddings are stated over it. Since 2026-09-26 over the THREAD MACHINE:
    every thread-machine run from the runtime's start, with any set `lebt0` of initially live
    threads -- the others are slots that `start` or `child` spawn at run time. Every G run is
    such a run (`lebt0` all live, nothing spawned: `fadenErreichbar_von_G`), so the statement of
    before that is a corollary too (`gabbro_ziel_g`). -/
def GabbroZielSC : Prop :=
  ∀ (C : Pruefer) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    C.akzeptiert E fs.1 ls.1 cs.1 = true →                     -- (a) the checker, on E
    NutzerPflicht E →                                           -- (b) the user, on E
    ∀ O : Orakel D, HardwareAnnahmen O E.Q →                    -- (c) the hardware
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit E sp init →                                      -- (d) the runtime, A4
      ∀ (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe),
        FadenErreichbar E.P.mitRuhe O.mitRuhe passes
          (FadenStart E.P.mitRuhe sp init lebt0) K →
          ZielF E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes (RufStartG E.P.mitRuhe sp init) K


/-! ## Starvation freedom (2026-10-22)

    `GabbroZiel` is a statement about every REACHED machine: safety. Whether a thread that waits for a lock ever
    gets it is a statement about infinite RUNS. It is stated here as a THIRD statement, under the same four premise
    groups, over the runs of the ticket lock (`FifoLauf`, Logik/Fortschritt/PlanLauf.lean) on which the scheduler is
    weakly fair (`Fair`). See the starvation block in the header. -/

/-- **GABBRO_ZIEL_LEBEN.** On every weakly fair run of the ticket lock from the runtime's start, a thread standing
    at `locks L` takes `L`, or some thread holds `L` from some step on for ever (a critical section of the program
    that does not end). -/
def GabbroZielLeben : Prop :=
  ∀ (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    C.akzeptiert E fs.1 ls.1 cs.1 = true →                     -- (a) the checker, on E
    NutzerPflichtA E →                                          -- (b) the user, with the rely
    ∀ O : Orakel D, HardwareAnnahmen O E.Q →                    -- (c) the hardware
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit E sp init →                                      -- (d) the runtime, A4
      ∀ R : FifoLauf E.P.mitRuhe O.mitRuhe passes,                -- the ticket lock
        R.M 0 = RufStartG E.P.mitRuhe sp init →
        Fair E.P.mitRuhe O.mitRuhe passes R.toPlanLauf →        -- the scheduler, weakly fair
        ∀ (n : Nat) (t : Faden) (L : D.mitRuhe.Lock), AnSperre (R.M n) t L →
          (∃ j, n ≤ j ∧ R.akt j = some t ∧ AnSperre (R.M j) t L) ∨
            ∃ u m, ∀ j, m ≤ j → L ∈ offen ((R.M j).faeden u).spur

/-! ## A waiting bound (2026-10-23; hold time derived 2026-11-13)

    Starvation freedom says a waiting thread gets its lock; the waiting bound says WHEN. A FIFTH statement under the
    same four premise groups, over the runs of the ticket lock, with three named premises of the run: the scheduler's
    fairness window `F` (`FairF`), no named stop inside a critical section (`HardwareImAbschnitt`) and the contenders
    (`Anwaerter`). The hold time of a critical section is no premise on the run (since 2026-11-13): it follows from
    the checker's hold bounds `N` and declared costs `decl` (`haltPasst`, K002 and K001 on the source program).
    See WAITING in the header. -/

/-- **GABBRO_ZIEL_WARTEN.** On every run of the ticket lock from the runtime's start whose scheduler has fairness
    window `F`, of a program whose every critical section of `L` the checker bounds by `N L` (`haltPasst`: in
    `kostenBlock`, calls only to functions of `ks` that fit their declared costs `decl`), without a named stop
    inside a section, and whose contenders for `L` are `Ts L`: a thread standing at `locks L` at step `n0` takes `L`
    before step `n0 + wartezeit ls Ts h h F L` with the hold time `h = haltSchranke ls N`
    (`N L + 1 + ls.length` own steps, derived by `haltezeit_aus`). Indirect calls inside
    sections and anywhere in functions of `ks` are refused by this check. Nested lock-head
    steps use the conservative bound `k = h`, not a separate acquisition count. -/
def GabbroZielWarten : Prop :=
  ∀ (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    C.akzeptiert E fs.1 ls.1 cs.1 = true →                     -- (a) the checker, on E
    NutzerPflichtA E →                                          -- (b) the user, with the rely
    ∀ O : Orakel D, HardwareAnnahmen O E.Q →                    -- (c) the hardware
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit E sp init →                                      -- (d) the runtime, A4
      ∀ (N : D.Lock → Nat) (decl : D.Fn → Nat) (ks : List D.Fn),
        haltPasst E.P passes N decl fs.1 ks = true →   -- (a') the hold bounds, K002/K001
      ∀ (R : FifoLauf E.P.mitRuhe O.mitRuhe passes) (F : Nat) (Ts : D.Lock → List Faden),
        R.M 0 = RufStartG E.P.mitRuhe sp init →
        FairF R.toPlanLauf F →                                  -- the scheduler's fairness window
        HardwareImAbschnitt R.toPlanLauf →                      -- no named stop inside a section
        Anwaerter R.toPlanLauf Ts →                             -- the contenders
        ∀ (L : D.Lock) (t : Faden) (n0 : Nat), AnSperre (R.M n0) t L →
          ∃ j, n0 ≤ j ∧
            j < n0 + wartezeit (D := D.mitRuhe) ls.1 Ts (haltSchranke ls.1 N) (haltSchranke ls.1 N) F L ∧
            R.akt j = some t ∧ L ∈ offen ((R.M (j + 1)).faeden t).spur

/-! ## Termination (2026-10-22)

    A FOURTH statement under the same four premise groups, with the measure duty beside (b). See TERMINATION in the
    header. -/

/-- **GABBRO_ZIEL_TERMINIERUNG.** Under the measure duty: on every infinite run of the thread machine over GX from
    the runtime's start (threads started, spawned and joined at run time included) every thread takes only finitely
    many steps, and a thread whose start is of class `endet` never stands at a spent
    `forever` budget. -/
def GabbroZielTerminierung : Prop :=
  ∀ (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    C.akzeptiert E fs.1 ls.1 cs.1 = true →                     -- (a) the checker, on E
    NutzerPflichtA E →                                          -- (b) the user, with the rely
    ∀ (passes : Nat) (m : Mass D),
      (∀ f, MassPflicht E.P passes E.Q E.S (GeteiltV (D := D) E.P E.ws) m (zykS E.P fs.1) f) →
                                                                -- (b') the measures fall (`decreases`)
      (∀ f g, zykS E.P fs.1 f g = true → (m f).length = (m g).length) →
    ∀ O : Orakel D, HardwareAnnahmen O E.Q →                    -- (c) the hardware
    ∀ (sp : Speicher D.mitRuhe) (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit E sp init →                                      -- (d) the runtime, A4
      ∀ (lebt0 : Faden → Bool) (R : FadenLaufX E.P.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)),
        R.K 0 = FadenStart E.P.mitRuhe sp init lebt0 →
        ∀ t : Faden, (∃ N, ∀ j, N ≤ j → R.akt j ≠ some t) ∧
          ((∀ w, (init t).1 = some w → klasse E.P fs.1 m.hat w = .endet) →
            ∀ j, ¬ HaltBenannt O.mitRuhe passes (R.K j).m .budget t)

/-! ## Linking separately compiled units (Opus agent E, 2026-09-26)

    `GabbroZiel` is about ONE `Einheit`. A program linked from two separately compiled units is
    stated here as a SECOND statement, `GabbroZielVerbund`, whose conclusion is `ZielF` on the
    LINKED unit `verbinde e E₁ E₂` and whose premises are per unit, plus the link check and the
    SAME hardware assumptions. See "WHAT CHANGED ON 2026-09-26 (OPUS AGENT E)" in the header. -/

/-- The program with the contracts of `P` and the bodies `r`. -/
def mitRumpf (P : Programm D)
    (r : ∀ f : D.Fn, Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f))) :
    Programm D :=
  { P with rumpf := r }

section Verbund

variable [DecidableEq D.Fn]

/-- **The linked program**: every function's body comes from its OWNER -- unit 1 owns `f` iff
    `e f`, unit 2 the rest -- and the contracts are the link declaration's (`Verbindbar` makes
    the two units' contracts one). -/
def verbindeP (e : D.Fn → Bool) (E₁ E₂ : Einheit D) : Programm D :=
  mitRumpf E₁.P (fun f => if e f then E₁.P.rumpf f else E₂.P.rumpf f)

/-- **The linked unit** `verbinde e E₁ E₂`: the linked program, the (shared) lock invariants,
    initial memory and axiom ensures, and BOTH units' declared starts, run-time roots,
    arenas and declared checks. A link whose checks do not compose -- a gate outside the
    linked functions, or a check name claimed by both units -- admits no
    `SchnittstelleSpec` proof: the link is refused, never silently check-free. -/
def verbinde (e : D.Fn → Bool) (E₁ E₂ : Einheit D) : Einheit D where
  P := verbindeP e E₁ E₂
  S := E₁.S
  Q := E₁.Q
  starts := E₁.starts ++ E₂.starts
  sp0 := E₁.sp0
  gestartet := E₁.gestartet ++ E₂.gestartet
  -- both units' arenas; ownership across a link is not claimed (NOT CLAIMED)
  arenen := E₁.arenen ++ E₂.arenen
  -- both units' accumulators (C15 link transport; the link check admits them)
  akku := E₁.akku ++ E₂.akku
  -- both units' declared checks; their joint admission is the link check's `pruef` field
  pruefungen := E₁.pruefungen ++ E₂.pruefungen
  grants0 := E₁.grants0 ++ E₂.grants0

/-- The OWNER's program of `f` (unit 1 iff `e f`). -/
def teilP (e : D.Fn → Bool) (E₁ E₂ : Einheit D) (f : D.Fn) : Programm D :=
  if e f then E₁.P else E₂.P

/-- **One link declaration** for both units: the two units are checked over ONE `Deklaration`
    (the union of their declarations: types, carriers, locks, signatures with their effects,
    axioms; `gabbro abi` / `--with` hand the importer only the EXPORTED part of it, and each
    Rust unit is checked over its own view, not over the union -- review E, F2), and they agree on everything that is not a
    body: every function's `requires`/`ensures` (so the importer relies on EXACTLY the
    exporter's contract; the Rust `N501`-`N503` refuse a head that differs), the existing
    pointer and axiom interface contract tables (C06), every table
    invariant, the lock invariants and the declared initial memory. The hardware assumptions
    are NOT here: `GabbroZielVerbund` names their equality as a premise of its own. -/
structure Verbindbar (E₁ E₂ : Einheit D) : Prop where
  invariante : E₁.P.invariante = E₂.P.invariante
  requires : E₁.P.requires = E₂.P.requires
  ensures : E₁.P.ensures = E₂.P.ensures
  ptrVertrag : E₁.P.ptrVertrag = E₂.P.ptrVertrag
  axVertrag : E₁.P.axVertrag = E₂.P.axVertrag
  sperren : E₁.S = E₂.S
  speicher : E₁.sp0 = E₂.sp0
  -- the dispatch facts agree, like the contracts (Opus agent H, 2026-09-26)
  unterbricht : E₁.P.unterbricht = E₂.P.unterbricht

/-- **A unit's placeholders are leaves**: every function the unit does not own (`eigen f =
    false`) calls nothing in the unit's own program. That is the `extern fn` of the importer:
    a head with the contract and the effects, and no body the checker could follow. -/
def Platzhalter (eigen : D.Fn → Bool) (P : Programm D) : Prop :=
  ∀ f g, eigen f = false → ruftB P f g = false

/-- **The COMPOSED call graph of a root `w`**, from the two units' own graphs: `h` is reached
    inside the owner of `w`, or `h` is reached inside the owner of a function `f` of the OTHER
    unit that the owner of `w` reaches (an import). The linker computes it from the units'
    summaries; no body crosses the boundary. -/
def HuelleV (fs : List D.Fn) (e : D.Fn → Bool) (E₁ E₂ : Einheit D) (w h : D.Fn) : Prop :=
  (e h = e w ∧ reachB (teilP e E₁ E₂ w) fs w h = true) ∨
  ∃ f, e f ≠ e w ∧ e h = e f ∧ reachB (teilP e E₁ E₂ w) fs w f = true ∧
    reachB (teilP e E₁ E₂ f) fs f h = true

/-- **No callback through an import**: the owner's graph of an imported function stays inside
    its owner. -/
def KeinRueckruf (fs : List D.Fn) (e : D.Fn → Bool) (E₁ E₂ : Einheit D) : Prop :=
  ∀ w f h, e f ≠ e w → reachB (teilP e E₁ E₂ w) fs w f = true →
    reachB (teilP e E₁ E₂ f) fs f h = true → e h = e f

/-- A carrier some function relies on as THREAD-LOCAL: it is in the function's footprint (or a
    register's device carriers), no signature lock guards it there, and (for the footprint) no
    lock invariant protects it -- the one case in which `FussS` asks for `lokW`. -/
def LokBedarf (e : D.Fn → Bool) (E₁ E₂ : Einheit D) (c : D.Tab ⊕ D.Glob) : Prop :=
  ∃ f, (c ∈ fussOrte (teilP e E₁ E₂ f) f ∧ sigB f c = false ∧
      ¬ ∃ L, Bewacht c L ∧ c ∈ E₁.S.orte L) ∨
    (c ∈ ((teilP e E₁ E₂ f).rumpf f).regs.flatMap D.rtraeger ∧ sigB f c = false)

/-- `Getrennt` over the COMPOSED hulls: the footprint leg of race freedom across the link. -/
def GetrenntV (fs : List D.Fn) (e : D.Fn → Bool) (E₁ E₂ : Einheit D) (ws : List D.Fn)
    (c : D.Tab ⊕ D.Glob) : Prop :=
  ∀ w₁ ∈ ws, ∀ w₂ ∈ ws, (w₁ ≠ w₂ ∨ Mehrfach ws w₁) → ∀ f g, HuelleV fs e E₁ E₂ w₁ f →
    c ∈ fussOrteG (teilP e E₁ E₂ f) f → HuelleV fs e E₁ E₂ w₂ g → TraegerSchreibt g c = false

/-- `SchreibGetrennt` over the COMPOSED hulls: the write leg of race freedom across the link. -/
def SchreibGetrenntV (fs : List D.Fn) (e : D.Fn → Bool) (E₁ E₂ : Einheit D) (ws : List D.Fn)
    (c : D.Tab ⊕ D.Glob) : Prop :=
  ∀ w₁ ∈ ws, ∀ w₂ ∈ ws, w₁ ≠ w₂ → ∀ g, HuelleV fs e E₁ E₂ w₁ g → TraegerSchreibt g c = true →
    ∀ h, HuelleV fs e E₁ E₂ w₂ h → TraegerSchreibt h c = false ∧ c ∉ fussOrteG (teilP e E₁ E₂ h) h

/-- `PoolSicher` over the COMPOSED hull of a routine declared twice. -/
def PoolSicherV (fs : List D.Fn) (e : D.Fn → Bool) (E₁ E₂ : Einheit D) (w : D.Fn) : Prop :=
  D.haelt w = [] ∧ D.gruende w = 0 ∧ ∀ f, HuelleV fs e E₁ E₂ w f → ∀ c,
    TraegerSchreibt f c = true → (∃ L, Bewacht c L) ∨ AtomarAusgenommen c

/-- **THE LINK CHECK** (decided exactly by `schnittstelleB`, Zielsatz/Verbund.lean). The
    interface of a unit carries its call graphs and its per-function footprints and writes (the
    effects of an exported head); the check composes them:
    * `blatt₁`, `blatt₂` -- each unit's placeholders for the other's functions are leaves;
    * `keinRueckruf` -- an imported function's graph stays in its owner;
    * `lok` -- every carrier some function relies on as thread-local IS thread-local among the
      linked unit's thread roots, over the composed hulls (footprints compose);
    * `renn` -- every unguarded, non-atomic carrier is write-separated over the composed hulls;
    * `einzeln` -- a routine declared twice in the linked unit is pool-safe over its composed
      hull (a routine both units start counts twice);
    * `masken` (Opus agent H, 2026-09-26) -- every function the composed hull of an interrupt
      handler reaches takes only locks declared `masks irqs` (`H102` across the link).
    * `pruef` (C16, 2026-11-02) -- the declared checks of BOTH units, admitted over the
      linked program: cross-unit gates consume across the boundary, names are disjoint.
    Every per-body component of `AkzeptiertSpec` (fragment, closed graphs, lock floors, lock
    invariant places, roots, answer sites) is each unit's own verdict; these five are the
    whole-program components, and they are the ones the link re-decides. -/
structure SchnittstelleSpec (fs : List D.Fn) (e : D.Fn → Bool) (E₁ E₂ : Einheit D) : Prop where
  blatt₁ : Platzhalter e E₁.P
  blatt₂ : Platzhalter (fun f => !e f) E₂.P
  keinRueckruf : KeinRueckruf fs e E₁ E₂
  lok : ∀ c, LokBedarf e E₁ E₂ c → GetrenntV fs e E₁ E₂ (verbinde e E₁ E₂).ws c
  renn : ∀ c, (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c →
    SchreibGetrenntV fs e E₁ E₂ (verbinde e E₁ E₂).ws c
  einzeln : ∀ w, Mehrfach (verbinde e E₁ E₂).ws w → PoolSicherV fs e E₁ E₂ w
  -- an interrupt handler's COMPOSED hull takes only masked locks (Opus agent H, 2026-09-26)
  masken : ∀ w, E₁.P.unterbricht w = true → ∀ h, HuelleV fs e E₁ E₂ w h →
    mE (NurMaskiert D) ((teilP e E₁ E₂ h).rumpf h) = true
  -- the linked accumulators, over the linked program (C15 link transport)
  akku : Kernzelle.AccumulatorAdmission (verbinde e E₁ E₂).P fs (verbinde e E₁ E₂).akku
  -- the declared checks of BOTH units, admitted over the linked program (C16, 2026-11-02):
  -- every gate of every carried check is a linked function (cross-unit gates consume
  -- across the boundary) and no check name is claimed twice. Without this proof the
  -- link is refused: `verbinde` carries the checks, never drops them.
  pruef : CheckAdmission (verbindeP e E₁ E₂) fs (E₁.pruefungen ++ E₂.pruefungen)

/-- **The user's logic of ONE unit** (the part of (b) a separately compiled unit owes): the
    bodies it OWNS at every budget, its lock and axiom families read only their carriers, and
    its start obligation. Each conforming target it owns also refines its pointer
    interface (C06). A placeholder owes nothing -- its owner supplies both proofs. -/
structure NutzerTeil (eigen : D.Fn → Bool) (E : Einheit D) : Prop where
  logik : (∀ (passes : Nat) (f : D.Fn), eigen f = true →
      KoerperGutS E.P passes E.Q E.S f ∧ InvGutS E.P passes E.Q E.S f ∧
        InvGutGrund E.P passes E.Q E.S f) ∧
    SperrInvLokal E.S ∧ AxEnsLokal E.Q ∧
      ∀ f, eigen f = true → ∀ n (hf : D.passt f n = true), PtrZielVerfeinert E.P f n hf
  start : StartPflicht E

/-- **The user's logic of ONE unit, with the atomic rely** (the rely over the unit's own shared
    atomics), including C06 target refinement only for its own functions. -/
structure NutzerTeilA [DecidableEq D.Fn] (eigen : D.Fn → Bool) (E : Einheit D) : Prop where
  logik : (∀ (passes : Nat) (f : D.Fn), eigen f = true →
      KoerperGutSA E.P passes E.Q E.S (GeteiltA E.P E.ws) f ∧
        InvGutSA E.P passes E.Q E.S (GeteiltA E.P E.ws) f ∧
        InvGutGrundA E.P passes E.Q E.S (GeteiltA E.P E.ws) f) ∧
    SperrInvLokal E.S ∧ AxEnsLokal E.Q ∧
      ∀ f, eigen f = true → ∀ n (hf : D.passt f n = true), PtrZielVerfeinert E.P f n hf
  start : StartPflicht E

end Verbund

/-- **GABBRO_ZIEL FOR LINKED UNITS** (2026-09-26, Opus agent E). Two units `E₁`, `E₂` over one
    link declaration, unit 1 owning the functions where `e` holds:
    (a) each unit is accepted by the checker ALONE, and the link check holds;
    (b) each unit's user proves the logic of the bodies IT owns, and its start;
    (c) the hardware meets the assumptions, and they are the SAME for both units
        (`E₂.Q = E₁.Q`: one oracle answers both units' axioms);
    (d) the runtime starts the LINKED unit.
    Then every leg of `ZielFX` holds on every reachable thread machine over GX of the linked
    program -- race freedom and lock discipline ACROSS the units, spawned threads and the
    weak-memory leg included, since the conclusion is `GabbroZiel`'s own. Since Opus lane O25c
    (2026-09-26) WITH THE ATOMIC RELY: (a) a checker for the rely on each unit, (b) each unit's
    logic with the rely over its own shared atomics (`NutzerTeilA`). The link check is
    unchanged: its `lok` demands every footprint carrier a function relies on without a lock
    thread-local over the composed hulls, atomics included, so the linked program has no
    admitted shared atomic (named in NOT CLAIMED). The statement of before is
    `GabbroZielVerbundSC`, a corollary (`gabbro_ziel_verbund_sc_aus`). -/
def GabbroZielVerbund : Prop :=
  ∀ (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (E₁ E₂ : Einheit D) (e : D.Fn → Bool)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    C.akzeptiert E₁ fs.1 ls.1 cs.1 = true →                    -- (a) unit 1, alone
    C.akzeptiert E₂ fs.1 ls.1 cs.1 = true →                    -- (a) unit 2, alone
    Verbindbar E₁ E₂ →                                          -- (a) one link declaration
    SchnittstelleSpec fs.1 e E₁ E₂ →                            -- (a) the link check
    NutzerTeilA e E₁ →                                          -- (b) unit 1's user, rely
    NutzerTeilA (fun f => !e f) E₂ →                            -- (b) unit 2's user, rely
    E₂.Q = E₁.Q →                                               -- (c) the SAME hardware assumptions
    ∀ O : Orakel D, HardwareAnnahmen O E₁.Q →                   -- (c) the hardware
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit (verbinde e E₁ E₂) sp init →                     -- (d) the runtime, linked
      ∀ (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe),
        FadenErreichbarX (verbinde e E₁ E₂).P.mitRuhe O.mitRuhe passes
          (GeteiltV (D := D) (verbinde e E₁ E₂).P (verbinde e E₁ E₂).ws)
          (FadenStart (verbinde e E₁ E₂).P.mitRuhe sp init lebt0) K →
          ZielFX (verbinde e E₁ E₂).P.mitRuhe (verbinde e E₁ E₂).S.mitRuhe O.mitRuhe passes
            (GeteiltV (D := D) (verbinde e E₁ E₂).P (verbinde e E₁ E₂).ws)
            (RufStartG (verbinde e E₁ E₂).P.mitRuhe sp init) [] K

/-- **THE LINKED STATEMENT OF BEFORE** (verbatim `GabbroZielVerbund` until Opus lane O25c): a
    corollary of `GabbroZielVerbund` (`gabbro_ziel_verbund_sc_aus`). -/
def GabbroZielVerbundSC : Prop :=
  ∀ (C : Pruefer) (D : Deklaration) [DecidableEq D.Fn] (E₁ E₂ : Einheit D) (e : D.Fn → Bool)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    C.akzeptiert E₁ fs.1 ls.1 cs.1 = true →                    -- (a) unit 1, alone
    C.akzeptiert E₂ fs.1 ls.1 cs.1 = true →                    -- (a) unit 2, alone
    Verbindbar E₁ E₂ →                                          -- (a) one link declaration
    SchnittstelleSpec fs.1 e E₁ E₂ →                            -- (a) the link check
    NutzerTeil e E₁ →                                           -- (b) unit 1's user
    NutzerTeil (fun f => !e f) E₂ →                             -- (b) unit 2's user
    E₂.Q = E₁.Q →                                               -- (c) the SAME hardware assumptions
    ∀ O : Orakel D, HardwareAnnahmen O E₁.Q →                   -- (c) the hardware
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit (verbinde e E₁ E₂) sp init →                     -- (d) the runtime, linked
      ∀ (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe),
        FadenErreichbar (verbinde e E₁ E₂).P.mitRuhe O.mitRuhe passes
          (FadenStart (verbinde e E₁ E₂).P.mitRuhe sp init lebt0) K →
          ZielF (verbinde e E₁ E₂).P.mitRuhe (verbinde e E₁ E₂).S.mitRuhe O.mitRuhe passes
            (RufStartG (verbinde e E₁ E₂).P.mitRuhe sp init) K

end Gabbro.Grammatik.Zielsatz
