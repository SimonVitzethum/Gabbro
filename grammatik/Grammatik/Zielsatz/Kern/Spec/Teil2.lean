module

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
public import Grammatik.Zielsatz.Kern.Spec.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz
open Gabbro.Grammatik
variable {D : Deklaration}

-- BEGIN weak-memory definition (Opus agent B, 2026-09-26) --
/-- **The weak machine adds no behaviour at `M`** (Opus agent B, 2026-09-26). For EVERY
    assignment `ord` of memory orders to the atomics, every weak state `W` over `M` (`W.g = M`)
    that machine W reaches from the weak start over `M0` (`RufStartW`: every carrier one
    message, every view empty), and every step W takes from there: it is a step of G from `M`
    to the successor's G-part. Machine W (Speichermodell/MaschineW.lean) lets a thread read
    ANY message of a carrier at or above its view -- relaxed, release/acquire and lock views --
    so this is the DRF theorem for the program: on it the weak memory reads only the newest
    write. -/
def SchwachSC (P : Programm D) (O : Orakel D) (passes : Nat) (M0 M : RufMaschineG D) : Prop :=
  ∀ (ord : D.Glob → Speichermodell.Ordnung) (W W' : RufMaschineW D) (u : Faden),
    RufErreichbarW P O passes ord (RufStartW M0) W → W.g = M →
    RufSchrittW P O passes ord W u W' → RufSchrittG P O passes M u W'.g
-- END weak-memory definition --

-- BEGIN invariant definitions (Opus agent D, 2026-09-26) --
/-- **The table/group invariant `i` reads only its declared carriers**: every carrier its
    predicate reads is one of `D.traeger i`. (`invSicht` only asks that a read carrier's GUARDS
    be among those of the declared carriers; a predicate reading another table under the same
    lock, or an unguarded table, reads carriers that functions NOT owing `i` may write.) -/
def InvTraeger (P : Programm D) (i : D.Inv) : Prop :=
  ∀ c ∈ (P.invariante i).orte, ∃ t ∈ D.traeger i, c = Sum.inl t

/-- **The invariant `i` is CLOSED at `M`**: no unfinished thread has a frame -- the head or a
    suspended caller -- of a function that owes `i` (`schuldet`: its effects write a carrier of
    `i`). A finished thread (empty stack, head at its return) is not asked: it moves nothing
    any more, and its start function's owed invariants hold where it stopped (`StartEndeG`). -/
def InvZu (M : RufMaschineG D) (i : D.Inv) : Prop :=
  ∀ t, ¬ FertigG M t → ∀ F ∈ (M.faeden t).kopf :: (M.faeden t).stapel, schuldet F.f i = false

/-- **Table and group invariants wherever no writer is running** (Opus agent D, 2026-09-26).
    Every invariant that reads only its carriers and held in the start memory holds in the
    shared memory of `M` whenever it is CLOSED there (`InvZu`). In particular at every function
    ENTRY reached while no unfinished thread is inside a writer of it, and at every machine of
    a program none of whose running functions writes it. The start memory is the leg's own
    hypothesis: (b) does not demand table invariants at `E.sp0`, and demanding them would drop
    programs the statement covered before. -/
def InvRuheG (P : Programm D) (M0 M : RufMaschineG D) : Prop :=
  ∀ i ∈ D.invs, InvTraeger P i → InvHaelt P i (M0.speicher.welt []) → InvZu M i →
    InvHaelt P i (M.speicher.welt [])

/-- **What a thread holding an invariant's guard observes** (Opus agent D, 2026-09-26): a
    thread `t` that holds a guard lock of a carrier of `i` and has no frame inside a writer of
    `i` sees `i` intact in shared memory -- whatever the other threads do. -/
def InvSichtG (P : Programm D) (M0 M : RufMaschineG D) : Prop :=
  ∀ i ∈ D.invs, InvTraeger P i → InvHaelt P i (M0.speicher.welt []) → ∀ t,
    (∀ F ∈ (M.faeden t).kopf :: (M.faeden t).stapel, schuldet F.f i = false) →
    (∃ tb ∈ D.traeger i, ∃ L, Sum.inl L ∈ D.braucht tb ∧ L ∈ offen (M.faeden t).spur) →
    InvHaelt P i (M.speicher.welt [])

/-- **Lock invariants at every lock move** (Opus agent D, 2026-09-26): every step from `M` that
    ACQUIRES `L` starts from a memory where `L`'s invariant holds and leaves one where it holds
    (the section begins with the invariant); every step that RELEASES `L` leaves a memory where
    it holds. -/
def SperrWechselG (P : Programm D) (O : Orakel D) (passes : Nat) (S : SperrInv D)
    (M : RufMaschineG D) : Prop :=
  ∀ (u : Faden) (M' : RufMaschineG D) (L : D.Lock), RufSchrittG P O passes M u M' →
    (L ∉ offen (M.faeden u).spur → L ∈ offen (M'.faeden u).spur →
      S.inv L M.speicher = true ∧ S.inv L M'.speicher = true) ∧
    (L ∈ offen (M.faeden u).spur → L ∉ offen (M'.faeden u).spur → S.inv L M'.speicher = true)

/-- **A held lock's invariant is observed by its holder alone** (Opus agent D, 2026-09-26).
    For every step from `M` and every carrier `c` protected by `L`: the step accesses `c` (a
    recorded read or write, or a change of `c`) only if its thread holds `L`; and while a thread
    holds `L`, no other thread's step changes `c`. So the holder may break the invariant inside
    its section, and no other thread can observe that: every observation of `c` lies inside an
    `L`-section of the observer, which began at an acquire where the invariant held
    (`SperrWechselG`) and in which only the observer moved `c`. -/
def SperrSichtG (P : Programm D) (O : Orakel D) (passes : Nat) (S : SperrInv D)
    (M : RufMaschineG D) : Prop :=
  ∀ (u : Faden) (M' : RufMaschineG D), RufSchrittG P O passes M u M' →
    ∀ (L : D.Lock) (c : D.Tab ⊕ D.Glob), c ∈ S.orte L →
      (ZugriffG M M' u c → L ∈ offen (M.faeden u).spur) ∧
      (∀ t, t ≠ u → L ∈ offen (M.faeden t).spur → TraegerGleich M'.speicher M.speicher c)
-- END invariant definitions --

/-- **THE GOAL at a reached machine `M` of a run from `M0`**: the four legs, nothing else.
    (Since Opus agent G, 2026-09-26, a fifth group: the order of effects in the call log,
    `folge`, OFFEN O1.)
    (Since Opus agent D, 2026-09-26, the contract leg names invariants beyond the returns:
    `invRuhe`, `invSicht`, `sperrWechsel`, `sperrSicht`.) -/
structure Ziel (P : Programm D) (S : SperrInv D) (O : Orakel D) (passes : Nat)
    (M0 M : RufMaschineG D) : Prop where
  -- memory safety (typing and in-range: intrinsic in `Programm D`)
  speicherSicher : SpurInv M
  -- data-race freedom
  rennfrei : RennfreiBis P O passes M0 M
  -- the weak memory adds no behaviour (DRF theorem; weak-memory hunk, Opus agent B 2026-09-26)
  schwach : SchwachSC P O passes M0 M
  -- contracts where claimed
  vertrag : VertragAmOrtG P M
  sperrInv : SperrInvG S M
  invRueck : InvAmOrtG P M
  invGrund : InvAmGrundG P M
  -- invariants beyond the returns (Opus agent D, 2026-09-26)
  invRuhe : InvRuheG P M0 M
  invSicht : InvSichtG P M0 M
  sperrWechsel : SperrWechselG P O passes S M
  sperrSicht : SperrSichtG P O passes S M
  startEnde : StartEndeG P M
  keinStartGrund : KeinStartGrundG M
  keinLogikHalt : KeinLogikHaltG O passes M
  -- progress
  keineVerklemmung : (∀ t, ¬ FertigG M t → WartetG M t) → ∀ t, FertigG M t
  keinZyklus : KeinWarteZyklus M
  keinKernHalt : KernHaltE P O passes M0 M
  fortschritt : FortschrittG P O passes M
  -- time
  zeit : ZeitAb P O passes M
  -- the order of effects (Opus agent G, 2026-09-26, OFFEN O1: L50, L52)
  folge : FolgeG P M

/-! ## Threads created at run time (2026-09-26, OFFEN O21/O22) -/

/-- Starter `t` waits for a root that has not finished (a JOIN wait). -/
def JoinWartet (K : FadenMaschine D) (t : Faden) : Prop :=
  ∃ u ∈ K.wartet t, ¬ FertigG K.m u

/-- **Thread `t` waits for thread `u`** on a thread machine: `t` joins nothing and stands at a
    lock `u` holds (`WartetAuf`), or `t` joins the unfinished root `u`. -/
def WartetF (K : FadenMaschine D) (t u : Faden) : Prop :=
  (K.wartet t = [] ∧ ∃ L, WartetAuf K.m t u L) ∨ (u ∈ K.wartet t ∧ ¬ FertigG K.m u)

/-- **No wait cycle, join waits included**: no threads `t₀ … tₙ₊₁ = t₀` each waiting for the
    next, by a lock or by a join -- whatever the other threads do. -/
def KeinWarteZyklusF (K : FadenMaschine D) : Prop :=
  ∀ (n : Nat) (ts : Nat → Faden), (∀ i, i ≤ n → WartetF K (ts i) (ts (i + 1))) → ts (n + 1) ≠ ts 0

/-- **Every stop is named, on the thread machine**: each thread is dormant (not spawned yet), or
    it is a starter that waits for an unfinished root or can end its join, or it joins nothing and
    is finished, waits for a lock, stands at a named stop, or takes a G step the thread machine
    admits. -/
def FortschrittF (P : Programm D) (O : Orakel D) (passes : Nat) (K : FadenMaschine D) : Prop :=
  ∀ t, K.lebt t = false ∨
    (K.wartet t ≠ [] ∧ (JoinWartet K t ∨
      ∃ K', FadenSchritt P O passes K K' ∧ K'.m = K.m ∧ K'.wartet t = [])) ∨
    (K.wartet t = [] ∧ (FertigG K.m t ∨ WartetG K.m t ∨ HaltBenannt O passes K.m .flagge t ∨
      HaltBenannt O passes K.m .budget t ∨ HaltBenannt O passes K.m .hardware t ∨
      HaltBenannt O passes K.m .nieZurueck t ∨
      ∃ M', RufSchrittG P O passes K.m t M' ∧
        FadenSchritt P O passes K ⟨M', K.lebt, K.wartet, K.rang, K.uhr⟩))

/-- **THE GOAL on a thread machine `K` reached from the start machine `M0`** (since 2026-09-26):
    every leg of `Ziel` on its G state -- which contains every spawned thread, as a G thread --
    and the legs the thread machine adds:
    * `schlafendUnberuehrt`, `schlafendFrei` -- a not-yet-spawned thread is its start thread,
      and holds no lock: a spawned thread ENTERS HOLDING NOTHING (the model side of `N456`);
    * `joinFrei` -- a starter that waits for its roots holds no lock (the side of `N461`);
    * `keineVerklemmung` -- if every live unfinished thread waits (for a lock, or for a root),
      every live thread is finished: no global deadlock, join waits included;
    * `keinZyklus` -- no wait cycle through locks AND joins;
    * `fortschritt` -- every stop is named (`FortschrittF`);
    * `spawnSicht` (Opus agent D, 2026-09-26) -- a step that makes a dormant slot live leaves
      the G state alone, and there the spawned thread holds no lock, every free lock has its
      invariant and every closed table invariant holds: its entry sees the invariants. -/
structure ZielF (P : Programm D) (S : SperrInv D) (O : Orakel D) (passes : Nat)
    (M0 : RufMaschineG D) (K : FadenMaschine D) : Prop where
  g : Ziel P S O passes M0 K.m
  schlafendUnberuehrt : ∀ t, K.lebt t = false → K.m.faeden t = M0.faeden t
  schlafendFrei : ∀ t, K.lebt t = false → ∀ L, L ∉ offen (K.m.faeden t).spur
  joinFrei : ∀ t, K.wartet t ≠ [] → ∀ L, L ∉ offen (K.m.faeden t).spur
  keineVerklemmung : (∀ t, K.lebt t = true → ¬ FertigG K.m t →
      (K.wartet t = [] ∧ WartetG K.m t) ∨ JoinWartet K t) →
    ∀ t, K.lebt t = true → FertigG K.m t
  keinZyklus : KeinWarteZyklusF K
  fortschritt : FortschrittF P O passes K
  -- a spawned thread's entry sees the invariants (Opus agent D, 2026-09-26)
  spawnSicht : ∀ (K' : FadenMaschine D) (t : Faden), FadenSchritt P O passes K K' →
    K.lebt t = false → K'.lebt t = true →
      K'.m = K.m ∧ (∀ L, L ∉ offen (K'.m.faeden t).spur) ∧ SperrInvG S K'.m ∧
        InvRuheG P M0 K'.m

-- BEGIN atomic-rely definitions (Opus lane O25c, 2026-09-26) --
/-! ## Shared atomics: the rely (Opus lanes O25, O25b, O25c; OFFEN O25, O17)

    The definitions of the atomic-rely block of the header: (a) `AkzeptiertSpecX`/`PrueferX`,
    (b) `NutzerPflichtA`, the legs `ZielX`/`ZielFX` over machine GX, and `GabbroZiel`. Moved here
    from Zielsatz/AtomarPflicht.lean, AtomarAkzeptiert.lean, AtomarZiel.lean,
    AtomarInvarianten.lean and AtomarMasken.lean (lane O25b) unchanged; `SchwachX`, `ZeitAbX`,
    `ZielX`, `FortschrittFX`, `ZielFX` are new (lane O25c). -/

section Atomar

variable [DecidableEq D.Fn]

/-- **The call closure of `w`** (enumeration-free): `w`, and every function a function of the
    closure calls (`ruftB`). -/
inductive Erreicht (P : Programm D) (w : D.Fn) : D.Fn → Prop
  | wurzel : Erreicht P w w
  | ruf {f g : D.Fn} : Erreicht P w f → ruftB P f g = true → Erreicht P w g

/-- **Thread-local among the starts `ws`, over the call closure** (the twin of `Getrennt`,
    Spec.lean, without a member list). -/
def GetrenntR (P : Programm D) (ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Prop :=
  ∀ w₁ ∈ ws, ∀ w₂ ∈ ws, (w₁ ≠ w₂ ∨ Mehrfach ws w₁) → ∀ f g, Erreicht P w₁ f →
    c ∈ fussOrteG P f → Erreicht P w₂ g → TraegerSchreibt g c = false

/-- **A shared atomic of the unit**: `atomic`, unguarded, and not thread-local. -/
def GeteiltA (P : Programm D) (ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Prop :=
  AtomarAusgenommen c ∧ (∀ L, ¬ Bewacht c L) ∧ ¬ GetrenntR P ws c

/-- **A shared atomic the checker admits**: shared (`GeteiltA`) and in no contract. -/
def GeteiltV (P : Programm D) (ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Prop :=
  GeteiltA P ws c ∧ VertragsFrei P c

/-- **(a) with the atomic rely**: `AkzeptiertSpec` with the footprint property `FussSX` over the
    admitted shared atomics `GeteiltV`, (since 2026-10-24) the ownership judgment of every
    arena in `B`: every body passes the ownership check against the arena's interfaces
    (`Checked`), and the arena's allocator words are plain (`ArenaPlain`: no weak-memory answer
    reaches them), and (since 2026-11-02, C15) the accumulator admission of every
    accumulator in `A`. Every other field is `AkzeptiertSpec`'s. -/
structure AkzeptiertSpecX (P : Programm D) (S : SperrInv D) (fs ws : List D.Fn)
    (B : List (ArenaOwnership.Body.ArenaIface D))
    (A : List (Kernzelle.AccumulatorDecl D)) : Prop where
  frag : programmImFragmentG P fs = true
  abg : ∀ w, AbgK P fs (reachB P fs w)
  fuss : ∀ f, FussSX P S (lokW P fs ws) (GeteiltV P ws) f
  stufen : StufenM P
  sperrOrte : ∀ L c, c ∈ S.orte L → Bewacht c L
  wurzeln : ∀ w ∈ ws, D.haelt w = [] ∧ D.gruende w = 0
  einzeln : EinzelnPool P fs ws
  renn : ∀ c, (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c → SchreibGetrennt P fs ws c
  antworten : ∀ f, ∀ x ∈ (P.rumpf f).ants, StelleOk D x
  -- the handler discipline `H102` (Opus agent H), as in `AkzeptiertSpec`
  masken : MaskenDisziplin P fs
  -- the ownership judgment (2026-10-24): every body, against every arena's interfaces
  besitz : ∀ a ∈ B, ArenaOwnership.Body.Checked P a.A a.I
  worte : ∀ a ∈ B, ArenaOwnership.Machine.ArenaPlain a.A
  -- the accumulator admission (C15, 2026-11-02)
  akku : Kernzelle.AccumulatorAdmission P fs A

/-- **The ownership start of a unit** (2026-10-24): every arena is empty in the declared start
    memory (nothing used, the free list full), and no declared start or run-time root is handed an
    allocation (every parameter mode of its interface is plain). Decided by the checker beside
    `AkzeptiertSpecX`, which does not see the unit's start. -/
structure BesitzStart (E : Einheit D) : Prop where
  leer : ∀ a ∈ E.arenen, ArenaOwnership.Machine.ArenaLeer a.A E.sp0
  start : ∀ a ∈ E.arenen, ∀ r ∈ E.starts ++ E.gestartet,
    (ArenaOwnership.Body.modeList (a.I r.1).parameters).all Option.isNone = true

/-- **Race freedom on GA runs** (`RennfreiBis` with `LaufGA`): on every run of GA -- so on the
    G-part of every run of W -- two accesses by different threads to a non-atomic carrier, one
    a write, are ordered through a guard lock. -/
def RennfreiBisGA (P : Programm D) (O : Orakel D) (passes : Nat) (M0 M : RufMaschineG D) : Prop :=
  ∀ (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat),
    LaufGA P O passes M0 ms fs n → ms n = M →
    ∀ (i j : Nat) (c : D.Tab ⊕ D.Glob), i < j → j < n → fs i ≠ fs j →
      ZugriffG (ms i) (ms (i + 1)) (fs i) c → ZugriffG (ms j) (ms (j + 1)) (fs j) c →
      (SchreibG (ms i) (ms (i + 1)) (fs i) c ∨ SchreibG (ms j) (ms (j + 1)) (fs j) c) →
      ¬ AtomarAusgenommen c →
      ∃ L, Bewacht c L ∧ GeordnetG ms fs L i j

end Atomar

/-- **A checker for the rely**: its soundness target is `AkzeptiertSpecX`. -/
structure PrueferX where
  akzeptiert : ∀ {D : Deklaration} [DecidableEq D.Fn],
    Einheit D → List D.Fn → List D.Lock → List (D.Tab ⊕ D.Glob) → Bool
  korrekt : ∀ {D : Deklaration} [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    akzeptiert E fs.1 ls.1 cs.1 = true →
      AkzeptiertSpecX E.P E.S fs.1 E.ws E.arenen E.akku ∧ BesitzStart E ∧ Kernzelle.AkkuStart E E.akku

/-- **The logic of the bodies with the atomic rely over `T`.** -/
def LogikPflichtA (P : Programm D) (S : SperrInv D) (Q : AxEns D) (T : D.Tab ⊕ D.Glob → Prop) :
    Prop :=
  (∀ (passes : Nat) (f : D.Fn),
    KoerperGutSA P passes Q S T f ∧ InvGutSA P passes Q S T f ∧ InvGutGrundA P passes Q S T f) ∧
  SperrInvLokal S ∧ AxEnsLokal Q

/-- **The user's own logic with the atomic rely**: the rely over the unit's shared atomics. -/
structure NutzerPflichtA [DecidableEq D.Fn] (E : Einheit D) : Prop where
  logik : LogikPflichtA E.P E.S E.Q (GeteiltA E.P E.ws)
  start : StartPflicht E

/-- **Lock invariants at every lock move, over GX steps** (`SperrWechselG` with `RufSchrittGX`). -/
def SperrWechselGX (P : Programm D) (O : Orakel D) (passes : Nat) (Tg : D.Tab ⊕ D.Glob → Prop)
    (S : SperrInv D) (M : RufMaschineG D) : Prop :=
  ∀ (u : Faden) (M' : RufMaschineG D) (L : D.Lock), RufSchrittGX P O passes Tg M u M' →
    (L ∉ offen (M.faeden u).spur → L ∈ offen (M'.faeden u).spur →
      S.inv L M.speicher = true ∧ S.inv L M'.speicher = true) ∧
    (L ∈ offen (M.faeden u).spur → L ∉ offen (M'.faeden u).spur → S.inv L M'.speicher = true)

/-- **A held lock's invariant is observed by its holder alone, over GX steps.** -/
def SperrSichtGX (P : Programm D) (O : Orakel D) (passes : Nat) (Tg : D.Tab ⊕ D.Glob → Prop)
    (S : SperrInv D) (M : RufMaschineG D) : Prop :=
  ∀ (u : Faden) (M' : RufMaschineG D), RufSchrittGX P O passes Tg M u M' →
    ∀ (L : D.Lock) (c : D.Tab ⊕ D.Glob), c ∈ S.orte L →
      (ZugriffG M M' u c → L ∈ offen (M.faeden u).spur) ∧
      (∀ t, t ≠ u → L ∈ offen (M.faeden t).spur → TraegerGleich M'.speicher M.speicher c)

/-- **No same-core interrupt deadlock, on GA runs** (`KernHaltG` with `LaufGA`). -/
def KernHaltGA (P : Programm D) (O : Orakel D) (passes : Nat) (M0 M : RufMaschineG D) : Prop :=
  ∀ (kern : Faden → Nat) (H : Faden → Prop) (Z : Faden → D.Fn → Prop)
    (A : Faden → D.Fn → Merkmal D),
    (∀ t, H t → MerkAbg P (Z t) (A t)) →
    (∀ t, H t → MerkInvG (Z t) (A t) (M0.faeden t)) →
    (∀ t, H t → ∀ (f : D.Fn) (L : D.Lock), Z t f → (A t f).sperre L = true →
      D.maskiert L = true) →
    (∀ (t : Faden) (L : D.Lock), ¬ AnSperre M0 t L) →
    ∀ (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat),
      LaufGA P O passes M0 ms fs n → ms n = M → KernPlan kern H ms fs n →
      ∀ (g f : Faden) (L : D.Lock), H g → f ≠ g → kern f = kern g →
        AnSperre M g L → L ∉ offen ((M.faeden f).spur)

/-- **No same-core interrupt deadlock, on GA runs** (`KernHaltE` of Opus agent H with `LaufGA`:
    the handlers are the program's own, `HandlerVon`). -/
def KernHaltEA (P : Programm D) (O : Orakel D) (passes : Nat) (M0 M : RufMaschineG D) : Prop :=
  ∀ (kern : Faden → Nat) (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat),
    LaufGA P O passes M0 ms fs n → ms n = M → KernPlan kern (HandlerVon P M0) ms fs n →
    ∀ (g f : Faden) (L : D.Lock), HandlerVon P M0 g → f ≠ g → kern f = kern g →
      AnSperre M g L → L ∉ offen ((M.faeden f).spur)

/-- **The weak machine adds no behaviour outside the shared atomics `Tg`, at `M`**. For EVERY
    assignment `ord` of memory orders, every weak state `W` over `M` reached from the weak start
    over `M0`, and every step W takes from there (with its presented memory `σ`): it is a step
    of GX from `M` to the successor's G-part -- machine G whose reads of `Tg` the weak memory
    answers -- and `σ` is G's memory at every carrier outside `Tg`. With `Tg` empty this is
    `SchwachSC` (`schwachSC_of_X`): the DRF theorem. -/
def SchwachX (P : Programm D) (O : Orakel D) (passes : Nat) (Tg : D.Tab ⊕ D.Glob → Prop)
    (M0 M : RufMaschineG D) : Prop :=
  ∀ (ord : D.Glob → Speichermodell.Ordnung) (W W' : RufMaschineW D) (u : Faden) (σ : Speicher D)
    (M'' : RufMaschineG D) (wahl : D.Tab ⊕ D.Glob → NachrichtW D) (neu : D.Tab ⊕ D.Glob → Nat),
    RufErreichbarW P O passes ord (RufStartW M0) W → W.g = M →
    SchrittW P O passes ord W u W' σ M'' wahl neu →
    RufSchrittGX P O passes Tg M u W'.g ∧ ∀ c, ¬ Tg c → TraegerGleich σ M.speicher c

/-- **Time over GX**: `ZeitAb` for every run of GX from `M` (the weak memory answering the
    shared atomics). -/
def ZeitAbX (P : Programm D) (O : Orakel D) (passes : Nat) (Tg : D.Tab ⊕ D.Glob → Prop)
    (M : RufMaschineG D) : Prop :=
  ∀ (f : Faden) (g : D.Fn) (n : Nat) (rho : Env D (D.params g)) (s0 : World D) (k : Nat),
    rufTief P (n + 1) g = true → Eintritt P f g rho s0 k M →
    ∀ (M2 : RufMaschineG D) (run : SegLaufX P O passes Tg M M2), aktivVorX f k run →
      segZaehleX run f ≤ kostenTief P passes (n + 1) g

/-- **THE GOAL at a machine `M` of a GX run from `M0`, with the shared atomics `Tg`.** -/
structure ZielX (P : Programm D) (S : SperrInv D) (O : Orakel D) (passes : Nat)
    (Tg : D.Tab ⊕ D.Glob → Prop) (M0 M : RufMaschineG D) : Prop where
  speicherSicher : SpurInv M
  rennfrei : RennfreiBisGA P O passes M0 M
  schwach : SchwachX P O passes Tg M0 M
  vertrag : VertragAmOrtG P M
  sperrInv : SperrInvG S M
  invRueck : InvAmOrtG P M
  invGrund : InvAmGrundG P M
  invRuhe : InvRuheG P M0 M
  invSicht : InvSichtG P M0 M
  sperrWechsel : SperrWechselGX P O passes Tg S M
  sperrSicht : SperrSichtGX P O passes Tg S M
  startEnde : StartEndeG P M
  keinStartGrund : KeinStartGrundG M
  keinLogikHalt : KeinLogikHaltG O passes M
  keineVerklemmung : (∀ t, ¬ FertigG M t → WartetG M t) → ∀ t, FertigG M t
  keinZyklus : KeinWarteZyklus M
  keinKernHalt : KernHaltEA P O passes M0 M
  fortschritt : FortschrittG P O passes M
  zeit : ZeitAbX P O passes Tg M
  folge : FolgeG P M
  -- memory at addresses (2026-10-22): if foreign code writes inside the declared extents (`ImBereichO`, a named
  -- assumption inside the leg), every cell the run has changed lies in its extent and, under every correct layout,
  -- with all its bytes in the region of its table
  speicherAdressen : ImBereichO O → ∀ (lay : AdressLayout D), LayoutOk lay → ∀ (t : D.Tab) (k : Int) (f : D.Feld t),
    M.speicher.slots t k f ≠ M0.speicher.slots t k f →
      ImBereich D t k ∧ ∀ a, lay.inZelle t k f a → lay.inTabelle t a

/-- **Every stop is named, on the thread machine over GX.** -/
def FortschrittFX (P : Programm D) (O : Orakel D) (passes : Nat) (Tg : D.Tab ⊕ D.Glob → Prop)
    (K : FadenMaschine D) : Prop :=
  ∀ t, K.lebt t = false ∨
    (K.wartet t ≠ [] ∧ (JoinWartet K t ∨
      ∃ K', FadenSchrittX P O passes Tg K K' ∧ K'.m = K.m ∧ K'.wartet t = [])) ∨
    (K.wartet t = [] ∧ (FertigG K.m t ∨ WartetG K.m t ∨ HaltBenannt O passes K.m .flagge t ∨
      HaltBenannt O passes K.m .budget t ∨ HaltBenannt O passes K.m .hardware t ∨
      HaltBenannt O passes K.m .nieZurueck t ∨
      ∃ M', RufSchrittG P O passes K.m t M' ∧
        FadenSchrittX P O passes Tg K ⟨M', K.lebt, K.wartet, K.rang, K.uhr⟩))

/-- **THE GOAL on a thread machine over GX.** -/
structure ZielFX (P : Programm D) (S : SperrInv D) (O : Orakel D) (passes : Nat)
    (Tg : D.Tab ⊕ D.Glob → Prop) (M0 : RufMaschineG D) (B : List (ArenaOwnership.Body.ArenaIface D))
    (K : FadenMaschine D) : Prop where
  g : ZielX P S O passes Tg M0 K.m
  schlafendUnberuehrt : ∀ t, K.lebt t = false → K.m.faeden t = M0.faeden t
  schlafendFrei : ∀ t, K.lebt t = false → ∀ L, L ∉ offen (K.m.faeden t).spur
  joinFrei : ∀ t, K.wartet t ≠ [] → ∀ L, L ∉ offen (K.m.faeden t).spur
  keineVerklemmung : (∀ t, K.lebt t = true → ¬ FertigG K.m t →
      (K.wartet t = [] ∧ WartetG K.m t) ∨ JoinWartet K t) →
    ∀ t, K.lebt t = true → FertigG K.m t
  keinZyklus : KeinWarteZyklusF K
  fortschritt : FortschrittFX P O passes Tg K
  spawnSicht : ∀ (K' : FadenMaschine D) (t : Faden), FadenSchrittX P O passes Tg K K' →
    K.lebt t = false → K'.lebt t = true →
      K'.m = K.m ∧ (∀ L, L ∉ offen (K'.m.faeden t).spur) ∧ SperrInvG S K'.m ∧
        InvRuheG P M0 K'.m
  -- the budget stop is no stop of the program (2026-10-22): one budget higher, from the same machine with every
  -- `forever` counter one higher, the stopped thread takes its next step
  budgetUnecht : ∀ t, HaltBenannt O passes K.m .budget t →
    ∃ M', RufSchrittG P O (passes + 1) (K.m.plus 1) t M'
  -- ownership (2026-10-24): for every arena of `B` one disciplined ledger of its slots agrees with the
  -- memory, the free list is well formed, and every thread's frames own exactly what their interfaces say
  besitz : ∀ a ∈ B, ArenaOwnership.Machine.OwnInv a.A a.I K.m
-- END atomic-rely definitions --

/-- **GABBRO_ZIEL** (since Opus lane O25c, 2026-09-26: WITH THE ATOMIC RELY). Over the THREAD
    MACHINE OVER GX: every run from the runtime's start, with any set `lebt0` of initially live
    threads -- the others are slots that `start` or `child` spawn at run time -- in which every
    read of an ADMITTED SHARED ATOMIC of the unit (`GeteiltV E.P E.ws`: `atomic`, unguarded, not
    thread-local among the starts, in no contract) may be answered by the weak memory rather
    than by the last write. (a) is a checker for the rely (`PrueferX`: sound against
    `AkzeptiertSpecX`, whose footprint rule admits exactly those carriers), (b) is the user's
    logic with the rely (`NutzerPflichtA`: every body against EVERY value such a read may
    return). Since 2026-10-24 (a) also decides the ownership judgment of every arena the unit
    declares (`E.arenen`, `BesitzStart`), and the conclusion carries the leg `besitz` for each,
    lifted to `E.P.mitRuhe`. Every run of before is such a run (`fadenErreichbarX_of`), every
    checker of before with the ownership acceptance is such a checker (`Pruefer.alsX`), and on
    every unit without an arena it accepts (b) is (b) of before and no admitted shared atomic
    exists: the statement of before, `GabbroZielSC`, is a corollary there (`gabbro_ziel_sc_aus`,
    Zielsatz/BeweisAtomar.lean). -/
def GabbroZiel : Prop :=
  ∀ (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    C.akzeptiert E fs.1 ls.1 cs.1 = true →                     -- (a) the checker, on E
    NutzerPflichtA E →                                          -- (b) the user, with the rely
    ∀ O : Orakel D, HardwareAnnahmen O E.Q →                    -- (c) the hardware
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit E sp init →                                      -- (d) the runtime, A4
      ∀ (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe),
        FadenErreichbarX E.P.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
          (FadenStart E.P.mitRuhe sp init lebt0) K →
          ZielFX E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
            (RufStartG E.P.mitRuhe sp init) (E.arenen.map (·.mitRuhe)) K

end Gabbro.Grammatik.Zielsatz
