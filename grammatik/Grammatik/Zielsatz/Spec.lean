/-
  File:    Grammatik/Zielsatz/Spec.lean -- THE GOAL AS ONE STATEMENT (PLAN-ZIELSATZ.md step 2).
  Content: definitions and `def GabbroZiel : Prop`. No proof. Review target.

  Goal (owner): a user proves only their OWN logic plus named hardware assumptions; memory
  safety, data-race freedom, contracts where claimed in concurrent runs, and time are carried
  by the language.

  SHAPE. Premises in three groups: (a) `C.akzeptiert … = true` -- ONE Bool of the checker
  (`Pruefer`: the Bool and its soundness against `AkzeptiertSpec`; the concrete checker is
  `Zielsatz/Akzeptiert.lean`, its signature `Akzeptiert P S fs ls ws` is the field's);
  (b) `NutzerPflicht` -- the user's logic, at EVERY `forever` budget; (c) `HardwareAnnahmen`.
  Then for every budget, start memory, start assignment meeting `StartZulaessig`, and every
  reached machine: `Ziel`. `fs`/`ls` are `Aufzaehlung`s (complete by their type: finite
  declarations only), not premises.

  REVIEW PACKAGE -- every model definition used, file:line, what it says / if it were wrong.
  Machine G and the sequential semantics (review question 4):
  * `RufMaschineG` RufMaschineG:151 -- shared memory, per thread a frame stack, trace, call log
    / a field G lacks is a behaviour no conjunct can speak of.
  * `RufSchrittG` RufMaschineG:246 -- the 70 rules, one thread per step, rules fire only on
    success outcomes / a rule G has and C lacks (or vice versa) makes every leg about another program.
  * `RufStartG` :2093, `RufErreichbarG` :2110 -- every thread in its start frame holding its
    signature locks; reachable = finitely many steps / a start C does not make is irrelevant.
  * `execStmt` Semantik:574, `keinRuf` Maschine:383, `Stmt.istBlatt` Maschine:392 -- one
    statement sequentially; leaves are what G runs in one step / wrong leaves = wrong steps.
  * `execEndH` SperreSem:353, `HavocOk` :71, `SperrInv` :45 -- the sequential body semantics the
    user proves against: `locks L` runs from any move keeping `S.inv L`, a release checks it /
    if it differs from `execStmt` outside `locks`, the user proves the wrong body.
  * `World` Semantik:77 (slots total over `Int`; in-range is the TYPE of `.index` values),
    `Speicher` Maschine:359, `Orakel` Semantik:355, `Faden` Wettlauf:46 (= Nat, all started).
  Premise definitions:
  * `GutO` Satz:965 -- axioms stay in their declared write frames, keep held locks and trace.
  * `RegLokal` ZielOrtGeraetSem:48 -- register/visibility answers depend only on declared carriers.
  * `AxVertragO`/`AxEnsLokal`/`AxEns` AxiomVertrag:50/56/44 -- axiom answers meet the declared
    `ensures`; the declared ensures reads only the axiom's write carriers.
  * `KoerperGutS` SperreFuss:374 -- per function, sequential: triple, caller duty, no `logik`
    outcome, against every frame-respecting handler (`RespektiertRahmen` ZielOrtRahmenSem:48,
    `OhneVorbedingung` ZielOrt:87, `OhneLogik` ZielOrtGanz:51), oracle (`RahmenO`
    ZielOrtVollBeweis:48) and move / an empty handler/oracle/move class empties it (probe A/D).
  * `InvGutS`/`InvAmRueck`/`InvHaelt` ZielOrtInv:54/46/41 -- owed invariants at a value return.
  * `ReqAmEintritt`/`EnsAmRueck` VertragOrtB:114/120, `StartGut` ZielOrt:113.
  * `programmImFragmentG` ZielOrtGeraetSem:502, `fussOrteG` :450, `FussS` SperreFuss:140,
    `AbgK` ZielOrtMehrfaden:107, `reachB` :146, `StufenM` Verklemmung:552, `Bewacht`
    InterferenzAllgemein:1350, `TraegerSchreibt` :123 -- the checker's program facts.
  Conclusion definitions:
  * `SpurInv` RennfreiVoll:249 (`Ereignis.gut` Satz:263, `Konsistent` :279) -- every recorded
    access carries its carrier's guards (locks AND marks) in `Λ`, whose locks are really held.
  * `LaufG`/`ZugriffG`/`SchreibG`/`GeordnetG` RennfreiVoll:485/333/337/563 -- runs by index;
    an access = recorded event or memory change; ordered = release by one, acquire by the other.
    `AtomarAusgenommen`/`PaarungAusgenommen` InterferenzAllgemein:609/614.
  * `VertragAmOrtG` ZielOrt:67 -- requires at every logged entry, ensures at every logged return.
  * `SperrInvG` SperreMaschine:424 -- every lock no thread holds has its invariant in memory.
  * `InvAmOrtG` ZielOrtInv:66; `StartEndeG` ZielOrtStart:70 (`RetKopf` :59); `KeinStartGrundG`
    :191; `KeinLogikHaltG`/`PrueftG` ZielOrtGanz:658/622 -- no thread stuck at a loop invariant
    or transition test. `FertigG`/`WartetG`/`AnSperre` Verklemmung:746/751/652.
  * `Eintritt`/`SegLauf`/`aktivVor`/`segZaehle`/`kostenTief`/`rufTief` KostenG:788/740/776/750/955/964.
  NEW here: `InvGutGrund`, `InvAmGrundG` (invariants at REASON exits), `HaltBenannt` (the
  named stops), `RennfreiBis` (DRF for every carrier, not only guarded ones), `Getrennt`,
  `Ruhig`, `AkzeptiertSpec`, `StartZulaessig`, `Ziel`, `GabbroZiel`.

  REVIEW QUESTIONS. 1. Does `Ziel` say the four legs, nothing weaker? 2. Is every premise in
  exactly one group? 3. Can a user-controlled choice empty an obligation? Known instances:
  probes A/D (closed by `NutzerPflicht` at every budget); an unsatisfiable lock invariant or
  root `requires` empties `StartZulaessig` (only the positive probes exclude it). 4. Does G run
  what the language means (translation validation takes over for the C)?

  NOT CLAIMED (PLAN §6): termination and a waiting bound under fairness (`zeit` bounds only
  frames with a finite call tree, `rufTief`); the C and the hardware; weak memory beyond DRF-SC
  (G is sequentially consistent; `atomic` globals and publish payloads are ordered by A10, not
  by locks, and are excluded from `rennfrei`); floats only as the kernel IEEE model of
  GLEITKOMMA §7 (no float assumption on G's side; `gleitkomma_ieee` is on the C side);
  starvation freedom; invariants at entry or while locks are held (claimed at returns only).
  Declared `costs` are not in `Deklaration`: `zeit` is the syntax-computed bound.

  FINDINGS (definitions in proof files, imported anyway): there is no definition-only layer.
  All three imports are mixed files; the goal predicates live in flagship proof files
  (ZielOrt, ZielOrtGanz, ZielOrtInv, ZielOrtStart, ZielOrtMehrfaden, SperreFuss,
  SperreMaschine, Verklemmung, RennfreiVoll, KostenG); the closure includes WITNESS files
  (AxiomVertrag imports ZielOrtVollZeuge, RennfreiG imports ZielOrtZeuge). To move: every
  definition listed above out of its proof file.
-/
import Grammatik.Verklemmung
import Grammatik.RennfreiVoll
import Grammatik.KostenG

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration}

/-- A complete enumeration: every element is in the list. -/
def Aufzaehlung (α : Type) : Type := {l : List α // ∀ a, a ∈ l}

/-! ## (a) What the checker decides -/

section Pruefer

variable [DecidableEq D.Fn]

/-- Carrier `c` is thread-local among the declared starts `ws`: no start reaches `c` in a
    footprint while a DIFFERENT start can write it (`GetrenntK` over the starts). -/
def Getrennt (P : Programm D) (fs ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Prop :=
  ∀ w₁ ∈ ws, ∀ w₂ ∈ ws, w₁ ≠ w₂ → ∀ f g, reachB P fs w₁ f = true → c ∈ fussOrteG P f →
    reachB P fs w₂ g = true → TraegerSchreibt g c = false

noncomputable def lokW (P : Programm D) (fs ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Bool :=
  @decide (Getrennt P fs ws c) (Classical.propDecidable _)

/-- Carrier `c` is WRITE-separated among the declared starts `ws`: if one start's call graph
    may write `c`, no DIFFERENT start's graph may write it or have it in a footprint. -/
def SchreibGetrennt (P : Programm D) (fs ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Prop :=
  ∀ w₁ ∈ ws, ∀ w₂ ∈ ws, w₁ ≠ w₂ → ∀ g, reachB P fs w₁ g = true → TraegerSchreibt g c = true →
    ∀ h, reachB P fs w₂ h = true → TraegerSchreibt h c = false ∧ c ∉ fussOrteG P h

/-- **What `Akzeptiert` must establish** (the Props of its components): fragment; closed call
    graphs; every footprint carrier signature-guarded, lock-protected or thread-local; lock
    floors; protected carriers guarded by their lock; declared starts hold no lock by
    signature and have no reasons; every carrier without a guard lock that is neither
    `atomic` nor a publish payload is write-separated among the declared starts (the
    counterpart of the checker's `H013`). -/
structure AkzeptiertSpec (P : Programm D) (S : SperrInv D) (fs ws : List D.Fn) : Prop where
  frag : programmImFragmentG P fs = true
  abg : ∀ w, AbgK P fs (reachB P fs w)
  fuss : ∀ f, FussS P S (lokW P fs ws) f
  stufen : StufenM P
  sperrOrte : ∀ L c, c ∈ S.orte L → Bewacht c L
  wurzeln : ∀ w ∈ ws, D.haelt w = [] ∧ D.gruende w = 0
  renn : ∀ c, (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c → ¬ PaarungAusgenommen c →
    SchreibGetrennt P fs ws c

end Pruefer

/-- **The checker interface.** `akzeptiert P S fs ls cs ws` is the Bool the Rust checker
    computes (signature of `Akzeptiert`: functions, locks, carriers, declared starts);
    `korrekt` is its soundness, the one link between the Bool and what the statement uses. -/
structure Pruefer where
  akzeptiert : ∀ {D : Deklaration} [DecidableEq D.Fn],
    Programm D → SperrInv D → List D.Fn → List D.Lock → List (D.Tab ⊕ D.Glob) → List D.Fn →
      Bool
  korrekt : ∀ {D : Deklaration} [DecidableEq D.Fn] (P : Programm D) (S : SperrInv D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob))
    (ws : List D.Fn),
    akzeptiert P S fs.1 ls.1 cs.1 ws = true → AkzeptiertSpec P S fs.1 ws

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
          execEndH (V := vertragVon D f) S O' U passes R (P.rumpf f) σ ρ = EndAusgang.grund σ' r →
            InvAmRueck P f σ'

/-- A lock invariant reads only its protected carriers (second half of `SperrInvOk`). -/
def SperrInvLokal (S : SperrInv D) : Prop :=
  ∀ L (s s' : Speicher D), (∀ c ∈ S.orte L, TraegerGleich s s' c) → S.inv L s = S.inv L s'

/-- **The user's own logic**: per function and at EVERY `forever` budget the body triple with
    caller duty and no `logik` outcome, owed invariants at value AND reason exits; the lock
    invariants and declared axiom ensures the user wrote read only their carriers. -/
def NutzerPflicht (P : Programm D) (S : SperrInv D) (Q : AxEns D) : Prop :=
  (∀ (passes : Nat) (f : D.Fn),
    KoerperGutS P passes Q S f ∧ InvGutS P passes Q S f ∧ InvGutGrund P passes Q S f) ∧
  SperrInvLokal S ∧ AxEnsLokal Q

/-! ## (c) What the hardware is assumed to do -/

def HardwareAnnahmen (O : Orakel D) (Q : AxEns D) : Prop :=
  GutO O ∧ RegLokal O ∧ AxVertragO Q O

/-! ## (d) The starts the statement speaks about -/

section Start

variable [DecidableEq D.Fn]

/-- An idle start: no signature lock, no reasons, every function it reaches has an empty
    footprint and writes nothing. Any number of threads may run it. -/
def Ruhig (P : Programm D) (fs : List D.Fn) (w : D.Fn) : Prop :=
  D.haelt w = [] ∧ D.gruende w = 0 ∧ ∀ f, reachB P fs w f = true →
    fussOrteG P f = [] ∧ ∀ c, TraegerSchreibt f c = false

/-- **Admissible starts**: every thread runs a declared start (each on ONE thread) or an idle
    one; the start functions' `requires` and every lock invariant hold at the start memory. -/
structure StartZulaessig (P : Programm D) (S : SperrInv D) (fs ws : List D.Fn)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) : Prop where
  wurzel : ∀ t, (init t).1 ∈ ws ∨ Ruhig P fs (init t).1
  einmal : ∀ t u, t ≠ u → (init t).1 = (init u).1 → Ruhig P fs (init t).1
  req : StartGut P sp init
  sperren : ∀ L, S.inv L sp = true

end Start

/-! ## The legs of the goal -/

/-- **Data-race freedom on every run from `M0` to `M`**: two accesses by different threads to
    ONE carrier, one a write, the carrier neither `atomic` nor a publish payload, are ordered
    through a guard lock (release by the first, acquire by the second). Unguarded carriers
    included: there such a pair must not exist. -/
def RennfreiBis (P : Programm D) (O : Orakel D) (passes : Nat) (M0 M : RufMaschineG D) : Prop :=
  ∀ (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat),
    LaufG P O passes M0 ms fs n → ms n = M →
    ∀ (i j : Nat) (c : D.Tab ⊕ D.Glob), i < j → j < n → fs i ≠ fs j →
      ZugriffG (ms i) (ms (i + 1)) (fs i) c → ZugriffG (ms j) (ms (j + 1)) (fs j) c →
      (SchreibG (ms i) (ms (i + 1)) (fs i) c ∨ SchreibG (ms j) (ms (j + 1)) (fs j) c) →
      ¬ AtomarAusgenommen c → ¬ PaarungAusgenommen c →
      ∃ L, Bewacht c L ∧ GeordnetG ms fs L i j

/-- At every logged REASON return, every invariant the function owes holds. -/
def InvAmGrundG (P : Programm D) (M : RufMaschineG D) : Prop :=
  ∀ (t : Faden) (ev : RufEreignisF D), ev ∈ (M.faeden t).log →
    ∀ (g : D.Fn) (rho : Env D (D.params g)) (r : Fin (D.gruende g)) (s0 s1 : World D),
      ev = RufEreignisF.grund g rho r s0 s1 → InvAmRueck P g s1

/-- The first layer of the head block answers a HARDWARE outcome at the world `σ`: a leaf's
    hardware outcome, an axiom answer outside its type, a register answer outside its type or
    against its promise, an invisible `awaits`, a float result outside its range. Exactly the
    failing side conditions of `blatt`/`dannBlatt`, `dannBindAxiom`, `dannRegLies*`,
    `dannAwaits`, `dannGleit*`. -/
def KopfHardware (O : Orakel D) (passes : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (σ : World D) (ρ : Env D Γ) : Block D V l Γ Λ Λ' → Prop
  | .cons s _ => s.istBlatt = true ∧ ∃ h, execStmt O passes keinRuf s σ ρ = .hardware h
  | .bindAxiom a args .. =>
      (axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).2 = none
  | .regLies r .. => ∀ v, einpassen (D.rtyp r) (O.regLies r σ) = some v → D.rzusage r v = false
  | .regLiesElse r .. => einpassen (D := D) (D.rtyp r) (O.regLies r σ) = none
  | .awaits g .. => O.sichtbar g σ = false
  | .gleit op a b lo hi _ =>
      gleitPasst lo hi (gleitRechne op (eval (σ.lese Λ (a.orte ++ b.orte)) a
        (σ.lese Λ (a.orte ++ b.orte)) ρ).x (eval (σ.lese Λ (a.orte ++ b.orte)) b
        (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = none
  | .gleitLit q lo hi _ => gleitPasst lo hi (bruch q) = none
  | .gleitVon e lo hi _ =>
      gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n) = none
  | _ => False

/-- A residue at a named hardware stop: a spent `forever` budget (`hardware fortschritt`), or
    its head block's first layer answers hardware. -/
def RestHardware (O : Orakel D) (passes : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (σ : World D) (ρ : Env D Γ) : GRest D V l Γ Λ → Prop
  | .ewig _ 0 _ _ _ => True
  | .ende (.cons s _) => s.istBlatt = true ∧ ∃ h, execStmt O passes keinRuf s σ ρ = .hardware h
  | .dann b _ => KopfHardware O passes σ ρ b
  | _ => False

/-- Thread `t` stands at a named stop: a named hardware assumption fails at its head. -/
def HaltBenannt (O : Orakel D) (passes : Nat) (M : RufMaschineG D) (t : Faden) : Prop :=
  ∃ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ)
    (r : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ),
    (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, r⟩ ∧ RestHardware O passes (M.weltVon t) ρ r

/-- **Every stop is named**: each thread is finished, waits for a lock another thread holds,
    stands at a named hardware stop, or can step. -/
def FortschrittG (P : Programm D) (O : Orakel D) (passes : Nat) (M : RufMaschineG D) : Prop :=
  ∀ t, FertigG M t ∨ WartetG M t ∨ HaltBenannt O passes M t ∨ ∃ M', RufSchrittG P O passes M t M'

/-- **Time**: a frame entered at `M`, of a function whose calls nest at most `n` deep, takes
    at most `kostenTief P passes (n + 1) g` own steps on every run while it is active. -/
def ZeitAb (P : Programm D) (O : Orakel D) (passes : Nat) (M : RufMaschineG D) : Prop :=
  ∀ (f : Faden) (g : D.Fn) (n : Nat) (rho : Env D (D.params g)) (s0 : World D) (k : Nat),
    rufTief P (n + 1) g = true → Eintritt P f g rho s0 k M →
    ∀ (M2 : RufMaschineG D) (run : SegLauf P O passes M M2), aktivVor f k run →
      segZaehle run f ≤ kostenTief P passes (n + 1) g

/-- **THE GOAL at a reached machine `M` of a run from `M0`**: the four legs, nothing else. -/
structure Ziel (P : Programm D) (S : SperrInv D) (O : Orakel D) (passes : Nat)
    (M0 M : RufMaschineG D) : Prop where
  -- memory safety (typing and in-range: intrinsic in `Programm D`)
  speicherSicher : SpurInv M
  -- data-race freedom
  rennfrei : RennfreiBis P O passes M0 M
  -- contracts where claimed
  vertrag : VertragAmOrtG P M
  sperrInv : SperrInvG S M
  invRueck : InvAmOrtG P M
  invGrund : InvAmGrundG P M
  startEnde : StartEndeG P M
  keinStartGrund : KeinStartGrundG M
  keinLogikHalt : KeinLogikHaltG O passes M
  -- progress
  keineVerklemmung : (∀ t, ¬ FertigG M t → WartetG M t) → ∀ t, FertigG M t
  fortschritt : FortschrittG P O passes M
  -- time
  zeit : ZeitAb P O passes M

/-- **GABBRO_ZIEL.** -/
def GabbroZiel : Prop :=
  ∀ (C : Pruefer) (D : Deklaration) [DecidableEq D.Fn] (P : Programm D) (S : SperrInv D)
    (Q : AxEns D) (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock)
    (cs : Aufzaehlung (D.Tab ⊕ D.Glob)) (ws : List D.Fn),
    C.akzeptiert P S fs.1 ls.1 cs.1 ws = true →               -- (a) the checker
    NutzerPflicht P S Q →                                     -- (b) the user
    ∀ O : Orakel D, HardwareAnnahmen O Q →                    -- (c) the hardware
    ∀ (passes : Nat) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)),
      StartZulaessig P S fs.1 ws sp init →
      ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
        Ziel P S O passes (RufStartG P sp init) M

end Gabbro.Grammatik.Zielsatz
