/-
  TEMPORARY (phase A of lane O25c): the new definitions of the goal statement with the atomic
  rely, before they move into Spec.lean.
-/
import Grammatik.Zielsatz.AtomarZiel
import Grammatik.Speichermodell.GXMaschine
import Grammatik.Zielsatz.Verbund

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik Speichermodell

variable {D : Deklaration}

-- BEGIN atomic-rely legs (Opus lane O25c, 2026-09-26) --
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
  keinKernHalt : KernHaltGA P O passes M0 M
  fortschritt : FortschrittG P O passes M
  zeit : ZeitAbX P O passes Tg M

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
    (Tg : D.Tab ⊕ D.Glob → Prop) (M0 : RufMaschineG D) (K : FadenMaschine D) : Prop where
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

/-- **GABBRO_ZIEL WITH THE ATOMIC RELY** (phase A name). -/
def GabbroZielX : Prop :=
  ∀ (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    C.akzeptiert E fs.1 ls.1 cs.1 = true →
    NutzerPflichtA E →
    ∀ O : Orakel D, HardwareAnnahmen O E.Q →
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit E sp init →
      ∀ (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe),
        FadenErreichbarX E.P.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
          (FadenStart E.P.mitRuhe sp init lebt0) K →
          ZielFX E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
            (RufStartG E.P.mitRuhe sp init) K

/-- **The user's logic of ONE unit, with the atomic rely** (the rely over the unit's own shared
    atomics). -/
structure NutzerTeilA [DecidableEq D.Fn] (eigen : D.Fn → Bool) (E : Einheit D) : Prop where
  logik : (∀ (passes : Nat) (f : D.Fn), eigen f = true →
      KoerperGutSA E.P passes E.Q E.S (GeteiltA E.P E.ws) f ∧
        InvGutSA E.P passes E.Q E.S (GeteiltA E.P E.ws) f ∧
        InvGutGrundA E.P passes E.Q E.S (GeteiltA E.P E.ws) f) ∧
    SperrInvLokal E.S ∧ AxEnsLokal E.Q
  start : StartPflicht E

/-- **GABBRO_ZIEL FOR LINKED UNITS, WITH THE ATOMIC RELY** (phase A name). -/
def GabbroZielVerbundX : Prop :=
  ∀ (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (E₁ E₂ : Einheit D) (e : D.Fn → Bool)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    C.akzeptiert E₁ fs.1 ls.1 cs.1 = true →
    C.akzeptiert E₂ fs.1 ls.1 cs.1 = true →
    Verbindbar E₁ E₂ →
    SchnittstelleSpec fs.1 e E₁ E₂ →
    NutzerTeilA e E₁ →
    NutzerTeilA (fun f => !e f) E₂ →
    E₂.Q = E₁.Q →
    ∀ O : Orakel D, HardwareAnnahmen O E₁.Q →
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit (verbinde e E₁ E₂) sp init →
      ∀ (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe),
        FadenErreichbarX (verbinde e E₁ E₂).P.mitRuhe O.mitRuhe passes
          (GeteiltV (D := D) (verbinde e E₁ E₂).P (verbinde e E₁ E₂).ws)
          (FadenStart (verbinde e E₁ E₂).P.mitRuhe sp init lebt0) K →
          ZielFX (verbinde e E₁ E₂).P.mitRuhe (verbinde e E₁ E₂).S.mitRuhe O.mitRuhe passes
            (GeteiltV (D := D) (verbinde e E₁ E₂).P (verbinde e E₁ E₂).ws)
            (RufStartG (verbinde e E₁ E₂).P.mitRuhe sp init) K
-- END atomic-rely legs --

end Gabbro.Grammatik.Zielsatz
