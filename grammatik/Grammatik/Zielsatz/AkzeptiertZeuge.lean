/-
  File:      Grammatik/Zielsatz/AkzeptiertZeuge.lean
  Subject:   witnesses for `Akzeptiert` / `StartZulaessig`
             (Zielsatz/Akzeptiert.lean), and the four flagships fed from
             them.

  * §1 The flagships from `Akzeptiert` + `StartZulaessig`: every decidable
    premise comes out of the two, only the user obligations, the hardware
    assumptions, the member lists and the run stay.
  * §2 The two-thread fixture `mP` (MehrfadenZeuge.lean): `Akzeptiert` by
    `decide`, `StartZulaessig` of its start `mInit` by `decide` over a start
    table, and `ziel_ort_mehrfaden_ende` / `keine_verklemmungG` on it with no
    decidable premise supplied by hand.
  * §3 The export of `beispiele/104` (Export104.lean): `Akzeptiert` by
    `decide` with the starts it declares (none); with its two functions as
    starts it is refused (both hold `M` by signature); and NO start is
    admitted (`gP_start_leer`) -- the export has no idle function.
  * §4 Refusals: two declared starts writing one unguarded table
    (`ak1_zwei_schreiber`), a lock-floor violation (`ak2_boden_falsch`);
    and the review finding of 2026-09-14: two starts writing one unguarded
    table that NOTHING reads (`ak3_zwei_schreiber_ohne_lesen`) -- accepted
    by the old Bool (`akzeptiertAlt`), refused by the race component.
-/
import Grammatik.Zielsatz.Akzeptiert
import Grammatik.RennfreiVoll
import Grammatik.MehrfadenZeuge
import Grammatik.Export104

namespace Gabbro.Grammatik

open Zielsatz

/-! ## 1. The flagships from `Akzeptiert` -/

section Flaggschiffe

variable {D : Deklaration} [DecidableEq D.Fn]

/-- **`ziel_ort_mehrfaden_ende` from `Akzeptiert`**: the checker's Bool and
    an admitted start replace every decidable premise; the call graphs are
    the computed ones. -/
theorem akzeptiert_mehrfaden (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock) (cs : List (D.Tab ⊕ D.Glob))
    (ws : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    (hA : Akzeptiert P S fs ls cs ws = true) (hZ : StartZulaessig P S fs ws sp init)
    (hSL : SperrInvLokal S) (hlok : AxEnsLokal Q)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hI : ∀ f : D.Fn, InvGutS P passes Q S f)
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      ((VertragAmOrtG P M ∧ SperrInvG S M ∧ KeinLogikHaltG O passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M') ∧
      InvAmOrtG P M) ∧ StartEndeG P M := by
  obtain ⟨hFrag, hAbg, hW, hFuss, hSO, hStart, hSs, hex, -, -, -⟩ :=
    Akzeptiert_ok hvoll (akzeptiertSpec_of hvoll hls hcs hA) hZ
  exact ziel_ort_mehrfaden_ende_bei P O passes Q S fs sp init (kVon P fs init) hO hRL hQ hlok
    ((sperrInvOk_iff S).mpr ⟨hSO, hSL⟩) hvoll hFrag hAbg hW hFuss hK hStart hSs hex hI

/-- **`keine_verklemmungG` from `Akzeptiert`.** -/
theorem akzeptiert_verklemmung {P : Programm D} {O : Orakel D} {passes : Nat} {S : SperrInv D}
    {fs : List D.Fn} {ls : List D.Lock} {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn}
    {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    (hA : Akzeptiert P S fs ls cs ws = true) (hZ : StartZulaessig P S fs ws sp init) (hO : GutO O)
    {M : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    (hW : ∀ t, ¬ FertigG M t → WartetG M t) : ∀ t, FertigG M t := by
  obtain ⟨-, -, -, -, -, -, -, -, hSt, hLeer, -⟩ :=
    Akzeptiert_ok hvoll (akzeptiertSpec_of hvoll hls hcs hA) hZ
  exact keine_verklemmungG hO hSt sp init hLeer ls hls hr hW

/-- **Race freedom for every carrier from `Akzeptiert`** (`rennfreiBis_of`). -/
theorem akzeptiert_rennfrei {P : Programm D} {O : Orakel D} {passes : Nat} {S : SperrInv D}
    {fs : List D.Fn} {ls : List D.Lock} {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn}
    {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    (hA : Akzeptiert P S fs ls cs ws = true) (hZ : StartZulaessig P S fs ws sp init) (hO : GutO O)
    (M : RufMaschineG D) : RennfreiBis P O passes (RufStartG P sp init) M :=
  rennfreiBis_of hvoll (akzeptiertSpec_of hvoll hls hcs hA) hZ hO passes M

/-- **`frame_schritte_beschraenkt`** for a function admitted at call depth
    `n + 1`. The time premise is no longer a component of `Akzeptiert`
    (it refused every recursive or indirect program); Spec's `ZeitAb` is
    conditional on `rufTief` per frame. -/
theorem akzeptiert_zeit {P : Programm D} (n : Nat) (O : Orakel D) (passes : Nat) (f : Faden)
    (g : D.Fn) (hadm : rufTief P (n + 1) g = true)
    {rho : Env D (D.params g)} {s0 : World D} {k : Nat} {M1 M2 : RufMaschineG D}
    (hE : Eintritt P f g rho s0 k M1) (run : SegLauf P O passes M1 M2) (hAk : aktivVor f k run) :
    segZaehle run f ≤ kostenTief P passes (n + 1) g :=
  frame_schritte_beschraenkt P O passes f g n hadm hE run hAk

end Flaggschiffe

/-! ## 2. The two-thread fixture `mP` -/

theorem mLocks_voll : ∀ L : mD.Lock, L ∈ ([()] : List mD.Lock) := fun L => by
  cases L; exact List.mem_singleton_self _

/-- The carriers of `mD`: the three tables (no globals). -/
def mCs : List (mD.Tab ⊕ mD.Glob) := [.inl MTab.konto, .inl MTab.privA, .inl MTab.privB]

theorem mCs_voll : ∀ c : mD.Tab ⊕ mD.Glob, c ∈ mCs := fun c => by
  rcases c with t | g
  · cases t <;> simp [mCs]
  · exact nomatch g

/-- **`Akzeptiert` holds on the two-thread fixture**, its declared starts
    being `hauptA` and `hauptB`: each writes its OWN private table
    unguarded, and `konto` is guarded (race component). -/
theorem mP_akzeptiert : Akzeptiert mP mSI mFs [()] mCs [mHauptA, mHauptB] = true := by decide

/-- `mInit` as a start table: thread 0 `hauptA`, thread 1 `hauptB`, every
    other thread `ruhe`. -/
def mTafel : StartTafel mD := ⟨[⟨mHauptA, .nil⟩, ⟨mHauptB, .nil⟩], ⟨mRuhe, .nil⟩⟩

theorem mTafel_start : startB mP mSI mFs [()] mCs [mHauptA, mHauptB] mTafel mSp = true := by
  decide

theorem mTafel_init : mTafel.init = mInit := by
  funext t
  match t with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- **`StartZulaessig` holds for the fixture's start.** -/
theorem mP_startZulaessig : StartZulaessig mP mSI mFs [mHauptA, mHauptB] mSp mInit := by
  rw [← mTafel_init]
  exact startB_ok mFs_voll mLocks_voll mCs_voll mTafel_start

/-- **The flagship on the fixture, fed by `Akzeptiert`**: only the user
    obligations (`mP_koerper`, `mP_inv`, `mSI_ok.2`), the hardware (`mO`)
    and the member lists are supplied by hand. -/
theorem mP_ziel_aus_akzeptiert : ∀ M : RufMaschineG mD,
    RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) M →
      ((VertragAmOrtG mP M ∧ SperrInvG mSI M ∧ KeinLogikHaltG mO 0 M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG mP mO 0 M t M') ∧
      InvAmOrtG mP M) ∧ StartEndeG mP M :=
  akzeptiert_mehrfaden mP mO 0 (axWahr mD) mSI mFs [()] mCs [mHauptA, mHauptB] mSp mInit
    mFs_voll mLocks_voll mCs_voll mP_akzeptiert mP_startZulaessig mSI_ok.2 axEnsLokal_wahr
    mP_koerper mP_inv mO_gut mO_lokal (axVertragO_wahr mO)

theorem mP_verklemmung_aus_akzeptiert : ∀ M : RufMaschineG mD,
    RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) M →
      (∀ t, ¬ FertigG M t → WartetG M t) → ∀ t, FertigG M t :=
  fun _ hr hW => akzeptiert_verklemmung mFs_voll mLocks_voll mCs_voll mP_akzeptiert
    mP_startZulaessig mO_gut hr hW

/-- **Race freedom for every carrier on the fixture**, private tables
    included. -/
theorem mP_rennfrei_aus_akzeptiert (passes : Nat) (M : RufMaschineG mD) :
    RennfreiBis mP mO passes (RufStartG mP mSp mInit) M :=
  akzeptiert_rennfrei mFs_voll mLocks_voll mCs_voll mP_akzeptiert mP_startZulaessig mO_gut M

/-- A second thread running `hauptA` is NOT admitted: `hauptA` is busy (it
    writes its private table), so it may run on one thread only. -/
theorem mTafel_doppelt_falsch :
    startB mP mSI mFs [()] mCs [mHauptA, mHauptB]
      ⟨[⟨mHauptA, .nil⟩, ⟨mHauptA, .nil⟩], ⟨mRuhe, .nil⟩⟩ mSp = false := by decide

/-! ## 3. The export of `beispiele/104` -/

section Export104

/-- The export's declaration, program and member lists, by short names
    (`gD`/`gP` alone clash with names of other files). -/
abbrev x104D : Deklaration := G104_referenz.gD
abbrev x104P : Programm x104D := G104_referenz.gP
abbrev x104Fs : List x104D.Fn := G104_referenz.gFs
abbrev x104Ls : List x104D.Lock := [G104_referenz.GLock.M]
abbrev x104Cs : List (x104D.Tab ⊕ x104D.Glob) := [.inl G104_referenz.GTab.Konto]
abbrev x104S : SperrInv x104D := SperrInv.leer x104D

theorem x104Ls_voll : ∀ L : x104D.Lock, L ∈ x104Ls := fun L => by
  cases L; exact List.mem_singleton_self _

theorem x104Cs_voll : ∀ c : x104D.Tab ⊕ x104D.Glob, c ∈ x104Cs := fun c => by
  rcases c with t | g
  · cases t; exact List.mem_singleton_self _
  · exact nomatch g

theorem x104Fs_voll : ∀ g : x104D.Fn, g ∈ x104Fs := fun g => by
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

/-- **`Akzeptiert` holds on the export** with the starts it declares: none
    (`104` dropped `concurrent` for `N240`, tests/referenz.rs). -/
theorem gP_akzeptiert : Akzeptiert x104P x104S x104Fs x104Ls x104Cs [] = true := by decide

/-- With its two functions as starts the export is refused by the start
    component (both hold `M` by signature); the other components hold. -/
theorem gP_als_starts :
    Akzeptiert x104P x104S x104Fs x104Ls x104Cs x104Fs = false ∧ wurzelnB x104Fs = false ∧
    (programmImFragmentG x104P x104Fs && abgAlleB x104P x104Fs &&
      fussWB x104P x104S x104Fs x104Fs && stufenB x104P x104Fs && sperrOrteB x104S x104Ls &&
      rennB x104P x104Fs x104Cs x104Fs) = true := by
  decide

/-- **No start is admitted for the export ITSELF**: both functions hold `M`
    by signature, so neither is idle, and with no declared start thread `0`
    has nothing to run. The runtime supplies the idle root: on
    `x104P.mitRuhe` a start IS admitted (`gP_mitRuhe_start`,
    Zielsatz/RuheZeuge.lean). -/
theorem gP_start_leer (sp : Speicher x104D)
    (init : Faden → Σ f : x104D.Fn, Env x104D (x104D.params f)) :
    ¬ StartZulaessig x104P x104S x104Fs [] sp init := by
  intro h
  rcases h.wurzel 0 with h0 | h0
  · exact absurd h0 List.not_mem_nil
  · have := h0.1
    revert this
    generalize (init 0).1 = f
    cases f <;> decide

end Export104

/-! ## 4. Refusals -/

inductive AkFn where
  | a
  | b
  | c
  | ruhe
  deriving DecidableEq

/-- A signature without parameters: signature locks, writes the table?, floor. -/
def akSig (w : Bool) (bo : Option Int) : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => w
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []
  boden := bo

def akSigNr : Nat → Signatur Unit Empty Unit Empty
  | 0 => akSig true none
  | 1 => akSig true none
  | 2 => akSig false (some 1)
  | _ => akSig false none

def akSigOf : AkFn → Nat
  | .a => 0
  | .b => 1
  | .c => 2
  | .ruhe => 3

/-- One UNGUARDED, unshared table of two slots; one lock of rank `0`; `a`
    and `b` may write the table, `c` has the lock floor `1`. -/
def akD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := AkFn
  sig := akSigOf
  sigNr := akSigNr
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun _ h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

instance : DecidableEq akD.Fn := inferInstanceAs (DecidableEq AkFn)

def akA : akD.Fn := AkFn.a
def akB : akD.Fn := AkFn.b
def akC : akD.Fn := AkFn.c
def akRuhe : akD.Fn := AkFn.ruhe

theorem akDarf (Λ : List (Res akD)) : darf akD () Λ := fun _ h => nomatch h

def akI0 {Γ : Ctx} {Λ : List (Res akD)} : Expr akD Γ Λ (.index 2) :=
  .weiter (by decide) (by decide) (.lit 0)

def ak1 {Γ : Ctx} {Λ : List (Res akD)} : Expr akD Γ Λ (.int 0 100) :=
  .weiter (by decide) (by decide) (.lit 1)

def ak2 {Γ : Ctx} {Λ : List (Res akD)} : Expr akD Γ Λ (.int 0 100) :=
  .weiter (by decide) (by decide) (.lit 2)

/-- `t[0] == 1`: `a`'s `ensures`, so `t` is in `a`'s footprint. -/
def akT1 {Γ : Ctx} {Λ : List (Res akD)} : Expr akD Γ Λ .bool :=
  .eq (.slot () () akI0 (akDarf Λ)) ak1

/-- `a`: `t[0] = 1; return`, `ensures t[0] == 1` -- no lock, the table is
    unguarded. -/
def akRumpfA : Endblock akD (vertragVon akD akA) false [] [] :=
  .cons (.assignSlot () () akI0 ak1 rfl (akDarf _)) (.ret .keine List.Perm.nil)

/-- `b`: `t[0] = 2; return`. -/
def akRumpfB : Endblock akD (vertragVon akD akB) false [] [] :=
  .cons (.assignSlot () () akI0 ak2 rfl (akDarf _)) (.ret .keine List.Perm.nil)

/-- `c` with floor `1`: `locks L { }; return` -- `L` has rank `0`. -/
def akRumpfC : Endblock akD (vertragVon akD akC) false [] [] :=
  .cons (.locks () (fun _ h => nomatch h) .nil) (.ret .keine List.Perm.nil)

/-- The program without the floor violation (`c` just returns). -/
def akP1 : Programm akD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures
    | .a => akT1
    | _ => .wahr
  rumpf
    | .a => akRumpfA
    | .b => akRumpfB
    | .c => .ret .keine List.Perm.nil
    | .ruhe => .ret .keine List.Perm.nil

/-- The same program with `c` taking a lock below its floor. -/
def akP2 : Programm akD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures
    | .a => akT1
    | _ => .wahr
  rumpf
    | .a => akRumpfA
    | .b => akRumpfB
    | .c => akRumpfC
    | .ruhe => .ret .keine List.Perm.nil

def akFs : List akD.Fn := [akA, akB, akC, akRuhe]

def akS : SperrInv akD := SperrInv.leer akD

def akSp : Speicher akD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

def akCs : List (akD.Tab ⊕ akD.Glob) := [.inl ()]

theorem akCs_voll : ∀ c : akD.Tab ⊕ akD.Glob, c ∈ akCs := fun c => by
  rcases c with t | g
  · cases t; exact List.mem_singleton_self _
  · exact nomatch g

/-- **An unguarded shared write is refused**: `a` and `b` are both declared
    starts and both write the unguarded table `t`; `t` is in `a`'s footprint
    (its `ensures` reads it) while another start writes it. Both the
    footprint check and the race component refuse; every other component
    holds. -/
theorem ak1_zwei_schreiber :
    Akzeptiert akP1 akS akFs [()] akCs [akA, akB] = false ∧
    fussWB akP1 akS akFs [akA, akB] = false ∧ rennB akP1 akFs akCs [akA, akB] = false ∧
    (programmImFragmentG akP1 akFs && abgAlleB akP1 akFs && stufenB akP1 akFs &&
      sperrOrteB akS [()] && wurzelnB [akA, akB]) = true := by
  decide

/-- With ONE writer as a declared start the same program is accepted -- and
    then a start running `b` (not declared, not idle) or `a` twice is not
    admitted. -/
theorem ak1_ein_schreiber :
    Akzeptiert akP1 akS akFs [()] akCs [akA] = true ∧
    startB akP1 akS akFs [()] akCs [akA] ⟨[⟨akA, .nil⟩], ⟨akRuhe, .nil⟩⟩ akSp = true ∧
    startB akP1 akS akFs [()] akCs [akA] ⟨[⟨akA, .nil⟩, ⟨akB, .nil⟩], ⟨akRuhe, .nil⟩⟩ akSp =
      false ∧
    startB akP1 akS akFs [()] akCs [akA] ⟨[⟨akA, .nil⟩, ⟨akA, .nil⟩], ⟨akRuhe, .nil⟩⟩ akSp =
      false := by
  decide

/-- **A lock-floor violation is refused**: `c` (floor `1`) takes the lock
    of rank `0`. Every other component holds: the floor check alone
    refuses. -/
theorem ak2_boden_falsch :
    Akzeptiert akP2 akS akFs [()] akCs [akA] = false ∧
    stufenB akP2 akFs = false ∧
    (programmImFragmentG akP2 akFs && abgAlleB akP2 akFs && fussWB akP2 akS akFs [akA] &&
      sperrOrteB akS [()] && wurzelnB [akA] && rennB akP2 akFs akCs [akA]) = true := by
  decide

/-! ### The write-write race no footprint sees (review finding, fixed 2026-09-14) -/

/-- The same two writers with NO read anywhere: every `ensures` is `true`,
    and `t[0] = 1` / `t[0] = 2` read nothing. No footprint contains `t`. -/
def akP3 : Programm akD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf
    | .a => akRumpfA
    | .b => akRumpfB
    | .c => .ret .keine List.Perm.nil
    | .ruhe => .ret .keine List.Perm.nil

/-- **The Bool as of master `cdfa8ac9`** (before the fix), recorded to show
    what it accepted: fragment, closure, footprint, floors, protected
    carriers, starts without signature locks, and `rufTief` for every
    function -- no race component. -/
def akzeptiertAlt {D : Deklaration} [DecidableEq D.Fn] (P : Programm D) (S : SperrInv D)
    (fs : List D.Fn) (ls : List D.Lock) (ws : List D.Fn) : Bool :=
  programmImFragmentG P fs && abgAlleB P fs && fussWB P S fs ws && stufenB P fs &&
    sperrOrteB S ls && ws.all (fun w => (D.haelt w).isEmpty) &&
    fs.all fun g => rufTief P (fs.length + 1) g

/-- **Probe (c) of the race fix**: two declared starts write one unguarded
    table and NOTHING reads it. The old Bool ACCEPTED the program -- every
    footprint is empty, so thread-locality over footprints saw no conflict;
    the new Bool REFUSES it, and only by the race component. -/
theorem ak3_zwei_schreiber_ohne_lesen :
    akzeptiertAlt akP3 akS akFs [()] [akA, akB] = true ∧
    Akzeptiert akP3 akS akFs [()] akCs [akA, akB] = false ∧
    rennB akP3 akFs akCs [akA, akB] = false ∧
    (programmImFragmentG akP3 akFs && abgAlleB akP3 akFs && fussWB akP3 akS akFs [akA, akB] &&
      stufenB akP3 akFs && sperrOrteB akS [()] && wurzelnB [akA, akB]) = true := by
  decide

theorem akFs_voll : ∀ g : akD.Fn, g ∈ akFs := fun g => by
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- The floor violation as the Prop: `StufenM` fails. -/
theorem ak2_nicht_stufen : ¬ StufenM akP2 := fun h =>
  absurd ((stufenB_iff akFs_voll).mpr h) (by rw [ak2_boden_falsch.2.1]; decide)

#print axioms Gabbro.Grammatik.akzeptiert_mehrfaden
#print axioms Gabbro.Grammatik.akzeptiert_verklemmung
#print axioms Gabbro.Grammatik.akzeptiert_rennfrei
#print axioms Gabbro.Grammatik.akzeptiert_zeit
#print axioms Gabbro.Grammatik.mP_akzeptiert
#print axioms Gabbro.Grammatik.mP_startZulaessig
#print axioms Gabbro.Grammatik.mP_ziel_aus_akzeptiert
#print axioms Gabbro.Grammatik.mP_verklemmung_aus_akzeptiert
#print axioms Gabbro.Grammatik.mTafel_doppelt_falsch
#print axioms Gabbro.Grammatik.gP_akzeptiert
#print axioms Gabbro.Grammatik.gP_als_starts
#print axioms Gabbro.Grammatik.gP_start_leer
#print axioms Gabbro.Grammatik.ak1_zwei_schreiber
#print axioms Gabbro.Grammatik.ak1_ein_schreiber
#print axioms Gabbro.Grammatik.ak2_boden_falsch
#print axioms Gabbro.Grammatik.ak2_nicht_stufen
#print axioms Gabbro.Grammatik.ak3_zwei_schreiber_ohne_lesen
#print axioms Gabbro.Grammatik.mP_rennfrei_aus_akzeptiert

end Gabbro.Grammatik
