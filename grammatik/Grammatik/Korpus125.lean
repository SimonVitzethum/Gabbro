/-
  File:      Grammatik/Korpus125.lean
  Subject:   THE G PROGRAM OF `beispiele/125-read-under-lock.gab`, attempted
             faithfully, with the exact blocking fact proved.

  The source: `static mut z : u32 = 0`, lock `WACHE` protecting `z`,
  `lese_schreibe() -> u32` (`locks WACHE { let v = z; z = v; return z; }`),
  `setze_null()` (`locks WACHE { z = 0; }`), `concurrent` starts. G forms
  exist for the global (`Glob`/`gtyp` with the declared initializer as
  `sp0`), the lock, the `locks` blocks, the global reads (`Expr.glob`) and
  writes (`Stmt.assignGlob`), the `let` (`Block.bind`) and the starts.

  THE BLOCKING FACT (proved as `offen125_ret_unter_locks` below, not
  asserted): the source's `return z` sits INSIDE `locks WACHE`, but a return
  needs `hΛ : Λ.Perm V.ende`, and `Vertrag.ende` is
  `V.haelt.map Res.held ++ …` (`Syntax.lean`) -- for `lese_schreibe`, whose
  signature holds nothing, `ende = []`, while inside the lock
  `Λ = [held WACHE]`. `[held W].Perm []` is uninhabited (`Perm.length_eq`),
  so no faithful body term exists. This is the G-side face of the exporter
  refusal LG004 (`lean_g.rs`: value readers under `locks` refused by name;
  the `Export108.lean` header records the same wall for the refused 108 root
  shape). Either the example moves its `return` out of the lock (corpus
  change, lane 204's territory) or G gains a form for value-return under
  lock. Until then the file carries the CLOSEST expressible program --
  `lese_schreibe` with the writeback inside and the `return z` outside --
  with premise groups proved on THAT program under honest
  `…_umgestaltet` names, never as `korpus125_nutzer`.
-/
import Grammatik.Zielsatz.Proben

namespace Gabbro.Grammatik

namespace K125

/-- The source declares no tables. -/
inductive QGlob where
  | z
  deriving DecidableEq

/-- Lock `WACHE` (rank 0, protects `z`). -/
inductive QLock where
  | w
  deriving DecidableEq

/-- Functions `lese_schreibe` and `setze_null`. -/
inductive QFn where
  | lese
  | setzeNull
  deriving DecidableEq

/-- A signature: result, written globals. Neither function holds a lock by
    signature (the source has no `requires Held`); both take `WACHE` in the
    body. -/
def kSig (e : Option Ty) (gs : List QGlob) :
    Signatur Empty QGlob QLock Empty where
  params := []
  erg := e
  gruende := 0
  haelt := []
  schreibt := fun t => nomatch t
  gschreibt := fun g => decide (g ∈ gs)
  konsumiert := []
  produziert := []

def kSigNr : Nat → Signatur Empty QGlob QLock Empty
  | 0 => kSig (some (.int 0 4294967295)) [.z]
  | 1 => kSig none [.z]
  | _ => kSig none []

def kSigOf : QFn → Nat
  | .lese => 0
  | .setzeNull => 1

/-- The declaration of `beispiele/125`: global `z = u32`, shared, guarded by
    `WACHE`; no tables, no table invariant, no axiom, no register. -/
def kD : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun e => nomatch e
  Feld := fun e => nomatch e
  decFeld := fun e => nomatch e
  typ := fun e => nomatch e
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => none
  Glob := QGlob
  decGlob := inferInstance
  gtyp := fun _ => .int 0 4294967295
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun e => nomatch e
  ggeteilt := fun _ => true
  Lock := QLock
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun e => nomatch e
  gbraucht := fun _ => [.inl QLock.w]
  eigner := fun e => nomatch e
  Fn := QFn
  sig := kSigOf
  sigNr := kSigNr
  eigner_nie_erzeugt := fun _ t _ _ _ => nomatch t
  Inv := Empty
  traeger := fun i => nomatch i
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
  geteilt_bewacht := fun e => nomatch e
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g _ => by cases g; exact Or.inl (by decide)

def kLese : kD.Fn := QFn.lese
def kSetzeNull : kD.Fn := QFn.setzeNull

instance : DecidableEq kD.Fn := inferInstanceAs (DecidableEq QFn)
instance : DecidableEq kD.Lock := inferInstanceAs (DecidableEq QLock)
instance : DecidableEq kD.Glob := inferInstanceAs (DecidableEq QGlob)

abbrev kLW : List (Res kD) := [Res.held (D := kD) QLock.w]

theorem kGdarfW : gdarf kD QGlob.z kLW := by
  intro w h
  change w ∈ ([Sum.inl QLock.w] : List (QLock ⊕ (Empty × Nat))) at h
  have e : w = Sum.inl QLock.w := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

/-- `0 : u32`, the constant `setze_null` writes. -/
def kNull {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (.int 0 4294967295) :=
  .weiter (by decide) (by decide) (.lit 0)

/-- `setze_null()`: `locks WACHE { z = 0; }` -- exactly the source body. -/
def kRumpfSetzeNull : Endblock kD (vertragVon kD kSetzeNull) false [] [] :=
  .cons (.locks QLock.w (fun _ h => nomatch h)
    (.cons (.assignGlob QGlob.z kNull rfl kGdarfW) .nil))
    (.ret .keine List.Perm.nil)

/-- `lese_schreibe` RESHAPED: the writeback `z = z` inside `locks WACHE`,
    `return 0` outside. The source returns `z` inside; that term does not
    exist (`offen125_ret_unter_locks` below), and a guarded read outside the
    lock is untypeable too (`offen125_lese_aussen`), so the reshaped return
    is a constant. Both divergences are findings, not silent changes. -/
def kRumpfLese : Endblock kD (vertragVon kD kLese) false [] [] :=
  .cons (.locks QLock.w (fun _ h => nomatch h)
    (.cons (.assignGlob QGlob.z (.glob QGlob.z kGdarfW) rfl kGdarfW) .nil))
    (.ret (.wert kNull) List.Perm.nil)

/-- **The program of `beispiele/125`** with the reshaped `lese_schreibe`;
    trivial contracts (the source declares no `requires`/`ensures`). -/
def kP : Programm kD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf
    | .lese => kRumpfLese
    | .setzeNull => kRumpfSetzeNull

def kFs : List kD.Fn := [kLese, kSetzeNull]

theorem kFs_voll : ∀ g : kD.Fn, g ∈ kFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

/-- **The lock family**: `WACHE` protects `z`; the source declares no
    invariant, so it is trivially true. -/
def kSI : SperrInv kD :=
  ⟨fun _ => [.inr QGlob.z], fun _ _ => true⟩

theorem kSI_ok : SperrInvOk kSI := by
  refine ⟨fun L c hc => ?_, fun L s s' h => rfl⟩
  · cases L
    have e : c = .inr QGlob.z := List.mem_singleton.mp hc
    subst e
    change Sum.inl QLock.w ∈ ([Sum.inl QLock.w] : List (QLock ⊕ (Empty × Nat)))
    exact List.mem_singleton.mpr rfl

theorem kLocks_voll : ∀ L : kD.Lock, L ∈ ([QLock.w] : List kD.Lock) := fun L => by
  cases L
  exact List.mem_singleton_self _

def kCs : List (kD.Tab ⊕ kD.Glob) := [.inr QGlob.z]

theorem kCs_voll : ∀ c : kD.Tab ⊕ kD.Glob, c ∈ kCs := fun c => by
  rcases c with t | g
  · exact nomatch t
  · cases g; simp [kCs]

/-- **The checker accepts the reshaped program** with its declared starts
    `lese_schreibe`, `setze_null` (the `concurrent` members). -/
theorem kP_akzeptiert : Akzeptiert kP kSI kFs [QLock.w] kCs [kLese, kSetzeNull] = true := by decide

/-! ## 3. The blocking facts, proved -/

/-- `lese_schreibe` holds nothing by signature, so its end holdings are `[]`. -/
theorem kEndeLese : (vertragVon kD kLese).ende = [] := rfl

/-- **No faithful `lese_schreibe` body exists**: a return inside
    `locks WACHE` would need `[held WACHE].Perm []` (the `hΛ` of `Stmt.ret`
    at `Λ = [held WACHE]` against `ende = []`), which is uninhabited. -/
theorem offen125_ret_unter_locks :
    ¬ (([Res.held (D := kD) QLock.w] : List (Res kD)).Perm (vertragVon kD kLese).ende) := by
  rw [kEndeLese]
  intro h
  have := List.Perm.length_eq h
  simp at this

/-- **No guarded read outside the lock**: `z` is shared and guarded, so
    `gdarf z []` is uninhabited -- the reshaped `return 0` cannot read `z`. -/
theorem offen125_lese_aussen : ¬ gdarf kD QGlob.z [] := by
  intro h
  have h2 : Res.held (D := kD) QLock.w ∈ ([] : List (Res kD)) :=
    h _ (List.mem_singleton.mpr rfl)
  simp at h2

/-- Named open premise for the corpus decision (lane 204's territory): the
    source-shape `return z` inside `locks WACHE` has no G term until the
    example moves it out or G gains value-return under lock. -/
def offen125 : String :=
  "lese_schreibe returns z inside locks WACHE: no G term (offen125_ret_unter_locks); move the return out or add the form"

/-! ## 4. The user obligations on the reshaped program -/

/-- Every `requires` is `.wahr`, at every function, world and environment. -/
theorem kReqWahr (f : kD.Fn) (W : World kD) (ρ : Env kD (kD.params f)) :
    ReqAmEintritt kP f W ρ := rfl

theorem kP_koerper_setzeNull : KoerperGutS kP 0 (axWahr kD) kSI kSetzeNull := by
  have hr : kP.rumpf kSetzeNull = kRumpfSetzeNull := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [kRumpfSetzeNull, execEndH, execStmtH, execBlockH, freiH, kSI] at hrun
    cases hrun
    rfl
  · rw [hr] at hrun
    simp only [kRumpfSetzeNull, execEndH] at hrun
    erw [execStmtH_locks_eins] at hrun
    simp only [freiH, kSI, execStmtH] at hrun
    simp at hrun
  · rw [hr] at hrun
    simp only [kRumpfSetzeNull, execEndH] at hrun
    erw [execStmtH_locks_eins] at hrun
    simp only [freiH, kSI, execStmtH] at hrun
    simp at hrun

theorem kP_koerper_lese : KoerperGutS kP 0 (axWahr kD) kSI kLese := by
  have hr : kP.rumpf kLese = kRumpfLese := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [kRumpfLese, execEndH, execStmtH, execBlockH, freiH, kSI] at hrun
    cases hrun
    rfl
  · rw [hr] at hrun
    simp only [kRumpfLese, execEndH] at hrun
    erw [execStmtH_locks_eins] at hrun
    simp only [freiH, kSI, execStmtH] at hrun
    simp at hrun
  · rw [hr] at hrun
    simp only [kRumpfLese, execEndH] at hrun
    erw [execStmtH_locks_eins] at hrun
    simp only [freiH, kSI, execStmtH] at hrun
    simp at hrun

theorem kP_koerper : ∀ f : kD.Fn, KoerperGutS kP 0 (axWahr kD) kSI f := by
  intro f
  cases f
  · exact kP_koerper_lese
  · exact kP_koerper_setzeNull

theorem kP_inv : ∀ f : kD.Fn, InvGutS kP 0 (axWahr kD) kSI f :=
  fun _ => invGutS_ohne fun i _ => nomatch i

theorem kP_ohneEwig : ohneEwigB kP kFs = true := by decide

theorem kP_koerper_alle : ∀ (passes : Nat) (f : kD.Fn), KoerperGutS kP passes (axWahr kD) kSI f :=
  koerperGutS_alle kFs_voll kP_ohneEwig kP_koerper

theorem kP_inv_alle : ∀ (passes : Nat) (f : kD.Fn), InvGutS kP passes (axWahr kD) kSI f :=
  invGutS_alle kFs_voll kP_ohneEwig kP_inv

/-! ## 5. The reshaped program as one declaration -/

/-- No tables: every slot function is vacuous. -/
theorem kTabLeer (t : kD.Tab) : False := by cases t

def kSlots : ∀ t : kD.Tab, Int → ∀ f : kD.Feld t, Wert kD (kD.typ t f) :=
  fun t => False.elim (kTabLeer t)

/-- The start memory: the declared initializer `z = 0`. -/
def kSp : Speicher kD :=
  ⟨kSlots, fun _ => ⟨0, by decide, by decide⟩⟩

/-- A world with `z = 5` (for the memory-changing witness run). -/
def kSp5 : Speicher kD :=
  ⟨kSlots, fun _ => ⟨5, by decide, by decide⟩⟩

/-- **`beispiele/125` as ONE declaration, reshaped**: code `kP` (with the
    reshaped `lese_schreibe`), lock family `kSI`, no axiom, declared starts
    `lese_schreibe` and `setze_null` (the `concurrent` members), initial
    memory `z = 0` as declared. -/
def kE : Zielsatz.Einheit kD := ⟨kP, kSI, axWahr kD, [⟨kLese, .nil⟩, ⟨kSetzeNull, .nil⟩], kSp⟩

/-- The premise group on the RESHAPED program -- honestly named, never
    `korpus125_nutzer`: the source-shape group stays open (`offen125`). -/
theorem korpus125_nutzer_umgestaltet : Zielsatz.NutzerPflicht kE :=
  ⟨⟨fun passes f => ⟨kP_koerper_alle passes f, kP_inv_alle passes f,
      invGutGrund_ohneGrund (by cases f <;> rfl)⟩, fun _ _ _ _ => rfl, axEnsLokal_wahr⟩,
    ⟨fun _ => rfl, fun a ha => by
      simp only [kE, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> rfl⟩⟩

/-- No axiom, no register: the oracle sees no global (the global is a
    carrier, not a device); nothing awaits, so visibility is constantly
    false. -/
def kO : Orakel kD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun _ _ => false

theorem kO_gut : GutO kO := fun a => nomatch a

theorem kO_lokal : RegLokal kO := ⟨(fun r _ _ _ => nomatch r), (fun g σ σ' _ => rfl)⟩

theorem kO_hw : Zielsatz.HardwareAnnahmen kO kE.Q := ⟨kO_gut, kO_lokal, axVertragO_wahr kO⟩

theorem kE_akzeptiert : akzeptiert_pruefer.akzeptiert kE kFs [QLock.w] kCs = true :=
  (by show Akzeptiert kP kSI kFs [QLock.w] kCs [kLese, kSetzeNull] = true; exact kP_akzeptiert)

/-- **The goal theorem on the reshaped 125 program** -- `gabbro_ziel` with
    the concrete checker. -/
theorem korpus125_ziel_umgestaltet (O : Orakel kD) (hO : Zielsatz.HardwareAnnahmen O kE.Q)
    (passes : Nat)
    (sp : Speicher kD.mitRuhe)
    (init : Faden → Σ f : kD.mitRuhe.Fn, Env kD.mitRuhe (kD.mitRuhe.params f))
    (hL : Zielsatz.Laufzeit kE sp init) (M : RufMaschineG kD.mitRuhe)
    (hM : RufErreichbarG kE.P.mitRuhe O.mitRuhe passes (RufStartG kE.P.mitRuhe sp init) M) :
    Zielsatz.Ziel kE.P.mitRuhe kE.S.mitRuhe O.mitRuhe passes (RufStartG kE.P.mitRuhe sp init) M :=
  Zielsatz.gabbro_ziel akzeptiert_pruefer kD kE ⟨kFs, kFs_voll⟩ ⟨[QLock.w], kLocks_voll⟩ ⟨kCs, kCs_voll⟩
    kE_akzeptiert korpus125_nutzer_umgestaltet O hO passes sp init hL
    (cloneAssume_empty _ _ _ _) M hM

/-- **Witness for the reshaped group** (rule 13): the premise group jointly
    with a non-degenerate run -- `setze_null`'s body from the `z = 5` world
    returns with `z = 0`: a reached run with a memory-changing step, on the
    table... the global a function writes. -/
theorem korpus125_nutzer_umgestaltet_zeuge
    (R : ∀ f : kD.Fn, World kD → Env kD (kD.params f) → RufAusgang f) :
    Zielsatz.NutzerPflicht kE ∧ ∃ (σ' : World kD) (v : ErgVal kD (kD.erg kSetzeNull)),
      execEndH kSI kO (fun _ σ => σ) 0 R kRumpfSetzeNull (kSp5.welt []) .nil = .zurueck σ' v ∧
      (σ'.globs QGlob.z).n = 0 ∧ ((kSp5.welt []).globs QGlob.z).n = 5 :=
  ⟨korpus125_nutzer_umgestaltet, _, _, rfl, rfl, rfl⟩

/-
  CUTS: the source-shape `lese_schreibe` (value `return` inside `locks
  WACHE`) has no G term -- proved (`offen125_ret_unter_locks`), named gap
  `offen125`. The file proves the full premise groups only for the reshaped
  program (return moved out, constant -- a guarded read outside is
  untypeable, `offen125_lese_aussen`). What is NOT claimed: `korpus125_nutzer`
  on the source shape (open), anything about the `.gab` source text (no
  exporter link -- lane 201), and no stage-(b) simulation certificate.
-/
#print axioms K125.kP_akzeptiert
#print axioms K125.korpus125_nutzer_umgestaltet
#print axioms K125.korpus125_ziel_umgestaltet
#print axioms K125.korpus125_nutzer_umgestaltet_zeuge
#print axioms K125.offen125_ret_unter_locks
#print axioms K125.offen125_lese_aussen

end K125

end Gabbro.Grammatik
