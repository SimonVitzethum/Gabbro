/-
  File:      Grammatik/Korpus125.lean
  Subject:   THE G PROGRAM OF `beispiele/0125-read-under-lock.gab`, value-
             faithful: `lese_schreibe` returns the `z` it read under the lock.

  The source: `static mut z : u32 = 0`, lock `WACHE` protecting `z`,
  `lese_schreibe() -> u32` (`locks WACHE { let v = z; z = v; return z; }`),
  `setze_null()` (`locks WACHE { z = 0; }`), `concurrent` starts. G forms
  exist for the global (`Glob`/`gtyp` with the declared initializer as
  `sp0`), the lock, the `locks` blocks, the global reads (`Expr.glob`) and
  writes (`Stmt.assignGlob`), the `let` (`Block.bind`), a write to an outer
  local (`Stmt.assignVar`) and the starts.

  THE ONE DIVERGENCE OF FORM: a `return` INSIDE `locks WACHE` has no G term
  (`offen125_ret_unter_locks`: a return needs `Λ.Perm V.ende`, and inside
  the lock `Λ = [held WACHE]` while `ende = []`). The body below is
  `let r = 0; locks WACHE { let v = z; z = v; r = z; } return r;` -- the
  value `z` is read under the lock into an outer local and returned right
  after the release, which is what the source's `return z` inside the lock
  returns (the release is the only thing between the read and the return,
  and a release writes no carrier). This is the term review G02 (2026-09-21)
  found; fix lane F8 built it and re-proved every premise group on it, so
  the earlier reshaped body (constant `return 0`) and its `…_umgestaltet`
  names are gone. The Rust exporter still refuses the source shape (LG004,
  `tests/lean_g.rs::return_under_locks_stays_refused`): it has no rule that
  rewrites a return under a lock into this outer-local form -- a gap of the
  exporter, not of G.
-/
module
public import Grammatik.Korpus.Programme.Korpus125Basis
import all Grammatik.Korpus.Programme.Korpus125Basis
public import Grammatik.Zielsatz.Kern.Proben
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


namespace Gabbro.Grammatik

namespace K125
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
  · exact (nomatch t)
  · cases g; simp only [kCs, List.mem_cons, List.not_mem_nil, or_false]

/-- **The checker accepts the program** with its declared starts
    `lese_schreibe`, `setze_null` (the `concurrent` members). -/
theorem kP_akzeptiert : Akzeptiert kP kSI kFs [QLock.w] kCs [kLese, kSetzeNull] [] = true := by decide

/-! ## 3. The blocking facts, proved -/

/-- `lese_schreibe` holds nothing by signature, so its end holdings are `[]`. -/
theorem kEndeLese : (vertragVon kD kLese).ende = [] := by rfl

/-- **A return INSIDE `locks WACHE` has no G term**: it would need
    `[held WACHE].Perm []` (the `hΛ` of `Stmt.ret` at `Λ = [held WACHE]`
    against `ende = []`), which is uninhabited. This is a fact about the
    FORM only: the value is returned through an outer local (`kRumpfLese`). -/
theorem offen125_ret_unter_locks :
    ¬ (([Res.held (D := kD) QLock.w] : List (Res kD)).Perm (vertragVon kD kLese).ende) := by
  rw [kEndeLese]
  intro h
  have := List.Perm.length_eq h
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.succ_ne_self] at this

/-- **No guarded read outside the lock**: `z` is shared and guarded, so
    `gdarf z []` is uninhabited -- the value must be read inside the lock
    and carried out in a local, as `kRumpfLese` does. -/
theorem offen125_lese_aussen : ¬ gdarf kD QGlob.z [] := by
  intro h
  have h2 : Res.held (D := kD) QLock.w ∈ ([] : List (Res kD)) :=
    h _ (List.mem_singleton.mpr rfl)
  simp only [List.not_mem_nil] at h2

/-- What stays open for 125: the Rust EXPORTER's form, not G's. The source's
    `return z` inside `locks WACHE` is refused by `lean_g.rs` (LG004); the
    hand term `kRumpfLese` shows the G program exists. -/
def offen125 : String :=
  "lese_schreibe returns z inside locks WACHE: the exporter refuses it (LG004); the G term via an outer local exists (kRumpfLese)"

/-! ## 4. The user obligations -/

/-- Every `requires` is `.tru`, at every function, world and environment. -/
theorem kReqWahr (f : kD.Fn) (W : World kD) (ρ : Env kD (kD.params f)) :
    ReqAmEintritt kP f W ρ := by rfl

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
    simp only [↓reduceIte, reduceCtorEq] at hrun
  · rw [hr] at hrun
    simp only [kRumpfSetzeNull, execEndH] at hrun
    erw [execStmtH_locks_eins] at hrun
    simp only [freiH, kSI, execStmtH] at hrun
    simp only [↓reduceIte, reduceCtorEq] at hrun

/-- `locks L { body }` for an arbitrary body block: take `L`, run the body,
    release (the general form of `execStmtH_locks_eins`). -/
theorem execStmtH_locks_blk {S : SperrInv kD} {O : Orakel kD} {U : Umwelt kD}
    {passes : Nat} {R : ∀ f : kD.Fn, World kD → Env kD (kD.params f) → RufAusgang f}
    {V : Vertrag kD} {l : Bool} {Γ : Ctx} {Λ : List (Res kD)} (L : kD.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → kD.rang M < kD.rang L)
    (b : Block kD V l Γ (Res.held L :: Λ) (Res.held L :: Λ)) (σ : World kD) (ρ : Env kD Γ) :
    execStmtH S O U passes R (Stmt.locks L hr b) σ ρ =
      freiH S L (execBlockH S O U passes R b ((U L σ).nimmt L) ρ) := by rfl

theorem kP_koerper_lese : KoerperGutS kP 0 (axWahr kD) kSI kLese := by
  have hr : kP.rumpf kLese = kRumpfLese := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rfl
  · rw [hr] at hrun
    simp only [kRumpfLese, execEndH] at hrun
    erw [execStmtH_locks_blk] at hrun
    simp only [freiH, kSI, execStmtH, execBlockH] at hrun
    simp only [EndAusgang.schrumpf, Ausgang.schrumpf, ↓reduceIte, reduceCtorEq] at hrun
  · rw [hr] at hrun
    simp only [kRumpfLese, execEndH] at hrun
    erw [execStmtH_locks_blk] at hrun
    simp only [freiH, kSI, execStmtH, execBlockH] at hrun
    simp only [EndAusgang.schrumpf, Ausgang.schrumpf, ↓reduceIte, reduceCtorEq] at hrun

theorem kP_koerper : ∀ f : kD.Fn, KoerperGutS kP 0 (axWahr kD) kSI f := by
  intro f
  cases f
  · exact kP_koerper_lese
  · exact kP_koerper_setzeNull

theorem kP_inv : ∀ f : kD.Fn, InvGutS kP 0 (axWahr kD) kSI f :=
  fun _ => invGutS_ohne fun i _ => (nomatch i)

theorem kP_ohneEwig : ohneEwigB kP kFs = true := by decide

theorem kP_koerper_alle : ∀ (passes : Nat) (f : kD.Fn), KoerperGutS kP passes (axWahr kD) kSI f :=
  koerperGutS_alle kFs_voll kP_ohneEwig kP_koerper

theorem kP_inv_alle : ∀ (passes : Nat) (f : kD.Fn), InvGutS kP passes (axWahr kD) kSI f :=
  invGutS_alle kFs_voll kP_ohneEwig kP_inv

/-! ## 5. The program as one declaration -/

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

/-- **`beispiele/125` as ONE declaration**: code `kP`, lock family `kSI`,
    no axiom, declared starts `lese_schreibe` and `setze_null` (the
    `concurrent` members), initial memory `z = 0` as declared. -/
def kE : Zielsatz.Einheit kD := ⟨kP, kSI, axWahr kD, [⟨kLese, .nil⟩, ⟨kSetzeNull, .nil⟩], kSp, [], []⟩

/-- **The user's premise group on `beispiele/125`.** -/
theorem korpus125_nutzer : Zielsatz.NutzerPflicht kE :=
  ⟨⟨fun passes f => ⟨kP_koerper_alle passes f, kP_inv_alle passes f,
      invGutGrund_ohneGrund (by cases f <;> rfl)⟩, fun _ _ _ _ => rfl, axEnsLokal_wahr, ptrVerfeinert_trivial (fun f _ _ => by cases f <;> rfl) (fun _ => rfl)⟩,
    ⟨fun _ => rfl, fun a ha => by
      simp only [kE, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> rfl⟩⟩

/-- No axiom, no register: the oracle sees no global (the global is a
    carrier, not a device); nothing awaits, so visibility is constantly
    false. -/
def kO : Orakel kD where
  wirkt := fun a => (nomatch a)
  regLies := fun r => (nomatch r)
  regSchreib := fun r _ => (nomatch r)
  sichtbar := fun _ _ => false

theorem kO_gut : GutO kO := fun a => (nomatch a)

theorem kO_lokal : RegLokal kO := ⟨(fun r _ _ _ => nomatch r), (fun g σ σ' _ => rfl)⟩

theorem kO_hw [RootNativeFloat.Hardware] : Zielsatz.HardwareAnnahmen kO kE.Q :=
  ⟨kO_gut, kO_lokal, axVertragO_wahr kO, inferInstance⟩

theorem kE_akzeptiert : akzeptiert_pruefer.akzeptiert kE kFs [QLock.w] kCs = true :=
  (by show Akzeptiert kP kSI kFs [QLock.w] kCs [kLese, kSetzeNull] [] = true; exact kP_akzeptiert)

/-- **The goal theorem on the 125 program** -- `gabbro_ziel` with
    the concrete checker. -/
theorem korpus125_ziel (O : Orakel kD) (hO : Zielsatz.HardwareAnnahmen O kE.Q)
    (passes : Nat)
    (sp : Speicher kD.mitRuhe)
    (init : Faden → Σ f : kD.mitRuhe.Fn, Env kD.mitRuhe (kD.mitRuhe.params f))
    (hL : Zielsatz.Laufzeit kE sp init) (M : RufMaschineG kD.mitRuhe)
    (hM : RufErreichbarG kE.P.mitRuhe O.mitRuhe passes (RufStartG kE.P.mitRuhe sp init) M) :
    Zielsatz.Ziel kE.P.mitRuhe kE.S.mitRuhe O.mitRuhe passes (RufStartG kE.P.mitRuhe sp init) M :=
  Zielsatz.gabbro_ziel_g akzeptiert_pruefer kD kE ⟨kFs, kFs_voll⟩ ⟨[QLock.w], kLocks_voll⟩ ⟨kCs, kCs_voll⟩
    kE_akzeptiert korpus125_nutzer O hO passes sp init hL M hM

/-- **Witness** (rule 13): the premise group jointly with two
    non-degenerate runs from the `z = 5` world -- `setze_null`'s body returns
    with `z = 0` (a memory-changing step), and `lese_schreibe`'s body returns
    the VALUE `5` it read under the lock, with `z` still `5` (the writeback
    `z = v` rewrote the same value). The second run is what the reshaped
    body of lane 203 could not show: it returned `0` whatever `z` held. -/
theorem korpus125_nutzer_zeuge
    (R : ∀ f : kD.Fn, World kD → Env kD (kD.params f) → RufAusgang f) :
    Zielsatz.NutzerPflicht kE ∧ (∃ (σ' : World kD) (v : ErgVal kD (kD.erg kSetzeNull)),
      execEndH kSI kO (fun _ σ => σ) 0 R kRumpfSetzeNull (kSp5.welt []) .nil = .zurueck σ' v ∧
      (σ'.globs QGlob.z).n = 0 ∧ ((kSp5.welt []).globs QGlob.z).n = 5) ∧
    ∃ (σ' : World kD) (v : ErgVal kD (kD.erg kLese)),
      execEndH kSI kO (fun _ σ => σ) 0 R kRumpfLese (kSp5.welt []) .nil = .zurueck σ' v ∧
      v = ⟨5, by decide, by decide⟩ ∧ (σ'.globs QGlob.z).n = 5 :=
  ⟨korpus125_nutzer, ⟨_, _, rfl, rfl, rfl⟩, _, _, rfl, rfl, rfl⟩

/-
  CUTS: the model's `lese_schreibe` returns through an outer local after the
  release instead of from inside the lock (`offen125_ret_unter_locks`: no G
  form for the latter); the value is the same (`korpus125_nutzer_zeuge`,
  second run). The source's `let v = z; z = v` is kept as is. What is NOT
  claimed: anything about the `.gab` source text (no exporter link -- the
  exporter refuses 125 with LG004, `offen125`), and no stage-(b) simulation
  certificate. The witness runs are body runs, not machine runs from the
  declared starts (review G02 F5).
-/
#print axioms K125.kP_akzeptiert
#print axioms K125.korpus125_nutzer
#print axioms K125.korpus125_ziel
#print axioms K125.korpus125_nutzer_zeuge
#print axioms K125.offen125_ret_unter_locks
#print axioms K125.offen125_lese_aussen

end K125

end Gabbro.Grammatik
