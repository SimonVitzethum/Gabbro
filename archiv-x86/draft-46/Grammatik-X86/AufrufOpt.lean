/-
  File:      Grammatik/X86/AufrufOpt.lean
  Subject:   CALL-LOG OBLIGATIONS FOR SOURCE INLINING (lane 310, wave-A follow-up).

  Selective inlining (IR-VALIDIERUNG.md §3.4) removes a physical call but must
  NOT drop the logged call, its contracts or the `FolgeG` order leg: the
  certificate carries a GHOST-EVENT reconstruction -- the inlined execution
  re-emits the callee entry/return pair (identity, actual arguments, actual
  result/reason, entry/return worlds) in source call-log order. This file
  states that obligation over the REAL source model (machine-G call logs
  `RufEreignisF`, `rufAt`, `RufSchrittG`; order `FolgeLog`/`FolgeG`) and proves
  the generic reconstruction lemmas. No new source syntax, no Spec change,
  no fake IR: every event below is a `RufEreignisF` with actual values.
-/
import Grammatik.RufMaschineG
import Grammatik.Folge
import Grammatik.Semantik
import Grammatik.ZielOrtEinfadenZeuge
import Grammatik.FolgeBeweis
import Grammatik.FolgeZeuge

namespace Gabbro.Grammatik.X86

variable {D : Deklaration}

/-- A ghost answer of an inlined call: the value case or the reason channel. -/
inductive GeistAntwort (D : Deklaration) (g : D.Fn) where
  | ok (v : ErgVal D (D.erg g)) (s1 : World D)
  | grund (r : Fin (D.gruende g)) (s1 : World D)

/-- The ghost pair of one inlined call, newest first: return over entry. -/
def geistPaar (g : D.Fn) (rho : Env D (D.params g)) (s0 : World D) :
    GeistAntwort D g → List (RufEreignisF D)
  | .ok v s1 =>
    [RufEreignisF.rueck g rho v s0 s1, RufEreignisF.eintritt g rho s0]
  | .grund r s1 =>
    [RufEreignisF.grund g rho r s0 s1, RufEreignisF.eintritt g rho s0]

/-- The ghost pair has exactly two events. -/
theorem geistPaar_laenge (g : D.Fn) (rho : Env D (D.params g)) (s0 : World D)
    (a : GeistAntwort D g) : (geistPaar g rho s0 a).length = 2 := by
  cases a <;> rfl

/-! ## 1. Ghost pairs preserve the call-log order.

    An inlined call disappears physically but its ghost pair (return over
    entry, with the ACTUAL `rho`/`v`/`s0`/`s1`) is spliced back into the
    thread log at the inline site. The two lemmas below are the checked
    reconstruction for the value and the reason channel: prepending the
    pair preserves `FolgeLog` exactly under the armed side conditions the
    surrounding log must satisfy. No trace equality is assumed: every
    premise is a computed `Bool` (`Pflichtig`/`Armiert`) or a `FolgeLog`
    of the physical log. -/

/-- VALUE CHANNEL: splicing the ghost pair over a physical log preserves
    the order leg under the armed side conditions. -/
theorem geistRekon_folge (Φ : Folge D) (g : D.Fn)
    (rho : Env D (D.params g)) (s0 s1 : World D) (v : ErgVal D (D.erg g))
    (rest : List (RufEreignisF D))
    (hord1 : rest ≠ [] →
      Pflichtig Φ (RufEreignisF.eintritt g rho s0) = true →
      Armiert Φ rest = true)
    (hrest : FolgeLog Φ rest)
    (hord2 : (RufEreignisF.eintritt g rho s0 :: rest) ≠ [] →
      Pflichtig Φ (RufEreignisF.rueck g rho v s0 s1) = true →
      Armiert Φ (RufEreignisF.eintritt g rho s0 :: rest) = true) :
    FolgeLog Φ (RufEreignisF.rueck g rho v s0 s1 ::
      RufEreignisF.eintritt g rho s0 :: rest) :=
  ⟨hord2, hord1, hrest⟩

/-- REASON CHANNEL: the same splice for a return through `grund`. -/
theorem geistRekon_folge_grund (Φ : Folge D) (g : D.Fn)
    (rho : Env D (D.params g)) (s0 s1 : World D) (r : Fin (D.gruende g))
    (rest : List (RufEreignisF D))
    (hord1 : rest ≠ [] →
      Pflichtig Φ (RufEreignisF.eintritt g rho s0) = true →
      Armiert Φ rest = true)
    (hrest : FolgeLog Φ rest)
    (hord2 : (RufEreignisF.eintritt g rho s0 :: rest) ≠ [] →
      Pflichtig Φ (RufEreignisF.grund g rho r s0 s1) = true →
      Armiert Φ (RufEreignisF.eintritt g rho s0 :: rest) = true) :
    FolgeLog Φ (RufEreignisF.grund g rho r s0 s1 ::
      RufEreignisF.eintritt g rho s0 :: rest) :=
  ⟨hord2, hord1, hrest⟩

/-! ## 2. Every machine step is log-silent or one real call/return event.

    Only pushes and pops touch the call log; every unfold, leaf and
    bookkeeping step is log-silent. Hence an inlined body -- which unfolds
    to exactly such silent steps -- contributes NO physical log event, and
    the ghost pair of §1 is exactly what its reconstruction must re-emit:
    one `eintritt` with the actual arguments plus one `rueck`/`grund` with
    the actual answer. The classification below is proved by case analysis
    over the REAL step relation, never over a model of it. -/

/-- LOG CLASSIFICATION: one `RufSchrittG` step leaves the acting thread's
    log unchanged, or pushes exactly one entry, value-return or
    reason-return event with the actual values. -/
theorem rufSchrittG_logSchritt (P : Programm D) (O : Orakel D) (passes : Nat)
    (M M' : RufMaschineG D) (f : Faden)
    (h : RufSchrittG P O passes M f M') :
    (M'.faeden f).log = (M.faeden f).log ∨
    (∃ g rho s0, (M'.faeden f).log =
      RufEreignisF.eintritt g rho s0 :: (M.faeden f).log) ∨
    (∃ g rho v s0 s1, (M'.faeden f).log =
      RufEreignisF.rueck g rho v s0 s1 :: (M.faeden f).log) ∨
    (∃ g rho r s0 s1, (M'.faeden f).log =
      RufEreignisF.grund g rho r s0 s1 :: (M.faeden f).log) := by
  cases h <;> simp only [rufUpdateG_self] <;> first
    | exact Or.inl trivial
    | exact Or.inr (Or.inl ⟨_, _, _, rfl⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, rfl⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, rfl⟩))

/-! ## 3. The inline obligation: what the certificate must exhibit.

    Replacing a direct call of `g` by its body is legal only with the SAME
    checks the call would have faced: the lock/resource discipline (`hp`,
    carried by both `Stmt.call` and `RufSchrittG.ruf`), the empty error
    channel (`hr`), and the contract duties at their places with the ACTUAL
    values -- `requires` over the actual argument environment at entry,
    `ensures` over the actual result between the entry and return worlds.
    Asserting identical contracts without these values is refused. -/

/-- INLINE OBLIGATION for replacing a direct call of `g` (from `caller`
    under holdings `Λ`) by its body, with the actual call data. -/
structure InlinePflicht (P : Programm D) (caller g : D.Fn) (Λ : List (Res D)) where
  hp : RufPasst D (vertragVon D caller) (D.signatur g) Λ
  hr : D.gruende g = 0
  rho : Env D (D.params g)
  s0 : World D
  s1 : World D
  val : ErgVal D (D.erg g)
  vorOk : wahr?
      (eval (s0.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte)
        (P.requires g)
        (s0.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) rho) =
      true
  nachOk : wahr?
      (eval (s0.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte)
        (P.ensures g)
        (s1.lese (vertragVon D g).ende (P.ensures g).orte)
        (ergEnv (D.erg g) val rho)) =
      true

/-- ENTRY DUTY: a successful `rufAt` outcome carries a true `requires`
    over the actual arguments -- the exact check the inlined site must
    re-emit as a ghost entry. -/
theorem rufAt_ok_vorOk (P : Programm D) (O : Orakel D) (passes n : Nat)
    (f : D.Fn) (σ : World D) (ρ : Env D (D.params f))
    (σ' : World D) (v : ErgVal D (D.erg f))
    (h : rufAt P O passes n f σ ρ = RufAusgang.ok σ' v) :
    wahr?
      (eval (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
        (P.requires f)
        (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ) =
      true := by
  cases n with
  | zero => simp [rufAt] at h
  | succ n =>
    simp only [rufAt] at h
    by_cases hc : wahr?
        (eval (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
          (P.requires f)
          (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
          ρ) = false
    · simp [hc] at h
    · cases hb : wahr?
          (eval (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
            (P.requires f)
            (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
            ρ) with
      | true => rfl
      | false => exact absurd hb hc

/-! ## 4. Joint witness on a non-degenerate source program.

    The fixture is the sequential program `eP` of ZielOrtEinfadenZeuge.lean
    (`setze` writes table `konto`, `pruefe` requires `konto[0] == 5`):
    on the reached five-step run (call `setze`, its write, its return,
    call `pruefe`, its return) the thread log holds the REAL ghost pair of
    `pruefe` -- entry over the return of `setze` -- with the actual argument
    environments, result and worlds; the start left `konto[0]` at `0` and
    the entry world carries `5`; the ghost pair built from the logged
    values is the logged pair; the orderedness side conditions hold with
    the value `true`; and the order leg holds there by the theorem. -/

/-- JOINT WITNESS: the ghost pair, the contract value, the memory change
    and the order leg co-occur on a reached run of a table-writing
    source program. -/
theorem geistRekon_zeuge : ∃ M : RufMaschineG eD,
    RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M ∧
    (eSp.slots () 0 ()).n = 0 ∧
    (eD.signatur eSetze).schreibt () = true ∧
    ∃ (rhoP : Env eD (eD.params ePruefe)) (wP bP : World eD)
      (vP : ErgVal eD (eD.erg ePruefe))
      (rhoS : Env eD (eD.params eSetze)) (vS : ErgVal eD (eD.erg eSetze))
      (aS bS : World eD) (rest : List (RufEreignisF eD)),
      (M.faeden 0).log = RufEreignisF.rueck ePruefe rhoP vP wP bP ::
        RufEreignisF.eintritt ePruefe rhoP wP ::
        RufEreignisF.rueck eSetze rhoS vS aS bS :: rest ∧
      (wP.slots () 0 ()).n = 5 ∧
      geistPaar ePruefe rhoP wP (.ok vP bP) =
        [RufEreignisF.rueck ePruefe rhoP vP wP bP,
         RufEreignisF.eintritt ePruefe rhoP wP] ∧
      Pflichtig Φ50 (RufEreignisF.eintritt ePruefe rhoP wP) = true ∧
      Armiert Φ50 (RufEreignisF.rueck eSetze rhoS vS aS bS :: rest) = true ∧
      FolgeLog Φ50 (M.faeden 0).log := by
  have h00 : (RufStartG eP eSp eInit).faeden 0 = ⟨[], ⟨eHaupt, .nil, eSp.welt [],
      ⟨false, [], [], .nil, .ende eRumpfHaupt⟩⟩, [],
      [RufEreignisF.eintritt eHaupt .nil (eSp.welt [])]⟩ := rfl
  have hoff0 : offen ((RufStartG eP eSp eInit).faeden 0).spur = [] := rfl
  obtain ⟨M1, s1, hZ1⟩ := w_rufEnde (P := eP) (O := eO) (passes := 0) h00 eSetze .nil eHpSetze rfl
    (.cons (.call ePruefe .nil eHpPruefe rfl) (.ret .keine List.Perm.nil)) .nil rfl (ehg0 hoff0).heldIn
  have hoff1 : offen (M1.faeden 0).spur = [] := by
    rw [hZ1.spur, (Erw.lese _ _ _).offen]; exact hoff0
  obtain ⟨M2, s2, hZ2⟩ := w_blatt (P := eP) (O := eO) (passes := 0) hZ1.1
    _ _ _ rfl rfl (ehg0 (eoff_z hZ1 hoff1)).heldIn _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff2 : offen (M2.faeden 0).spur = [] := by
    rw [hZ2.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans hoff1
  obtain ⟨M3, s3, hG3⟩ := w_rueckP (P := eP) (O := eO) (passes := 0) hZ2.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (ehg0 (eoff_z hZ2 hoff2)).heldIn
  have hoff3 : offen (M3.faeden 0).spur = [] := by
    rw [hG3.1]
    exact ((Erw.lese _ _ _).offen).trans hoff2
  obtain ⟨M4, s4, hZ4⟩ := w_rufEnde (P := eP) (O := eO) (passes := 0) hG3.1 ePruefe .nil eHpPruefe
    rfl (.ret .keine List.Perm.nil) .nil rfl (ehg0 (eoff_g hG3 hoff3)).heldIn
  have hoff4 : offen (M4.faeden 0).spur = [] := by
    rw [hZ4.spur, (Erw.lese _ _ _).offen]; exact hoff3
  obtain ⟨M5, s5, hG5⟩ := w_rueckP (P := eP) (O := eO) (passes := 0) hZ4.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (ehg0 (eoff_z hZ4 hoff4)).heldIn
  have hr5 : RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M5 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1)
      s2) s3) s4) s5
  have hlog5 : ∃ (rhoP : Env eD (eD.params ePruefe)) (wP bP : World eD)
      (vP : ErgVal eD (eD.erg ePruefe))
      (rhoS : Env eD (eD.params eSetze)) (vS : ErgVal eD (eD.erg eSetze))
      (aS bS : World eD) (rest : List (RufEreignisF eD)),
      (M5.faeden 0).log = RufEreignisF.rueck ePruefe rhoP vP wP bP ::
        RufEreignisF.eintritt ePruefe rhoP wP ::
        RufEreignisF.rueck eSetze rhoS vS aS bS :: rest := by
    rw [hG5.1]
    exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
  obtain ⟨rhoP, wP, bP, vP, rhoS, vS, aS, bS, rest, hl5⟩ := hlog5
  have hm5 : RufEreignisF.eintritt ePruefe rhoP wP ∈ (M5.faeden 0).log := by
    rw [hl5]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have hreq5 := ((eP_zertifiziert M5 hr5).1 0 _ hm5).1 _ _ _ rfl
  refine ⟨M5, hr5, rfl, rfl, rhoP, wP, bP, vP, rhoS, vS, aS, bS, rest,
    hl5, of_decide_eq_true hreq5, rfl, rfl, rfl, ?_⟩
  have hfol := (folgeG_erreichbar eSp eInit hr5 Φ50 eP_folge50 0).1
  exact hfol

/- CUTS:
  - No executable source-body inline rewrite: there is no function splicing
    a callee body at a call site, hence no proved body-splice simulation
    (inlined steps against `rufAt`). What is proved instead is CHECKED
    GHOST RECONSTRUCTION: the exact pair to re-emit (`geistPaar`), its
    order preservation (`geistRekon_folge`, both channels), the step
    classification that leaves silent steps with nothing to re-emit
    (`rufSchrittG_logSchritt`), and the entry duty (`rufAt_ok_vorOk`).
  - Return-duty extraction is OPEN: `InlinePflicht.nachOk` (ensures over
    the actual result between entry and return worlds) is STATED with the
    exact `rufAt` shapes but its derivation from a successful `rufAt`
    outcome is not proved -- only the entry half (`vorOk`) is.
  - Duty discharge is OPEN: `InlinePflicht.hp`/`hr` are CARRIED (the same
    `RufPasst` and empty-channel proofs the call would have needed,
    including lock/resource sets), not discharged against the caller's
    declared writes footprint or lock floor; callee-duties-subset-caller
    is a validator-side check, stated here only as data.
  - Indirect calls (`callInd`/`bindCallInd`) have no ghost form: the
    reconstruction covers direct calls and the `grund` channel only.
  - Bounds/depth and budget timing are separate preserved obligations
    (decreases/depth discipline, cost model) and are not touched here.
  - No SCFG/target bridge: everything is source-side (`RufEreignisF`,
    `rufAt`, `RufSchrittG`, `FolgeLog`); the lowering to the shared
    representation (QUELLBRUECKE, phase B) is the next dependency.
-/

#print axioms geistPaar_laenge
#print axioms geistRekon_folge
#print axioms geistRekon_folge_grund
#print axioms rufSchrittG_logSchritt
#print axioms rufAt_ok_vorOk
#print axioms geistRekon_zeuge

end Gabbro.Grammatik.X86
