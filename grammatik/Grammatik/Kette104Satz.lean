/-
  File:      Grammatik/Kette104Satz.lean
  Subject:   `kette_104 : Kette src104real` and the generic closing theorem
             applied to it (data and checks: Kette104.lean).

  CHAIN-INSTANCE beispiele/104-referenz.gab kette_104
-/
import Grammatik.Kette104
import Grammatik.CText104

namespace Gabbro.Grammatik.Kette104

open Gabbro.Grammatik Parser Parser.Uebersetze Parser.UebersetzeAllg Parser.UebersetzeAllg2 Zielsatz
open Gabbro.Grammatik.CParser Gabbro.Grammatik.CText104

set_option maxRecDepth 100000

/-! ## 4. The unit: the parsed code, and what the source declares about its run -/

/-- The declared initial memory: every slot `0` (`static Konto Konto_speicher;`
    is zero-initialised storage). -/
def sp4 : Speicher D4 where
  slots := fun t _ f => by
    have e := tab_eins t
    subst e
    rw [feld_eins f]
    exact (⟨0, by decide, by decide⟩ : Zahl 0 100)
  globs := fun g => nomatch g

/-- **104 as the goal theorem's unit**: the parsed code; no lock invariant
    (`lock M` declares none: the empty family), no axiom (the trivial axiom
    ensures), no declared start (104 has no `concurrent`), the zero memory. -/
def E4 : Einheit D4 where
  P := P4
  S := SperrInv.leer D4
  Q := axWahr D4
  starts := []
  sp0 := sp4

/-- The checker accepts the unit, by computation. -/
theorem akzeptiert4 : akzeptiert_pruefer.akzeptiert E4 fsA.1 lsA.1 csA.1 = true := by decide

/-! ## 5. The user's logic on the parsed program -/

/-- `lies` meets its obligation: it returns the slot it reads. -/
theorem lies4_V : KoerperGutV P4 0 lies4 := by
  intro O' _ R _ _ σ ρ _
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · rw [rumpf_lies4] at hrun
    simp only [bodyLies4, execEnd] at hrun
    cases hrun
    unfold EnsAmRueck
    rw [ens_lies4]
    exact decide_eq_true rfl
  · rw [rumpf_lies4] at hrun
    simp only [bodyLies4, execEnd] at hrun
    cases hrun

/-- A call through the gate never fails the gate when the handler blames
    nobody (over `D4`, whose functions all require `true`). -/
theorem d4_call_tor {V : Vertrag D4} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D4)} (O : Orakel D4) (passes : Nat)
    (R : ∀ f : D4.Fn, World D4 → Env D4 (D4.params f) → RufAusgang f) (hOV : OhneVorbedingung R)
    (g : D4.Fn) (args : Args D4 Γ Λ (D4.params g))
    (hp : RufPasst D4 V (D4.signatur g) Λ) (hr : D4.gruende g = 0) (σ : World D4)
    (ρ : Env D4 Γ) (g' : D4.Fn) :
    execStmt O passes (torRuf P4 R) (Stmt.call (l := l) g args hp hr) σ ρ ≠
      .logik (.vorbedingung g') := by
  have ht : ∀ σ1 ρ1, torRuf P4 R g σ1 ρ1 = R g σ1 ρ1 := fun _ _ => if_pos (by rw [req4]; rfl)
  simp only [execStmt, ht]
  cases hR : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | ok σ' v => intro h; cases h
  | grund σ' r => exact (Fin.cast hr r).elim0
  | logik e => intro h; cases h; exact hOV _ _ _ _ hR g' rfl
  | hardware e => intro h; cases h

/-- **`einzahlen` of the parsed program meets its obligation** against
    declared frames: the write sets the slot to `100`, `lies` declares no
    write, so `old(stand) <= stand` is `old(stand) <= 100`, true by the range
    (the argument of `gP_einzahlen_R`, over the parser's declaration). -/
theorem ein4_R : KoerperGutR P4 0 ein4 := by
  intro O' _ _ R hR hOV σ ρ _
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · rw [rumpf_ein4] at hrun
    rcases execEnd_cons_zurueck _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, h1, hrun1⟩
    · simp [execStmt] at h1
    rcases execEnd_cons_zurueck _ _ _ _ _ hrun1 with h2 | ⟨σ2, ρ2, h2, hrun2⟩
    · simp only [execStmt] at h2
      split at h2
      · cases h2
      · rename_i r _
        exact r.elim0
      · cases h2
      · cases h2
    simp only [execEnd] at hrun2
    simp only [execStmt] at h2
    split at h2
    · rename_i σ3 w hRv
      cases h2
      cases hrun2
      have hfr := (hR.2 lies4 _ _ σ2 w hRv).1.1 t4 rfl
      simp only [execStmt] at h1
      cases h1
      unfold EnsAmRueck
      rw [ens_ein4]
      show decide ((σ.slots t4 (ρ.get (.dort .hier)).n f4).n ≤
        (σ2.slots t4 (ρ.get (.dort .hier)).n f4).n) = true
      have e3 := (hfr (ρ.get (.dort .hier)).n f4).trans
        (storeSlot_hit (D := D4) _ t4 _ f4 _)
      have h100 : (σ2.slots t4 (ρ.get (.dort .hier)).n f4).n = 100 :=
        (congrArg (fun z : Zahl 0 100 => z.n) e3).trans rfl
      apply decide_eq_true
      exact Int.le_trans (σ.slots t4 (ρ.get (.dort .hier)).n f4).le_hi (Int.le_of_eq h100.symm)
    · rename_i r _
      exact r.elim0
    · cases h2
    · cases h2
  · rw [rumpf_ein4] at hrun
    rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, _, h1⟩
    · simp [execStmt] at h1
    · rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ h1 with h2 | ⟨σ2, ρ2, _, h2⟩
      · exact d4_call_tor _ _ R hOV _ _ _ _ _ _ _ h2
      · simp only [execEnd] at h2
        cases h2

theorem logikFrei4 : programmLogikFrei P4 fsA.1 = true := by decide

theorem ohneEwig4 : ohneEwigB P4 fsA.1 = true := by decide

theorem koerperS4 : ∀ f : D4.Fn, KoerperGutS P4 0 (axWahr D4) (SperrInv.leer D4) f := by
  intro f
  refine koerperGutS_leer ⟨koerperGutRQ_of_R _ ?_, programmLogikFrei_ok fsA.2 logikFrei4 0 _ f⟩
  rcases fn_zwei f with e | e <;> subst e
  · exact ein4_R
  · exact koerperGutR_of_V lies4_V

/-- **THE USER'S LOGIC on 104** (the goal theorem's (b)): the bodies at every
    budget, the owed invariants (none) at value and reason exits (no reason
    exists), the empty lock family and the trivial axiom ensures read only
    their carriers; the start obligation (no lock invariant, no declared
    start). -/
theorem nutzer4 : NutzerPflicht E4 where
  logik := ⟨fun passes f => ⟨koerperGutS_alle fsA.2 ohneEwig4 koerperS4 passes f, invGutS_leer rfl f,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ r _ => by
        have h := r.isLt
        have h0 : D4.gruende f = 0 := sigGruende_zero uExp104 f
        omega⟩,
    fun _ _ _ _ => rfl, axEnsLokal_wahr⟩
  start := ⟨fun _ => rfl, fun _ h => absurd h List.not_mem_nil⟩

/-! ## 6. The closed chain, and the closing theorem on it -/

/-- **THE CLOSED CHAIN OF `beispiele/104-referenz.gab`.** -/
def kette_104 : Kette src104real where
  u := uExp104
  E := E4
  fs0 := fs4
  uebersetzt := uebersetzt4
  fs := fsA
  ls := lsA
  cs := csA
  akzeptiert := akzeptiert4
  nutzer := nutzer4
  EL := EL4
  zert := zert104
  zertOk := zert104_ok

/-! ## 7. Witnesses (rule 13): the premises hold jointly, on a run that moves memory -/

/-- The oracle of `D4`: no axiom, register or global exists. -/
def O4 : Orakel D4 where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem hw4 : HardwareAnnahmen O4 E4.Q :=
  And.intro (fun a => nomatch a)
    (And.intro (And.intro (fun r => nomatch r) (fun g => nomatch g)) (axVertragO_wahr O4))

/-- Gabbro's arguments of `einzahlen(k, 0, 7)`. -/
def rho7 : Env D4 (D4.params ein4) :=
  .cons () (.cons ⟨0, by decide, by decide⟩ (.cons ⟨7, by decide, by decide⟩ .nil))

/-- The driver's start: thread `0` runs `einzahlen(k, 0, 7)`, every other thread idles. -/
def init4 : Faden → Σ f : D4.mitRuhe.Fn, Env D4.mitRuhe (D4.mitRuhe.params f) :=
  fun t => if t = 0 then ⟨some ein4, envR rho7⟩ else ⟨none, .nil⟩

theorem start4 : EinFadenStart E4 (speicherR E4.sp0) init4 where
  lader := rfl
  ruhe := fun u hu => by unfold init4; rw [if_neg hu]
  treiber := Or.inr ⟨ein4, rho7, rfl, rfl, rfl⟩

/-- The C locals `einzahlen(k, 0, 7)` binds. -/
def rho0 : CLok := lokUpd (lokUpd (lokUpd (fun _ => .undef) 2 (.int 7)) 1 (.int 0)) 0 (.ptr ⟨.tab 0, 0⟩)

theorem corr4 : corrW EL4 (sp4.welt []) refSt0 := by
  refine ⟨?_, And.intro (fun g => nomatch g) (fun _ h => Bool.noConfusion h)⟩
  intro t _
  have e := tab_eins t
  subst e
  refine ⟨rfl, ?_⟩
  intro k f _ _
  rw [feld_eins f]
  rfl

theorem env4 : EnvRel EL4 (zert104[0]'(by decide)).lay rho7 rho0 := by
  refine ⟨?_, fun q hq => absurd hq List.not_mem_nil, fun q hq => absurd hq List.not_mem_nil⟩
  intro τ x
  cases x with
  | hier => exact ⟨t4, rfl, rfl⟩
  | dort y =>
      cases y with
      | hier => rfl
      | dort z =>
          cases z with
          | hier => rfl
          | dort w => exact nomatch w

/-- **WITNESS of `schlusssatz` on 104** (every premise of the theorem holds
    jointly: the chain `kette_104`, the oracle `O4` with the hardware
    assumptions, the C semantics itself as the binary's behaviour (A1 with
    equality), the driver's single-threaded start `init4` (A4)): through
    part 4 of the GENERIC theorem, `einzahlen(k, 0, 7)` from the zero state
    -- the Gabbro call ends `ok` with the slot moved `0 -> 100`, the C call
    has a run, and EVERY C run ends with the C cell at `100`, returning
    nothing. -/
theorem kette_104_zeuge :
    ∃ σ' : World D4, rufAt P4 O4 0 2 ein4 (sp4.welt []) rho7 = .ok σ' () ∧
      ((sp4.welt []).slots t4 0 f4).n = 0 ∧ (σ'.slots t4 0 f4).n = 100 ∧
      refSt0.mem (.tab 0) 0 = .int 0 ∧
      (∃ st' rv, CallAt EL4.lay tvOrc tvXR (kProg zert104) 2 0 refSt0 einArgs st' rv) ∧
      ∀ st' rv, CallAt EL4.lay tvOrc tvXR (kProg zert104) 2 0 refSt0 einArgs st' rv →
        st'.mem (.tab 0) 0 = .int 100 ∧ rv = none := by
  have hR : rufAt P4 O4 0 2 ein4 (sp4.welt []) rho7 = .ok _ () := rfl
  have hR' : rufAt kette_104.E.P O4 0 2 ein4 (sp4.welt []) rho7 = .ok _ () := hR
  have h := (schlusssatz kette_104 O4 hw4 tvOrc tvXR tvXR_funktional
    (fun f => CallAt EL4.lay tvOrc tvXR (kProg zert104) 2 (fnNr f)) (fun _ => 2)
    (fun _ _ _ _ _ h => h) (speicherR E4.sp0) init4 start4).2.2.2.1 0 2 ein4
    (zert104[0]'(by decide)) rfl (sp4.welt []) refSt0 rho7 einArgs rho0 corr4 rfl env4
    (by rw [hR']; rfl)
  obtain ⟨hex, hall⟩ := h
  refine ⟨_, hR, rfl, rfl, rfl, hex, fun st' rv hC => ?_⟩
  have hO := hall st' rv hC
  rw [hR'] at hO
  obtain ⟨hc, hrv⟩ := hO
  exact ⟨(hc.1 t4 rfl).2 0 f4 (by decide) (by decide), hrv⟩

/-- **WITNESS of the new clauses 4b and 4d on 104**, non-degenerate: the
    chain's program can never end a call in a HARDWARE outcome (clause 4b,
    at every depth, every budget, every world and every argument list),
    part 4's condition implies the caller's duty (clause 4d), and both are
    exercised on the call that actually moves memory -- `einzahlen(k, 0, 7)`
    from the zero state, whose duty holds and whose slot goes `0 -> 100`.
    What is left of part 4's condition on this program is therefore the
    writer's logic alone (clause 4c). -/
theorem kette_104_ohne_hardware :
    (∀ (passes n : Nat) (f : D4.Fn) (σ : World D4) (ρ : Env D4 (D4.params f))
      (e : Hardware D4), rufAt P4 O4 passes n f σ ρ ≠ .hardware e) ∧
    (∀ (passes n : Nat) (f : D4.Fn) (σ : World D4) (ρ : Env D4 (D4.params f)),
      (rufAt P4 O4 passes (n + 1) f σ ρ).istFehler = false → ReqAmEintritt P4 f σ ρ) ∧
    ReqAmEintritt P4 ein4 (sp4.welt []) rho7 ∧
    ∃ σ' : World D4, rufAt P4 O4 0 2 ein4 (sp4.welt []) rho7 = .ok σ' () ∧
      ((sp4.welt []).slots t4 0 f4).n = 0 ∧ (σ'.slots t4 0 f4).n = 100 := by
  have h := schlusssatz kette_104 O4 hw4 tvOrc tvXR tvXR_funktional
    (fun f => CallAt EL4.lay tvOrc tvXR (kProg zert104) 2 (fnNr f)) (fun _ => 2)
    (fun _ _ _ _ _ h => h) (speicherR E4.sp0) init4 start4
  have hR : rufAt P4 O4 0 2 ein4 (sp4.welt []) rho7 = .ok _ () := rfl
  refine ⟨h.2.2.2.2.1, h.2.2.2.2.2.2.1, ?_, _, hR, rfl, rfl⟩
  exact h.2.2.2.2.2.2.1 0 1 ein4 (sp4.welt []) rho7 rfl

/-! ## 8. A2 discharged: the C side READ FROM THE EMITTED TEXT

    Until 2026-09-15 the C side of this chain was the certificate's
    elaboration `kProg zert104`, and that the EMITTED TEXT means the same
    thing was assumption A2 -- a hand transcription. `CText104.lean` pins
    the emitted text (`ctext104`, byte-identical to `gabbro emit`) and
    proves `parseC ctext104 = some (kFuns zert104)` by kernel reduction,
    so the two theorems below say the same as their neighbours above,
    about the TEXT. What stays of A2 is "the C compiler's front end reads
    this subset as `parseC` does" -- part of A1. -/

/-- **A2 DISCHARGED on 104, part 6 of the closing theorem**: every run of
    the compiled binary of `f` ends related to the Gabbro call -- under
    A1 stated about the C unit of the EMITTED TEXT. -/
theorem kette_104_binaer_text
    (orc : DevOrc) (XR : CCallR) (hXR : XR.Funktional)
    (bin : D4.Fn → CSt → List CVal → CSt → Option CVal → Prop) (tief : D4.Fn → Nat)
    (hA1 : ∀ f st vs st' rv, bin f st vs st' rv →
      CallAt EL4.lay orc XR (cProgC ctext104) (tief f) (fnNr f) st vs st' rv)
    (sp : Speicher D4.mitRuhe)
    (init : Faden → Σ f : D4.mitRuhe.Fn, Env D4.mitRuhe (D4.mitRuhe.params f))
    (hA4 : EinFadenStart E4 sp init) :
    ∀ (passes : Nat) (f : D4.Fn) (k : KFun D4), zert104[fnNr f]? = some k →
      ∀ (σ : World D4) (st : CSt) (ρG : Env D4 (D4.params f)) (vs : List CVal) (ρ0 : CLok),
        corrW EL4 σ st → bindParams k.params vs = some ρ0 → EnvRel EL4 k.lay ρG ρ0 →
        (rufAt P4 O4 passes (tief f) f σ ρG).istFehler = false →
        ∀ st' rv, bin f st vs st' rv → RufOut EL4 (rufAt P4 O4 passes (tief f) f σ ρG) st' rv :=
  (schlusssatz_text kette_104 a2_104 O4 hw4 orc XR hXR bin tief hA1 sp init hA4).2.2.2.2.2.2.2.2.2

/-- **WITNESS**: `kette_104_zeuge` again, with the C side read from the
    emitted TEXT -- `einzahlen(k, 0, 7)` from the zero state moves the
    Gabbro slot `0 -> 100`, and EVERY run of the C the emitted text
    denotes ends with the C cell at `100`. -/
theorem kette_104_zeuge_text :
    ∃ σ' : World D4, rufAt P4 O4 0 2 ein4 (sp4.welt []) rho7 = .ok σ' () ∧
      ((sp4.welt []).slots t4 0 f4).n = 0 ∧ (σ'.slots t4 0 f4).n = 100 ∧
      refSt0.mem (.tab 0) 0 = .int 0 ∧
      (∃ st' rv, CallAt EL4.lay tvOrc tvXR (cProgC ctext104) 2 0 refSt0 einArgs st' rv) ∧
      ∀ st' rv, CallAt EL4.lay tvOrc tvXR (cProgC ctext104) 2 0 refSt0 einArgs st' rv →
        st'.mem (.tab 0) 0 = .int 100 ∧ rv = none := by
  rw [cprog_104]
  exact kette_104_zeuge

#print axioms Gabbro.Grammatik.Kette104.nutzer4
#print axioms Gabbro.Grammatik.Kette104.kette_104
#print axioms Gabbro.Grammatik.Kette104.kette_104_zeuge
#print axioms Gabbro.Grammatik.Kette104.kette_104_ohne_hardware
#print axioms Gabbro.Grammatik.Kette104.kette_104_binaer_text
#print axioms Gabbro.Grammatik.Kette104.kette_104_zeuge_text

end Gabbro.Grammatik.Kette104
