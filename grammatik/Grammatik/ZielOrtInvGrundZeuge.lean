/-
  Gabbro/Grammatik/ZielOrtInvGrundZeuge.lean

  **Witnesses for `ziel_ort_sperre_invGrund`** (invariants at REASON
  returns, SATZKARTE §19.1).

      lock L protects konto (two slots, 0 .. 10) rank 0
      invariant gleich: konto[0] == konto[1]        -- carriers: konto
      fn haupt()  holds L, writes konto {
        breaking gleich {
          let x = setze() else { r => konto[0] := 1; konto[1] := 1; return }
        };
        konto[0] := 1; konto[1] := 1; return }
      fn setze() -> bool, one reason, holds L, writes konto
        { konto[0] := 5; konto[1] := 5; return R }             -- grPgut
        { konto[0] := 5; return R }                            -- grPschlecht
      fn nichts() { return }

  Thread 0 starts in `haupt`, every other thread in `nichts`. Every contract
  is `true`. `setze` never returns a VALUE, so the value-return obligation
  `InvGutS` holds for both programs, and `ziel_ort_sperre_inv` certifies the
  broken one (`grPschlecht_alt`): its `setze` leaves by the reason with
  `konto[0] = 5`, `konto[1] = 0`, breaking the invariant it owes -- and on a
  reached machine the logged reason return shows it
  (`grPschlecht_verletzt`). The new obligation `InvGutGrund` refutes it
  (`grPschlecht_nicht_invGutGrund`); the correct program meets every
  premise of `ziel_ort_sperre_invAlle` (`grPgut_zertifiziert`), and on its
  reached run the logged reason return meets the invariant BY THE THEOREM
  (`grGut_zeuge`).
-/
import Grammatik.ZielOrtInvGrund
import Grammatik.InvZeuge

namespace Gabbro.Grammatik

/-! ## 1. The declaration -/

inductive GrFn where
  | haupt
  | setze
  | nichts
  deriving DecidableEq

def grSig (e : Option Ty) (n : Nat) (h : List Unit) (w : Bool) :
    Signatur Unit Empty Unit Empty where
  params := []
  erg := e
  gruende := n
  haelt := h
  schreibt := fun _ => w
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def grSigNr : Nat → Signatur Unit Empty Unit Empty
  | 0 => grSig none 0 [()] true
  | 1 => grSig (some .bool) 1 [()] true
  | _ => grSig none 0 [] false

/-- As `ivD`, with `setze` answering a `bool` and declaring one reason. -/
def grD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 10
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => true
  ggeteilt := fun e => nomatch e
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => [.inl ()]
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := GrFn
  sig := fun | .haupt => 0 | .setze => 1 | .nichts => 2
  sigNr := grSigNr
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Unit
  traeger := fun _ => [()]
  invs := [()]
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
  geteilt_bewacht := fun t _ => by decide
  invarianten_gehalten := fun n _ h _ _ L _ => by
    cases L
    match n, h with
    | 0, _ => exact List.mem_singleton.mpr rfl
    | 1, _ => exact List.mem_singleton.mpr rfl
    | n + 2, h => simp [grSigNr, grSig] at h
  ggeteilt_bewacht := fun e => nomatch e

def grHaupt : grD.Fn := GrFn.haupt
def grSetze : grD.Fn := GrFn.setze
def grNichts : grD.Fn := GrFn.nichts

abbrev grL : List (Res grD) := [Res.held (D := grD) ()]

theorem grDarf : darf grD () grL := by
  intro w h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  rw [e]
  exact List.mem_singleton.mpr rfl

/-! ## 2. The invariant and the bodies -/

def grIdx {Γ : Ctx} {Λ : List (Res grD)} (k : Int) (h0 : 0 ≤ k) (h1 : k ≤ 1) :
    Expr grD Γ Λ (.index (grD.count ())) :=
  .weiter (lo := k) (hi := k) h0 h1 (.lit k)

def grWert {Γ : Ctx} {Λ : List (Res grD)} (k : Int) (h0 : 0 ≤ k) (h1 : k ≤ 10) :
    Expr grD Γ Λ (grD.typ () ()) :=
  .weiter (lo := k) (hi := k) h0 h1 (.lit k)

/-- `invariant gleich: konto[0] == konto[1]`. -/
def grInv : Expr grD [] (invSicht grD ()) .bool :=
  .eq (show Expr grD [] (invSicht grD ()) (.int 0 10) from
        .slot () () (grIdx 0 (by decide) (by decide)) grDarf)
      (show Expr grD [] (invSicht grD ()) (.int 0 10) from
        .slot () () (grIdx 1 (by decide) (by decide)) grDarf)

/-- `konto[k] := v` in a function that writes `konto`. -/
def grSchreib (f : grD.Fn) (hw : (vertragVon grD f).schreibt () = true) {Γ : Ctx} (k v : Int)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 10) :
    Stmt grD (vertragVon grD f) false Γ grL grL :=
  .assignSlot () () (grIdx k hk0 hk1) (grWert v hv0 hv1) hw grDarf

def grS0 : Stmt grD (vertragVon grD grSetze) false [] grL grL :=
  grSchreib grSetze rfl 0 5 (by decide) (by decide) (by decide) (by decide)
def grS1 : Stmt grD (vertragVon grD grSetze) false [] grL grL :=
  grSchreib grSetze rfl 1 5 (by decide) (by decide) (by decide) (by decide)

/-- `return R` from `setze`. -/
def grGrund : Endblock grD (vertragVon grD grSetze) false [] grL :=
  .retGrund ⟨0, by decide⟩ (List.Perm.refl _)

/-- `setze` (correct): both slots `5`, then the reason. -/
def grRumpfGut : Endblock grD (vertragVon grD grSetze) false [] grL :=
  .cons grS0 (.cons grS1 grGrund)

/-- `setze` (broken): only slot `0`, then the reason. -/
def grRumpfSchlecht : Endblock grD (vertragVon grD grSetze) false [] grL :=
  .cons grS0 grGrund

/-- The call of `setze` from `haupt`: both hold `L` by signature. -/
theorem grHp : RufPasst grD (vertragVon grD grHaupt) (grD.signatur grSetze) grL where
  hw := fun _ _ => rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp⟩
  hh := fun L _ => by cases L; exact List.mem_singleton.mpr rfl
  hx := fun L _ hn => absurd (by cases L; exact List.mem_singleton.mpr rfl) hn

/-- `konto[k] := 1` in `haupt`, at any context. -/
def grH (Γ : Ctx) (k : Int) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) :
    Stmt grD (vertragVon grD grHaupt) false Γ grL grL :=
  grSchreib grHaupt rfl (Γ := Γ) k 1 hk0 hk1 (by decide) (by decide)

/-- The reason branch of `haupt`: re-establish, return. -/
def grErr : Endblock grD (vertragVon grD grHaupt) false (.grund (grD.gruende grSetze) :: [])
    (nach grD grSetze grL) :=
  .cons (grH _ 0 (by decide) (by decide)) (.cons (grH _ 1 (by decide) (by decide))
    (.ret .keine (List.Perm.refl _)))

/-- `let x = setze() else { r => … }`, the value branch empty. -/
def grB : Block grD (vertragVon grD grHaupt) false [] grL grL :=
  .bindCallElse grSetze .nil rfl grHp (by decide) grErr .nil

/-- The tail of `haupt`: re-establish, return. -/
def grTail : Endblock grD (vertragVon grD grHaupt) false [] grL :=
  .cons (grH [] 0 (by decide) (by decide)) (.cons (grH [] 1 (by decide) (by decide))
    (.ret .keine (List.Perm.refl _)))

def grRumpfHaupt : Endblock grD (vertragVon grD grHaupt) false [] grL :=
  .cons (.breaking () grB) grTail

def grRumpfNichts : Endblock grD (vertragVon grD grNichts) false [] [] :=
  .ret .keine List.Perm.nil

def grP (setze : Endblock grD (vertragVon grD grSetze) false [] grL) : Programm grD where
  invariante := fun _ => grInv
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf
    | .haupt => grRumpfHaupt
    | .setze => setze
    | .nichts => grRumpfNichts

def grPgut : Programm grD := grP grRumpfGut
def grPschlecht : Programm grD := grP grRumpfSchlecht

/-! ## 3. The fixed premises -/

def grFs : List grD.Fn := [grHaupt, grSetze, grNichts]

theorem grFs_voll : ∀ g : grD.Fn, g ∈ grFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

def grO : Orakel grD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem grO_gut : GutO grO := fun a => nomatch a

theorem grO_lokal : RegLokal grO := ⟨(fun r _ _ _ => nomatch r), (fun g _ _ _ => nomatch g)⟩

def grSp : Speicher grD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- Thread `0` runs `haupt`, every other thread `nichts`. -/
def grInit : Faden → Σ f : grD.Fn, Env grD (grD.params f) :=
  fun t => if t = 0 then ⟨grHaupt, .nil⟩ else ⟨grNichts, .nil⟩

theorem grInit_sonst {t : Faden} (ht : t ≠ 0) : grInit t = ⟨grNichts, .nil⟩ := if_neg ht

theorem grStart (setze : Endblock grD (vertragVon grD grSetze) false [] grL) :
    StartGut (grP setze) grSp grInit := by
  intro t
  by_cases ht : t = 0
  · subst ht; rfl
  · rw [grInit_sonst ht]; rfl

theorem grInit_exklusiv : StartExklusiv (D := grD) grInit := by
  intro t u htu L hL hL'
  by_cases ht : t = 0
  · have hu : u ≠ 0 := fun h => htu (ht.trans h.symm)
    rw [grInit_sonst hu] at hL'
    exact absurd hL' List.not_mem_nil
  · rw [grInit_sonst ht] at hL
    exact absurd hL List.not_mem_nil

def grE0 : Ereignis grD := .gibt ()

theorem grPgut_frag : programmImFragmentG grPgut grFs = true := by decide
theorem grPschlecht_frag : programmImFragmentG grPschlecht grFs = true := by decide
theorem grPgut_fuss : fussSperreB grPgut (SperrInv.leer grD) grFs = true := by decide
theorem grPschlecht_fuss : fussSperreB grPschlecht (SperrInv.leer grD) grFs = true := by decide

/-! ## 4. The obligations -/

/-- **`haupt` against any handler**: the answer of `setze` decides the
    path -- a value continues to the tail, a reason runs the else branch,
    `logik`/hardware answers end the body. -/
theorem grHaupt_fall (S : SperrInv grD) (O : Orakel grD) (U : Umwelt grD) (passes : Nat)
    (setze : Endblock grD (vertragVon grD grSetze) false [] grL)
    (R : ∀ f : grD.Fn, World grD → Env grD (grD.params f) → RufAusgang f)
    (σ : World grD) (ρ : Env grD (grD.params grHaupt)) :
    (∃ σ1 v1, R grSetze (σ.lese grL []) .nil = .ok σ1 v1 ∧
      execEndH (V := vertragVon grD grHaupt) S O U passes R ((grP setze).rumpf grHaupt) σ ρ =
        execEndH S O U passes R grTail σ1 ρ) ∨
    (∃ σ1 r1, R grSetze (σ.lese grL []) .nil = .grund σ1 r1 ∧
      execEndH (V := vertragVon grD grHaupt) S O U passes R ((grP setze).rumpf grHaupt) σ ρ =
        (execEndH S O U passes R grErr σ1 (.cons r1 ρ)).schrumpf) ∨
    (∃ e1, R grSetze (σ.lese grL []) .nil = .logik e1 ∧
      execEndH (V := vertragVon grD grHaupt) S O U passes R ((grP setze).rumpf grHaupt) σ ρ =
        .logik e1) ∨
    (∃ e1, execEndH (V := vertragVon grD grHaupt) S O U passes R ((grP setze).rumpf grHaupt) σ ρ =
        .hardware e1) := by
  cases hR : R grSetze (σ.lese grL []) .nil with
  | ok σ1 v1 =>
      refine Or.inl ⟨σ1, v1, rfl, ?_⟩
      show execEndH S O U passes R grRumpfHaupt σ ρ = _
      simp only [grRumpfHaupt, grB, execEndH, execStmtH, execBlockH, Args.orte, evalArgs, hR]
      rfl
  | grund σ1 r1 =>
      refine Or.inr (Or.inl ⟨σ1, r1, rfl, ?_⟩)
      show execEndH S O U passes R grRumpfHaupt σ ρ = _
      simp only [grRumpfHaupt, grB, execEndH, execStmtH, execBlockH, Args.orte, evalArgs, hR]
      cases execEndH S O U passes R grErr σ1 (.cons r1 ρ) <;> rfl
  | logik e1 =>
      refine Or.inr (Or.inr (Or.inl ⟨e1, rfl, ?_⟩))
      show execEndH S O U passes R grRumpfHaupt σ ρ = _
      simp only [grRumpfHaupt, grB, execEndH, execStmtH, execBlockH, Args.orte, evalArgs, hR]
      rfl
  | hardware e1 =>
      refine Or.inr (Or.inr (Or.inr ⟨e1, ?_⟩))
      show execEndH S O U passes R grRumpfHaupt σ ρ = _
      simp only [grRumpfHaupt, grB, execEndH, execStmtH, execBlockH, Args.orte, evalArgs, hR]
      rfl

theorem gr_koerper_nichts (setze : Endblock grD (vertragVon grD grSetze) false [] grL) :
    KoerperGutS (grP setze) 0 (axWahr grD) (SperrInv.leer grD) grNichts := by
  have hr : (grP setze).rumpf grNichts = grRumpfNichts := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [grRumpfNichts, execEndH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [grRumpfNichts, execEndH] at hrun
    cases hrun

theorem gr_koerper_gut : KoerperGutS grPgut 0 (axWahr grD) (SperrInv.leer grD) grSetze := by
  have hr : grPgut.rumpf grSetze = grRumpfGut := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [grRumpfGut, grS0, grS1, grSchreib, grGrund, execEndH, execStmtH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [grRumpfGut, grS0, grS1, grSchreib, grGrund, execEndH, execStmtH] at hrun
    cases hrun

theorem gr_koerper_schlecht : KoerperGutS grPschlecht 0 (axWahr grD) (SperrInv.leer grD) grSetze := by
  have hr : grPschlecht.rumpf grSetze = grRumpfSchlecht := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [grRumpfSchlecht, grS0, grSchreib, grGrund, execEndH, execStmtH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [grRumpfSchlecht, grS0, grSchreib, grGrund, execEndH, execStmtH] at hrun
    cases hrun

theorem gr_koerper_haupt (setze : Endblock grD (vertragVon grD grSetze) false [] grL) :
    KoerperGutS (grP setze) 0 (axWahr grD) (SperrInv.leer grD) grHaupt := by
  refine ⟨fun O' _ _ _ U _ R hR hOV σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R hR hOL σ ρ _ e hrun => ?_⟩
  · rcases grHaupt_fall (SperrInv.leer grD) O' U 0 setze (torRuf (grP setze) R) σ ρ with
      ⟨σ1, v1, _, h1⟩ | ⟨σ1, r1, _, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> rw [h1] at hrun
    · simp only [grTail, grH, grSchreib, execEndH, execStmtH] at hrun
      cases hrun
    · simp only [grErr, grH, grSchreib, execEndH, execStmtH, EndAusgang.schrumpf] at hrun
      cases hrun
    · cases hrun
      exact hOV _ _ _ _ he1 g rfl
    · cases hrun
  · rcases grHaupt_fall (SperrInv.leer grD) O' U 0 setze R σ ρ with
      ⟨σ1, v1, _, h1⟩ | ⟨σ1, r1, _, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> rw [h1] at hrun
    · simp only [grTail, grH, grSchreib, execEndH, execStmtH] at hrun
      cases hrun
    · simp only [grErr, grH, grSchreib, execEndH, execStmtH, EndAusgang.schrumpf] at hrun
      cases hrun
    · cases hrun
      exact hOL _ _ _ _ he1
    · cases hrun

theorem grPgut_koerper : ∀ f : grD.Fn, KoerperGutS grPgut 0 (axWahr grD) (SperrInv.leer grD) f
  | .haupt => gr_koerper_haupt _
  | .setze => gr_koerper_gut
  | .nichts => gr_koerper_nichts _

theorem grPschlecht_koerper :
    ∀ f : grD.Fn, KoerperGutS grPschlecht 0 (axWahr grD) (SperrInv.leer grD) f
  | .haupt => gr_koerper_haupt _
  | .setze => gr_koerper_schlecht
  | .nichts => gr_koerper_nichts _

/-- `haupt` meets its owed invariant at every VALUE return: both paths
    re-establish it. -/
theorem gr_inv_haupt (setze : Endblock grD (vertragVon grD grSetze) false [] grL) :
    InvGutS (grP setze) 0 (axWahr grD) (SperrInv.leer grD) grHaupt := by
  intro O' _ _ _ U _ R _ _ σ ρ _ σ' v hrun
  rcases grHaupt_fall (SperrInv.leer grD) O' U 0 setze R σ ρ with
    ⟨σ1, v1, _, h1⟩ | ⟨σ1, r1, _, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> rw [h1] at hrun
  · simp only [grTail, grH, grSchreib, execEndH, execStmtH] at hrun
    cases hrun
    intro i _ _
    cases i
    simp [InvHaelt, grP, grInv, grIdx, grWert, eval, World.storeSlot, World.merke,
      World.lese, World.schreibSlot, Zahl.weiter]
    rfl
  · simp only [grErr, grH, grSchreib, execEndH, execStmtH, EndAusgang.schrumpf] at hrun
    cases hrun
    intro i _ _
    cases i
    simp [InvHaelt, grP, grInv, grIdx, grWert, eval, World.storeSlot, World.merke,
      World.lese, World.schreibSlot, Zahl.weiter]
    rfl
  · cases hrun
  · cases hrun

/-- `setze` never returns a VALUE: the value-return obligation holds for
    both bodies, whatever they do to `konto`. -/
theorem gr_inv_setze (setze : Endblock grD (vertragVon grD grSetze) false [] grL)
    (h : setze = grRumpfGut ∨ setze = grRumpfSchlecht) :
    InvGutS (grP setze) 0 (axWahr grD) (SperrInv.leer grD) grSetze := by
  intro O' _ _ _ U _ R _ _ σ ρ _ σ' v hrun
  have hr : (grP setze).rumpf grSetze = setze := rfl
  rw [hr] at hrun
  rcases h with rfl | rfl
  · simp only [grRumpfGut, grS0, grS1, grSchreib, grGrund, execEndH, execStmtH] at hrun
    cases hrun
  · simp only [grRumpfSchlecht, grS0, grSchreib, grGrund, execEndH, execStmtH] at hrun
    cases hrun

theorem gr_inv_nichts (setze : Endblock grD (vertragVon grD grSetze) false [] grL) :
    InvGutS (grP setze) 0 (axWahr grD) (SperrInv.leer grD) grNichts :=
  invGutS_ohne fun _ _ => rfl

theorem grPgut_inv : ∀ f : grD.Fn, InvGutS grPgut 0 (axWahr grD) (SperrInv.leer grD) f
  | .haupt => gr_inv_haupt _
  | .setze => gr_inv_setze _ (Or.inl rfl)
  | .nichts => gr_inv_nichts _

theorem grPschlecht_inv : ∀ f : grD.Fn, InvGutS grPschlecht 0 (axWahr grD) (SperrInv.leer grD) f
  | .haupt => gr_inv_haupt _
  | .setze => gr_inv_setze _ (Or.inr rfl)
  | .nichts => gr_inv_nichts _

/-- **The correct `setze` meets the new obligation**: its reason exit leaves
    both slots `5`. -/
theorem gr_invGrund_gut : Zielsatz.InvGutGrund grPgut 0 (axWahr grD) (SperrInv.leer grD) grSetze := by
  intro O' _ _ _ U _ R _ _ σ ρ _ σ' r hrun
  have hr : grPgut.rumpf grSetze = grRumpfGut := rfl
  rw [hr] at hrun
  simp only [grRumpfGut, grS0, grS1, grSchreib, grGrund, execEndH, execStmtH] at hrun
  cases hrun
  intro i _ _
  cases i
  simp [InvHaelt, grPgut, grP, grInv, grIdx, grWert, eval, World.storeSlot, World.merke,
    World.lese, World.schreibSlot, Zahl.weiter]
  rfl

theorem grPgut_invGrund :
    ∀ f : grD.Fn, Zielsatz.InvGutGrund grPgut 0 (axWahr grD) (SperrInv.leer grD) f
  | .haupt => invGutGrund_ohneGrund rfl
  | .setze => gr_invGrund_gut
  | .nichts => invGutGrund_ohneGrund rfl

/-! ## 5. The certified and the refuted program -/

/-- **`grPgut` is certified by `ziel_ort_sperre_invAlle`**: every premise,
    the reason obligation included. -/
theorem grPgut_zertifiziert : ∀ M : RufMaschineG grD,
    RufErreichbarG grPgut grO 0 (RufStartG grPgut grSp grInit) M →
      InvAmOrtG grPgut M ∧ Zielsatz.InvAmGrundG grPgut M :=
  ziel_ort_sperre_invAlle grPgut grO 0 (axWahr grD) (SperrInv.leer grD) grFs grSp grInit grE0
    grO_gut grO_lokal (axVertragO_wahr grO) axEnsLokal_wahr sperrInvOk_leer grFs_voll grPgut_frag
    grPgut_fuss grPgut_koerper (grStart _) (fun _ => rfl) grInit_exklusiv grPgut_inv
    grPgut_invGrund

/-- **The broken program was certified by `ziel_ort_sperre_inv`** (every
    premise holds: `setze` never returns a value) -- the gap this file
    closes. -/
theorem grPschlecht_alt : ∀ M : RufMaschineG grD,
    RufErreichbarG grPschlecht grO 0 (RufStartG grPschlecht grSp grInit) M →
      (VertragAmOrtG grPschlecht M ∧ SperrInvG (SperrInv.leer grD) M ∧ KeinLogikHaltG grO 0 M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG grPschlecht grO 0 M t M') ∧
      InvAmOrtG grPschlecht M :=
  ziel_ort_sperre_inv grPschlecht grO 0 (axWahr grD) (SperrInv.leer grD) grFs grSp grInit grE0
    grO_gut grO_lokal (axVertragO_wahr grO) axEnsLokal_wahr sperrInvOk_leer grFs_voll
    grPschlecht_frag grPschlecht_fuss grPschlecht_koerper (grStart _) (fun _ => rfl)
    grInit_exklusiv grPschlecht_inv

/-- The identity environment move meets `HavocOk` of the empty family. -/
theorem gr_havoc : HavocOk (SperrInv.leer grD) (fun _ σ => σ) :=
  fun _ _ => ⟨rfl, fun c _ => traegerGleich_refl _ c, rfl⟩

/-- **The new obligation fails for the broken `setze`**: from the zero
    memory its body leaves by the reason with `konto[0] = 5`,
    `konto[1] = 0`. -/
theorem grPschlecht_nicht_invGutGrund :
    ¬ Zielsatz.InvGutGrund grPschlecht 0 (axWahr grD) (SperrInv.leer grD) grSetze := by
  intro h
  have h3 := h grO (gutO_rahmenO grO_gut) grO_lokal (axVertragO_wahr grO) (fun _ σ => σ) gr_havoc
    (rufAusV []) (rufAusV_rahmen (vertraegeOkR_nil grPschlecht))
    (rufAusV_ohneVorbedingung (vertraegeOkR_nil grPschlecht).1) (grSp.welt []) .nil rfl _ _ rfl ()
    (List.mem_singleton.mpr rfl) rfl
  revert h3
  simp [InvHaelt, grPschlecht, grP, grInv, grIdx, grWert, eval, World.storeSlot, World.merke,
    World.lese, World.schreibSlot, Zahl.weiter, grSp, Speicher.welt]
  decide

/-! ## 6. The runs -/

theorem grM0_faden0 (setze : Endblock grD (vertragVon grD grSetze) false [] grL) :
    (RufStartG (grP setze) grSp grInit).faeden 0 =
    ⟨[], ⟨grHaupt, .nil, grSp.welt [], ⟨false, [], grL, .nil, .ende grRumpfHaupt⟩⟩,
      startSpur grHaupt, [RufEreignisF.eintritt grHaupt .nil (grSp.welt [])]⟩ := rfl

theorem grHeld {s : List (Ereignis grD)} (h : offen s = [()]) : HeldIn grL (offen s) :=
  fun L _ => by cases L; rw [h]; exact List.mem_singleton.mpr rfl

/-- **The run to the reason return of `setze`**, for either body: `haupt`
    unfolds `breaking` (1, 2), calls `setze` through `let … else` (3),
    `setze` writes slot `0` (4). -/
theorem grVorlauf (setze : Endblock grD (vertragVon grD grSetze) false [] grL) :
    ∃ (M3 : RufMaschineG grD) (s0 : World grD) (log : List (RufEreignisF grD)),
      RufErreichbarG (grP setze) grO 0 (RufStartG (grP setze) grSp grInit) M3 ∧
      M3.faeden 0 = ⟨[⟨grHaupt, .nil, grSp.welt [],
          ⟨false, [], grL, .nil, .wartetSonst (τ := .bool) (grD.gruende grSetze) grErr .nil
            (.dann .nil (.ende grTail))⟩⟩],
        ⟨grSetze, .nil, s0, ⟨false, [], grL, .nil, .ende setze⟩⟩,
        s0.spur, log⟩ ∧
      M3.weltVon 0 = s0 ∧ offen s0.spur = [()] ∧
      s0.slots = grSp.slots := by
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := grP setze) (O := grO) (passes := 0)
    (grM0_faden0 setze) (.breaking () grB) grTail .nil rfl rfl
  obtain ⟨M2, s2, hZ2⟩ := w_breaking (P := grP setze) (O := grO) (passes := 0) hZ1.1 () grB .nil
    (.ende grTail) .nil rfl
  have hoff2 : offen (M1.weltVon 0).spur = [()] := by
    rw [hZ1.welt]
    rfl
  obtain ⟨M3, s3, hZ3⟩ := w_bindCallElse (P := grP setze) (O := grO) (passes := 0) hZ2.1 grSetze
    .nil rfl grHp (by decide) grErr .nil (.dann .nil (.ende grTail)) .nil rfl (grHeld hoff2)
  refine ⟨M3, _, _, .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3,
    hZ3.1, hZ3.welt, ?_, ?_⟩
  · show offen ((M2.weltVon 0).lese grL []).spur = [()]
    rw [(Erw.lese _ _ _).offen, hZ2.welt]
    exact hoff2
  · show ((M2.weltVon 0).lese grL []).slots = grSp.slots
    rw [hZ2.welt, hZ1.welt]
    rfl

/-- **The new conclusion fails on a machine of `grPschlecht` reachable in
    five steps** (thread 0: `haupt` unfolds `breaking`, calls `setze`
    through `let … else`, `setze` writes slot `0` and leaves by the
    reason): the logged reason return of `setze` breaks the invariant --
    while `grPschlecht_alt` certified the program. -/
theorem grPschlecht_verletzt : ∃ M : RufMaschineG grD,
    RufErreichbarG grPschlecht grO 0 (RufStartG grPschlecht grSp grInit) M ∧
    ¬ Zielsatz.InvAmGrundG grPschlecht M := by
  obtain ⟨M3, s0, log, hr3, hz3, hw3, hoff3, hsl3⟩ := grVorlauf grRumpfSchlecht
  obtain ⟨M4, s4, hZ4⟩ := w_blatt (P := grPschlecht) (O := grO) (passes := 0) hz3 grS0 grGrund
    .nil rfl rfl (grHeld hoff3) _ _ rfl
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff4 : offen (M4.faeden 0).spur = [()] := by
    rw [hZ4.spur]
    exact ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen.trans
      (by rw [hw3]; exact hoff3)
  obtain ⟨M5, s5, hG5⟩ := w_rueckGrundP (P := grPschlecht) (O := grO) (passes := 0) hZ4.1 _ _ rfl
    (PopGrund.sonst grErr .nil (.dann .nil (.ende grTail)) .nil rfl) ⟨0, Nat.zero_lt_one⟩
    (List.Perm.refl grL) .nil rfl (by rw [← hZ4.1]; exact grHeld hoff4)
  refine ⟨M5, .schritt _ _ _ (.schritt _ _ _ hr3 s4) s5, fun h => ?_⟩
  have h3 := h 0 _ (by rw [hG5.1]; exact List.mem_cons_self) _ _ _ _ _ rfl ()
    (List.mem_singleton.mpr rfl) rfl
  revert h3
  rw [hZ4.welt, hw3]
  simp [InvHaelt, grPschlecht, grP, grInv, grIdx, grWert, eval, World.storeSlot, World.merke,
    World.lese, World.schreibSlot, Zahl.weiter, hsl3, grSp]
  rfl

/-- **`grGut_zeuge`**: on a machine of `grPgut` reached in six steps
    (thread 0: `haupt` calls `setze` through `let … else`, `setze` writes
    both slots and leaves by the reason), the logged reason return of
    `setze` meets the invariant it owes BY THE THEOREM
    (`grPgut_zertifiziert`), at a world whose two slots hold `5`. -/
theorem grGut_zeuge : ∃ M : RufMaschineG grD,
    RufErreichbarG grPgut grO 0 (RufStartG grPgut grSp grInit) M ∧
    ∃ (r : Fin (grD.gruende grSetze)) (s0 s1 : World grD),
      RufEreignisF.grund grSetze .nil r s0 s1 ∈ (M.faeden 0).log ∧
      InvAmRueck grPgut grSetze s1 ∧
      (s1.slots () 0 ()).n = 5 ∧ (s1.slots () 1 ()).n = 5 := by
  obtain ⟨M3, s0, log, hr3, hz3, hw3, hoff3, hsl3⟩ := grVorlauf grRumpfGut
  obtain ⟨M4, s4, hZ4⟩ := w_blatt (P := grPgut) (O := grO) (passes := 0) hz3 grS0 (.cons grS1 grGrund)
    .nil rfl rfl (grHeld hoff3) _ _ rfl
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff4 : offen (M4.faeden 0).spur = [()] := by
    rw [hZ4.spur]
    exact ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen.trans
      (by rw [hw3]; exact hoff3)
  have e4 := hZ4.1
  obtain ⟨M5, s5, hZ5⟩ := w_blatt (P := grPgut) (O := grO) (passes := 0) e4 grS1 grGrund
    .nil rfl rfl (by rw [← e4]; exact grHeld hoff4) _ _ rfl
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff5 : offen (M5.faeden 0).spur = [()] := by
    rw [hZ5.spur]
    exact ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen.trans
      hoff4
  obtain ⟨M6, s6, hG6⟩ := w_rueckGrundP (P := grPgut) (O := grO) (passes := 0) hZ5.1 _ _ rfl
    (PopGrund.sonst grErr .nil (.dann .nil (.ende grTail)) .nil rfl) ⟨0, Nat.zero_lt_one⟩
    (List.Perm.refl grL) .nil rfl (by rw [← hZ5.1]; exact grHeld hoff5)
  have hr6 : RufErreichbarG grPgut grO 0 (RufStartG grPgut grSp grInit) M6 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ hr3 s4) s5) s6
  obtain ⟨r, a, b, hm, hb⟩ : ∃ (r : Fin (grD.gruende grSetze)) (a b : World grD),
      RufEreignisF.grund grSetze .nil r a b ∈ (M6.faeden 0).log ∧ b = M5.weltVon 0 := by
    rw [hG6.1]; exact ⟨_, _, _, List.mem_cons_self, rfl⟩
  refine ⟨M6, hr6, r, a, b, hm, (grPgut_zertifiziert M6 hr6).2 0 _ hm _ _ _ _ _ rfl, ?_, ?_⟩
  · rw [hb, hZ5.welt, hZ4.welt, hw3]
    simp [World.storeSlot, World.merke, World.lese, World.schreibSlot, Zahl.weiter, hsl3,
      grSp, grSchreib, grIdx, grWert, eval]
    rfl
  · rw [hb, hZ5.welt, hZ4.welt, hw3]
    simp [World.storeSlot, World.merke, World.lese, World.schreibSlot, Zahl.weiter, hsl3,
      grSp, grSchreib, grIdx, grWert, eval]
    rfl

#print axioms Gabbro.Grammatik.grPgut_frag
#print axioms Gabbro.Grammatik.grPgut_fuss
#print axioms Gabbro.Grammatik.grHaupt_fall
#print axioms Gabbro.Grammatik.grPgut_koerper
#print axioms Gabbro.Grammatik.grPschlecht_koerper
#print axioms Gabbro.Grammatik.grPgut_inv
#print axioms Gabbro.Grammatik.grPschlecht_inv
#print axioms Gabbro.Grammatik.grPgut_invGrund
#print axioms Gabbro.Grammatik.grPgut_zertifiziert
#print axioms Gabbro.Grammatik.grPschlecht_alt
#print axioms Gabbro.Grammatik.grPschlecht_nicht_invGutGrund
#print axioms Gabbro.Grammatik.grVorlauf
#print axioms Gabbro.Grammatik.grPschlecht_verletzt
#print axioms Gabbro.Grammatik.grGut_zeuge

end Gabbro.Grammatik
