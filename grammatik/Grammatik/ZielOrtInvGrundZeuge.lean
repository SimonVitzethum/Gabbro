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
        { konto[0] := 5; konto[1] := 5; return R }             -- igPgut
        { konto[0] := 5; return R }                            -- igPschlecht
      fn nichts() { return }

  Thread 0 starts in `haupt`, every other thread in `nichts`. Every contract
  is `true`. `setze` never returns a VALUE, so the value-return obligation
  `InvGutS` holds for both programs, and `ziel_ort_sperre_inv` certifies the
  broken one (`igPschlecht_alt`): its `setze` leaves by the reason with
  `konto[0] = 5`, `konto[1] = 0`, breaking the invariant it owes -- and on a
  reached machine the logged reason return shows it
  (`igPschlecht_verletzt`). The new obligation `InvGutGrund` refutes it
  (`igPschlecht_nicht_invGutGrund`); the correct program meets every
  premise of `ziel_ort_sperre_invAlle` (`igPgut_zertifiziert`), and on its
  reached run the logged reason return meets the invariant BY THE THEOREM
  (`igGut_zeuge`).
-/
import Grammatik.ZielOrtInvGrund
import Grammatik.InvZeuge

namespace Gabbro.Grammatik

/-! ## 1. The declaration -/

inductive IgFn where
  | haupt
  | setze
  | nichts
  deriving DecidableEq

def igSig (e : Option Ty) (n : Nat) (h : List Unit) (w : Bool) :
    Signatur Unit Empty Unit Empty where
  params := []
  erg := e
  gruende := n
  haelt := h
  schreibt := fun _ => w
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def igSigNr : Nat → Signatur Unit Empty Unit Empty
  | 0 => igSig none 0 [()] true
  | 1 => igSig (some .bool) 1 [()] true
  | _ => igSig none 0 [] false

/-- As `ivD`, with `setze` answering a `bool` and declaring one reason. -/
def igD : Deklaration where
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
  Fn := IgFn
  sig := fun | .haupt => 0 | .setze => 1 | .nichts => 2
  sigNr := igSigNr
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
    | n + 2, h => simp [igSigNr, igSig] at h
  ggeteilt_bewacht := fun e => nomatch e

def igHaupt : igD.Fn := IgFn.haupt
def igSetze : igD.Fn := IgFn.setze
def igNichts : igD.Fn := IgFn.nichts

abbrev igL : List (Res igD) := [Res.held (D := igD) ()]

theorem igDarf : darf igD () igL := by
  intro w h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  rw [e]
  exact List.mem_singleton.mpr rfl

/-! ## 2. The invariant and the bodies -/

def igIdx {Γ : Ctx} {Λ : List (Res igD)} (k : Int) (h0 : 0 ≤ k) (h1 : k ≤ 1) :
    Expr igD Γ Λ (.index (igD.count ())) :=
  .weiter (lo := k) (hi := k) h0 h1 (.lit k)

def igWert {Γ : Ctx} {Λ : List (Res igD)} (k : Int) (h0 : 0 ≤ k) (h1 : k ≤ 10) :
    Expr igD Γ Λ (igD.typ () ()) :=
  .weiter (lo := k) (hi := k) h0 h1 (.lit k)

/-- `invariant gleich: konto[0] == konto[1]`. -/
def igInv : Expr igD [] (invSicht igD ()) .bool :=
  .eq (show Expr igD [] (invSicht igD ()) (.int 0 10) from
        .slot () () (igIdx 0 (by decide) (by decide)) igDarf)
      (show Expr igD [] (invSicht igD ()) (.int 0 10) from
        .slot () () (igIdx 1 (by decide) (by decide)) igDarf)

/-- `konto[k] := v` in a function that writes `konto`. -/
def igSchreib (f : igD.Fn) (hw : (vertragVon igD f).schreibt () = true) {Γ : Ctx} (k v : Int)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 10) :
    Stmt igD (vertragVon igD f) false Γ igL igL :=
  .assignSlot () () (igIdx k hk0 hk1) (igWert v hv0 hv1) hw igDarf

def igS0 : Stmt igD (vertragVon igD igSetze) false [] igL igL :=
  igSchreib igSetze rfl 0 5 (by decide) (by decide) (by decide) (by decide)
def igS1 : Stmt igD (vertragVon igD igSetze) false [] igL igL :=
  igSchreib igSetze rfl 1 5 (by decide) (by decide) (by decide) (by decide)

/-- `return R` from `setze`. -/
def igGrund : Endblock igD (vertragVon igD igSetze) false [] igL :=
  .retGrund ⟨0, by decide⟩ (List.Perm.refl _)

/-- `setze` (correct): both slots `5`, then the reason. -/
def igRumpfGut : Endblock igD (vertragVon igD igSetze) false [] igL :=
  .cons igS0 (.cons igS1 igGrund)

/-- `setze` (broken): only slot `0`, then the reason. -/
def igRumpfSchlecht : Endblock igD (vertragVon igD igSetze) false [] igL :=
  .cons igS0 igGrund

/-- The call of `setze` from `haupt`: both hold `L` by signature. -/
theorem igHp : RufPasst igD (vertragVon igD igHaupt) (igD.signatur igSetze) igL where
  hw := fun _ _ => rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp⟩
  hh := fun L _ => by cases L; exact List.mem_singleton.mpr rfl
  hx := fun L _ hn => absurd (by cases L; exact List.mem_singleton.mpr rfl) hn

/-- `konto[k] := 1` in `haupt`, at any context. -/
def igH (Γ : Ctx) (k : Int) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) :
    Stmt igD (vertragVon igD igHaupt) false Γ igL igL :=
  igSchreib igHaupt rfl (Γ := Γ) k 1 hk0 hk1 (by decide) (by decide)

/-- The reason branch of `haupt`: re-establish, return. -/
def igErr : Endblock igD (vertragVon igD igHaupt) false (.grund (igD.gruende igSetze) :: [])
    (nach igD igSetze igL) :=
  .cons (igH _ 0 (by decide) (by decide)) (.cons (igH _ 1 (by decide) (by decide))
    (.ret .keine (List.Perm.refl _)))

/-- `let x = setze() else { r => … }`, the value branch empty. -/
def igB : Block igD (vertragVon igD igHaupt) false [] igL igL :=
  .bindCallElse igSetze .nil rfl igHp (by decide) igErr .nil

/-- The tail of `haupt`: re-establish, return. -/
def igTail : Endblock igD (vertragVon igD igHaupt) false [] igL :=
  .cons (igH [] 0 (by decide) (by decide)) (.cons (igH [] 1 (by decide) (by decide))
    (.ret .keine (List.Perm.refl _)))

def igRumpfHaupt : Endblock igD (vertragVon igD igHaupt) false [] igL :=
  .cons (.breaking () igB) igTail

def igRumpfNichts : Endblock igD (vertragVon igD igNichts) false [] [] :=
  .ret .keine List.Perm.nil

def igP (setze : Endblock igD (vertragVon igD igSetze) false [] igL) : Programm igD where
  invariante := fun _ => igInv
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf
    | .haupt => igRumpfHaupt
    | .setze => setze
    | .nichts => igRumpfNichts

def igPgut : Programm igD := igP igRumpfGut
def igPschlecht : Programm igD := igP igRumpfSchlecht

/-! ## 3. The fixed premises -/

def igFs : List igD.Fn := [igHaupt, igSetze, igNichts]

theorem igFs_voll : ∀ g : igD.Fn, g ∈ igFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

def igO : Orakel igD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem igO_gut : GutO igO := fun a => nomatch a

theorem igO_lokal : RegLokal igO := ⟨(fun r _ _ _ => nomatch r), (fun g _ _ _ => nomatch g)⟩

def igSp : Speicher igD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- Thread `0` runs `haupt`, every other thread `nichts`. -/
def igInit : Faden → Σ f : igD.Fn, Env igD (igD.params f) :=
  fun t => if t = 0 then ⟨igHaupt, .nil⟩ else ⟨igNichts, .nil⟩

theorem igInit_sonst {t : Faden} (ht : t ≠ 0) : igInit t = ⟨igNichts, .nil⟩ := if_neg ht

theorem igStart (setze : Endblock igD (vertragVon igD igSetze) false [] igL) :
    StartGut (igP setze) igSp igInit := by
  intro t
  by_cases ht : t = 0
  · subst ht; rfl
  · rw [igInit_sonst ht]; rfl

theorem igInit_exklusiv : StartExklusiv (D := igD) igInit := by
  intro t u htu L hL hL'
  by_cases ht : t = 0
  · have hu : u ≠ 0 := fun h => htu (ht.trans h.symm)
    rw [igInit_sonst hu] at hL'
    exact absurd hL' List.not_mem_nil
  · rw [igInit_sonst ht] at hL
    exact absurd hL List.not_mem_nil

def igE0 : Ereignis igD := .gibt ()

theorem igPgut_frag : programmImFragmentG igPgut igFs = true := by decide
theorem igPschlecht_frag : programmImFragmentG igPschlecht igFs = true := by decide
theorem igPgut_fuss : fussSperreB igPgut (SperrInv.leer igD) igFs = true := by decide
theorem igPschlecht_fuss : fussSperreB igPschlecht (SperrInv.leer igD) igFs = true := by decide

/-! ## 4. The obligations -/

/-- **`haupt` against any handler**: the answer of `setze` decides the
    path -- a value continues to the tail, a reason runs the else branch,
    `logik`/hardware answers end the body. -/
theorem igHaupt_fall (S : SperrInv igD) (O : Orakel igD) (U : Umwelt igD) (passes : Nat)
    (setze : Endblock igD (vertragVon igD igSetze) false [] igL)
    (R : ∀ f : igD.Fn, World igD → Env igD (igD.params f) → RufAusgang f)
    (σ : World igD) (ρ : Env igD (igD.params igHaupt)) :
    (∃ σ1 v1, R igSetze (σ.lese igL []) .nil = .ok σ1 v1 ∧
      execEndH (V := vertragVon igD igHaupt) S O U passes R ((igP setze).rumpf igHaupt) σ ρ =
        execEndH S O U passes R igTail σ1 ρ) ∨
    (∃ σ1 r1, R igSetze (σ.lese igL []) .nil = .grund σ1 r1 ∧
      execEndH (V := vertragVon igD igHaupt) S O U passes R ((igP setze).rumpf igHaupt) σ ρ =
        (execEndH S O U passes R igErr σ1 (.cons r1 ρ)).schrumpf) ∨
    (∃ e1, R igSetze (σ.lese igL []) .nil = .logik e1 ∧
      execEndH (V := vertragVon igD igHaupt) S O U passes R ((igP setze).rumpf igHaupt) σ ρ =
        .logik e1) ∨
    (∃ e1, execEndH (V := vertragVon igD igHaupt) S O U passes R ((igP setze).rumpf igHaupt) σ ρ =
        .hardware e1) := by
  cases hR : R igSetze (σ.lese igL []) .nil with
  | ok σ1 v1 =>
      refine Or.inl ⟨σ1, v1, rfl, ?_⟩
      show execEndH S O U passes R igRumpfHaupt σ ρ = _
      simp only [igRumpfHaupt, igB, execEndH, execStmtH, execBlockH, Args.orte, evalArgs, hR]
      rfl
  | grund σ1 r1 =>
      refine Or.inr (Or.inl ⟨σ1, r1, rfl, ?_⟩)
      show execEndH S O U passes R igRumpfHaupt σ ρ = _
      simp only [igRumpfHaupt, igB, execEndH, execStmtH, execBlockH, Args.orte, evalArgs, hR]
      cases execEndH S O U passes R igErr σ1 (.cons r1 ρ) <;> rfl
  | logik e1 =>
      refine Or.inr (Or.inr (Or.inl ⟨e1, rfl, ?_⟩))
      show execEndH S O U passes R igRumpfHaupt σ ρ = _
      simp only [igRumpfHaupt, igB, execEndH, execStmtH, execBlockH, Args.orte, evalArgs, hR]
      rfl
  | hardware e1 =>
      refine Or.inr (Or.inr (Or.inr ⟨e1, ?_⟩))
      show execEndH S O U passes R igRumpfHaupt σ ρ = _
      simp only [igRumpfHaupt, igB, execEndH, execStmtH, execBlockH, Args.orte, evalArgs, hR]
      rfl

theorem ig_koerper_nichts (setze : Endblock igD (vertragVon igD igSetze) false [] igL) :
    KoerperGutS (igP setze) 0 (axWahr igD) (SperrInv.leer igD) igNichts := by
  have hr : (igP setze).rumpf igNichts = igRumpfNichts := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [igRumpfNichts, execEndH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [igRumpfNichts, execEndH] at hrun
    cases hrun

theorem ig_koerper_gut : KoerperGutS igPgut 0 (axWahr igD) (SperrInv.leer igD) igSetze := by
  have hr : igPgut.rumpf igSetze = igRumpfGut := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [igRumpfGut, igS0, igS1, igSchreib, igGrund, execEndH, execStmtH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [igRumpfGut, igS0, igS1, igSchreib, igGrund, execEndH, execStmtH] at hrun
    cases hrun

theorem ig_koerper_schlecht : KoerperGutS igPschlecht 0 (axWahr igD) (SperrInv.leer igD) igSetze := by
  have hr : igPschlecht.rumpf igSetze = igRumpfSchlecht := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [igRumpfSchlecht, igS0, igSchreib, igGrund, execEndH, execStmtH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [igRumpfSchlecht, igS0, igSchreib, igGrund, execEndH, execStmtH] at hrun
    cases hrun

theorem ig_koerper_haupt (setze : Endblock igD (vertragVon igD igSetze) false [] igL) :
    KoerperGutS (igP setze) 0 (axWahr igD) (SperrInv.leer igD) igHaupt := by
  refine ⟨fun O' _ _ _ U _ R hR hOV σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R hR hOL σ ρ _ e hrun => ?_⟩
  · rcases igHaupt_fall (SperrInv.leer igD) O' U 0 setze (torRuf (igP setze) R) σ ρ with
      ⟨σ1, v1, _, h1⟩ | ⟨σ1, r1, _, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> rw [h1] at hrun
    · simp only [igTail, igH, igSchreib, execEndH, execStmtH] at hrun
      cases hrun
    · simp only [igErr, igH, igSchreib, execEndH, execStmtH, EndAusgang.schrumpf] at hrun
      cases hrun
    · cases hrun
      exact hOV _ _ _ _ he1 g rfl
    · cases hrun
  · rcases igHaupt_fall (SperrInv.leer igD) O' U 0 setze R σ ρ with
      ⟨σ1, v1, _, h1⟩ | ⟨σ1, r1, _, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> rw [h1] at hrun
    · simp only [igTail, igH, igSchreib, execEndH, execStmtH] at hrun
      cases hrun
    · simp only [igErr, igH, igSchreib, execEndH, execStmtH, EndAusgang.schrumpf] at hrun
      cases hrun
    · cases hrun
      exact hOL _ _ _ _ he1
    · cases hrun

theorem igPgut_koerper : ∀ f : igD.Fn, KoerperGutS igPgut 0 (axWahr igD) (SperrInv.leer igD) f
  | .haupt => ig_koerper_haupt _
  | .setze => ig_koerper_gut
  | .nichts => ig_koerper_nichts _

theorem igPschlecht_koerper :
    ∀ f : igD.Fn, KoerperGutS igPschlecht 0 (axWahr igD) (SperrInv.leer igD) f
  | .haupt => ig_koerper_haupt _
  | .setze => ig_koerper_schlecht
  | .nichts => ig_koerper_nichts _

/-- `haupt` meets its owed invariant at every VALUE return: both paths
    re-establish it. -/
theorem ig_inv_haupt (setze : Endblock igD (vertragVon igD igSetze) false [] igL) :
    InvGutS (igP setze) 0 (axWahr igD) (SperrInv.leer igD) igHaupt := by
  intro O' _ _ _ U _ R _ _ σ ρ _ σ' v hrun
  rcases igHaupt_fall (SperrInv.leer igD) O' U 0 setze R σ ρ with
    ⟨σ1, v1, _, h1⟩ | ⟨σ1, r1, _, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> rw [h1] at hrun
  · simp only [igTail, igH, igSchreib, execEndH, execStmtH] at hrun
    cases hrun
    intro i _ _
    cases i
    simp [InvHaelt, igP, igInv, igIdx, igWert, eval, World.storeSlot, World.merke,
      World.lese, World.schreibSlot, Zahl.weiter]
    rfl
  · simp only [igErr, igH, igSchreib, execEndH, execStmtH, EndAusgang.schrumpf] at hrun
    cases hrun
    intro i _ _
    cases i
    simp [InvHaelt, igP, igInv, igIdx, igWert, eval, World.storeSlot, World.merke,
      World.lese, World.schreibSlot, Zahl.weiter]
    rfl
  · cases hrun
  · cases hrun

/-- `setze` never returns a VALUE: the value-return obligation holds for
    both bodies, whatever they do to `konto`. -/
theorem ig_inv_setze (setze : Endblock igD (vertragVon igD igSetze) false [] igL)
    (h : setze = igRumpfGut ∨ setze = igRumpfSchlecht) :
    InvGutS (igP setze) 0 (axWahr igD) (SperrInv.leer igD) igSetze := by
  intro O' _ _ _ U _ R _ _ σ ρ _ σ' v hrun
  have hr : (igP setze).rumpf igSetze = setze := rfl
  rw [hr] at hrun
  rcases h with rfl | rfl
  · simp only [igRumpfGut, igS0, igS1, igSchreib, igGrund, execEndH, execStmtH] at hrun
    cases hrun
  · simp only [igRumpfSchlecht, igS0, igSchreib, igGrund, execEndH, execStmtH] at hrun
    cases hrun

theorem ig_inv_nichts (setze : Endblock igD (vertragVon igD igSetze) false [] igL) :
    InvGutS (igP setze) 0 (axWahr igD) (SperrInv.leer igD) igNichts :=
  invGutS_ohne fun _ _ => rfl

theorem igPgut_inv : ∀ f : igD.Fn, InvGutS igPgut 0 (axWahr igD) (SperrInv.leer igD) f
  | .haupt => ig_inv_haupt _
  | .setze => ig_inv_setze _ (Or.inl rfl)
  | .nichts => ig_inv_nichts _

theorem igPschlecht_inv : ∀ f : igD.Fn, InvGutS igPschlecht 0 (axWahr igD) (SperrInv.leer igD) f
  | .haupt => ig_inv_haupt _
  | .setze => ig_inv_setze _ (Or.inr rfl)
  | .nichts => ig_inv_nichts _

/-- **The correct `setze` meets the new obligation**: its reason exit leaves
    both slots `5`. -/
theorem ig_invGrund_gut : Zielsatz.InvGutGrund igPgut 0 (axWahr igD) (SperrInv.leer igD) igSetze := by
  intro O' _ _ _ U _ R _ _ σ ρ _ σ' r hrun
  have hr : igPgut.rumpf igSetze = igRumpfGut := rfl
  rw [hr] at hrun
  simp only [igRumpfGut, igS0, igS1, igSchreib, igGrund, execEndH, execStmtH] at hrun
  cases hrun
  intro i _ _
  cases i
  simp [InvHaelt, igPgut, igP, igInv, igIdx, igWert, eval, World.storeSlot, World.merke,
    World.lese, World.schreibSlot, Zahl.weiter]
  rfl

theorem igPgut_invGrund :
    ∀ f : igD.Fn, Zielsatz.InvGutGrund igPgut 0 (axWahr igD) (SperrInv.leer igD) f
  | .haupt => invGutGrund_ohneGrund rfl
  | .setze => ig_invGrund_gut
  | .nichts => invGutGrund_ohneGrund rfl

/-! ## 5. The certified and the refuted program -/

/-- **`igPgut` is certified by `ziel_ort_sperre_invAlle`**: every premise,
    the reason obligation included. -/
theorem igPgut_zertifiziert : ∀ M : RufMaschineG igD,
    RufErreichbarG igPgut igO 0 (RufStartG igPgut igSp igInit) M →
      InvAmOrtG igPgut M ∧ Zielsatz.InvAmGrundG igPgut M :=
  ziel_ort_sperre_invAlle igPgut igO 0 (axWahr igD) (SperrInv.leer igD) igFs igSp igInit igE0
    igO_gut igO_lokal (axVertragO_wahr igO) axEnsLokal_wahr sperrInvOk_leer igFs_voll igPgut_frag
    igPgut_fuss igPgut_koerper (igStart _) (fun _ => rfl) igInit_exklusiv igPgut_inv
    igPgut_invGrund

/-- **The broken program was certified by `ziel_ort_sperre_inv`** (every
    premise holds: `setze` never returns a value) -- the gap this file
    closes. -/
theorem igPschlecht_alt : ∀ M : RufMaschineG igD,
    RufErreichbarG igPschlecht igO 0 (RufStartG igPschlecht igSp igInit) M →
      (VertragAmOrtG igPschlecht M ∧ SperrInvG (SperrInv.leer igD) M ∧ KeinLogikHaltG igO 0 M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG igPschlecht igO 0 M t M') ∧
      InvAmOrtG igPschlecht M :=
  ziel_ort_sperre_inv igPschlecht igO 0 (axWahr igD) (SperrInv.leer igD) igFs igSp igInit igE0
    igO_gut igO_lokal (axVertragO_wahr igO) axEnsLokal_wahr sperrInvOk_leer igFs_voll
    igPschlecht_frag igPschlecht_fuss igPschlecht_koerper (igStart _) (fun _ => rfl)
    igInit_exklusiv igPschlecht_inv

/-- The identity environment move meets `HavocOk` of the empty family. -/
theorem ig_havoc : HavocOk (SperrInv.leer igD) (fun _ σ => σ) :=
  fun _ _ => ⟨rfl, fun c _ => traegerGleich_refl _ c, rfl⟩

/-- **The new obligation fails for the broken `setze`**: from the zero
    memory its body leaves by the reason with `konto[0] = 5`,
    `konto[1] = 0`. -/
theorem igPschlecht_nicht_invGutGrund :
    ¬ Zielsatz.InvGutGrund igPschlecht 0 (axWahr igD) (SperrInv.leer igD) igSetze := by
  intro h
  have h3 := h igO (gutO_rahmenO igO_gut) igO_lokal (axVertragO_wahr igO) (fun _ σ => σ) ig_havoc
    (rufAusV []) (rufAusV_rahmen (vertraegeOkR_nil igPschlecht))
    (rufAusV_ohneVorbedingung (vertraegeOkR_nil igPschlecht).1) (igSp.welt []) .nil rfl _ _ rfl ()
    (List.mem_singleton.mpr rfl) rfl
  revert h3
  simp [InvHaelt, igPschlecht, igP, igInv, igIdx, igWert, eval, World.storeSlot, World.merke,
    World.lese, World.schreibSlot, Zahl.weiter, igSp, Speicher.welt]
  decide

/-! ## 6. The runs -/

theorem igM0_faden0 (setze : Endblock igD (vertragVon igD igSetze) false [] igL) :
    (RufStartG (igP setze) igSp igInit).faeden 0 =
    ⟨[], ⟨igHaupt, .nil, igSp.welt [], ⟨false, [], igL, .nil, .ende igRumpfHaupt⟩⟩,
      startSpur igHaupt, [RufEreignisF.eintritt igHaupt .nil (igSp.welt [])]⟩ := rfl

theorem igHeld {s : List (Ereignis igD)} (h : offen s = [()]) : HeldIn igL (offen s) :=
  fun L _ => by cases L; rw [h]; exact List.mem_singleton.mpr rfl

/-- **The run to the reason return of `setze`**, for either body: `haupt`
    unfolds `breaking` (1, 2), calls `setze` through `let … else` (3),
    `setze` writes slot `0` (4). -/
theorem igVorlauf (setze : Endblock igD (vertragVon igD igSetze) false [] igL) :
    ∃ (M3 : RufMaschineG igD) (s0 : World igD) (log : List (RufEreignisF igD)),
      RufErreichbarG (igP setze) igO 0 (RufStartG (igP setze) igSp igInit) M3 ∧
      M3.faeden 0 = ⟨[⟨igHaupt, .nil, igSp.welt [],
          ⟨false, [], igL, .nil, .wartetSonst (τ := .bool) (igD.gruende igSetze) igErr .nil
            (.dann .nil (.ende igTail))⟩⟩],
        ⟨igSetze, .nil, s0, ⟨false, [], igL, .nil, .ende setze⟩⟩,
        s0.spur, log⟩ ∧
      M3.weltVon 0 = s0 ∧ offen s0.spur = [()] ∧
      s0.slots = igSp.slots := by
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := igP setze) (O := igO) (passes := 0)
    (igM0_faden0 setze) (.breaking () igB) igTail .nil rfl rfl
  obtain ⟨M2, s2, hZ2⟩ := w_breaking (P := igP setze) (O := igO) (passes := 0) hZ1.1 () igB .nil
    (.ende igTail) .nil rfl
  have hoff2 : offen (M1.weltVon 0).spur = [()] := by
    rw [hZ1.welt]
    rfl
  obtain ⟨M3, s3, hZ3⟩ := w_bindCallElse (P := igP setze) (O := igO) (passes := 0) hZ2.1 igSetze
    .nil rfl igHp (by decide) igErr .nil (.dann .nil (.ende igTail)) .nil rfl (igHeld hoff2)
  refine ⟨M3, _, _, .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3,
    hZ3.1, hZ3.welt, ?_, ?_⟩
  · show offen ((M2.weltVon 0).lese igL []).spur = [()]
    rw [(Erw.lese _ _ _).offen, hZ2.welt]
    exact hoff2
  · show ((M2.weltVon 0).lese igL []).slots = igSp.slots
    rw [hZ2.welt, hZ1.welt]
    rfl

/-- **The new conclusion fails on a machine of `igPschlecht` reachable in
    five steps** (thread 0: `haupt` unfolds `breaking`, calls `setze`
    through `let … else`, `setze` writes slot `0` and leaves by the
    reason): the logged reason return of `setze` breaks the invariant --
    while `igPschlecht_alt` certified the program. -/
theorem igPschlecht_verletzt : ∃ M : RufMaschineG igD,
    RufErreichbarG igPschlecht igO 0 (RufStartG igPschlecht igSp igInit) M ∧
    ¬ Zielsatz.InvAmGrundG igPschlecht M := by
  obtain ⟨M3, s0, log, hr3, hz3, hw3, hoff3, hsl3⟩ := igVorlauf igRumpfSchlecht
  obtain ⟨M4, s4, hZ4⟩ := w_blatt (P := igPschlecht) (O := igO) (passes := 0) hz3 igS0 igGrund
    .nil rfl rfl (igHeld hoff3) _ _ rfl
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff4 : offen (M4.faeden 0).spur = [()] := by
    rw [hZ4.spur]
    exact ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen.trans
      (by rw [hw3]; exact hoff3)
  obtain ⟨M5, s5, hG5⟩ := w_rueckGrundP (P := igPschlecht) (O := igO) (passes := 0) hZ4.1 _ _ rfl
    (PopGrund.sonst igErr .nil (.dann .nil (.ende igTail)) .nil rfl) ⟨0, Nat.zero_lt_one⟩
    (List.Perm.refl igL) .nil rfl (by rw [← hZ4.1]; exact igHeld hoff4)
  refine ⟨M5, .schritt _ _ _ (.schritt _ _ _ hr3 s4) s5, fun h => ?_⟩
  have h3 := h 0 _ (by rw [hG5.1]; exact List.mem_cons_self) _ _ _ _ _ rfl ()
    (List.mem_singleton.mpr rfl) rfl
  revert h3
  rw [hZ4.welt, hw3]
  simp [InvHaelt, igPschlecht, igP, igInv, igIdx, igWert, eval, World.storeSlot, World.merke,
    World.lese, World.schreibSlot, Zahl.weiter, hsl3, igSp]
  rfl

/-- **`igGut_zeuge`**: on a machine of `igPgut` reached in six steps
    (thread 0: `haupt` calls `setze` through `let … else`, `setze` writes
    both slots and leaves by the reason), the logged reason return of
    `setze` meets the invariant it owes BY THE THEOREM
    (`igPgut_zertifiziert`), at a world whose two slots hold `5`. -/
theorem igGut_zeuge : ∃ M : RufMaschineG igD,
    RufErreichbarG igPgut igO 0 (RufStartG igPgut igSp igInit) M ∧
    ∃ (r : Fin (igD.gruende igSetze)) (s0 s1 : World igD),
      RufEreignisF.grund igSetze .nil r s0 s1 ∈ (M.faeden 0).log ∧
      InvAmRueck igPgut igSetze s1 ∧
      (s1.slots () 0 ()).n = 5 ∧ (s1.slots () 1 ()).n = 5 := by
  obtain ⟨M3, s0, log, hr3, hz3, hw3, hoff3, hsl3⟩ := igVorlauf igRumpfGut
  obtain ⟨M4, s4, hZ4⟩ := w_blatt (P := igPgut) (O := igO) (passes := 0) hz3 igS0 (.cons igS1 igGrund)
    .nil rfl rfl (igHeld hoff3) _ _ rfl
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff4 : offen (M4.faeden 0).spur = [()] := by
    rw [hZ4.spur]
    exact ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen.trans
      (by rw [hw3]; exact hoff3)
  have e4 := hZ4.1
  obtain ⟨M5, s5, hZ5⟩ := w_blatt (P := igPgut) (O := igO) (passes := 0) e4 igS1 igGrund
    .nil rfl rfl (by rw [← e4]; exact igHeld hoff4) _ _ rfl
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff5 : offen (M5.faeden 0).spur = [()] := by
    rw [hZ5.spur]
    exact ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen.trans
      hoff4
  obtain ⟨M6, s6, hG6⟩ := w_rueckGrundP (P := igPgut) (O := igO) (passes := 0) hZ5.1 _ _ rfl
    (PopGrund.sonst igErr .nil (.dann .nil (.ende igTail)) .nil rfl) ⟨0, Nat.zero_lt_one⟩
    (List.Perm.refl igL) .nil rfl (by rw [← hZ5.1]; exact igHeld hoff5)
  have hr6 : RufErreichbarG igPgut igO 0 (RufStartG igPgut igSp igInit) M6 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ hr3 s4) s5) s6
  obtain ⟨r, a, b, hm, hb⟩ : ∃ (r : Fin (igD.gruende igSetze)) (a b : World igD),
      RufEreignisF.grund igSetze .nil r a b ∈ (M6.faeden 0).log ∧ b = M5.weltVon 0 := by
    rw [hG6.1]; exact ⟨_, _, _, List.mem_cons_self, rfl⟩
  refine ⟨M6, hr6, r, a, b, hm, (igPgut_zertifiziert M6 hr6).2 0 _ hm _ _ _ _ _ rfl, ?_, ?_⟩
  · rw [hb, hZ5.welt, hZ4.welt, hw3]
    simp [World.storeSlot, World.merke, World.lese, World.schreibSlot, Zahl.weiter, hsl3,
      igSp, igSchreib, igIdx, igWert, eval]
    rfl
  · rw [hb, hZ5.welt, hZ4.welt, hw3]
    simp [World.storeSlot, World.merke, World.lese, World.schreibSlot, Zahl.weiter, hsl3,
      igSp, igSchreib, igIdx, igWert, eval]
    rfl

#print axioms Gabbro.Grammatik.igPgut_frag
#print axioms Gabbro.Grammatik.igPgut_fuss
#print axioms Gabbro.Grammatik.igHaupt_fall
#print axioms Gabbro.Grammatik.igPgut_koerper
#print axioms Gabbro.Grammatik.igPschlecht_koerper
#print axioms Gabbro.Grammatik.igPgut_inv
#print axioms Gabbro.Grammatik.igPschlecht_inv
#print axioms Gabbro.Grammatik.igPgut_invGrund
#print axioms Gabbro.Grammatik.igPgut_zertifiziert
#print axioms Gabbro.Grammatik.igPschlecht_alt
#print axioms Gabbro.Grammatik.igPschlecht_nicht_invGutGrund
#print axioms Gabbro.Grammatik.igVorlauf
#print axioms Gabbro.Grammatik.igPschlecht_verletzt
#print axioms Gabbro.Grammatik.igGut_zeuge

end Gabbro.Grammatik
