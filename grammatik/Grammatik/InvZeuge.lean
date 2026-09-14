/-
  Gabbro/Grammatik/InvZeuge.lean

  **Witnesses for `ziel_ort_sperre_inv`** (table invariants, SATZKARTE
  §15.4).

      lock L protects konto (two slots, 0 .. 10) rank 0
      invariant gleich: konto[0] == konto[1]        -- carriers: konto
      fn haupt()  holds L, writes konto { setze(); konto[0] := 1; konto[1] := 1; return }
      fn setze()  holds L, writes konto { konto[0] := 5; konto[1] := 5; return }   -- ivPgut
      fn setze()  holds L, writes konto { konto[0] := 5; return }                  -- ivPschlecht
      fn nichts() { return }

  Thread 0 starts in `haupt`, every other thread in `nichts`. Every contract
  is `true`, so `ziel_ort_sperre` certifies BOTH programs
  (`ivPschlecht_alt`) -- the gap: `setze` of `ivPschlecht` returns with
  `konto[0] = 5`, `konto[1] = 0`, breaking the invariant it owes.

  * `ivPgut_zertifiziert`: every premise of `ziel_ort_sperre_inv` holds on
    `ivPgut` (the new obligation `InvGutS` proved per function).
    `ivGut_zeuge`: on a reached run (thread 0 calls `setze`, which writes
    both slots and returns) the logged return meets the invariant BY THE
    THEOREM, at a world where both slots hold `5`.
  * `ivPschlecht_nicht_invGutS`: the new obligation FAILS for `setze` of
    `ivPschlecht`; `ivPschlecht_verletzt`: the new conclusion fails on a
    machine reachable in three steps. A refutation, where `ziel_ort_sperre`
    certified.
-/
import Grammatik.ZielOrtInv
import Grammatik.ZielOrtSperreZeuge

namespace Gabbro.Grammatik

/-! ## 1. The declaration -/

inductive IvFn where
  | haupt
  | setze
  | nichts
  deriving DecidableEq

def ivSigL : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := [()]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def ivSigFrei : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- One table `konto` (two slots, `0 .. 10`) guarded by the lock `()`, one
    invariant over it; `haupt` and `setze` hold the lock by signature and
    write `konto`, `nichts` neither. -/
def ivD : Deklaration where
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
  Fn := IvFn
  sig := fun | .haupt => 0 | .setze => 0 | .nichts => 1
  sigNr := fun | 0 => ivSigL | _ => ivSigFrei
  eigner_nie_erzeugt := fun n _ _ _ h => by
    cases n with
    | zero => simp at h
    | succ n => simp at h
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
    cases n with
    | zero => cases L; exact List.mem_singleton.mpr rfl
    | succ n => simp [ivSigFrei] at h
  ggeteilt_bewacht := fun e => nomatch e

def ivHaupt : ivD.Fn := IvFn.haupt
def ivSetze : ivD.Fn := IvFn.setze
def ivNichts : ivD.Fn := IvFn.nichts

abbrev ivL : List (Res ivD) := [Res.held (D := ivD) ()]

theorem ivDarf : darf ivD () ivL := by
  intro w h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  rw [e]
  exact List.mem_singleton.mpr rfl

/-! ## 2. The invariant and the bodies -/

def ivIdx {Λ : List (Res ivD)} (k : Int) (h0 : 0 ≤ k) (h1 : k ≤ 1) :
    Expr ivD [] Λ (.index (ivD.count ())) :=
  .weiter (lo := k) (hi := k) h0 h1 (.lit k)

def ivWert {Λ : List (Res ivD)} (k : Int) (h0 : 0 ≤ k) (h1 : k ≤ 10) :
    Expr ivD [] Λ (ivD.typ () ()) :=
  .weiter (lo := k) (hi := k) h0 h1 (.lit k)

theorem ivInvSicht : invSicht ivD () = ivL := rfl

/-- `invariant gleich: konto[0] == konto[1]`. -/
def ivInv : Expr ivD [] (invSicht ivD ()) .bool :=
  .eq (show Expr ivD [] (invSicht ivD ()) (.int 0 10) from
        .slot () () (ivIdx 0 (by decide) (by decide)) ivDarf)
      (show Expr ivD [] (invSicht ivD ()) (.int 0 10) from
        .slot () () (ivIdx 1 (by decide) (by decide)) ivDarf)

/-- `konto[k] := v` in a function that writes `konto`. -/
def ivSchreib (f : ivD.Fn) (hw : (vertragVon ivD f).schreibt () = true) (k v : Int)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 10) :
    Stmt ivD (vertragVon ivD f) false [] ivL ivL :=
  .assignSlot () () (ivIdx k hk0 hk1) (ivWert v hv0 hv1) hw ivDarf

def ivRetS : Endblock ivD (vertragVon ivD ivSetze) false [] ivL := .ret .keine (List.Perm.refl _)
def ivRetH : Endblock ivD (vertragVon ivD ivHaupt) false [] ivL := .ret .keine (List.Perm.refl _)

def ivS0 : Stmt ivD (vertragVon ivD ivSetze) false [] ivL ivL :=
  ivSchreib ivSetze rfl 0 5 (by decide) (by decide) (by decide) (by decide)
def ivS1 : Stmt ivD (vertragVon ivD ivSetze) false [] ivL ivL :=
  ivSchreib ivSetze rfl 1 5 (by decide) (by decide) (by decide) (by decide)

/-- `setze` (correct): both slots `5`. -/
def ivRumpfGut : Endblock ivD (vertragVon ivD ivSetze) false [] ivL :=
  .cons ivS0 (.cons ivS1 ivRetS)

/-- `setze` (broken): only slot `0`. -/
def ivRumpfSchlecht : Endblock ivD (vertragVon ivD ivSetze) false [] ivL :=
  .cons ivS0 ivRetS

/-- The call of `setze` from `haupt`: both hold `L` by signature. -/
theorem ivHp : RufPasst ivD (vertragVon ivD ivHaupt) (ivD.signatur ivSetze) ivL where
  hw := fun _ _ => rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp⟩
  hh := fun L _ => by cases L; exact List.mem_singleton.mpr rfl
  hx := fun L _ hn => absurd (by cases L; exact List.mem_singleton.mpr rfl) hn

def ivRuf : Stmt ivD (vertragVon ivD ivHaupt) false [] ivL ivL :=
  .call ivSetze .nil ivHp rfl

def ivH0 : Stmt ivD (vertragVon ivD ivHaupt) false [] ivL ivL :=
  ivSchreib ivHaupt rfl 0 1 (by decide) (by decide) (by decide) (by decide)
def ivH1 : Stmt ivD (vertragVon ivD ivHaupt) false [] ivL ivL :=
  ivSchreib ivHaupt rfl 1 1 (by decide) (by decide) (by decide) (by decide)

def ivHauptRest : Endblock ivD (vertragVon ivD ivHaupt) false [] ivL :=
  .cons ivH0 (.cons ivH1 ivRetH)

/-- `haupt`: call `setze`, then re-establish the invariant itself. -/
def ivRumpfHaupt : Endblock ivD (vertragVon ivD ivHaupt) false [] ivL :=
  .cons ivRuf ivHauptRest

def ivRumpfNichts : Endblock ivD (vertragVon ivD ivNichts) false [] [] :=
  .ret .keine List.Perm.nil

def ivP (setze : Endblock ivD (vertragVon ivD ivSetze) false [] ivL) : Programm ivD where
  invariante := fun _ => ivInv
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf
    | .haupt => ivRumpfHaupt
    | .setze => setze
    | .nichts => ivRumpfNichts

def ivPgut : Programm ivD := ivP ivRumpfGut
def ivPschlecht : Programm ivD := ivP ivRumpfSchlecht

/-! ## 3. The fixed premises -/

def ivFs : List ivD.Fn := [ivHaupt, ivSetze, ivNichts]

theorem ivFs_voll : ∀ g : ivD.Fn, g ∈ ivFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

def ivO : Orakel ivD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem ivO_gut : GutO ivO := fun a => nomatch a

theorem ivO_lokal : RegLokal ivO := ⟨(fun r _ _ _ => nomatch r), (fun g _ _ _ => nomatch g)⟩

def ivSp : Speicher ivD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- Thread `0` runs `haupt`, every other thread `nichts`. -/
def ivInit : Faden → Σ f : ivD.Fn, Env ivD (ivD.params f) :=
  fun t => if t = 0 then ⟨ivHaupt, .nil⟩ else ⟨ivNichts, .nil⟩

theorem ivInit_sonst {t : Faden} (ht : t ≠ 0) : ivInit t = ⟨ivNichts, .nil⟩ := if_neg ht

theorem ivStart (setze : Endblock ivD (vertragVon ivD ivSetze) false [] ivL) :
    StartGut (ivP setze) ivSp ivInit := by
  intro t
  by_cases ht : t = 0
  · subst ht; rfl
  · rw [ivInit_sonst ht]; rfl

theorem ivInit_exklusiv : StartExklusiv (D := ivD) ivInit := by
  intro t u htu L hL hL'
  by_cases ht : t = 0
  · have hu : u ≠ 0 := fun h => htu (ht.trans h.symm)
    rw [ivInit_sonst hu] at hL'
    exact absurd hL' List.not_mem_nil
  · rw [ivInit_sonst ht] at hL
    exact absurd hL List.not_mem_nil

def ivE0 : Ereignis ivD := .gibt ()

theorem ivPgut_frag : programmImFragmentG ivPgut ivFs = true := by decide
theorem ivPschlecht_frag : programmImFragmentG ivPschlecht ivFs = true := by decide
theorem ivPgut_fuss : fussSperreB ivPgut (SperrInv.leer ivD) ivFs = true := by decide
theorem ivPschlecht_fuss : fussSperreB ivPschlecht (SperrInv.leer ivD) ivFs = true := by decide


/-! ## 4. The obligations -/

theorem iv_koerper_nichts (setze : Endblock ivD (vertragVon ivD ivSetze) false [] ivL) :
    KoerperGutS (ivP setze) 0 (axWahr ivD) (SperrInv.leer ivD) ivNichts := by
  have hr : (ivP setze).rumpf ivNichts = ivRumpfNichts := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [ivRumpfNichts, execEndH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [ivRumpfNichts, execEndH] at hrun
    cases hrun

theorem iv_koerper_gut : KoerperGutS ivPgut 0 (axWahr ivD) (SperrInv.leer ivD) ivSetze := by
  have hr : ivPgut.rumpf ivSetze = ivRumpfGut := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [ivRumpfGut, ivS0, ivS1, ivSchreib, ivRetS, execEndH, execStmtH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [ivRumpfGut, ivS0, ivS1, ivSchreib, ivRetS, execEndH, execStmtH] at hrun
    cases hrun

theorem iv_koerper_schlecht : KoerperGutS ivPschlecht 0 (axWahr ivD) (SperrInv.leer ivD) ivSetze := by
  have hr : ivPschlecht.rumpf ivSetze = ivRumpfSchlecht := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [ivRumpfSchlecht, ivS0, ivSchreib, ivRetS, execEndH, execStmtH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [ivRumpfSchlecht, ivS0, ivSchreib, ivRetS, execEndH, execStmtH] at hrun
    cases hrun

theorem iv_koerper_haupt (setze : Endblock ivD (vertragVon ivD ivSetze) false [] ivL) :
    KoerperGutS (ivP setze) 0 (axWahr ivD) (SperrInv.leer ivD) ivHaupt := by
  have hr : (ivP setze).rumpf ivHaupt = ivRumpfHaupt := rfl
  refine ⟨fun O' _ _ _ U _ R hR hOV σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [ivRumpfHaupt, ivRuf, execEndH] at hrun
    rcases execStmtH_call_fall (S := SperrInv.leer ivD) (O := O') (U := U) (passes := 0)
      (R := torRuf (ivP setze) R) (l := false) (Γ := []) ivSetze .nil ivHp rfl σ ρ with
      ⟨σ1, v1, _, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · simp only [ivHauptRest, ivH0, ivH1, ivSchreib, ivRetH, execEndH, execStmtH] at hrun
      cases hrun
    · cases hrun
      exact hOV _ _ _ _ he1 g rfl
    · cases hrun
  · rw [hr] at hrun
    simp only [ivRumpfHaupt, ivRuf, execEndH] at hrun
    rcases execStmtH_call_fall (S := SperrInv.leer ivD) (O := O') (U := U) (passes := 0)
      (R := R) (l := false) (Γ := []) ivSetze .nil ivHp rfl σ ρ with
      ⟨σ1, v1, _, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · simp only [ivHauptRest, ivH0, ivH1, ivSchreib, ivRetH, execEndH, execStmtH] at hrun
      cases hrun
    · cases hrun
      exact hOL _ _ _ _ he1
    · cases hrun

theorem ivPgut_koerper : ∀ f : ivD.Fn, KoerperGutS ivPgut 0 (axWahr ivD) (SperrInv.leer ivD) f
  | .haupt => iv_koerper_haupt _
  | .setze => iv_koerper_gut
  | .nichts => iv_koerper_nichts _

theorem ivPschlecht_koerper :
    ∀ f : ivD.Fn, KoerperGutS ivPschlecht 0 (axWahr ivD) (SperrInv.leer ivD) f
  | .haupt => iv_koerper_haupt _
  | .setze => iv_koerper_schlecht
  | .nichts => iv_koerper_nichts _

theorem iv_inv_gut : InvGutS ivPgut 0 (axWahr ivD) (SperrInv.leer ivD) ivSetze := by
  intro O' _ _ _ U _ R _ _ σ ρ _ σ' v hrun
  have hr : ivPgut.rumpf ivSetze = ivRumpfGut := rfl
  rw [hr] at hrun
  simp only [ivRumpfGut, ivS0, ivS1, ivSchreib, ivRetS, execEndH, execStmtH] at hrun
  cases hrun
  intro i _ _
  cases i
  simp [InvHaelt, ivPgut, ivP, ivInv, ivIdx, ivWert, eval, World.storeSlot, World.merke,
    World.lese, World.schreibSlot, Zahl.weiter]
  rfl

theorem iv_inv_haupt (setze : Endblock ivD (vertragVon ivD ivSetze) false [] ivL) :
    InvGutS (ivP setze) 0 (axWahr ivD) (SperrInv.leer ivD) ivHaupt := by
  intro O' _ _ _ U _ R _ _ σ ρ _ σ' v hrun
  have hr : (ivP setze).rumpf ivHaupt = ivRumpfHaupt := rfl
  rw [hr] at hrun
  simp only [ivRumpfHaupt, ivRuf, execEndH] at hrun
  rcases execStmtH_call_fall (S := SperrInv.leer ivD) (O := O') (U := U) (passes := 0)
    (R := R) (l := false) (Γ := []) ivSetze .nil ivHp rfl σ ρ with
    ⟨σ1, v1, _, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
  · simp only [ivHauptRest, ivH0, ivH1, ivSchreib, ivRetH, execEndH, execStmtH] at hrun
    cases hrun
    intro i _ _
    cases i
    simp [InvHaelt, ivP, ivInv, ivIdx, ivWert, eval, World.storeSlot, World.merke,
      World.lese, World.schreibSlot, Zahl.weiter]
    rfl
  · cases hrun
  · cases hrun

theorem iv_inv_nichts (setze : Endblock ivD (vertragVon ivD ivSetze) false [] ivL) :
    InvGutS (ivP setze) 0 (axWahr ivD) (SperrInv.leer ivD) ivNichts :=
  invGutS_ohne fun _ _ => rfl

theorem ivPgut_inv : ∀ f : ivD.Fn, InvGutS ivPgut 0 (axWahr ivD) (SperrInv.leer ivD) f
  | .haupt => iv_inv_haupt _
  | .setze => iv_inv_gut
  | .nichts => iv_inv_nichts _

/-! ## 5. The correct program is certified -/

/-- **`ivPgut` is certified by `ziel_ort_sperre_inv`**: every premise,
    the new obligation included. -/
theorem ivPgut_zertifiziert : ∀ M : RufMaschineG ivD,
    RufErreichbarG ivPgut ivO 0 (RufStartG ivPgut ivSp ivInit) M →
      (VertragAmOrtG ivPgut M ∧ SperrInvG (SperrInv.leer ivD) M ∧ KeinLogikHaltG ivO 0 M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG ivPgut ivO 0 M t M') ∧
      InvAmOrtG ivPgut M :=
  ziel_ort_sperre_inv ivPgut ivO 0 (axWahr ivD) (SperrInv.leer ivD) ivFs ivSp ivInit ivE0 ivO_gut
    ivO_lokal (axVertragO_wahr ivO) axEnsLokal_wahr sperrInvOk_leer ivFs_voll ivPgut_frag
    ivPgut_fuss ivPgut_koerper (ivStart _) (fun _ => rfl) ivInit_exklusiv ivPgut_inv

/-- **The broken program was certified by `ziel_ort_sperre`** (every
    premise holds: its contracts are `true`) -- the gap this section closes. -/
theorem ivPschlecht_alt : ∀ M : RufMaschineG ivD,
    RufErreichbarG ivPschlecht ivO 0 (RufStartG ivPschlecht ivSp ivInit) M →
      VertragAmOrtG ivPschlecht M ∧ SperrInvG (SperrInv.leer ivD) M ∧ KeinLogikHaltG ivO 0 M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG ivPschlecht ivO 0 M t M' :=
  ziel_ort_sperre ivPschlecht ivO 0 (axWahr ivD) (SperrInv.leer ivD) ivFs ivSp ivInit ivE0 ivO_gut
    ivO_lokal (axVertragO_wahr ivO) axEnsLokal_wahr sperrInvOk_leer ivFs_voll ivPschlecht_frag
    ivPschlecht_fuss ivPschlecht_koerper (ivStart _) (fun _ => rfl) ivInit_exklusiv

/-! ## 6. The broken program is refuted -/

/-- The identity environment move meets `HavocOk` of the empty family. -/
theorem iv_havoc : HavocOk (SperrInv.leer ivD) (fun _ σ => σ) :=
  fun _ _ => ⟨rfl, fun c _ => traegerGleich_refl _ c, rfl⟩

/-- **The new obligation fails for the broken `setze`**: from the zero
    memory its body returns with `konto[0] = 5`, `konto[1] = 0`. -/
theorem ivPschlecht_nicht_invGutS :
    ¬ InvGutS ivPschlecht 0 (axWahr ivD) (SperrInv.leer ivD) ivSetze := by
  intro h
  have h3 := h ivO (gutO_rahmenO ivO_gut) ivO_lokal (axVertragO_wahr ivO) (fun _ σ => σ) iv_havoc
    (rufAusV []) (rufAusV_rahmen (vertraegeOkR_nil ivPschlecht))
    (rufAusV_ohneVorbedingung (vertraegeOkR_nil ivPschlecht).1) (ivSp.welt []) .nil rfl _ _ rfl ()
    (List.mem_singleton.mpr rfl) rfl
  revert h3
  simp [InvHaelt, ivPschlecht, ivP, ivInv, ivIdx, ivWert, eval, World.storeSlot, World.merke,
    World.lese, World.schreibSlot, Zahl.weiter, ivSp, Speicher.welt]
  decide

theorem ivM0_faden0 (setze : Endblock ivD (vertragVon ivD ivSetze) false [] ivL) :
    (RufStartG (ivP setze) ivSp ivInit).faeden 0 =
    ⟨[], ⟨ivHaupt, .nil, ivSp.welt [], ⟨false, [], ivL, .nil, .ende ivRumpfHaupt⟩⟩,
      startSpur ivHaupt, [RufEreignisF.eintritt ivHaupt .nil (ivSp.welt [])]⟩ := rfl

theorem ivOffen0 : offen (startSpur (D := ivD) ivHaupt) = [()] := rfl

theorem ivHeld {s : List (Ereignis ivD)} (h : offen s = [()]) : HeldIn ivL (offen s) :=
  fun L _ => by cases L; rw [h]; exact List.mem_singleton.mpr rfl

/-- **The new conclusion fails on a machine of `ivPschlecht` reachable in
    three steps** (thread 0: `haupt` calls `setze`, `setze` writes slot `0`
    and returns): the logged return of `setze` breaks the invariant. -/
theorem ivPschlecht_verletzt : ∃ M : RufMaschineG ivD,
    RufErreichbarG ivPschlecht ivO 0 (RufStartG ivPschlecht ivSp ivInit) M ∧
    ¬ InvAmOrtG ivPschlecht M := by
  obtain ⟨M1, s1, hZ1⟩ := w_rufEnde (P := ivPschlecht) (O := ivO) (passes := 0)
    (ivM0_faden0 ivRumpfSchlecht) ivSetze .nil ivHp rfl ivHauptRest .nil rfl (ivHeld ivOffen0)
  have hoff1 : offen (M1.faeden 0).spur = [()] := by
    rw [hZ1.spur, (Erw.lese _ _ _).offen]; exact ivOffen0
  have e1 := hZ1.1
  obtain ⟨M2, s2, hZ2⟩ := w_blatt (P := ivPschlecht) (O := ivO) (passes := 0) e1 ivS0 ivRetS .nil
    rfl rfl (by rw [← e1]; exact ivHeld hoff1) _ _ rfl
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff2 : offen (M2.faeden 0).spur = [()] := by
    rw [hZ2.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans
      (by rw [← hZ1.welt] at *; exact hoff1)
  have e2 := hZ2.1
  obtain ⟨M3, s3, hG3⟩ := w_rueckP (P := ivPschlecht) (O := ivO) (passes := 0) e2 _ _ rfl
    (PopArt.wie rfl) .keine (List.Perm.refl _) _ rfl
    (by show HeldIn ivL _; rw [← e2]; exact ivHeld hoff2)
  refine ⟨M3, .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3, fun h => ?_⟩
  have h3 := h 0 _ (by rw [hG3.1]; exact List.mem_cons_self) _ _ _ _ _ rfl ()
    (List.mem_singleton.mpr rfl) rfl
  revert h3
  rw [hZ2.welt, hZ1.welt]
  simp [InvHaelt, ivPschlecht, ivP, ivInv, ivIdx, ivWert, eval, World.storeSlot, World.merke,
    World.lese, World.schreibSlot, Zahl.weiter, ivSp, Speicher.welt, RufMaschineG.weltVon,
    RufStartG]
  decide

/-! ## 7. The correct program on a reached run -/

/-- **`ivGut_zeuge`**: on a machine of `ivPgut` reached in four steps
    (thread 0: `haupt` calls `setze`, `setze` writes both slots and
    returns), the logged return of `setze` meets the invariant it owes BY
    THE THEOREM (`ivPgut_zertifiziert`), at a world whose two slots hold
    `5`. -/
theorem ivGut_zeuge : ∃ M : RufMaschineG ivD,
    RufErreichbarG ivPgut ivO 0 (RufStartG ivPgut ivSp ivInit) M ∧
    ∃ (v : ErgVal ivD (ivD.erg ivSetze)) (s0 s1 : World ivD),
      RufEreignisF.rueck ivSetze .nil v s0 s1 ∈ (M.faeden 0).log ∧
      InvAmRueck ivPgut ivSetze s1 ∧
      (s1.slots () 0 ()).n = 5 ∧ (s1.slots () 1 ()).n = 5 := by
  obtain ⟨M1, s1, hZ1⟩ := w_rufEnde (P := ivPgut) (O := ivO) (passes := 0)
    (ivM0_faden0 ivRumpfGut) ivSetze .nil ivHp rfl ivHauptRest .nil rfl (ivHeld ivOffen0)
  have hoff1 : offen (M1.faeden 0).spur = [()] := by
    rw [hZ1.spur, (Erw.lese _ _ _).offen]; exact ivOffen0
  have e1 := hZ1.1
  obtain ⟨M2, s2, hZ2⟩ := w_blatt (P := ivPgut) (O := ivO) (passes := 0) e1 ivS0 (.cons ivS1 ivRetS)
    .nil rfl rfl (by rw [← e1]; exact ivHeld hoff1) _ _ rfl
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff2 : offen (M2.faeden 0).spur = [()] := by
    rw [hZ2.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans
      (by rw [← hZ1.welt] at *; exact hoff1)
  have e2 := hZ2.1
  obtain ⟨M3, s3, hZ3⟩ := w_blatt (P := ivPgut) (O := ivO) (passes := 0) e2 ivS1 ivRetS
    .nil rfl rfl (by rw [← e2]; exact ivHeld hoff2) _ _ rfl
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff3 : offen (M3.faeden 0).spur = [()] := by
    rw [hZ3.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans
      (by rw [← hZ2.welt] at *; exact hoff2)
  have e3 := hZ3.1
  obtain ⟨M4, s4, hG4⟩ := w_rueckP (P := ivPgut) (O := ivO) (passes := 0) e3 _ _ rfl
    (PopArt.wie rfl) .keine (List.Perm.refl _) _ rfl
    (by show HeldIn ivL _; rw [← e3]; exact ivHeld hoff3)
  have hr4 : RufErreichbarG ivPgut ivO 0 (RufStartG ivPgut ivSp ivInit) M4 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3) s4
  obtain ⟨v, a, b, hm, hb⟩ : ∃ (v : ErgVal ivD (ivD.erg ivSetze)) (a b : World ivD),
      RufEreignisF.rueck ivSetze .nil v a b ∈ (M4.faeden 0).log ∧
      b = (M3.weltVon 0).lese ivL [] := by
    rw [hG4.1]; exact ⟨_, _, _, List.mem_cons_self, rfl⟩
  refine ⟨M4, hr4, v, a, b, hm, (ivPgut_zertifiziert M4 hr4).2 0 _ hm _ _ _ _ _ rfl, ?_, ?_⟩
  · rw [hb, hZ3.welt, hZ2.welt, hZ1.welt]
    simp [World.storeSlot, World.merke, World.lese, World.schreibSlot, Zahl.weiter, ivSp,
      Speicher.welt, RufMaschineG.weltVon, RufStartG, ivS0, ivS1, ivSchreib, ivIdx, ivWert, eval]
    rfl
  · rw [hb, hZ3.welt, hZ2.welt, hZ1.welt]
    simp [World.storeSlot, World.merke, World.lese, World.schreibSlot, Zahl.weiter, ivSp,
      Speicher.welt, RufMaschineG.weltVon, RufStartG, ivS0, ivS1, ivSchreib, ivIdx, ivWert, eval]
    rfl

/-! ## CUTS:

  What is proved: on a declaration with one table invariant, the correct
  program meets every premise of `ziel_ort_sperre_inv`
  (`ivPgut_zertifiziert`) and its reached run logs a return of `setze` at
  which the invariant holds by the theorem (`ivGut_zeuge`); the broken
  program, which `ziel_ort_sperre` certifies (`ivPschlecht_alt`), fails
  the new obligation (`ivPschlecht_nicht_invGutS`) and the new conclusion
  on a reached machine (`ivPschlecht_verletzt`).

  What is NOT covered: the root frame's return is not a logged event (G
  logs returns at pops only), so an invariant owed by a thread's start
  function is not checked at the end of the thread; `haupt` re-establishes
  the invariant itself only to meet `InvGutS`. -/

#print axioms ivPgut_zertifiziert
#print axioms ivPschlecht_alt
#print axioms ivPschlecht_nicht_invGutS
#print axioms ivPschlecht_verletzt
#print axioms ivGut_zeuge

end Gabbro.Grammatik
