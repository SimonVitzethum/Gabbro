/-
  File:      Grammatik/ZielOrtEinfadenZeuge.lean
  Subject:   WITNESSES for `ziel_ort_einfaden` (one active thread, no
             footprint check).

  1. Corpus 104 (`r4P`, thread 0 the driver, every other thread idle in
     `ruhe`): certified by `ziel_ort_einfaden` WITHOUT `fussOrtGB`.
  2. A sequential program BOTH footprint checks refuse: an UNGUARDED table
     (no lock at all, not shared) written by `setze` and required by
     `pruefe` (`requires konto[0] == 5`); `haupt` calls `setze` then
     `pruefe`, so its caller duty rests on `setze`'s `ensures` across two
     calls. `ePB_fussG_falsch`/`eP_fussS_falsch`: the checks fail;
     `ziel_ort_einfaden_zeuge`: every premise of `ziel_ort_einfaden` holds,
     and on a reached run `pruefe`'s `requires` holds at its logged entry,
     BY THE THEOREM, over the value `setze` wrote.
-/
import Grammatik.ZielOrtEinfaden
import Grammatik.ZielOrtSperreZeuge

namespace Gabbro.Grammatik

/-! ## 1. Corpus 104 without the footprint check -/

theorem r4_ruhig : ∀ u, u ≠ 0 → ruhig r4P (r4Init u).1 = true := by
  intro u hu
  unfold r4Init
  rw [if_neg hu]
  decide

/-- **`ziel_ort_einfaden_ref104`**: `beispiele/104-referenz.gab` certified by
    the one-thread theorem, whose premises contain no footprint check. -/
theorem ziel_ort_einfaden_ref104 :
    ∀ M : RufMaschineG r4D, RufErreichbarG r4P r4O 0 (RufStartG r4P r4Sp r4Init) M →
      VertragAmOrtG r4P M ∧ SperrInvG (SperrInv.leer r4D) M ∧ KeinLogikHaltG r4O 0 M ∧
      ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
        AnPruefungG M t → ∃ M', RufSchrittG r4P r4O 0 M t M' :=
  ziel_ort_einfaden r4P r4O 0 (axWahr r4D) (SperrInv.leer r4D) r4Fs r4Sp r4Init r4O_gut
    r4O_lokal (axVertragO_wahr r4O) axEnsLokal_wahr sperrInvOk_leer r4Fs_voll r4P_fragmentG r4_ruhig
    (fun f => koerperGutS_leer (r4P_koerperZ f)) r4P_start (fun _ => rfl)

/-! ## 2. An unguarded sequential program -/

inductive EFn where
  | setze
  | pruefe
  | haupt
  | ruhe
  deriving DecidableEq

def eSigSetze : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def eSigLeer : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- The declaration: one table `konto` (one slot, values `0 .. 100`) with
    NO guard (not shared), no lock used. -/
def eD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
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
  Fn := EFn
  sig := fun | .setze => 0 | .haupt => 0 | _ => 1
  sigNr := fun | 0 => eSigSetze | _ => eSigLeer
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
  geteilt_bewacht := fun t h => by cases h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

def eSetze : eD.Fn := EFn.setze
def ePruefe : eD.Fn := EFn.pruefe
def eHaupt : eD.Fn := EFn.haupt
def eRuhe : eD.Fn := EFn.ruhe

theorem eDarf (Λ : List (Res eD)) : darf eD () Λ := fun _ h => nomatch h

def eIdx {Γ : Ctx} {Λ : List (Res eD)} : Expr eD Γ Λ (.index (eD.count ())) :=
  .weiter (by decide) (by decide) (.lit 0)

def eFuenf {Γ : Ctx} {Λ : List (Res eD)} : Expr eD Γ Λ (.int 0 100) :=
  .weiter (by decide) (by decide) (.lit 5)

/-- `konto[0] == 5`. -/
def eFuenfGleich {Γ : Ctx} {Λ : List (Res eD)} : Expr eD Γ Λ .bool :=
  .eq (.slot () () eIdx (eDarf Λ)) eFuenf

theorem eHp (caller callee : eD.Fn) (hw : ∀ t, (eD.signatur callee).schreibt t = true →
    (vertragVon eD caller).schreibt t = true) (hh : (eD.signatur callee).haelt = [])
    (hk : (eD.signatur callee).konsumiert = []) :
    RufPasst eD (vertragVon eD caller) (eD.signatur callee) [] where
  hw := hw
  hg := fun g => nomatch g
  hb := fun c hc => by revert hc; cases caller <;> intro hc <;> cases hc
  hk := by rw [hk]; exact ⟨[], List.Perm.refl [], by simp⟩
  hh := RufPasst.hh_von (by
    intro L
    rw [hh]
    exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩)
  hx := RufPasst.hx_von (by
    intro L
    rw [hh]
    exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩)

theorem eHpSetze : RufPasst eD (vertragVon eD eHaupt) (eD.signatur eSetze) [] :=
  eHp eHaupt eSetze (fun _ _ => rfl) rfl rfl

theorem eHpPruefe : RufPasst eD (vertragVon eD eHaupt) (eD.signatur ePruefe) [] :=
  eHp eHaupt ePruefe (fun _ h => by cases h) rfl rfl

/-- `setze`: `konto[0] = 5; return`. -/
def eRumpfSetze : Endblock eD (vertragVon eD eSetze) false [] [] :=
  .cons (.assignSlot () () eIdx eFuenf rfl (eDarf _)) (.ret .keine List.Perm.nil)

/-- `pruefe`: `return` (its `requires` is the point). -/
def eRumpfPruefe : Endblock eD (vertragVon eD ePruefe) false [] [] := .ret .keine List.Perm.nil

/-- `haupt`: `setze(); pruefe(); return`. -/
def eRumpfHaupt : Endblock eD (vertragVon eD eHaupt) false [] [] :=
  .cons (.call eSetze .nil eHpSetze rfl) (.cons (.call ePruefe .nil eHpPruefe rfl)
    (.ret .keine List.Perm.nil))

def eRumpfRuhe : Endblock eD (vertragVon eD eRuhe) false [] [] := .ret .keine List.Perm.nil

/-- The program: `setze` ensures `konto[0] == 5`, `pruefe` REQUIRES it. -/
def eP : Programm eD where
  invariante := fun i => nomatch i
  requires
    | .pruefe => eFuenfGleich
    | _ => .wahr
  ensures
    | .setze => eFuenfGleich
    | _ => .wahr
  rumpf
    | .setze => eRumpfSetze
    | .pruefe => eRumpfPruefe
    | .haupt => eRumpfHaupt
    | .ruhe => eRumpfRuhe

def eFs : List eD.Fn := [eSetze, ePruefe, eHaupt, eRuhe]

theorem eFs_voll : ∀ g : eD.Fn, g ∈ eFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self))

/-- **Both footprint checks refuse the program**: `haupt`'s footprint holds
    `pruefe`'s contract carrier `konto`, guarded by nothing and written by
    `setze`. -/
theorem eP_fussG_falsch : fussOrtGB eP eFs = false := by decide

theorem eP_fussS_falsch : fussSperreB eP (SperrInv.leer eD) eFs = false := by decide

theorem eP_fragmentG : programmImFragmentG eP eFs = true := by decide

def eO : Orakel eD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem eO_gut : GutO eO := fun a => nomatch a

theorem eO_lokal : RegLokal eO := ⟨(fun r _ _ _ => nomatch r), (fun g _ _ _ => nomatch g)⟩

def eSp : Speicher eD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- Thread 0 runs `haupt`, every other thread is idle. -/
def eInit : Faden → Σ f : eD.Fn, Env eD (eD.params f) :=
  fun t => if t = 0 then ⟨eHaupt, .nil⟩ else ⟨eRuhe, .nil⟩

theorem eP_start : StartGut eP eSp eInit := by
  intro t
  unfold eInit
  by_cases h0 : t = 0
  · rw [if_pos h0]; rfl
  · rw [if_neg h0]; rfl

theorem e_ruhig : ∀ u, u ≠ 0 → ruhig eP (eInit u).1 = true := by
  intro u hu
  unfold eInit
  rw [if_neg hu]
  decide

theorem eP_koerper_setze : KoerperGutS eP 0 (axWahr eD) (SperrInv.leer eD) eSetze := by
  have hr : eP.rumpf eSetze = eRumpfSetze := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [eRumpfSetze, execEndH, execStmtH] at hrun
    cases hrun
    rfl
  · rw [hr] at hrun
    simp only [eRumpfSetze, execEndH, execStmtH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [eRumpfSetze, execEndH, execStmtH] at hrun
    cases hrun

theorem eP_koerper_pruefe : KoerperGutS eP 0 (axWahr eD) (SperrInv.leer eD) ePruefe := by
  have hf : eP.rumpf ePruefe = eRumpfPruefe := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hf] at hrun
    simp only [eRumpfPruefe, execEndH] at hrun
    cases hrun
  · rw [hf] at hrun
    simp only [eRumpfPruefe, execEndH] at hrun
    cases hrun

theorem eP_koerper_ruhe : KoerperGutS eP 0 (axWahr eD) (SperrInv.leer eD) eRuhe := by
  have hf : eP.rumpf eRuhe = eRumpfRuhe := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hf] at hrun
    simp only [eRumpfRuhe, execEndH] at hrun
    cases hrun
  · rw [hf] at hrun
    simp only [eRumpfRuhe, execEndH] at hrun
    cases hrun

/-- `haupt`: the gate of `pruefe` passes because `setze`'s `ensures` holds
    at the world `setze` returned (sequentially -- no other thread moves). -/
theorem eP_koerper_haupt : KoerperGutS eP 0 (axWahr eD) (SperrInv.leer eD) eHaupt := by
  have hr : eP.rumpf eHaupt = eRumpfHaupt := rfl
  refine ⟨fun O' _ _ _ U _ R hR hOV σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [eRumpfHaupt, execEndH] at hrun
    rcases execStmtH_call_fall (S := SperrInv.leer eD) (O := O') (U := U) (passes := 0)
      (R := torRuf eP R) (l := false) (Γ := []) eSetze .nil eHpSetze rfl σ ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · simp only at hrun
      have hR1' : R eSetze (σ.lese [] []) .nil = .ok σ1 v1 := hR1
      have hens1 := hR.1 _ _ _ (by rfl) _ _ hR1'
      have hreq : ReqAmEintritt eP ePruefe (σ1.lese [] []) .nil := hens1
      rcases execStmtH_call_fall (S := SperrInv.leer eD) (O := O') (U := U) (passes := 0)
        (R := torRuf eP R) (l := false) (Γ := []) ePruefe .nil eHpPruefe rfl σ1 ρ with
        ⟨σ2, v2, _, h2⟩ | ⟨e2, he2, h2⟩ | ⟨e2, h2⟩ <;> erw [h2] at hrun
      · cases hrun
      · cases hrun
        have htor : torRuf eP R ePruefe (σ1.lese [] []) .nil = R ePruefe (σ1.lese [] []) .nil :=
          if_pos hreq
        exact hOV _ _ _ _ (htor.symm.trans he2) g rfl
      · cases hrun
    · cases hrun
      exact hOV _ _ _ _ he1 g rfl
    · cases hrun
  · rw [hr] at hrun
    simp only [eRumpfHaupt, execEndH] at hrun
    rcases execStmtH_call_fall (S := SperrInv.leer eD) (O := O') (U := U) (passes := 0) (R := R)
      (l := false) (Γ := []) eSetze .nil eHpSetze rfl σ ρ with
      ⟨σ1, v1, _, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · simp only at hrun
      rcases execStmtH_call_fall (S := SperrInv.leer eD) (O := O') (U := U) (passes := 0) (R := R)
        (l := false) (Γ := []) ePruefe .nil eHpPruefe rfl σ1 ρ with
        ⟨σ2, v2, _, h2⟩ | ⟨e2, he2, h2⟩ | ⟨e2, h2⟩ <;> erw [h2] at hrun
      · cases hrun
      · cases hrun
        exact hOL _ _ _ _ he2
      · cases hrun
    · cases hrun
      exact hOL _ _ _ _ he1
    · cases hrun

theorem eP_koerper : ∀ f : eD.Fn, KoerperGutS eP 0 (axWahr eD) (SperrInv.leer eD) f := by
  intro f
  cases f
  · exact eP_koerper_setze
  · exact eP_koerper_pruefe
  · exact eP_koerper_haupt
  · exact eP_koerper_ruhe

/-- **Every premise of `ziel_ort_einfaden` holds on `eP`**, a program both
    footprint checks refuse. -/
theorem eP_zertifiziert : ∀ M : RufMaschineG eD,
    RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M →
      VertragAmOrtG eP M ∧ SperrInvG (SperrInv.leer eD) M ∧ KeinLogikHaltG eO 0 M ∧
      ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
        AnPruefungG M t → ∃ M', RufSchrittG eP eO 0 M t M' :=
  ziel_ort_einfaden eP eO 0 (axWahr eD) (SperrInv.leer eD) eFs eSp eInit eO_gut eO_lokal
    (axVertragO_wahr eO) axEnsLokal_wahr sperrInvOk_leer eFs_voll eP_fragmentG e_ruhig eP_koerper
    eP_start (fun _ => rfl)

theorem ehg0 {s : List (Ereignis eD)} (h : offen s = []) :
    HeldGenau ([] : List (Res eD)) (offen s) := by
  rw [h]
  intro L
  exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

theorem eoff_z {M : RufMaschineG eD} {f : Faden} {stapel : List (RufRahmenG eD)} {fn : eD.Fn}
    {rho : Env eD (eD.params fn)} {s0 : World eD} {log : List (RufEreignisF eD)} {l : Bool}
    {Γ : Ctx} {Λ : List (Res eD)} {ρ : Env eD Γ} {r : GRest eD (vertragVon eD fn) l Γ Λ}
    {σ : World eD} {x : List eD.Lock} (h : ZustandG M f stapel fn rho s0 log ρ r σ)
    (ho : offen (M.faeden f).spur = x) : offen σ.spur = x := by
  rw [← h.spur]; exact ho

theorem eoff_g {M : RufMaschineG eD} {f : Faden} {caller : RufRahmenG eD}
    {rst : List (RufRahmenG eD)} {fn : eD.Fn} {rho : Env eD (eD.params fn)} {s0 : World eD}
    {log : List (RufEreignisF eD)} {v : ErgVal eD (eD.erg fn)} {σ : World eD} {x : List eD.Lock}
    (h : GepopptG M f caller rst fn rho s0 log v σ) (ho : offen (M.faeden f).spur = x) :
    offen σ.spur = x := by
  rw [h.1] at ho; exact ho

/-- **`ziel_ort_einfaden_zeuge`.** On a reached run of four steps of thread 0
    (call `setze`, its write of `5`, its return, call `pruefe`) the log holds
    the entry of `pruefe`, and its `requires konto[0] == 5` holds there, BY
    THE THEOREM -- over an unguarded table the start left at `0`. -/
theorem ziel_ort_einfaden_zeuge : ∃ M : RufMaschineG eD,
    RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M ∧ (eSp.slots () 0 ()).n = 0 ∧
    ∃ (rho : Env eD (eD.params ePruefe)) (s0 : World eD),
      RufEreignisF.eintritt ePruefe rho s0 ∈ (M.faeden 0).log ∧ ReqAmEintritt eP ePruefe s0 rho ∧
      (s0.slots () 0 ()).n = 5 := by
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
  have hr4 : RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M4 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3) s4
  obtain ⟨rho, w0, hm⟩ : ∃ (rho : Env eD (eD.params ePruefe)) (w0 : World eD),
      RufEreignisF.eintritt ePruefe rho w0 ∈ (M4.faeden 0).log := by
    rw [hZ4.1]
    exact ⟨_, _, List.mem_cons_self⟩
  have hreq := ((eP_zertifiziert M4 hr4).1 0 _ hm).1 _ _ _ rfl
  exact ⟨M4, hr4, rfl, rho, w0, hm, hreq, of_decide_eq_true hreq⟩

#print axioms Gabbro.Grammatik.ziel_ort_einfaden_ref104
#print axioms Gabbro.Grammatik.eP_zertifiziert
#print axioms Gabbro.Grammatik.ziel_ort_einfaden_zeuge

end Gabbro.Grammatik
