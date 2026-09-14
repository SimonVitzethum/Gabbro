/-
  File:      Grammatik/HelferZeuge.lean
  Subject:   WITNESS of the held-set relaxation (verdict note T, 2026-09-13):
             ONE pure helper, called both inside a `locks` block and from a
             lock-free function, has a `Programm D` term and is CERTIFIED by
             the goal theorem `ziel_ort_sperre`.

  The scratch program of the verdict (`URTEIL-OPUS-2026-09-13.md`, note T),
  in the model:

      lock L protects konto rank 0
      fn helfer(x : 0 .. 10) -> 0 .. 10  ensures result == x  { return x; }
      fn frei()   { helfer(3); return; }
      fn setze()  { locks L { helfer(5); } return; }

  Before the relaxation `RufPasst.hh` demanded the callee's held set to be
  EXACTLY the caller's: `setze` holds `L` at its call, `frei` holds nothing,
  so no `haelt` list for `helfer` fits both call sites (`hilfe_alt_untypbar`).
  Now `helfer` requires no lock and carries the floor `some 1`: the extra lock
  `L` (rank 0) of `setze` ranks below it (`RufPasst.hx`), and `helfer`'s body
  takes no lock (`ntStufen`).

  Thread 0 runs `setze`, every other thread `frei`. On a reached machine
  (seven steps: thread 0 takes `L`, enters `helfer(5)` -- a frame whose
  static holdings are EMPTY while its thread holds `L` -- and returns;
  thread 1 enters `helfer(3)` without a lock and returns) both logged
  returns of `helfer` meet `result == x`, BY THE THEOREM, and at the first
  one thread 0 held `L` (`helfer_zeuge`).
-/
import Grammatik.ZielOrtSperreZeuge

namespace Gabbro.Grammatik

/-! ## 1. The declaration -/

inductive HFn where
  | helfer
  | frei
  | setze
  deriving DecidableEq

def ntSigHelfer : Signatur Unit Empty Unit Empty where
  params := [.int 0 10]
  erg := some (.int 0 10)
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []
  boden := some 1

def ntSigFrei : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- The declaration: one table `konto` (one slot, `0 .. 10`) guarded by the
    lock `()` of rank `0`, three functions. -/
def ntD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 1
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
  Fn := HFn
  sig := fun | .helfer => 0 | .frei => 1 | .setze => 1
  sigNr := fun | 0 => ntSigHelfer | _ => ntSigFrei
  eigner_nie_erzeugt := fun n _ _ _ h => by
    cases n with
    | zero => simp [ntSigHelfer] at h
    | succ n => simp [ntSigFrei] at h
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
  geteilt_bewacht := fun t _ => by decide
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

def ntHelfer : ntD.Fn := HFn.helfer
def ntFrei : ntD.Fn := HFn.frei
def ntSetze : ntD.Fn := HFn.setze

abbrev ntL : List (Res ntD) := [Res.held (D := ntD) ()]

/-! ## 2. The bodies: one helper, two call sites with different held sets -/

/-- `x` as an argument in `0 .. 10`. -/
def ntArg (k : Int) (h0 : 0 ≤ k) (h1 : k ≤ 10) {Γ : Ctx} {Λ : List (Res ntD)} :
    Args ntD Γ Λ (ntD.params ntHelfer) :=
  .cons (.weiter (lo := k) (hi := k) h0 h1 (.lit k)) .nil

/-- `helfer` ensures `result == x`. -/
def ntEnsHelfer : Expr ntD (ErgCtx (ntD.params ntHelfer) (ntD.erg ntHelfer)) (vertragVon ntD ntHelfer).ende .bool :=
  .eq (.var .hier) (.var (.dort .hier))

/-- `helfer(x)`: `return x`. -/
def ntRumpfHelfer : Endblock ntD (vertragVon ntD ntHelfer) false [.int 0 10]
    (Signatur.anfang ntD (ntD.signatur ntHelfer)) :=
  .ret (.wert (.var .hier)) (List.Perm.refl _)

/-- The call from `frei`: no lock held, exactly `helfer`'s (empty) held set. -/
theorem ntHpFrei : RufPasst ntD (vertragVon ntD ntFrei) (ntD.signatur ntHelfer) [] where
  hw := fun _ h => nomatch h
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp⟩
  hh := fun _ h => nomatch h

/-- **The call from inside `locks L`: the caller holds `L`, the callee
    requires nothing.** Only the relaxed `hh` (`⊆`) admits it; the extra
    lock `L` (rank `0`) ranks below `helfer`'s floor `1` (`hx`). -/
theorem ntHpSetze : RufPasst ntD (vertragVon ntD ntSetze) (ntD.signatur ntHelfer) ntL where
  hw := fun _ h => nomatch h
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp⟩
  hh := fun _ h => nomatch h
  hx := fun L _ _ => by cases L; exact ⟨1, rfl, by decide⟩

/-- `frei()`: `helfer(3); return`. -/
def ntRumpfFrei : Endblock ntD (vertragVon ntD ntFrei) false [] [] :=
  .cons (.call ntHelfer (ntArg 3 (by decide) (by decide)) ntHpFrei rfl) (.ret .keine List.Perm.nil)

/-- The call of `setze` inside the lock. -/
def ntRufL : Stmt ntD (vertragVon ntD ntSetze) false [] ntL ntL :=
  .call ntHelfer (ntArg 5 (by decide) (by decide)) ntHpSetze rfl

/-- The `locks` statement of `setze`. -/
def ntLocks : Stmt ntD (vertragVon ntD ntSetze) false [] [] [] :=
  .locks () (fun _ h => nomatch h) (.cons ntRufL .nil)

def ntSetzeRet : Endblock ntD (vertragVon ntD ntSetze) false [] [] := .ret .keine List.Perm.nil

/-- `setze()`: `locks L { helfer(5) }; return`. -/
def ntRumpfSetze : Endblock ntD (vertragVon ntD ntSetze) false [] [] :=
  .cons ntLocks ntSetzeRet

/-- The program of note T. -/
def ntP : Programm ntD where
  invariante := fun i => nomatch i
  requires
    | .helfer => .wahr
    | .frei => .wahr
    | .setze => .wahr
  ensures
    | .helfer => ntEnsHelfer
    | .frei => .wahr
    | .setze => .wahr
  rumpf
    | .helfer => ntRumpfHelfer
    | .frei => ntRumpfFrei
    | .setze => ntRumpfSetze

/-- **Before the relaxation the program had no term**: no held set for
    `helfer` equals both the held set at `setze`'s call (`[L]`) and at
    `frei`'s (`[]`) -- the exact form of the old `RufPasst.hh`. -/
theorem hilfe_alt_untypbar (H : List ntD.Lock) :
    ¬ ((∀ L, Res.held L ∈ ntL ↔ L ∈ H) ∧ (∀ L, Res.held L ∈ ([] : List (Res ntD)) ↔ L ∈ H)) := by
  rintro ⟨h1, h2⟩
  have hin : () ∈ H := (h1 ()).mp List.mem_cons_self
  exact absurd ((h2 ()).mpr hin) List.not_mem_nil

/-- The floors are respected: `helfer`'s body (floor `1`) takes no lock. -/
theorem ntStufen : StufenOk ntP := by
  intro f c hc
  cases f <;> cases hc <;> rfl

def ntFs : List ntD.Fn := [ntHelfer, ntFrei, ntSetze]

theorem ntFs_voll : ∀ g : ntD.Fn, g ∈ ntFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- The lock `()` protects `konto`; its invariant is `true`. -/
def ntS : SperrInv ntD := ⟨fun _ => [.inl ()], fun _ _ => true⟩

theorem ntS_ok : SperrInvOk ntS := by
  refine ⟨fun L c hc => ?_, fun _ _ _ _ => rfl⟩
  cases L
  rw [List.mem_singleton.mp hc]
  exact List.mem_singleton.mpr rfl

theorem ntP_fussS : fussSperreB ntP ntS ntFs = true := by decide

theorem ntP_fragmentG : programmImFragmentG ntP ntFs = true := by decide

def ntO : Orakel ntD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem ntO_gut : GutO ntO := fun a => nomatch a

theorem ntO_lokal : RegLokal ntO := ⟨(fun r _ _ _ => nomatch r), (fun g _ _ _ => nomatch g)⟩

def ntSp : Speicher ntD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- Thread `0` runs `setze`, every other thread `frei`. -/
def ntInit : Faden → Σ f : ntD.Fn, Env ntD (ntD.params f) :=
  fun t => if t = 0 then ⟨ntSetze, .nil⟩ else ⟨ntFrei, .nil⟩

theorem ntInit_null : ntInit 0 = ⟨ntSetze, .nil⟩ := rfl

theorem ntInit_sonst {t : Faden} (ht : t ≠ 0) : ntInit t = ⟨ntFrei, .nil⟩ := if_neg ht

theorem ntP_start : StartGut ntP ntSp ntInit := by
  intro t
  by_cases ht : t = 0
  · subst ht; rfl
  · rw [ntInit_sonst ht]; rfl

theorem ntInit_exklusiv : StartExklusiv (D := ntD) ntInit :=
  startExklusiv_ohne_haelt ntInit (fun t => by
    by_cases ht : t = 0
    · subst ht; rfl
    · rw [ntInit_sonst ht]; rfl)

/-! ## 3. The obligation, per function -/

theorem ntP_koerper_helfer : KoerperGutS ntP 0 (axWahr ntD) ntS ntHelfer := by
  have hr : ntP.rumpf ntHelfer = ntRumpfHelfer := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [ntRumpfHelfer, execEndH] at hrun
    cases hrun
    cases ρ with
    | cons x rest =>
      cases rest
      exact (decide_eq_true_eq).mpr rfl
  · rw [hr] at hrun
    simp only [ntRumpfHelfer, execEndH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [ntRumpfHelfer, execEndH] at hrun
    cases hrun

theorem ntP_koerper_frei : KoerperGutS ntP 0 (axWahr ntD) ntS ntFrei := by
  have hr : ntP.rumpf ntFrei = ntRumpfFrei := rfl
  refine ⟨fun O' _ _ _ U _ R hR hOV σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [ntRumpfFrei, execEndH] at hrun
    rcases execStmtH_call_fall (S := ntS) (O := O') (U := U) (passes := 0) (R := torRuf ntP R)
      (l := false) (Γ := []) ntHelfer (ntArg 3 (by decide) (by decide)) ntHpFrei rfl σ ρ with
      ⟨σ1, v1, _, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · cases hrun
    · cases hrun
      exact hOV _ _ _ _ he1 g rfl
    · cases hrun
  · rw [hr] at hrun
    simp only [ntRumpfFrei, execEndH] at hrun
    rcases execStmtH_call_fall (S := ntS) (O := O') (U := U) (passes := 0) (R := R)
      (l := false) (Γ := []) ntHelfer (ntArg 3 (by decide) (by decide)) ntHpFrei rfl σ ρ with
      ⟨σ1, v1, _, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · cases hrun
    · cases hrun
      exact hOL _ _ _ _ he1
    · cases hrun

theorem ntP_koerper_setze : KoerperGutS ntP 0 (axWahr ntD) ntS ntSetze := by
  have hr : ntP.rumpf ntSetze = ntRumpfSetze := rfl
  refine ⟨fun O' _ _ _ U _ R hR hOV σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [ntRumpfSetze, ntLocks, execEndH] at hrun
    erw [execStmtH_locks_eins] at hrun
    rcases execStmtH_call_fall (S := ntS) (O := O') (U := U) (passes := 0) (R := torRuf ntP R)
      (l := false) (Γ := []) ntHelfer (ntArg 5 (by decide) (by decide)) ntHpSetze rfl
      ((U () σ).nimmt ()) ρ with ⟨σ1, v1, _, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · simp only [freiH, ntS, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOV _ _ _ _ he1 g rfl
    · simp only [freiH] at hrun
      cases hrun
  · rw [hr] at hrun
    simp only [ntRumpfSetze, ntLocks, execEndH] at hrun
    erw [execStmtH_locks_eins] at hrun
    rcases execStmtH_call_fall (S := ntS) (O := O') (U := U) (passes := 0) (R := R)
      (l := false) (Γ := []) ntHelfer (ntArg 5 (by decide) (by decide)) ntHpSetze rfl
      ((U () σ).nimmt ()) ρ with ⟨σ1, v1, _, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · simp only [freiH, ntS, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOL _ _ _ _ he1
    · simp only [freiH] at hrun
      cases hrun

theorem ntP_koerper : ∀ f : ntD.Fn, KoerperGutS ntP 0 (axWahr ntD) ntS f := by
  intro f
  cases f
  · exact ntP_koerper_helfer
  · exact ntP_koerper_frei
  · exact ntP_koerper_setze

/-- **The note-T program is certified by the goal theorem**: every premise
    of `ziel_ort_sperre` holds on `ntP`, a program whose one helper is called
    under a lock and without one. -/
theorem ntP_zertifiziert : ∀ M : RufMaschineG ntD,
    RufErreichbarG ntP ntO 0 (RufStartG ntP ntSp ntInit) M →
      VertragAmOrtG ntP M ∧ SperrInvG ntS M ∧ KeinLogikHaltG ntO 0 M ∧
      ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
        AnPruefungG M t → ∃ M', RufSchrittG ntP ntO 0 M t M' :=
  ziel_ort_sperre ntP ntO 0 (axWahr ntD) ntS ntFs ntSp ntInit ntO_gut ntO_lokal
    (axVertragO_wahr ntO)
    axEnsLokal_wahr ntS_ok ntFs_voll ntP_fragmentG ntP_fussS ntP_koerper ntP_start (fun _ => rfl)
    ntInit_exklusiv

/-! ## 4. The run: the helper under a lock and without one -/

theorem ntM0_faden0 : (RufStartG ntP ntSp ntInit).faeden 0 =
    ⟨[], ⟨ntSetze, .nil, ntSp.welt [], ⟨false, [], [], .nil, .ende ntRumpfSetze⟩⟩, [],
      [RufEreignisF.eintritt ntSetze .nil (ntSp.welt [])]⟩ := rfl

theorem ntM0_faden1 : (RufStartG ntP ntSp ntInit).faeden 1 =
    ⟨[], ⟨ntFrei, .nil, ntSp.welt [], ⟨false, [], [], .nil, .ende ntRumpfFrei⟩⟩, [],
      [RufEreignisF.eintritt ntFrei .nil (ntSp.welt [])]⟩ := rfl

theorem ntM0_offen (t : Faden) : offen ((RufStartG ntP ntSp ntInit).faeden t).spur = [] := by
  by_cases ht : t = 0
  · subst ht; rfl
  · show offen (match ntInit t with
      | ⟨g, _⟩ => startSpur g) = []
    rw [ntInit_sonst ht]; rfl

theorem ntHeld0 {s : List (Ereignis ntD)} : HeldIn ([] : List (Res ntD)) (offen s) :=
  fun _ h => nomatch h

/-- **`helfer_zeuge` -- one helper, two held sets, both contracts BY THE
    THEOREM.** On a reached machine: thread 0 (`setze`) took the lock `L`,
    called `helfer(5)` inside the `locks` block and returned; at that return
    `L` was held by thread 0 while `helfer`'s frame named no lock; thread 1
    (`frei`) called `helfer(3)` holding nothing and returned. Both logged
    returns meet `helfer`'s `ensures result == x` -- the values `5` and `3`
    -- by `ntP_zertifiziert`. -/
theorem helfer_zeuge : ∃ M : RufMaschineG ntD,
    RufErreichbarG ntP ntO 0 (RufStartG ntP ntSp ntInit) M ∧
    (∃ (v : ErgVal ntD (ntD.erg ntHelfer)) (s0 s1 : World ntD),
      RufEreignisF.rueck ntHelfer (.cons ⟨5, by decide, by decide⟩ .nil) v s0 s1 ∈ (M.faeden 0).log ∧
      () ∈ offen s1.spur ∧
      EnsAmRueck ntP ntHelfer s0 s1 (.cons ⟨5, by decide, by decide⟩ .nil) v ∧ v.n = 5) ∧
    (∃ (v : ErgVal ntD (ntD.erg ntHelfer)) (s0 s1 : World ntD),
      RufEreignisF.rueck ntHelfer (.cons ⟨3, by decide, by decide⟩ .nil) v s0 s1 ∈ (M.faeden 1).log ∧
      offen s1.spur = [] ∧
      EnsAmRueck ntP ntHelfer s0 s1 (.cons ⟨3, by decide, by decide⟩ .nil) v ∧ v.n = 3) := by
  -- thread 0: unfold `locks`, take `L`, call `helfer(5)`, return
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := ntP) (O := ntO) (passes := 0) ntM0_faden0 ntLocks
    ntSetzeRet .nil rfl rfl
  obtain ⟨M2, s2, hZ2⟩ := w_locks (P := ntP) (O := ntO) (passes := 0) hZ1.1 ()
    _ _ _ _ .nil rfl
    (fun L => by
      cases L
      constructor
      · intro h; exact nomatch h
      · intro h; exact absurd h List.not_mem_nil)
    (fun u hu h => by rw [rufSchrittG_fremd s1 u hu, ntM0_offen] at h; exact List.not_mem_nil h)
  have hoff2 : offen (M2.faeden 0).spur = [()] := by
    rw [hZ2.spur]
    show offen (Ereignis.nimmt () (offen (M1.weltVon 0).spur) :: (M1.weltVon 0).spur) = [()]
    simp only [offen]
    show () :: offen (M1.faeden 0).spur = [()]
    rw [hZ1.spur]
    show () :: offen ((RufStartG ntP ntSp ntInit).faeden 0).spur = [()]
    rw [ntM0_offen]
    rfl
  obtain ⟨M3, s3, hZ3⟩ := w_rufDann (P := ntP) (O := ntO) (passes := 0) hZ2.1 ntHelfer
    (ntArg 5 (by decide) (by decide)) ntHpSetze rfl .nil _ .nil rfl
    (fun L _ => by
      cases L
      have h := hoff2
      rw [hZ2.1] at h
      rw [h]
      exact List.mem_cons_self)
  have hoff3 : offen (M3.faeden 0).spur = [()] := by
    rw [hZ3.spur, (Erw.lese _ _ _).offen]; exact hoff2
  obtain ⟨M4, s4, hG4⟩ := w_rueckP (P := ntP) (O := ntO) (passes := 0) hZ3.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl ntHeld0
  -- thread 1: call `helfer(3)` holding nothing, return
  have h41 : M4.faeden 1 = (RufStartG ntP ntSp ntInit).faeden 1 := by
    rw [rufSchrittG_fremd s4 1 (by decide), rufSchrittG_fremd s3 1 (by decide),
      rufSchrittG_fremd s2 1 (by decide), rufSchrittG_fremd s1 1 (by decide)]
  obtain ⟨M5, s5, hZ5⟩ := w_rufEnde (P := ntP) (O := ntO) (passes := 0) (h41.trans ntM0_faden1)
    ntHelfer (ntArg 3 (by decide) (by decide)) ntHpFrei rfl (.ret .keine List.Perm.nil) .nil rfl ntHeld0
  obtain ⟨M6, s6, hG6⟩ := w_rueckP (P := ntP) (O := ntO) (passes := 0) hZ5.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl ntHeld0
  have hr6 : RufErreichbarG ntP ntO 0 (RufStartG ntP ntSp ntInit) M6 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _
      (.schritt _ _ _ .start s1) s2) s3) s4) s5) s6
  have hZ := ntP_zertifiziert M6 hr6
  have h60 : M6.faeden 0 = M4.faeden 0 := by
    rw [rufSchrittG_fremd s6 0 (by decide), rufSchrittG_fremd s5 0 (by decide)]
  obtain ⟨v0, a0, b0, hm0, hb0⟩ : ∃ (v : ErgVal ntD (ntD.erg ntHelfer)) (a b : World ntD),
      RufEreignisF.rueck ntHelfer (.cons ⟨5, by decide, by decide⟩ .nil) v a b ∈ (M6.faeden 0).log ∧
      offen b.spur = [()] := by
    rw [h60, hG4.1]
    exact ⟨_, _, _, List.mem_cons_self, ((Erw.lese _ _ _).offen).trans hoff3⟩
  obtain ⟨v1, a1, b1, hm1, hb1⟩ : ∃ (v : ErgVal ntD (ntD.erg ntHelfer)) (a b : World ntD),
      RufEreignisF.rueck ntHelfer (.cons ⟨3, by decide, by decide⟩ .nil) v a b ∈ (M6.faeden 1).log ∧
      offen b.spur = [] := by
    rw [hG6.1]
    refine ⟨_, _, _, List.mem_cons_self, ?_⟩
    rw [(Erw.lese _ _ _).offen]
    show offen (M5.faeden 1).spur = []
    rw [hZ5.spur, (Erw.lese _ _ _).offen]
    show offen (M4.faeden 1).spur = []
    rw [h41, ntM0_offen]
  have hEns0 := (hZ.1 0 _ hm0).2 _ _ _ _ _ rfl
  have hEns1 := (hZ.1 1 _ hm1).2 _ _ _ _ _ rfl
  have hv0 : v0.n = 5 := of_decide_eq_true hEns0
  have hv1 : v1.n = 3 := of_decide_eq_true hEns1
  exact ⟨M6, hr6, ⟨v0, a0, b0, hm0, by rw [hb0]; exact List.mem_cons_self, hEns0, hv0⟩,
    ⟨v1, a1, b1, hm1, hb1, hEns1, hv1⟩⟩

/-- **Witness of `ziel_ort_sperre_fortschritt`** (inhabitation): on the loop
    program `lP` of `ZielOrtGanzZeuge.lean` (the empty lock-invariant family)
    a reached machine stands at the `traverse` boundary, and the new progress
    corollary -- WITHOUT the `HeldGenau` hypothesis -- yields a step there. -/
theorem ziel_ort_sperre_fortschritt_zeuge :
    ∃ M2 : RufMaschineG zD, RufErreichbarG lP zO 0 (RufStartG lP zSp lInit) M2 ∧
      AnPruefungG M2 0 ∧ ∃ M3 : RufMaschineG zD, RufSchrittG lP zO 0 M2 0 M3 := by
  obtain ⟨M2, hr2, hA, _, _⟩ := ziel_ort_ganz_fortschritt_zeuge
  exact ⟨M2, hr2, hA, ziel_ort_sperre_fortschritt lP zO 0 (axWahr zD) (SperrInv.leer zD) zFs zSp
    lInit zO_gut zO_lokal (axVertragO_wahr zO) axEnsLokal_wahr sperrInvOk_leer zFs_voll
    lP_fragmentG (fussSperreB_of_G _ _ _ lP_fussG) (fun f => koerperGutS_leer (lP_koerperZ f))
    lP_start (fun _ => rfl) lInit_exklusiv M2 hr2 0 hA⟩

#print axioms hilfe_alt_untypbar
#print axioms ntStufen
#print axioms ntP_zertifiziert
#print axioms helfer_zeuge
#print axioms ziel_ort_sperre_fortschritt_zeuge

end Gabbro.Grammatik
