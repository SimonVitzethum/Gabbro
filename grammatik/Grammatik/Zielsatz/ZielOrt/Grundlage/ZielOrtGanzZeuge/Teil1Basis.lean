module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz
public import Grammatik.Korpus.Referenz.Referenz104Rahmen
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtZeuge
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAxZeuge

@[expose] public section



namespace Gabbro.Grammatik

/-! ## 1. The corpus program `0104-referenz.gab` -/

/-- No body of `r4P` has a loop invariant or a `state` transition. -/
theorem r4P_logikFrei : programmLogikFrei r4P r4Fs = true := by decide

/-- **Every function of `r4P` meets the obligation of the goal theorem**:
    the frame obligation from `Referenz104Rahmen.lean`, the new clause by
    the syntactic check. -/
theorem r4P_koerperZ : ∀ f : r4D.Fn, KoerperGutZ r4P 0 (axWahr r4D) f :=
  fun f => ⟨koerperGutRQ_of_R _ (r4P_koerperR f),
    programmLogikFrei_ok r4Fs_voll r4P_logikFrei 0 _ f⟩

/-- **`ziel_ort_ganz_ref104` -- `beispiele/0104-referenz.gab` certified by the
    goal theorem.** All premises of `ziel_ort_ganz` hold jointly on `r4P`
    (with the trivial declared axiom ensures: the declaration has no axiom),
    the conclusion holds on EVERY reachable machine, and on the reached run
    of `r4Lauf` -- memory `0 -> 100`, the return of `einzahlen` logged -- the
    `ensures` of `einzahlen` holds at its logged return, and no thread is
    stopped at a `logik` check. -/
theorem ziel_ort_ganz_ref104 :
    GutO r4O ∧ RegLokal r4O ∧ AxVertragO (axWahr r4D) r4O ∧ AxEnsLokal (axWahr r4D) ∧
    (∀ g : r4D.Fn, g ∈ r4Fs) ∧
    programmImFragmentG r4P r4Fs = true ∧ fussOrtGB r4P r4Fs = true ∧
    (∀ f : r4D.Fn, KoerperGutZ r4P 0 (axWahr r4D) f) ∧ StartGut r4P r4Sp r4Init ∧
    StartExklusiv (D := r4D) r4Init ∧
    (∀ M : RufMaschineG r4D, RufErreichbarG r4P r4O 0 (RufStartG r4P r4Sp r4Init) M →
      VertragAmOrtG r4P M ∧ KeinLogikHaltG r4O 0 M ∧
      ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
        AnPruefungG M t → ∃ M', RufSchrittG r4P r4O 0 M t M') ∧
    ∃ M : RufMaschineG r4D, RufErreichbarG r4P r4O 0 (RufStartG r4P r4Sp r4Init) M ∧
      (r4Sp.slots () 0 ()).n = 0 ∧ (M.speicher.slots () 0 ()).n = 100 ∧
      (∃ (rho : Env r4D (r4D.params r4Ein)) (s0 s1 : World r4D),
        RufEreignisF.rueck r4Ein rho () s0 s1 ∈ (M.faeden 0).log ∧
        EnsAmRueck r4P r4Ein s0 s1 rho ()) ∧
      VertragAmOrtG r4P M ∧ KeinLogikHaltG r4O 0 M := by
  have hZ := ziel_ort_ganz r4P r4O 0 (axWahr r4D) r4Fs r4Sp r4Init r4E0 r4O_gut r4O_lokal
    (axVertragO_wahr r4O) axEnsLokal_wahr r4Fs_voll r4P_fragmentG r4P_fussG r4P_koerperZ
    r4P_start r4Init_exklusiv
  obtain ⟨M, hr, hsp, ⟨rho, s0, s1, hlog⟩, _⟩ := r4Lauf
  have hV := hZ M hr
  refine ⟨r4O_gut, r4O_lokal, axVertragO_wahr r4O, axEnsLokal_wahr, r4Fs_voll, r4P_fragmentG,
    r4P_fussG, r4P_koerperZ, r4P_start, r4Init_exklusiv, hZ, M, hr, rfl, hsp,
    ⟨rho, s0, s1, hlog, ?_⟩, hV.1, hV.2.1⟩
  exact (hV.1 0 _ hlog).2 r4Ein rho () s0 s1 rfl

/-! ## 2. The concurrent program `zP` -/

theorem zO_lokal : RegLokal zO := ⟨(fun r _ _ _ => nomatch r), (fun g _ _ _ => nomatch g)⟩

theorem zP_fragmentG : programmImFragmentG zP zFs = true := by decide

theorem zP_fussG : fussOrtGB zP zFs = true := by decide

theorem zP_logikFrei : programmLogikFrei zP zFs = true := by decide

theorem zP_koerperZ : ∀ f : zD.Fn, KoerperGutZ zP 0 (axWahr zD) f :=
  fun f => ⟨koerperGutRQ_of_R _ (koerperGutR_of_V (koerperGutV_of_kOk zP zO 0 f (zP_fragmentF f)
    (zP_koerper f))), programmLogikFrei_ok zFs_voll zP_logikFrei 0 _ f⟩

/-- **`ziel_ort_ganz_zeuge` -- the premises jointly on a concurrent program,
    with a cross-thread return.** Every premise of `ziel_ort_ganz` holds on
    `zP` (every thread in `haupt`, `locks { wrap() }`); on the reached run
    of `zLauf` thread 1 writes `konto[0] := 100` under the lock, then
    thread 0's `lies` returns `100` -- a value no step of its own wrote --
    and its `ensures result = konto[0]` holds at that logged return, from
    the goal theorem; no thread of that machine is stopped at a `logik`
    check. -/
theorem ziel_ort_ganz_zeuge :
    GutO zO ∧ RegLokal zO ∧ AxVertragO (axWahr zD) zO ∧ AxEnsLokal (axWahr zD) ∧
    (∀ g : zD.Fn, g ∈ zFs) ∧ programmImFragmentG zP zFs = true ∧ fussOrtGB zP zFs = true ∧
    (∀ f : zD.Fn, KoerperGutZ zP 0 (axWahr zD) f) ∧ StartGut zP zSp zInit ∧
    StartExklusiv (D := zD) zInit ∧
    ∃ M18 : RufMaschineG zD, RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M18 ∧
      (zSp.slots () 0 ()).n = 0 ∧
      (∃ (rho : Env zD (zD.params zLies)) (v : ErgVal zD (zD.erg zLies)) (s0 s1 : World zD),
        RufEreignisF.rueck zLies rho v s0 s1 ∈ (M18.faeden 0).log ∧
        (show Zahl 0 100 from v).n = 100 ∧ EnsAmRueck zP zLies s0 s1 rho v) ∧
      VertragAmOrtG zP M18 ∧ KeinLogikHaltG zO 0 M18 := by
  have hZ := ziel_ort_ganz zP zO 0 (axWahr zD) zFs zSp zInit zE0 zO_gut zO_lokal
    (axVertragO_wahr zO) axEnsLokal_wahr zFs_voll zP_fragmentG zP_fussG zP_koerperZ zP_start
    zInit_exklusiv
  obtain ⟨M9, M17, M18, h9, h17, h18, _, _, _, _, _, _, _,
    ⟨rho, v, s0, s1, hm, hv, _⟩, _, _⟩ := zLauf
  have h18' : RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M18 :=
    rufErreichbarG_trans (rufErreichbarG_trans h9 h17) h18
  have hV := hZ M18 h18'
  exact ⟨zO_gut, zO_lokal, axVertragO_wahr zO, axEnsLokal_wahr, zFs_voll, zP_fragmentG, zP_fussG,
    zP_koerperZ, zP_start, zInit_exklusiv, M18, h18', rfl,
    ⟨rho, v, s0, s1, hm, hv, (hV.1 0 _ hm).2 _ _ _ _ _ rfl⟩, hV.1, hV.2.1⟩

/-! ## 3. Probe A: a false loop invariant -/

/-- The loop of the probe: `traverse konto invariant false {}`. -/
def paTrav {V : Vertrag zD} {Γ : Ctx} {Λ : List (Res zD)} : Stmt zD V false Γ Λ Λ :=
  .traverse () .fls .nil

def paRumpfEin : Endblock zD (vertragVon zD zEin) false [] zL :=
  .cons paTrav (.ret .empty (by simp [Vertrag.ende]))

def paRumpfLies : Endblock zD (vertragVon zD zLies) false [] zL :=
  .cons paTrav (.ret (.val zHundert) (by simp [Vertrag.ende]))

def paRumpfWrap : Endblock zD (vertragVon zD zWrap) false [] zL :=
  .cons paTrav (.ret .empty (by simp [Vertrag.ende]))

def paRumpfHaupt : Endblock zD (vertragVon zD zHaupt) false [] [] :=
  .cons paTrav (.ret .empty List.Perm.nil)

/-- **Probe A**: every function `ensures false`, every body
    `traverse () invariant false {}; return`. -/
def paP : Programm zD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .fls
  rumpf
    | .ein => paRumpfEin
    | .lies => paRumpfLies
    | .wrap => paRumpfWrap
    | .haupt => paRumpfHaupt

/-- Every body of the probe ends in `logik schleife`, whatever the handler
    and the oracle: the invariant fails at the first boundary. -/
theorem paP_lauf (O' : Orakel zD) (R : ∀ f : zD.Fn, World zD → Env zD (zD.params f) → RufAusgang f)
    (f : zD.Fn) (σ : World zD) (ρ : Env zD (zD.params f)) :
    execEnd (V := vertragVon zD f) O' 0 R (paP.rumpf f) σ ρ = .logik .schleife := by
  cases f <;> rfl

theorem paP_koerperR : ∀ f : zD.Fn, KoerperGutR paP 0 f := by
  intro f O' _ _ R _ _ σ ρ _
  refine ⟨fun σ' v h => ?_, fun g h => ?_⟩
  · rw [paP_lauf] at h; cases h
  · rw [paP_lauf] at h; cases h

theorem paP_fragmentG : programmImFragmentG paP zFs = true := by decide

theorem paP_fussG : fussOrtGB paP zFs = true := by decide

theorem paP_start : StartGut paP zSp zInit := fun _ => rfl

/-- **The old goal theorem certifies probe A**: all premises of
    `ziel_ort_rahmen` hold on `paP`, so its conclusion `VertragAmOrtG` holds
    on every reachable machine -- although every `ensures` is `false`
    (vacuously: G stops at the invariant before any return is logged). -/
theorem paP_rahmen_zertifiziert :
    ∀ M, RufErreichbarG paP zO 0 (RufStartG paP zSp zInit) M → VertragAmOrtG paP M :=
  ziel_ort_rahmen paP zO 0 zFs zSp zInit zE0 zO_gut zO_lokal zFs_voll paP_fragmentG paP_fussG
    paP_koerperR paP_start zInit_exklusiv

/-- The handler that answers every call with a hardware failure: it respects
    every contract and frame (it never answers normally) and answers no
    `logik` outcome. -/
def hwRuf : ∀ f : zD.Fn, World zD → Env zD (zD.params f) → RufAusgang f :=
  fun _ _ _ => .hardware .ieee

theorem hwRuf_rahmen (P : Programm zD) : RespektiertRahmen P hwRuf :=
  ⟨fun _ _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ h => (by cases h)⟩

theorem hwRuf_ohneLogik : OhneLogik hwRuf := fun _ _ _ _ h => by cases h

theorem zO_rahmen : RahmenO zO := fun a => nomatch a

theorem zO_vertrag (Q : AxEns zD) : AxVertragO Q zO := fun a => nomatch a

/-- **Probe A fails the new obligation**: no function of `paP` meets
    `KeineLogik`, for any declared axiom ensures -- the body runs into its
    false invariant from its (true) `requires`. -/
theorem paP_nicht_keineLogik (Q : AxEns zD) (f : zD.Fn) : ¬ KeineLogik paP 0 Q f := by
  intro h
  exact h zO zO_rahmen zO_lokal (zO_vertrag Q) hwRuf (hwRuf_rahmen paP) hwRuf_ohneLogik
    (zSp.welt []) (by cases f <;> exact .nil) rfl .schleife (paP_lauf zO hwRuf f _ _)

/-- **Probe A: the premise of the goal theorem is refuted.** -/
theorem paP_nicht_ganz (Q : AxEns zD) : ¬ ∀ f : zD.Fn, KoerperGutZ paP 0 Q f :=
  fun h => paP_nicht_keineLogik Q zHaupt (h zHaupt).2

/-- **Probe A: the conclusion of the goal theorem is refuted.** Two steps of
    thread 0 (`endeEntf`, `dannTrav`) reach a machine whose head stands at
    the `traverse` boundary with the invariant `false` -- G is stuck there,
    and `KeinLogikHaltG` fails. So `ziel_ort_ganz` cannot certify `paP` with
    ANY premises that hold: its conclusion is false on a reachable machine. -/
theorem paP_halt : ∃ M : RufMaschineG zD, RufErreichbarG paP zO 0 (RufStartG paP zSp zInit) M ∧
    ¬ KeinLogikHaltG zO 0 M := by
  have h00 : (RufStartG paP zSp zInit).faeden 0 = ⟨[], ⟨zHaupt, .nil, zSp.welt [],
      ⟨false, [], [], .nil, .ende paRumpfHaupt⟩⟩, [],
      [RufEreignisF.eintritt zHaupt .nil (zSp.welt [])]⟩ := rfl
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := paP) (O := zO) (passes := 0) h00 paTrav
    (.ret .empty List.Perm.nil) .nil rfl rfl
  obtain ⟨M2, s2, hZ2⟩ := w_dannTrav (P := paP) (O := zO) (passes := 0) hZ1.1 () .fls .nil .nil
    (.ende (.ret .empty List.Perm.nil)) .nil rfl
  refine ⟨M2, .schritt _ _ _ (.schritt _ _ _ .start s1) s2, fun h => ?_⟩
  have h0 := h 0
  unfold PrueftG at h0
  rw [hZ2.1] at h0
  exact absurd (h0.1 _ _ _ _ _ _ _ _ _ rfl) (by simp only [wahr?, eval, Bool.false_eq_true, not_false_eq_true])

end Gabbro.Grammatik
