/-
  File:      Grammatik/ZielOrtGanzZeuge.lean
  Subject:   WITNESSES AND THE PROBE for the goal theorem `ziel_ort_ganz`.

  * `ziel_ort_ganz_ref104`: the corpus program `beispiele/104-referenz.gab`
    (hand translation `r4P`) meets EVERY premise of `ziel_ort_ganz` jointly
    -- the new clause `KeineLogik` by the syntactic check -- and on its
    reached run (memory `0 -> 100`, the return of `einzahlen` logged) the
    `ensures` holds at the logged return and no thread is stopped at a
    `logik` check.
  * `ziel_ort_ganz_zeuge`: the concurrent program `zP` (`ZielOrtZeuge.lean`):
    every premise jointly, and thread 0's `lies` returns the value `100`
    thread 1 wrote, with its `ensures` at that return, from `ziel_ort_ganz`.
  * `ziel_ort_ganz_schleife`: a program WITH a loop whose invariant reads
    the shared table (`konto[0] <= 100`): `KeineLogik` proved against every
    handler and oracle, all premises jointly, and a reached machine whose
    head stands at the `traverse` boundary -- where the goal theorem says
    the invariant holds.
  * `ziel_ort_ganz_ax_zeuge`: the axiom program `axP` (`AxiomVertrag.lean`)
    with the declared ensures of its axiom: callee frames, axiom ensures
    and the check conjunct in the one theorem, on a contract no frame-only
    obligation proves.
  * PROBE A of the verdict (`messung/URTEIL-OPUS-2026-09-13.md` §2),
    reconstructed: `paP` gives every function `ensures false` and the body
    `traverse () invariant false {}; return`. `ziel_ort_rahmen` certifies
    it (`paP_rahmen_zertifiziert`); the new obligation fails on it
    (`paP_nicht_ganz`), and so does the new conclusion on a reachable machine
    (`paP_halt`): the stuck state is now a refutation, not a certificate.
-/
import Grammatik.ZielOrtGanz
import Grammatik.Referenz104Rahmen
import Grammatik.ZielOrtZeuge
import Grammatik.ZielOrtAxZeuge

namespace Gabbro.Grammatik

/-! ## 1. The corpus program `104-referenz.gab` -/

/-- No body of `r4P` has a loop invariant or a `state` transition. -/
theorem r4P_logikFrei : programmLogikFrei r4P r4Fs = true := by decide

/-- **Every function of `r4P` meets the obligation of the goal theorem**:
    the frame obligation from `Referenz104Rahmen.lean`, the new clause by
    the syntactic check. -/
theorem r4P_koerperZ : ∀ f : r4D.Fn, KoerperGutZ r4P 0 (axWahr r4D) f :=
  fun f => ⟨koerperGutRQ_of_R _ (r4P_koerperR f),
    programmLogikFrei_ok r4Fs_voll r4P_logikFrei 0 _ f⟩

/-- **`ziel_ort_ganz_ref104` -- `beispiele/104-referenz.gab` certified by the
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
  .traverse () .falsch .nil

def paRumpfEin : Endblock zD (vertragVon zD zEin) false [] zL :=
  .cons paTrav (.ret .keine (by rfl))

def paRumpfLies : Endblock zD (vertragVon zD zLies) false [] zL :=
  .cons paTrav (.ret (.wert zHundert) (by rfl))

def paRumpfWrap : Endblock zD (vertragVon zD zWrap) false [] zL :=
  .cons paTrav (.ret .keine (by rfl))

def paRumpfHaupt : Endblock zD (vertragVon zD zHaupt) false [] [] :=
  .cons paTrav (.ret .keine List.Perm.nil)

/-- **Probe A**: every function `ensures false`, every body
    `traverse () invariant false {}; return`. -/
def paP : Programm zD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .falsch
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
    (.ret .keine List.Perm.nil) .nil rfl rfl
  obtain ⟨M2, s2, hZ2⟩ := w_dannTrav (P := paP) (O := zO) (passes := 0) hZ1.1 () .falsch .nil .nil
    (.ende (.ret .keine List.Perm.nil)) .nil rfl
  refine ⟨M2, .schritt _ _ _ (.schritt _ _ _ .start s1) s2, fun h => ?_⟩
  have h0 := h 0
  unfold PrueftG at h0
  rw [hZ2.1] at h0
  exact absurd (h0.1 _ _ _ _ _ _ _ _ _ rfl) (by simp [eval, wahr?])

/-! ## 4. A program with a loop: the check is reached, and it passes -/

/-- The loop invariant: `konto[0] <= 100` -- it reads the shared table. -/
def lInv {Γ : Ctx} : Expr zD Γ zL .bool := .le (.slot () () zIdx zDarf) zHundert

theorem lInv_orte {Γ : Ctx} : (lInv (Γ := Γ)).orte = [.inl ()] := rfl

theorem lInv_wahr {Γ : Ctx} (σ₀ σ : World zD) (ρ : Env zD Γ) : wahr? (eval σ₀ lInv σ ρ) = true := by
  show decide ((σ.slots () 0 ()).n ≤ 100) = true
  exact decide_eq_true (σ.slots () 0 ()).le_hi

/-- The loop: `traverse konto invariant konto[0] <= 100 {}`. -/
def lTrav {V : Vertrag zD} : Stmt zD V false [] zL zL := .traverse () lInv .nil

def lRumpfEin : Endblock zD (vertragVon zD zEin) false [] zL := .cons lTrav (.ret .keine (by rfl))

def lRumpfLies : Endblock zD (vertragVon zD zLies) false [] zL :=
  .cons lTrav (.ret (.wert zHundert) (by rfl))

def lRumpfWrap : Endblock zD (vertragVon zD zWrap) false [] zL := .cons lTrav (.ret .keine (by rfl))

def lRumpfHaupt : Endblock zD (vertragVon zD zHaupt) false [] [] := .ret .keine List.Perm.nil

/-- **The loop program**: the three lock holders run the loop and return,
    `haupt` returns; every contract `true`. -/
def lP : Programm zD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf
    | .ein => lRumpfEin
    | .lies => lRumpfLies
    | .wrap => lRumpfWrap
    | .haupt => lRumpfHaupt

/-- Thread 0 starts in `wrap` (holding the lock), every other thread in
    `haupt` (holding none). -/
def lInit : Faden → Σ f : zD.Fn, Env zD (zD.params f) :=
  fun t => if t = 0 then ⟨zWrap, .nil⟩ else ⟨zHaupt, .nil⟩

theorem lInit_exklusiv : StartExklusiv (D := zD) lInit := by
  intro t u htu L hL hLu
  by_cases ht : t = 0
  · have hu : u ≠ 0 := fun h => htu (ht.trans h.symm)
    simp only [lInit, if_neg hu] at hLu
    exact nomatch hLu
  · simp only [lInit, if_neg ht] at hL
    exact nomatch hL

theorem lP_start : StartGut lP zSp lInit := by
  intro t
  by_cases ht : t = 0
  · subst ht; rfl
  · simp only [lInit]; rw [if_neg ht]; rfl

/-- A `traverse` with an empty body and an invariant true everywhere runs
    through: its outcome is `ok`, with the environment unchanged. -/
theorem traverseLauf_leer_ok {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {τ : Ty}
    (inv : World D → Env D Γ → World D × Bool) (hinv : ∀ σ ρ, (inv σ ρ).2 = true) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ),
      ∃ σ', traverseLauf (V := V) (l := l)
        (fun σ (ρ : Env D (τ :: Γ)) => (Ausgang.ok σ ρ : Ausgang V true (τ :: Γ))) inv ks σ ρ =
        .ok σ' ρ
  | [], σ, ρ => ⟨(inv σ ρ).1, by simp only [traverseLauf, hinv, if_true]⟩
  | k :: ks, σ, ρ => by
      obtain ⟨σ', h⟩ := traverseLauf_leer_ok inv hinv ks (inv σ ρ).1 ρ
      refine ⟨σ', ?_⟩
      simp only [traverseLauf, hinv]
      exact h

/-- An end block that starts with such a loop continues with its rest. -/
theorem execEnd_trav_leer {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (t : D.Tab)
    (inv : Expr D Γ Λ .bool) (rest : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hinv : ∀ (σ₀ σ : World D) (ρ : Env D Γ), wahr? (eval σ₀ inv σ ρ) = true) :
    ∃ σ', execEnd O passes R (.cons (.traverse t inv .nil) rest) σ ρ =
      execEnd O passes R rest σ' ρ := by
  obtain ⟨σ', h⟩ := traverseLauf_leer_ok (V := V) (l := l) (τ := .index (D.count t))
    (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ)))
    (fun σ ρ => hinv _ _ ρ) (alleIndizes (D.count t)) σ ρ
  refine ⟨σ', ?_⟩
  have hs : execStmt (V := V) O passes R (Stmt.traverse (l := l) t inv .nil) σ ρ = .ok σ' ρ := h
  simp only [execEnd, hs]

/-- Every body of the loop program RETURNS, against every handler and
    oracle: both loop boundaries pass (`lInv_wahr`). -/
theorem lP_lauf (O' : Orakel zD) (R : ∀ f : zD.Fn, World zD → Env zD (zD.params f) → RufAusgang f)
    (f : zD.Fn) (σ : World zD) (ρ : Env zD (zD.params f)) :
    ∃ σ' v, execEnd (V := vertragVon zD f) O' 0 R (lP.rumpf f) σ ρ = .zurueck σ' v := by
  cases f with
  | haupt => exact ⟨_, _, rfl⟩
  | ein =>
      obtain ⟨σ', h⟩ := execEnd_trav_leer (V := vertragVon zD zEin) (Λ := zL) O' 0 R () lInv
        (.ret .keine (by rfl)) σ ρ (fun _ _ _ => lInv_wahr _ _ _)
      exact ⟨_, _, h⟩
  | lies =>
      obtain ⟨σ', h⟩ := execEnd_trav_leer (V := vertragVon zD zLies) (Λ := zL) O' 0 R () lInv
        (.ret (.wert zHundert) (by rfl)) σ ρ (fun _ _ _ => lInv_wahr _ _ _)
      exact ⟨_, _, h⟩
  | wrap =>
      obtain ⟨σ', h⟩ := execEnd_trav_leer (V := vertragVon zD zWrap) (Λ := zL) O' 0 R () lInv
        (.ret .keine (by rfl)) σ ρ (fun _ _ _ => lInv_wahr _ _ _)
      exact ⟨_, _, h⟩

theorem lP_koerperZ : ∀ f : zD.Fn, KoerperGutZ lP 0 (axWahr zD) f := by
  intro f
  refine ⟨fun O' _ _ _ R _ _ σ ρ _ => ⟨fun _ _ _ => rfl, fun g h => ?_⟩,
    fun O' _ _ _ R _ _ σ ρ _ e h => ?_⟩
  · obtain ⟨σ', v, hl⟩ := lP_lauf O' (torRuf lP R) f σ ρ
    rw [hl] at h
    cases h
  · obtain ⟨σ', v, hl⟩ := lP_lauf O' R f σ ρ
    rw [hl] at h
    cases h

theorem lP_fragmentG : programmImFragmentG lP zFs = true := by decide

theorem lP_fussG : fussOrtGB lP zFs = true := by decide

/-- **`ziel_ort_ganz_schleife` -- the check conjunct is not vacuous.** Every
    premise of `ziel_ort_ganz` holds on the loop program `lP` (with
    `KeineLogik` PROVED for a body with a loop whose invariant reads the
    shared table, not by the syntactic check). Two steps of thread 0
    (`endeEntf`, `dannTrav`) reach a machine whose head stands at the
    `traverse` boundary; there the goal theorem gives that the invariant
    holds at the machine world, and that is exactly the premise with which
    G fires the next iteration (`travNext`): the machine moves on. -/
theorem ziel_ort_ganz_schleife :
    GutO zO ∧ RegLokal zO ∧ (∀ g : zD.Fn, g ∈ zFs) ∧ programmImFragmentG lP zFs = true ∧
    fussOrtGB lP zFs = true ∧ (∀ f : zD.Fn, KoerperGutZ lP 0 (axWahr zD) f) ∧
    StartGut lP zSp lInit ∧ StartExklusiv (D := zD) lInit ∧
    ∃ M2 : RufMaschineG zD, RufErreichbarG lP zO 0 (RufStartG lP zSp lInit) M2 ∧
      (∃ (spur : List (Ereignis zD)) (log : List (RufEreignisF zD)),
        M2.faeden 0 = ⟨[], ⟨zWrap, .nil, zSp.welt [], ⟨false, [], zL, .nil,
          .trav () lInv .nil (alleIndizes (zD.count ())) (.dann .nil (.ende (.ret .keine (by rfl))))⟩⟩,
          spur, log⟩) ∧
      wahr? (eval ((M2.weltVon 0).lese zL (lInv (Γ := [])).orte) lInv
        ((M2.weltVon 0).lese zL (lInv (Γ := [])).orte) .nil) = true ∧
      ∃ M3 : RufMaschineG zD, RufSchrittG lP zO 0 M2 0 M3 := by
  have hZ := ziel_ort_ganz lP zO 0 (axWahr zD) zFs zSp lInit zE0 zO_gut zO_lokal
    (axVertragO_wahr zO) axEnsLokal_wahr zFs_voll lP_fragmentG lP_fussG lP_koerperZ lP_start
    lInit_exklusiv
  have h00 : (RufStartG lP zSp lInit).faeden 0 = ⟨[], ⟨zWrap, .nil, zSp.welt [],
      ⟨false, [], zL, .nil, .ende lRumpfWrap⟩⟩, startSpur zWrap,
      [RufEreignisF.eintritt zWrap .nil (zSp.welt [])]⟩ := rfl
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := lP) (O := zO) (passes := 0) h00 lTrav
    (.ret .keine (by rfl)) .nil rfl rfl
  obtain ⟨M2, s2, hZ2⟩ := w_dannTrav (P := lP) (O := zO) (passes := 0) hZ1.1 () lInv .nil .nil
    (.ende (.ret .keine (by rfl))) .nil rfl
  have hr2 : RufErreichbarG lP zO 0 (RufStartG lP zSp lInit) M2 :=
    .schritt _ _ _ (.schritt _ _ _ .start s1) s2
  have h0 := (hZ M2 hr2).2.1 0
  unfold PrueftG at h0
  rw [hZ2.1] at h0
  have hw := h0.1 _ _ _ _ _ _ _ _ _ rfl
  have hoff : offen (M2.faeden 0).spur = [()] := by
    rw [hZ2.spur, offen_weltVon, hZ1.spur]
    rfl
  obtain ⟨M3, s3, _⟩ := w_travNext (P := lP) (O := zO) (passes := 0) hZ2.1 () lInv .nil _ _
    (.dann .nil (.ende (.ret .keine (by rfl)))) .nil rfl
    (by rw [hZ2.welt] at hw ⊢; exact hw) (hgL (by rw [← hZ2.spur]; exact hoff)).heldIn
  refine ⟨zO_gut, zO_lokal, zFs_voll, lP_fragmentG, lP_fussG, lP_koerperZ, lP_start,
    lInit_exklusiv, M2, hr2, ⟨_, _, hZ2.1⟩, ?_, M3, s3⟩
  rw [hZ2.welt]
  exact lInv_wahr _ _ _

/-- **`ziel_ort_ganz_fortschritt_zeuge`.** On the loop program, the machine
    reached after two steps of thread 0 stands at a `logik` check
    (`AnPruefungG`: the `traverse` boundary), its head's holdings are exactly
    the held lock, and the progress theorem `ziel_ort_ganz_fortschritt`
    yields a step of thread 0 there. -/
theorem ziel_ort_ganz_fortschritt_zeuge :
    ∃ M2 : RufMaschineG zD, RufErreichbarG lP zO 0 (RufStartG lP zSp lInit) M2 ∧
      AnPruefungG M2 0 ∧ HeldGenau (M2.faeden 0).kopf.rest.2.2.1 (offen (M2.faeden 0).spur) ∧
      ∃ M3 : RufMaschineG zD, RufSchrittG lP zO 0 M2 0 M3 := by
  have h00 : (RufStartG lP zSp lInit).faeden 0 = ⟨[], ⟨zWrap, .nil, zSp.welt [],
      ⟨false, [], zL, .nil, .ende lRumpfWrap⟩⟩, startSpur zWrap,
      [RufEreignisF.eintritt zWrap .nil (zSp.welt [])]⟩ := rfl
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := lP) (O := zO) (passes := 0) h00 lTrav
    (.ret .keine (by rfl)) .nil rfl rfl
  obtain ⟨M2, s2, hZ2⟩ := w_dannTrav (P := lP) (O := zO) (passes := 0) hZ1.1 () lInv .nil .nil
    (.ende (.ret .keine (by rfl))) .nil rfl
  have hr2 : RufErreichbarG lP zO 0 (RufStartG lP zSp lInit) M2 :=
    .schritt _ _ _ (.schritt _ _ _ .start s1) s2
  have hA : AnPruefungG M2 0 := by
    unfold AnPruefungG
    rw [hZ2.1]
    exact Or.inl ⟨_, _, _, _, _, _, _, _, _, rfl⟩
  have hH : HeldGenau (M2.faeden 0).kopf.rest.2.2.1 (offen (M2.faeden 0).spur) := by
    rw [hZ2.1]
    exact hgL (by rw [← hZ2.spur, hZ2.spur, offen_weltVon, hZ1.spur]; rfl)
  exact ⟨M2, hr2, hA, hH, ziel_ort_ganz_fortschritt lP zO 0 (axWahr zD) zFs zSp lInit zE0 zO_gut
    zO_lokal (axVertragO_wahr zO) axEnsLokal_wahr zFs_voll lP_fragmentG lP_fussG lP_koerperZ
    lP_start lInit_exklusiv M2 hr2 0 hH hA⟩

/-! ## 5. Declared axiom ensures inside the one theorem -/

theorem axO_lokal : RegLokal axO := ⟨(fun r _ _ _ => nomatch r), (fun g _ _ _ => nomatch g)⟩

theorem axP_logikFrei : programmLogikFrei axP axFs = true := by decide

theorem axP_koerperZ : ∀ f : axD.Fn, KoerperGutZ axP 0 axQ f :=
  fun f => ⟨koerperGutRQ_of_A (axP_koerperA f), programmLogikFrei_ok axFs_voll axP_logikFrei 0 _ f⟩

/-- **`ziel_ort_ganz_ax_zeuge` -- the declared axiom ensures inside the goal
    theorem.** On the axiom program `axP` (`AxiomVertrag.lean`: `zaehle`
    calls the axiom `inc` and promises `result == tab[0]`, which NO
    frame-only obligation can prove, `inc_ensures_nicht_V`), every premise of
    `ziel_ort_ganz` holds with the declared ensures `axQ` of `inc`; on the
    reached run (memory `0 -> 1`, `zaehle` returns `1`, logged) its
    `ensures` holds at the logged return, from `ziel_ort_ganz`, and no
    thread is stopped at a `logik` check. -/
theorem ziel_ort_ganz_ax_zeuge :
    GutO axO ∧ RegLokal axO ∧ AxVertragO axQ axO ∧ AxEnsLokal axQ ∧ (∀ g : axD.Fn, g ∈ axFs) ∧
    programmImFragmentG axP axFs = true ∧ fussOrtGB axP axFs = true ∧
    (∀ f : axD.Fn, KoerperGutZ axP 0 axQ f) ∧ StartGut axP axSp axInit ∧
    StartExklusiv (D := axD) axInit ∧ ¬ KoerperGutV axP 0 axZaehle ∧
    ∃ M : RufMaschineG axD, RufErreichbarG axP axO 0 (RufStartG axP axSp axInit) M ∧
      (axSp.slots () 0 ()).n = 0 ∧ (M.speicher.slots () 0 ()).n = 1 ∧
      (∃ (rho : Env axD (axD.params axZaehle)) (v : ErgVal axD (axD.erg axZaehle))
        (s0 s1 : World axD),
        (v : Zahl 0 3).n = 1 ∧ RufEreignisF.rueck axZaehle rho v s0 s1 ∈ (M.faeden 0).log ∧
        EnsAmRueck axP axZaehle s0 s1 rho v) ∧
      VertragAmOrtG axP M ∧ KeinLogikHaltG axO 0 M := by
  have hFragG := programmImFragmentG_of_V axP axFs axP_fragment
  have hFussG := fussOrtGB_of_V axP axFs axP_fragment axP_fuss
  have hZ := ziel_ort_ganz axP axO 0 axQ axFs axSp axInit axE0 axO_gut axO_lokal axO_vertrag
    axQ_lokal axFs_voll hFragG hFussG axP_koerperZ axP_start axInit_exklusiv
  obtain ⟨M, hr, hslot, rho, v, s0, s1, hv, hlog⟩ := axLauf
  have hV := hZ M hr
  exact ⟨axO_gut, axO_lokal, axO_vertrag, axQ_lokal, axFs_voll, hFragG, hFussG, axP_koerperZ,
    axP_start, axInit_exklusiv, inc_ensures_nicht_V, M, hr, rfl, hslot,
    ⟨rho, v, s0, s1, hv, hlog, (hV.1 0 _ hlog).2 axZaehle rho v s0 s1 rfl⟩, hV.1, hV.2.1⟩

/-- **`ziel_ort_ganz_vertrag_zeuge`** -- the contract half with a non-trivial
    declared ensures, its premises jointly on `axP`. -/
theorem ziel_ort_ganz_vertrag_zeuge :
    (∀ f : axD.Fn, KoerperGutRQ axP 0 axQ f) ∧
    ∀ M : RufMaschineG axD, RufErreichbarG axP axO 0 (RufStartG axP axSp axInit) M →
      VertragAmOrtG axP M :=
  ⟨fun f => (axP_koerperZ f).1,
    ziel_ort_ganz_vertrag axP axO 0 axQ axFs axSp axInit axE0 axO_gut axO_lokal axO_vertrag
      axQ_lokal axFs_voll (programmImFragmentG_of_V axP axFs axP_fragment)
      (fussOrtGB_of_V axP axFs axP_fragment axP_fuss) (fun f => (axP_koerperZ f).1) axP_start
      axInit_exklusiv⟩

/-- **`ziel_ort_voll_ax_lokal_aus_ganz_zeuge`** -- the premises of
    `ziel_ort_voll_ax` (plus `RegLokal`) jointly on `axP`, through the new
    derivation. -/
theorem ziel_ort_voll_ax_lokal_aus_ganz_zeuge :
    ∀ M : RufMaschineG axD, RufErreichbarG axP axO 0 (RufStartG axP axSp axInit) M →
      VertragAmOrtG axP M :=
  ziel_ort_voll_ax_lokal_aus_ganz axP axO 0 axQ axFs axSp axInit axE0 axO_gut axO_lokal axO_vertrag
    axQ_lokal axFs_voll axP_fragment axP_fuss axP_koerperA axP_start axInit_exklusiv

/-! ## CUTS:

  What is proved: all premises of `ziel_ort_ganz` jointly on four programs
  -- the corpus program 104 (`ziel_ort_ganz_ref104`: memory `0 -> 100`,
  `ensures` of `einzahlen` at its logged return), the concurrent `zP`
  (`ziel_ort_ganz_zeuge`: a cross-thread return of `100` with its
  `ensures`), the axiom program `axP` with a declared axiom ensures
  (`ziel_ort_ganz_ax_zeuge`), and a loop program `lP` whose invariant reads
  the shared table (`ziel_ort_ganz_schleife`, `ziel_ort_ganz_fortschritt_zeuge`:
  a reached machine at the `traverse` boundary, the invariant from the
  theorem, and a step from the progress conjunct). Probe A of the verdict:
  certified by `ziel_ort_rahmen` (`paP_rahmen_zertifiziert`), refuted by
  the new obligation (`paP_nicht_ganz`) and by the new conclusion on a
  reachable machine (`paP_halt`).

  What is NOT covered: every contract of `lP` is `true` (the loop fixture
  shows the check, the other three the contracts); no witness reaches a
  `state` transition (`zD` declares no transition); the non-existence of a
  step at probe A's stuck machine is shown through the conclusion
  (`KeinLogikHaltG` fails there), not by inverting the step relation.
-/

#print axioms Gabbro.Grammatik.lP_koerperZ
#print axioms Gabbro.Grammatik.ziel_ort_ganz_schleife
#print axioms Gabbro.Grammatik.ziel_ort_ganz_fortschritt_zeuge

#print axioms Gabbro.Grammatik.ziel_ort_ganz_ref104
#print axioms Gabbro.Grammatik.ziel_ort_ganz_zeuge
#print axioms Gabbro.Grammatik.ziel_ort_ganz_ax_zeuge
#print axioms Gabbro.Grammatik.ziel_ort_ganz_vertrag_zeuge
#print axioms Gabbro.Grammatik.ziel_ort_voll_ax_lokal_aus_ganz_zeuge
#print axioms Gabbro.Grammatik.paP_rahmen_zertifiziert
#print axioms Gabbro.Grammatik.paP_nicht_ganz
#print axioms Gabbro.Grammatik.paP_halt

end Gabbro.Grammatik
