module
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanzZeuge.Teil1Basis
import all Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanzZeuge.Teil1Basis

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz
public import Grammatik.Korpus.Referenz.Referenz104Rahmen
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtZeuge
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAxZeuge

@[expose] public section



namespace Gabbro.Grammatik
/-! ## 4. A program with a loop: the check is reached, and it passes -/

/-- The loop invariant: `konto[0] <= 100` -- it reads the shared table. -/
def lInv {Γ : Ctx} : Expr zD Γ zL .bool := .le (.slot () () zIdx zDarf) zHundert

theorem lInv_orte {Γ : Ctx} : (lInv (Γ := Γ)).orte = [.inl ()] := by rfl

theorem lInv_wahr {Γ : Ctx} (σ₀ σ : World zD) (ρ : Env zD Γ) : wahr? (eval σ₀ lInv σ ρ) = true := by
  show decide ((σ.slots () 0 ()).n ≤ 100) = true
  exact decide_eq_true (σ.slots () 0 ()).le_hi

/-- The loop: `traverse konto invariant konto[0] <= 100 {}`. -/
def lTrav {V : Vertrag zD} : Stmt zD V false [] zL zL := .traverse () lInv .nil

def lRumpfEin : Endblock zD (vertragVon zD zEin) false [] zL := .cons lTrav (.ret .empty (by rfl))

def lRumpfLies : Endblock zD (vertragVon zD zLies) false [] zL :=
  .cons lTrav (.ret (.val zHundert) (by rfl))

def lRumpfWrap : Endblock zD (vertragVon zD zWrap) false [] zL := .cons lTrav (.ret .empty (by rfl))

def lRumpfHaupt : Endblock zD (vertragVon zD zHaupt) false [] [] := .ret .empty List.Perm.nil

/-- **The loop program**: the three lock holders run the loop and return,
    `haupt` returns; every contract `true`. -/
def lP : Programm zD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
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
        (.ret .empty (by rfl)) σ ρ (fun _ _ _ => lInv_wahr _ _ _)
      exact ⟨_, _, h⟩
  | lies =>
      obtain ⟨σ', h⟩ := execEnd_trav_leer (V := vertragVon zD zLies) (Λ := zL) O' 0 R () lInv
        (.ret (.val zHundert) (by rfl)) σ ρ (fun _ _ _ => lInv_wahr _ _ _)
      exact ⟨_, _, h⟩
  | wrap =>
      obtain ⟨σ', h⟩ := execEnd_trav_leer (V := vertragVon zD zWrap) (Λ := zL) O' 0 R () lInv
        (.ret .empty (by rfl)) σ ρ (fun _ _ _ => lInv_wahr _ _ _)
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
          .trav () lInv .nil (alleIndizes (zD.count ())) (.dann .nil (.ende (.ret .empty (by rfl))))⟩⟩,
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
    (.ret .empty (by rfl)) .nil rfl rfl
  obtain ⟨M2, s2, hZ2⟩ := w_dannTrav (P := lP) (O := zO) (passes := 0) hZ1.1 () lInv .nil .nil
    (.ende (.ret .empty (by rfl))) .nil rfl
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
    (.dann .nil (.ende (.ret .empty (by rfl)))) .nil rfl
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
    (.ret .empty (by rfl)) .nil rfl rfl
  obtain ⟨M2, s2, hZ2⟩ := w_dannTrav (P := lP) (O := zO) (passes := 0) hZ1.1 () lInv .nil .nil
    (.ende (.ret .empty (by rfl))) .nil rfl
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

end Gabbro.Grammatik
