/-
  File:      Grammatik/ProbeD.lean
  Subject:   PROBE D (`messung/URTEIL-OPUS-2026-09-14.md` §5), rebuilt and
             REFUTED by the budget-quantified goal theorem.

  Probe A with `forever` instead of `traverse`: on `zD`, every function
  `ensures false`, every body `forever () invariant w { leave }; return`.
  Two variants, `fvP false` (invariant `false`, the verdict's `fvP`) and
  `fvP true` (invariant `true`, the verdict's `fwP` -- the shape of
  `manifest_pruefen` in `beispiele/04-schleifen.gab`, where the loop leaves
  and the function returns).

  * At budget `0` every body stops at the loop's named assumption before
    the first pass (`fvP_lauf0`: `hardware (fortschritt ())`), so the
    per-budget obligation holds vacuously (`fvP_koerper0`) and the
    per-budget lemma certifies both variants (`probeD_bei0_zertifiziert`)
    -- the defect the verdict found, kept as a theorem.
  * The emitted C does not test the invariant and runs the loop once: at
    budget `1` the body ends in `logik schleife` (`w = false`) or returns
    under `ensures false` (`w = true`).
  * **The goal theorem demands the obligation at every budget, and both
    variants fail it** (`probeD_nicht`, `probeD_nicht_leer`, `fwP_nicht`),
    for every declared axiom ensures and every well-formed lock-invariant
    family with a satisfiable invariant.
  * **Its conclusion fails on a reachable machine** (as `paP_halt` for
    probe A): at budget `1`, two steps reach a `forever` head whose
    invariant is `false` (`probeD_halt`: `¬ KeinLogikHaltG`); five steps
    reach a finished start frame whose `ensures` is `false`
    (`fwP_ende_verletzt`: `¬ StartEndeG`).
-/
import Grammatik.ZielOrtStart
import Grammatik.ZielOrtSperreZeuge

namespace Gabbro.Grammatik

/-! ## 1. The probe -/

/-- The loop invariant of the probe: `true` or `false`. -/
def fvInv {Γ : Ctx} {Λ : List (Res zD)} : Bool → Expr zD Γ Λ .bool
  | true => .wahr
  | false => .falsch

/-- `forever () invariant w { leave }`. -/
def fvSchleife {V : Vertrag zD} {Γ : Ctx} {Λ : List (Res zD)} (w : Bool) :
    Stmt zD V false Γ Λ Λ :=
  .forever () (fvInv w) (.cons (.leave rfl) .nil)

def fvRumpfEin (w : Bool) : Endblock zD (vertragVon zD zEin) false [] zL :=
  .cons (fvSchleife w) (.ret .keine (by rfl))

def fvRumpfLies (w : Bool) : Endblock zD (vertragVon zD zLies) false [] zL :=
  .cons (fvSchleife w) (.ret (.wert zHundert) (by rfl))

def fvRumpfWrap (w : Bool) : Endblock zD (vertragVon zD zWrap) false [] zL :=
  .cons (fvSchleife w) (.ret .keine (by rfl))

def fvRumpfHaupt (w : Bool) : Endblock zD (vertragVon zD zHaupt) false [] [] :=
  .cons (fvSchleife w) (.ret .keine List.Perm.nil)

/-- **Probe D**: every function `ensures false`, every body
    `forever () invariant w { leave }; return`. `fvP false` is the
    verdict's `fvP`, `fvP true` its `fwP`. -/
def fvP (w : Bool) : Programm zD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .falsch
  rumpf
    | .ein => fvRumpfEin w
    | .lies => fvRumpfLies w
    | .wrap => fvRumpfWrap w
    | .haupt => fvRumpfHaupt w

theorem fvP_ohneLocks (w : Bool) (f : zD.Fn) : ((fvP w).rumpf f).ohneLocks = true := by
  cases w <;> cases f <;> rfl

/-- **At budget `0`** every body stops before the first pass, at the
    loop's named assumption -- whatever the handler, oracle and world. -/
theorem fvP_lauf0 (w : Bool) (O' : Orakel zD)
    (R : ∀ f : zD.Fn, World zD → Env zD (zD.params f) → RufAusgang f)
    (f : zD.Fn) (σ : World zD) (ρ : Env zD (zD.params f)) :
    execEnd (V := vertragVon zD f) O' 0 R ((fvP w).rumpf f) σ ρ =
      .hardware (.fortschritt ()) := by
  cases w <;> cases f <;> rfl

/-- **At budget `1`, invariant `false`**: the loop is entered and its
    invariant fails. -/
theorem fvP_lauf1_falsch (O' : Orakel zD)
    (R : ∀ f : zD.Fn, World zD → Env zD (zD.params f) → RufAusgang f)
    (f : zD.Fn) (σ : World zD) (ρ : Env zD (zD.params f)) :
    execEnd (V := vertragVon zD f) O' 1 R ((fvP false).rumpf f) σ ρ = .logik .schleife := by
  cases f <;> rfl

/-- **At budget `1`, invariant `true`**: the loop is entered, left, and the
    body RETURNS -- under `ensures false`. -/
theorem fvP_lauf1_wahr (O' : Orakel zD)
    (R : ∀ f : zD.Fn, World zD → Env zD (zD.params f) → RufAusgang f)
    (f : zD.Fn) (σ : World zD) (ρ : Env zD (zD.params f)) :
    ∃ σ' v, execEnd (V := vertragVon zD f) O' 1 R ((fvP true).rumpf f) σ ρ = .zurueck σ' v := by
  cases f <;> exact ⟨_, _, rfl⟩

/-! ## 2. The per-budget obligation at `0` holds: the defect, kept -/

/-- **The obligation at budget `0` holds vacuously**, for both variants,
    every declared axiom ensures and every lock-invariant family. -/
theorem fvP_koerper0 (w : Bool) (Q : AxEns zD) (S : SperrInv zD) (f : zD.Fn) :
    KoerperGutS (fvP w) 0 Q S f := by
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v h => ?_, fun g h => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e h => ?_⟩ <;>
    rw [Endblock.execH_ohne S O' U 0 _ _ (fvP_ohneLocks w f), fvP_lauf0] at h <;> cases h

theorem fvP_fragmentG (w : Bool) : programmImFragmentG (fvP w) zFs = true := by
  cases w <;> decide

theorem fvP_fussS (w : Bool) : fussSperreB (fvP w) (SperrInv.leer zD) zFs = true := by
  cases w <;> decide

theorem fvP_start (w : Bool) : StartGut (fvP w) zSp zInit := fun _ => rfl

/-- **THE DEFECT, as a theorem**: the per-budget lemma at budget `0`
    certifies probe D -- every premise holds, so its conclusion holds on
    every reachable machine of budget `0` -- although every `ensures` is
    `false` and the emitted C runs every loop once. -/
theorem probeD_bei0_zertifiziert (w : Bool) : ∀ M : RufMaschineG zD,
    RufErreichbarG (fvP w) zO 0 (RufStartG (fvP w) zSp zInit) M →
      ((VertragAmOrtG (fvP w) M ∧ SperrInvG (SperrInv.leer zD) M ∧ KeinLogikHaltG zO 0 M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG (fvP w) zO 0 M t M') ∧
      InvAmOrtG (fvP w) M) ∧ StartEndeG (fvP w) M :=
  ziel_ort_sperre_ende_bei (fvP w) zO 0 (axWahr zD) (SperrInv.leer zD) zFs zSp zInit zE0 zO_gut
    zO_lokal (axVertragO_wahr zO) axEnsLokal_wahr sperrInvOk_leer zFs_voll (fvP_fragmentG w)
    (fvP_fussS w) (fvP_koerper0 w _ _) (fvP_start w) (fun _ => rfl) zInit_exklusiv
    (invGutS_leer rfl)

/-! ## 3. The obligation over EVERY budget fails -/

/-- The (empty) arguments of `haupt`. -/
def fvRho : Env zD (zD.params zHaupt) := .nil

theorem hwRuf_ohneVorbedingung : OhneVorbedingung hwRuf := fun _ _ _ _ h => by cases h

/-- **Probe D (invariant `false`) fails the goal theorem's obligation**: at
    budget `1` every body ends in `logik schleife`, which the no-`logik`
    clause excludes -- for every declared axiom ensures and every
    well-formed family whose invariants hold somewhere. -/
theorem probeD_nicht (Q : AxEns zD) (S : SperrInv zD) (hS : SperrInvOk S) (s : Speicher zD)
    (hs : ∀ L, S.inv L s = true) : ¬ ∀ (passes : Nat) (f : zD.Fn), KoerperGutS (fvP false) passes Q S f := by
  intro h
  refine (h 1 zHaupt).2 zO zO_rahmen zO_lokal (zO_vertrag Q) (fun L σ => mischU S L σ s)
    (havocOk_misch hS (fun _ _ => s) (fun L _ => hs L)) hwRuf (hwRuf_rahmen _) hwRuf_ohneLogik
    (zSp.welt []) fvRho rfl .schleife ?_
  rw [Endblock.execH_ohne S zO _ 1 hwRuf _ (fvP_ohneLocks false zHaupt)]
  exact fvP_lauf1_falsch zO hwRuf zHaupt _ _

/-- Probe D at the empty family. -/
theorem probeD_nicht_leer (Q : AxEns zD) :
    ¬ ∀ (passes : Nat) (f : zD.Fn), KoerperGutS (fvP false) passes Q (SperrInv.leer zD) f :=
  probeD_nicht Q _ sperrInvOk_leer zSp (fun _ => rfl)

/-- **The leaving variant (invariant `true`, the shape of
    `manifest_pruefen`) fails too**: at budget `1` the body returns, and
    `ensures false` does not hold -- the triple clause fails. -/
theorem fwP_nicht (Q : AxEns zD) (S : SperrInv zD) (hS : SperrInvOk S) (s : Speicher zD)
    (hs : ∀ L, S.inv L s = true) : ¬ ∀ (passes : Nat) (f : zD.Fn), KoerperGutS (fvP true) passes Q S f := by
  intro h
  have h1 := ((h 1 zHaupt).1 zO zO_rahmen zO_lokal (zO_vertrag Q) (fun L σ => mischU S L σ s)
    (havocOk_misch hS (fun _ _ => s) (fun L _ => hs L)) hwRuf (hwRuf_rahmen _)
    hwRuf_ohneVorbedingung (zSp.welt []) fvRho rfl).1
  obtain ⟨σ', v, hrun⟩ := fvP_lauf1_wahr zO hwRuf zHaupt (zSp.welt []) fvRho
  rw [← Endblock.execH_ohne S zO (fun L σ => mischU S L σ s) 1 hwRuf _
    (fvP_ohneLocks true zHaupt)] at hrun
  have := h1 σ' v hrun
  simp [EnsAmRueck, fvP, eval, wahr?] at this

/-! ## 4. The conclusion over every budget fails on reachable machines -/

theorem fvStart0 (w : Bool) : (RufStartG (fvP w) zSp zInit).faeden 0 = ⟨[], ⟨zHaupt, .nil, zSp.welt [],
    ⟨false, [], [], .nil, .ende (fvRumpfHaupt w)⟩⟩, [],
    [RufEreignisF.eintritt zHaupt .nil (zSp.welt [])]⟩ := rfl

/-- **Probe D: the conclusion is refuted at budget `1`.** Two steps of
    thread 0 (`endeEntf`, `dannForever`) reach a machine whose head stands
    at the `forever` head with one pass left and the invariant `false`: G
    is stuck there, and `KeinLogikHaltG` fails. -/
theorem probeD_halt : ∃ M : RufMaschineG zD,
    RufErreichbarG (fvP false) zO 1 (RufStartG (fvP false) zSp zInit) M ∧ ¬ KeinLogikHaltG zO 1 M := by
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := fvP false) (O := zO) (passes := 1) (fvStart0 false)
    (fvSchleife false) (.ret .keine List.Perm.nil) .nil rfl rfl
  obtain ⟨M2, s2, hZ2⟩ := w_dannForever (P := fvP false) (O := zO) (passes := 1) hZ1.1 () .falsch
    (.cons (.leave rfl) .nil) .nil (.ende (.ret .keine List.Perm.nil)) .nil rfl
  refine ⟨M2, .schritt _ _ _ (.schritt _ _ _ .start s1) s2, fun h => ?_⟩
  have h0 := h 0
  unfold PrueftG at h0
  rw [hZ2.1] at h0
  exact absurd (h0.2.1 _ _ _ _ _ _ _ _ _ rfl) (by simp [eval, wahr?])

/-- **The leaving variant: the conclusion is refuted at budget `1`.** Five
    steps of thread 0 (`endeEntf`, `dannForever`, `ewigWeiter`, the `leave`,
    `dannLeer`) reach a machine where thread 0 has finished its start
    function at `return` -- with `ensures false`. `StartEndeG` fails: the
    goal theorem cannot certify this program, while the per-budget lemma at
    `0` did (`probeD_bei0_zertifiziert true`). -/
theorem fwP_ende_verletzt : ∃ M : RufMaschineG zD,
    RufErreichbarG (fvP true) zO 1 (RufStartG (fvP true) zSp zInit) M ∧ ¬ StartEndeG (fvP true) M := by
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := fvP true) (O := zO) (passes := 1) (fvStart0 true)
    (fvSchleife true) (.ret .keine List.Perm.nil) .nil rfl rfl
  obtain ⟨M2, s2, hZ2⟩ := w_dannForever (P := fvP true) (O := zO) (passes := 1) hZ1.1 () .wahr
    (.cons (.leave rfl) .nil) .nil (.ende (.ret .keine List.Perm.nil)) .nil rfl
  obtain ⟨M3, s3, hZ3⟩ := w_ewigWeiter (P := fvP true) (O := zO) (passes := 1) hZ2.1 () 0 .wahr
    (.cons (.leave rfl) .nil) (.dann .nil (.ende (.ret .keine List.Perm.nil))) .nil rfl rfl
    (fun _ h => nomatch h)
  obtain ⟨M4, s4, hZ4⟩ := w_abbEwig (P := fvP true) (O := zO) (passes := 1) hZ3.1 true () 0 .wahr
    (.cons (.leave rfl) .nil) (.dann .nil (.ende (.ret .keine List.Perm.nil))) .nil .nil rfl
    (fun _ h => nomatch h)
  obtain ⟨M5, s5, hZ5⟩ := w_dannLeer (P := fvP true) (O := zO) (passes := 1) hZ4.1
    (.ende (.ret .keine List.Perm.nil)) .nil rfl
  refine ⟨M5, .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _
    (.schritt _ _ _ .start s1) s2) s3) s4) s5, fun h => ?_⟩
  have h0 := h 0
  rw [hZ5.1] at h0
  have := (h0 rfl false [] [] .nil (.ende (.ret .keine List.Perm.nil)) .keine rfl
    ⟨List.Perm.nil, Or.inl rfl⟩).1
  simp [EnsAmRueck, fvP, eval, wahr?] at this

/-! ## 5. Inhabitation: a `forever` loop that meets the obligation at EVERY budget

`ewP`: `lP` of `ZielOrtGanzZeuge.lean` with `forever () invariant
konto[0] <= 100 { leave }` in place of the `traverse` -- the invariant reads
the shared table. At budget `0` every body stops at the assumption; at
every budget `n + 1` the invariant holds, the loop is left, and the body
returns. The obligation is PROVED at every budget, the flagship
(`ziel_ort_sperre_ende`, over every budget) certifies the program, and on a
machine of budget `1` reached in two steps thread 0 stands at the
`forever` head with a pass left: the invariant holds there BY THE THEOREM,
and G takes the pass (`ewigWeiter`). -/

/-- An end block that starts with `forever a invariant inv { leave }`,
    `inv` true everywhere, continues with its rest at every budget `n + 1`. -/
theorem execEnd_ewig_leave {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (O : Orakel D) (n : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (a : D.Annahme)
    (inv : Expr D Γ Λ .bool) (rest : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hinv : ∀ (σ₀ σ : World D) (ρ : Env D Γ), wahr? (eval σ₀ inv σ ρ) = true) :
    execEnd O (n + 1) R (.cons (.forever a inv (.cons (.leave rfl) .nil)) rest) σ ρ =
      execEnd O (n + 1) R rest (σ.lese Λ inv.orte) ρ := by
  simp [execEnd, execStmt, foreverLauf, hinv, execBlock]

def ewSchleife {V : Vertrag zD} : Stmt zD V false [] zL zL :=
  .forever () lInv (.cons (.leave rfl) .nil)

def ewRumpfEin : Endblock zD (vertragVon zD zEin) false [] zL := .cons ewSchleife (.ret .keine (by rfl))

def ewRumpfLies : Endblock zD (vertragVon zD zLies) false [] zL :=
  .cons ewSchleife (.ret (.wert zHundert) (by rfl))

def ewRumpfWrap : Endblock zD (vertragVon zD zWrap) false [] zL := .cons ewSchleife (.ret .keine (by rfl))

/-- **The `forever` program**: the three lock holders run the loop and
    return, `haupt` returns; every contract `true`. -/
def ewP : Programm zD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf
    | .ein => ewRumpfEin
    | .lies => ewRumpfLies
    | .wrap => ewRumpfWrap
    | .haupt => lRumpfHaupt

theorem ewP_ohneLocks (f : zD.Fn) : (ewP.rumpf f).ohneLocks = true := by cases f <;> rfl

/-- **Every body of `ewP`, at every budget**, either stops at the loop's
    assumption (budget `0`) or returns. -/
theorem ewP_lauf (O' : Orakel zD) (R : ∀ f : zD.Fn, World zD → Env zD (zD.params f) → RufAusgang f)
    (n : Nat) (f : zD.Fn) (σ : World zD) (ρ : Env zD (zD.params f)) :
    execEnd (V := vertragVon zD f) O' n R (ewP.rumpf f) σ ρ = .hardware (.fortschritt ()) ∨
      ∃ σ' v, execEnd (V := vertragVon zD f) O' n R (ewP.rumpf f) σ ρ = .zurueck σ' v := by
  cases f with
  | haupt => exact Or.inr ⟨_, _, rfl⟩
  | ein =>
      cases n with
      | zero => exact Or.inl rfl
      | succ n =>
          have e : execEnd (V := vertragVon zD zEin) O' (n + 1) R (ewP.rumpf zEin) σ ρ =
              execEnd O' (n + 1) R (.ret .keine (by rfl)) (σ.lese zL (lInv (Γ := [])).orte) ρ :=
            execEnd_ewig_leave O' n R () lInv _ σ ρ (fun _ _ _ => lInv_wahr _ _ _)
          exact Or.inr ⟨_, _, e.trans rfl⟩
  | lies =>
      cases n with
      | zero => exact Or.inl rfl
      | succ n =>
          have e : execEnd (V := vertragVon zD zLies) O' (n + 1) R (ewP.rumpf zLies) σ ρ =
              execEnd O' (n + 1) R (.ret (.wert zHundert) (by rfl)) (σ.lese zL (lInv (Γ := [])).orte) ρ :=
            execEnd_ewig_leave O' n R () lInv _ σ ρ (fun _ _ _ => lInv_wahr _ _ _)
          exact Or.inr ⟨_, _, e.trans rfl⟩
  | wrap =>
      cases n with
      | zero => exact Or.inl rfl
      | succ n =>
          have e : execEnd (V := vertragVon zD zWrap) O' (n + 1) R (ewP.rumpf zWrap) σ ρ =
              execEnd O' (n + 1) R (.ret .keine (by rfl)) (σ.lese zL (lInv (Γ := [])).orte) ρ :=
            execEnd_ewig_leave O' n R () lInv _ σ ρ (fun _ _ _ => lInv_wahr _ _ _)
          exact Or.inr ⟨_, _, e.trans rfl⟩

/-- **The obligation of `ewP` at EVERY budget**, for every lock-invariant
    family (the bodies take no lock): no `logik` outcome -- the invariant
    holds at every pass -- and the (true) contracts. -/
theorem ewP_koerper (S : SperrInv zD) : ∀ (passes : Nat) (f : zD.Fn),
    KoerperGutS ewP passes (axWahr zD) S f := by
  intro n f
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun _ _ _ => rfl, fun g h => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e h => ?_⟩ <;>
    rw [Endblock.execH_ohne S O' U n _ _ (ewP_ohneLocks f)] at h
  · rcases ewP_lauf O' (torRuf ewP R) n f σ ρ with hl | ⟨σ', v, hl⟩ <;> rw [hl] at h <;> cases h
  · rcases ewP_lauf O' R n f σ ρ with hl | ⟨σ', v, hl⟩ <;> rw [hl] at h <;> cases h

theorem ewP_fragmentG : programmImFragmentG ewP zFs = true := by decide

theorem ewP_fussS : fussSperreB ewP (SperrInv.leer zD) zFs = true := by decide

theorem ewP_start : StartGut ewP zSp lInit := by
  intro t
  by_cases ht : t = 0
  · subst ht; rfl
  · simp only [lInit]; rw [if_neg ht]; rfl

/-- **`ewP` is certified by the budget-quantified flagship.** -/
theorem ewP_zertifiziert : ∀ (passes : Nat) (M : RufMaschineG zD),
    RufErreichbarG ewP zO passes (RufStartG ewP zSp lInit) M →
      ((VertragAmOrtG ewP M ∧ SperrInvG (SperrInv.leer zD) M ∧ KeinLogikHaltG zO passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG ewP zO passes M t M') ∧
      InvAmOrtG ewP M) ∧ StartEndeG ewP M :=
  ziel_ort_sperre_ende ewP zO (axWahr zD) (SperrInv.leer zD) zFs zSp lInit zE0 zO_gut zO_lokal
    (axVertragO_wahr zO) axEnsLokal_wahr sperrInvOk_leer zFs_voll ewP_fragmentG ewP_fussS
    (ewP_koerper _) ewP_start (fun _ => rfl) lInit_exklusiv (fun _ => invGutS_leer rfl)

/-- **WITNESS: the loop check is reached at budget `1`, and it passes BY
    THE THEOREM.** Two steps of thread 0 (`endeEntf`, `dannForever`) reach
    a machine of budget `1` whose head stands at the `forever` head with one
    pass left; the flagship gives the invariant at the machine world there,
    and that is exactly the premise with which G takes the pass. -/
theorem ziel_ort_ewig_zeuge :
    ∃ M2 : RufMaschineG zD, RufErreichbarG ewP zO 1 (RufStartG ewP zSp lInit) M2 ∧
      (∃ (spur : List (Ereignis zD)) (log : List (RufEreignisF zD)),
        M2.faeden 0 = ⟨[], ⟨zWrap, .nil, zSp.welt [], ⟨false, [], zL, .nil,
          .ewig () 1 lInv (.cons (.leave rfl) .nil) (.dann .nil (.ende (.ret .keine (by rfl))))⟩⟩,
          spur, log⟩) ∧
      wahr? (eval ((M2.weltVon 0).lese zL (lInv (Γ := [])).orte) lInv
        ((M2.weltVon 0).lese zL (lInv (Γ := [])).orte) .nil) = true ∧
      ∃ M3 : RufMaschineG zD, RufSchrittG ewP zO 1 M2 0 M3 := by
  have h00 : (RufStartG ewP zSp lInit).faeden 0 = ⟨[], ⟨zWrap, .nil, zSp.welt [],
      ⟨false, [], zL, .nil, .ende ewRumpfWrap⟩⟩, startSpur zWrap,
      [RufEreignisF.eintritt zWrap .nil (zSp.welt [])]⟩ := rfl
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := ewP) (O := zO) (passes := 1) h00 ewSchleife
    (.ret .keine (by rfl)) .nil rfl rfl
  obtain ⟨M2, s2, hZ2⟩ := w_dannForever (P := ewP) (O := zO) (passes := 1) hZ1.1 () lInv
    (.cons (.leave rfl) .nil) .nil (.ende (.ret .keine (by rfl))) .nil rfl
  have hr2 : RufErreichbarG ewP zO 1 (RufStartG ewP zSp lInit) M2 :=
    .schritt _ _ _ (.schritt _ _ _ .start s1) s2
  have h0 := (ewP_zertifiziert 1 M2 hr2).1.1.2.2.1 0
  unfold PrueftG at h0
  rw [hZ2.1] at h0
  have hw := h0.2.1 _ _ _ _ _ _ _ _ _ rfl
  have hoff : offen (M2.faeden 0).spur = [()] := by
    rw [hZ2.spur, offen_weltVon, hZ1.spur]
    rfl
  obtain ⟨M3, s3, _⟩ := w_ewigWeiter (P := ewP) (O := zO) (passes := 1) hZ2.1 () 0 lInv
    (.cons (.leave rfl) .nil) (.dann .nil (.ende (.ret .keine (by rfl)))) .nil rfl
    (by rw [hZ2.welt] at hw ⊢; exact hw) (hgL (by rw [← hZ2.spur]; exact hoff)).heldIn
  refine ⟨M2, hr2, ⟨_, _, hZ2.1⟩, ?_, M3, s3⟩
  rw [hZ2.welt]
  exact lInv_wahr _ _ _

#print axioms Gabbro.Grammatik.fvP_koerper0
#print axioms Gabbro.Grammatik.probeD_bei0_zertifiziert
#print axioms Gabbro.Grammatik.probeD_nicht
#print axioms Gabbro.Grammatik.probeD_nicht_leer
#print axioms Gabbro.Grammatik.fwP_nicht
#print axioms Gabbro.Grammatik.probeD_halt
#print axioms Gabbro.Grammatik.fwP_ende_verletzt
#print axioms Gabbro.Grammatik.ewP_koerper
#print axioms Gabbro.Grammatik.ewP_zertifiziert
#print axioms Gabbro.Grammatik.ziel_ort_ewig_zeuge

end Gabbro.Grammatik
