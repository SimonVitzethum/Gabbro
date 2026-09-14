/-
  File:      Grammatik/ZielOrtAxZeuge.lean
  Subject:   WITNESS FOR `ziel_ort_voll_ax` -- the axiom-calling body with the
             result-dependent contract `result == tab[0]` (`AxiomVertrag.lean`),
             every premise jointly, a reached run that fires the axiom and
             logs the return of `zaehle`, and the contract checked there.

  The oracle `axO` implements `inc` as "increment the slot, capped at 3, and
  answer the new value", records its write (`GutO`), and meets `inc`'s
  declared ensures `result == tab[0]` (`AxVertragO axQ axO`). The contract
  is NOT a `KoerperGutV` contract (`inc_ensures_nicht_V`), so this program
  is outside `ziel_ort_voll`'s obligation and inside `ziel_ort_voll_ax`'s.
-/
import Grammatik.ZielOrtAx

namespace Gabbro.Grammatik

/-! ## 1. Program facts, oracle, start -/

def axFs : List axD.Fn := [axHaupt, axZaehle, axRuhe]

theorem axFs_voll : ∀ g : axD.Fn, g ∈ axFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem axP_fragment : programmImFragmentV axP axFs = true := by decide

theorem axP_fuss : fussOrtB axP axFs = true := by decide

/-- The new value of the slot: incremented, capped at 3. -/
def axNeu (σ : World axD) : Wert axD (.int 0 3) :=
  ⟨min ((σ.slots () 0 ()).n + 1) 3,
   Int.le_min.mpr ⟨by have := (σ.slots () 0 ()).lo_le; omega, by decide⟩,
   Int.min_le_right _ _⟩

/-- The oracle: `inc` increments the slot (capped) and answers the new
    value, recording its write. -/
def axO : Orakel axD where
  wirkt := fun _ σ _ =>
    ({ slots := fun _ _ _ => axNeu σ
       globs := fun g => nomatch g
       spur := axiomSpur [()] [] () [Res.held ()] σ.haelt ++ σ.spur }, (axNeu σ).n)
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem axO_gut : GutO axO := by
  intro a σ ρ
  cases a
  have hW : axO.wirkt () σ ρ =
      ({ slots := fun _ _ _ => axNeu σ
         globs := fun g => nomatch g
         spur := axiomSpur [()] [] () [Res.held ()] σ.haelt ++ σ.spur }, (axNeu σ).n) := rfl
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro t ht
      cases ht
    · intro g
      exact nomatch g
  · rw [hW]
    show offen (axiomSpur [()] [] () [Res.held ()] σ.haelt ++ σ.spur) = offen σ.spur
    exact offen_nurZugriff _ _ (fun e he => by
      simp only [axiomSpur, List.mem_append, List.mem_map, List.mem_filter] at he
      rcases he with ⟨t, _, rfl⟩ | ⟨g, _, _⟩
      · rfl
      · exact nomatch g)
  · intro hgt _
    refine ⟨[()], [], [Res.held ()], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t _
      cases t
      exact List.Mem.head _
    · intro g
      exact nomatch g
    · intro t _
      cases t
      exact axDarf
    · intro g
      exact nomatch g
    · intro m st hm
      simp at hm
    · intro L hL
      have eL : L = () := rfl
      rw [eL]
      exact hgt () rfl () (List.Mem.head _)
    · rw [hW]

/-- **The machine's `inc` meets its declared ensures**: the answer is the
    new value of the slot. -/
theorem axO_vertrag : AxVertragO axQ axO := by
  intro a σ ρ v hv
  have hv' : einpassen (.int 0 3) (axNeu σ).n = some v := hv
  simp only [einpassen, dif_pos (show 0 ≤ (axNeu σ).n ∧ (axNeu σ).n ≤ 3 from
    ⟨(axNeu σ).lo_le, (axNeu σ).le_hi⟩)] at hv'
  cases hv'
  show decide ((axNeu σ).n = (axNeu σ).n) = true
  exact decide_eq_true rfl

def axSp : Speicher axD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- Thread 0 starts in `haupt` (holding `L`), every other thread in `ruhe`. -/
def axInit : Faden → Σ f : axD.Fn, Env axD (axD.params f) :=
  fun t => if t = 0 then ⟨axHaupt, .nil⟩ else ⟨axRuhe, .nil⟩

theorem axP_start : StartGut axP axSp axInit := by
  intro t
  unfold axInit
  by_cases h0 : t = 0
  · rw [if_pos h0]; rfl
  · rw [if_neg h0]; rfl

theorem axInit_exklusiv : StartExklusiv (D := axD) axInit := by
  intro t u htu L ht hu
  unfold axInit at ht hu
  by_cases h0 : t = 0
  · have hu0 : u ≠ 0 := fun e => htu (h0.trans e.symm)
    rw [if_neg hu0] at hu
    exact absurd hu List.not_mem_nil
  · rw [if_neg h0] at ht
    exact absurd ht List.not_mem_nil

def axE0 : Ereignis axD := .gibt ()

/-- **All premises of `ziel_ort_voll_ax` hold jointly on `axP`.** -/
theorem axP_vertragAmOrt : ∀ M : RufMaschineG axD,
    RufErreichbarG axP axO 0 (RufStartG axP axSp axInit) M → VertragAmOrtG axP M :=
  ziel_ort_voll_ax axP axO 0 axQ axFs axSp axInit axE0 axO_gut axO_vertrag axQ_lokal axFs_voll
    axP_fragment axP_fuss axP_koerperA axP_start axInit_exklusiv

/-! ## 2. The run -/

/-- The `dannBindAxiom` step, as the other `w_*` lemmas. -/
theorem w_bindAxiom {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
    {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
    (hw : ∀ t, D.aschreibt a t = true → (vertragVon D z.kopf.f).schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → (vertragVon D z.kopf.f).gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Block D (vertragVon D z.kopf.f) l (τ :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.bindAxiom a args he hw hg hd hgd rest) k⟩)
    (σ₂ : World D) (v : ErgVal D (D.aerg a))
    (hax : axiomAntwort O a ((M.weltVon f).lese Λ args.orte)
      (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ) =
      (σ₂, some v))
    (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ (M.weltVon f).spur)
    (hΛ : HeldGenau Λ (offen z.spur)) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (.cons (ergWert he v) ρ)
        (.dann rest (.schrumpf k)) σ₂ := by
  subst hz
  exact ⟨_, RufSchrittG.dannBindAxiom M f l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ hhead _ rfl
    σ₂ v hax neu hneu hΛ.heldIn, zustandG_neu rfl rfl⟩

theorem axHgL {s : List (Ereignis axD)} (h : offen s = [()]) : HeldGenau axL (offen s) := by
  rw [h]
  intro L
  cases L
  exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩

theorem axHoff {M : RufMaschineG axD} {f : Faden} {z : RufFadenG axD} {x : List Unit}
    (e : M.faeden f = z) (ho : offen (M.faeden f).spur = x) : offen z.spur = x := by
  rw [← e]; exact ho

/-- The value `1`, the new slot value after one `inc` from `0`. -/
def axEins : Wert axD (.int 0 3) := ⟨1, by decide, by decide⟩

/-- **The run.** Thread 0: `haupt` calls `zaehle` (1), `zaehle` unfolds its
    `if` (2, 3), calls the axiom `inc` (4: memory `0 -> 1`, answer `1`),
    returns it (5: the return of `zaehle` with result `1` is logged). -/
theorem axLauf : ∃ M : RufMaschineG axD,
    RufErreichbarG axP axO 0 (RufStartG axP axSp axInit) M ∧
    (M.speicher.slots () 0 ()).n = 1 ∧
    ∃ (rho : Env axD (axD.params axZaehle)) (v : ErgVal axD (axD.erg axZaehle))
      (s0 s1 : World axD),
      (v : Zahl 0 3).n = 1 ∧ RufEreignisF.rueck axZaehle rho v s0 s1 ∈ (M.faeden 0).log := by
  have h00 : (RufStartG axP axSp axInit).faeden 0 = ⟨[], ⟨axHaupt, .nil, axSp.welt [],
      ⟨false, [], axL, .nil, .ende axRumpfHaupt⟩⟩, startSpur axHaupt,
      [RufEreignisF.eintritt axHaupt .nil (axSp.welt [])]⟩ := rfl
  have hoff0 : offen ((RufStartG axP axSp axInit).faeden 0).spur = [()] := rfl
  obtain ⟨M1, s1, hZ1⟩ := w_rufEnde (P := axP) (O := axO) (passes := 0) h00 axZaehle .nil
    axHpZaehle rfl axRetH .nil rfl (axHgL hoff0).heldIn
  have hoff1 : offen (M1.faeden 0).spur = [()] := by
    rw [hZ1.spur, (Erw.lese _ _ _).offen]; exact hoff0
  have e1 := hZ1.1
  try dsimp only at e1
  obtain ⟨M2, s2, hZ2⟩ := w_endeEntf (P := axP) (O := axO) (passes := 0) e1 axIte axRetNull .nil
    rfl rfl
  have hoff2 : offen (M2.faeden 0).spur = [()] := by rw [hZ2.spur]; exact hoff1
  have e2 := hZ2.1
  try dsimp only at e2
  obtain ⟨M3, s3, hZ3⟩ := w_iteWahr (P := axP) (O := axO) (passes := 0) e2 .wahr axIncBlock .nil
    .nil (.ende axRetNull) .nil rfl rfl (axHgL (axHoff e2 hoff2)).heldIn
  have hoff3 : offen (M3.faeden 0).spur = [()] := by
    rw [hZ3.spur, (Erw.lese _ _ _).offen]; exact hoff2
  have e3 := hZ3.1
  try dsimp only at e3
  have hsp3 : M3.speicher = axSp := hZ3.2.trans (hZ2.2.trans hZ1.2)
  obtain ⟨M4, s4, hZ4⟩ := w_bindAxiom (P := axP) (O := axO) (passes := 0) e3 axInc .nil rfl
    (fun _ _ => rfl) (fun e => nomatch e) (fun _ _ => axDarf) (fun e => nomatch e)
    (.cons (.ret (.wert (.var .hier)) (List.Perm.refl _)) .nil) (.dann .nil (.ende axRetNull)) .nil
    rfl _ axEins (by
      show (_, einpassen (.int 0 3) (axNeu ((M3.weltVon 0).lese axL [])).n) = _
      have hn : (axNeu ((M3.weltVon 0).lese axL [])).n = 1 := by
        show min ((M3.speicher.slots () 0 ()).n + 1) 3 = 1
        rw [hsp3]
        rfl
      rw [hn]
      rfl)
    (axiomSpur [()] [] () [Res.held ()] ((M3.weltVon 0).lese axL []).haelt) rfl
    (axHgL (axHoff e3 hoff3))
  have hoff4 : offen (M4.faeden 0).spur = [()] := by
    rw [hZ4.spur]
    exact (offen_nurZugriff _ _ (fun e he => by
      simp only [axiomSpur, List.mem_append, List.mem_map, List.mem_filter] at he
      rcases he with ⟨t, _, rfl⟩ | ⟨g, _, _⟩
      · rfl
      · exact nomatch g)).trans (((Erw.lese _ _ _).offen).trans hoff3)
  have e4 := hZ4.1
  try dsimp only at e4
  obtain ⟨M5, s5, hG5⟩ := w_dannRetP (P := axP) (O := axO) (passes := 0) e4 _ _ rfl
    (PopArt.wie rfl) _ (List.Perm.refl _) .nil _ _ rfl (axHgL (axHoff e4 hoff4)).heldIn
  have hr5 : RufErreichbarG axP axO 0 (RufStartG axP axSp axInit) M5 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1)
      s2) s3) s4) s5
  refine ⟨M5, hr5, ?_, _, _, _, _, rfl, by rw [hG5.1]; exact List.mem_cons_self⟩
  rw [hG5.2]
  show (M4.speicher.slots () 0 ()).n = 1
  rw [hZ4.2]
  show min ((M3.speicher.slots () 0 ()).n + 1) 3 = 1
  rw [hsp3]
  rfl

/-! ## 3. The witness -/

/-- **`ziel_ort_voll_ax_zeuge`.** On `axP` -- `zaehle` calls the axiom
    `inc` and returns its answer, with the result-dependent contract
    `result == tab[0]` over the axiom's declared write -- every premise of
    `ziel_ort_voll_ax` holds jointly: `GutO`, the machine's `inc` meets its
    declared ensures, the declared ensures is local, the complete member
    list, the fragment, the footprint check, the strengthened obligation
    `KoerperGutA` for every function, the start obligation, the exclusive
    start. The contract is NOT a `KoerperGutV` contract. On a machine
    reached by five steps (the axiom moved memory `0 -> 1`), the return of
    `zaehle` with result `1` is logged, and its `ensures` holds there. -/
theorem ziel_ort_voll_ax_zeuge :
    GutO axO ∧ AxVertragO axQ axO ∧ AxEnsLokal axQ ∧ (∀ g : axD.Fn, g ∈ axFs) ∧
    programmImFragmentV axP axFs = true ∧ fussOrtB axP axFs = true ∧
    (∀ f : axD.Fn, KoerperGutA axP 0 axQ f) ∧ StartGut axP axSp axInit ∧
    StartExklusiv (D := axD) axInit ∧ axP.ensures axZaehle = axEnsInc ∧
    ¬ KoerperGutV axP 0 axZaehle ∧
    ∃ M : RufMaschineG axD, RufErreichbarG axP axO 0 (RufStartG axP axSp axInit) M ∧
      (axSp.slots () 0 ()).n = 0 ∧ (M.speicher.slots () 0 ()).n = 1 ∧
      ∃ (rho : Env axD (axD.params axZaehle)) (v : ErgVal axD (axD.erg axZaehle))
        (s0 s1 : World axD),
        (v : Zahl 0 3).n = 1 ∧ RufEreignisF.rueck axZaehle rho v s0 s1 ∈ (M.faeden 0).log ∧
        EnsAmRueck axP axZaehle s0 s1 rho v ∧ VertragAmOrtG axP M := by
  obtain ⟨M, hr, hslot, rho, v, s0, s1, hv, hlog⟩ := axLauf
  have hV := axP_vertragAmOrt M hr
  exact ⟨axO_gut, axO_vertrag, axQ_lokal, axFs_voll, axP_fragment, axP_fuss, axP_koerperA,
    axP_start, axInit_exklusiv, rfl, inc_ensures_nicht_V, M, hr, rfl, hslot, rho, v, s0, s1, hv,
    hlog, (hV 0 _ hlog).2 axZaehle rho v s0 s1 rfl, hV⟩

/-! ## CUTS:

  What is proved: every premise of `ziel_ort_voll_ax` jointly on `axP`
  (`axP_vertragAmOrt`), with a contract that `KoerperGutV` refutes
  (`inc_ensures_nicht_V`); a five-step reached run that fires
  `dannBindAxiom` (memory `0 -> 1`) and `dannRet`, and the logged return of
  `zaehle` meets `result == tab[0]` (`ziel_ort_voll_ax_zeuge`).

  What is NOT covered: a declared ensures over the axiom's parameters or
  old world (see `ZielOrtAx.lean`); a second thread in this witness (the
  table is held by thread 0's signature lock for the whole run).
-/

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.axO_gut
#print axioms Gabbro.Grammatik.axO_vertrag
#print axioms Gabbro.Grammatik.axLauf
#print axioms Gabbro.Grammatik.ziel_ort_voll_ax_zeuge
