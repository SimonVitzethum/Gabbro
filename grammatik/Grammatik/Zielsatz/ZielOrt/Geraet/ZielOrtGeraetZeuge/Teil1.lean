module
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetZeuge.Teil1Basis
import all Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetZeuge.Teil1Basis

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraet
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollZeuge
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtZeuge

@[expose] public section



namespace Gabbro.Grammatik
/-- The device carrier is in the reader's widened footprint (and not in the
    footprint of `ziel_ort_voll`: `leser` never reads `geraet` itself). -/
theorem geLeser_fuss : fussOrteG geP geLeser = [.inl .geraet, .inl .geraet] ∧
    fussOrte geP geLeser = [] := ⟨rfl, rfl⟩

/-! ## 2. Oracle, start, and the user obligations -/

/-- The oracle: the register answers the device's state `geraet[0]`. -/
def geO : Orakel geD where
  wirkt := fun a => nomatch a
  regLies := fun _ σ => (σ.slots GeTab.geraet 0 ()).n
  regSchreib := fun _ _ => ()
  sichtbar := fun g => nomatch g

theorem geO_gut : GutO geO := fun a => nomatch a

/-- **The oracle is register-local**: it reads the device carrier only. -/
theorem geO_lokal : RegLokal geO :=
  ⟨fun _ σ σ' h => by
    show (σ.slots GeTab.geraet 0 ()).n = (σ'.slots GeTab.geraet 0 ()).n
    rw [h.1 GeTab.geraet List.mem_cons_self], fun g => nomatch g⟩

/-- ... and it is not memory-independent: two worlds, two answers. -/
theorem geO_liest_speicher : ∃ σ σ' : World geD, geO.regLies () σ ≠ geO.regLies () σ' :=
  ⟨⟨fun _ _ _ => ⟨0, by decide, by decide⟩, (fun g => nomatch g), []⟩,
   ⟨fun _ _ _ => ⟨1, by decide, by decide⟩, (fun g => nomatch g), []⟩, by
    show (0 : Int) ≠ 1
    decide⟩

def geSp : Speicher geD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- Thread 0 starts in `haupt`, thread 1 in `schreiber`, every other thread
    in `ruhe`. -/
def geInit : Faden → Σ f : geD.Fn, Env geD (geD.params f) :=
  fun t => if t = 0 then ⟨geHaupt, .nil⟩ else if t = 1 then ⟨geSchreiber, .nil⟩
    else ⟨geRuhe, .nil⟩

theorem geP_start : StartGut geP geSp geInit := by
  intro t
  unfold geInit
  by_cases h0 : t = 0
  · rw [if_pos h0]; rfl
  · rw [if_neg h0]
    by_cases h1 : t = 1
    · rw [if_pos h1]; rfl
    · rw [if_neg h1]; rfl

theorem geInit_haelt (t : Faden) :
    geD.haelt (geInit t).1 = (if t = 0 then [GeLock.lg] else if t = 1 then [GeLock.lt] else []) := by
  unfold geInit
  by_cases h0 : t = 0
  · rw [if_pos h0, if_pos h0]; rfl
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : t = 1
    · rw [if_pos h1, if_pos h1]; rfl
    · rw [if_neg h1, if_neg h1]; rfl

theorem geInit_exklusiv : StartExklusiv (D := geD) geInit := by
  intro t u htu L ht hu
  rw [geInit_haelt] at ht hu
  by_cases h0 : t = 0
  · rw [if_pos h0] at ht
    have hu0 : u ≠ 0 := fun e => htu (h0.trans e.symm)
    rw [if_neg hu0] at hu
    by_cases hu1 : u = 1
    · rw [if_pos hu1] at hu
      have e := (List.mem_singleton.mp ht).symm.trans (List.mem_singleton.mp hu)
      cases e
    · rw [if_neg hu1] at hu
      exact absurd hu List.not_mem_nil
  · rw [if_neg h0] at ht
    by_cases h1 : t = 1
    · rw [if_pos h1] at ht
      have hu1 : u ≠ 1 := fun e => htu (h1.trans e.symm)
      by_cases hu0 : u = 0
      · rw [if_pos hu0] at hu
        have e := (List.mem_singleton.mp ht).symm.trans (List.mem_singleton.mp hu)
        cases e
      · rw [if_neg hu0, if_neg hu1] at hu
        exact absurd hu List.not_mem_nil
    · rw [if_neg h1] at ht
      exact absurd ht List.not_mem_nil

/-- A write to `notiz` leaves the device carrier alone. -/
theorem geNotiz_geraet (σ : World geD) (Λ : List (Res geD)) (k : Int)
    (v : Wert geD (geD.typ GeTab.notiz ())) :
    GleichAuf (geD.rtraeger ()) (σ.schreibSlot GeTab.notiz Λ k () v) σ := by
  refine ⟨fun t ht => ?_, fun g => nomatch g⟩
  have e : t = GeTab.geraet := by
    have := List.mem_singleton.mp ht
    cases this
    rfl
  subst e
  funext k' f'
  simp only [World.schreibSlot, World.merke, World.storeSlot, List.cons_append, List.nil_append, reduceCtorEq,
  ↓reduceDIte]

/-- **What `leser`'s body does for every register-local oracle**: a return
    of `true`, or a hardware outcome. The reader's own write between the
    two reads changes the sequential world; locality gives the same answer. -/
theorem geLeser_lauf (O' : Orakel geD) (hRL : RegLokal O') (passes : Nat)
    (R : ∀ f : geD.Fn, World geD → Env geD (geD.params f) → RufAusgang f) (σ : World geD)
    (ρ : Env geD (geD.params geLeser)) :
    (∃ σ', execEnd O' passes R (geP.rumpf geLeser) σ ρ = .zurueck σ' true) ∨
      ∃ e, execEnd O' passes R (geP.rumpf geLeser) σ ρ = .hardware e := by
  show (∃ σ', execEnd O' passes R geRumpfLeser σ ρ = .zurueck σ' true) ∨
    ∃ e, execEnd O' passes R geRumpfLeser σ ρ = .hardware e
  simp only [geRumpfLeser, geLesBlock, geNotiz, execEnd, execStmt, execBlock]
  generalize hσ1 : σ.lese geLg (Expr.tru : Expr geD [] geLg .bool).orte = σ1
  simp only [eval, wahr?, if_true]
  cases hv : einpassen O'.zeiger (geD.rtyp ()) (O'.regLies () (σ1.fragt (.inr (.inl ())))) with
  | none =>
      right
      exact ⟨_, rfl⟩
  | some v =>
      left
      have hz : geD.rzusage () v = true := rfl
      simp only [hz, if_true]
      generalize hσ3 : ((σ1.fragt (Sum.inr (Sum.inl (() : geD.Reg)))).lese geLg _).schreibSlot GeTab.notiz geLg _ () _ = σ3
      have hloc : O'.regLies () (σ3.fragt (.inr (.inl ()))) = O'.regLies () (σ1.fragt (.inr (.inl ()))) := by
        rw [← hσ3]
        exact hRL.1 () _ _ (geNotiz_geraet ((σ1.fragt (Sum.inr (Sum.inl (() : geD.Reg)))).lese geLg _) geLg _ _)
      rw [hloc, hv]
      simp only [hz, if_true, Ausgang.schrumpf, evalErg, eval]
      exact ⟨_, congrArg (EndAusgang.zurueck _) (decide_eq_true rfl)⟩

/-- The gate of a `requires true` callee lets every call through. -/
theorem geTor (R : ∀ f : geD.Fn, World geD → Env geD (geD.params f) → RufAusgang f) (g : geD.Fn)
    (σ : World geD) (ρ : Env geD (geD.params g)) : torRuf geP R g σ ρ = R g σ ρ := if_pos rfl

theorem geP_koerper_leser : KoerperGutG geP 0 geLeser := by
  intro O' _ hRL R _ _ σ ρ _
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · rcases geLeser_lauf O' hRL 0 R σ ρ with ⟨σ'', h⟩ | ⟨e, h⟩
    · rw [h] at hrun
      cases hrun
      rfl
    · rw [h] at hrun
      cases hrun
  · rcases geLeser_lauf O' hRL 0 (torRuf geP R) σ ρ with ⟨σ'', h⟩ | ⟨e, h⟩
    · rw [h] at hrun
      cases hrun
    · rw [h] at hrun
      cases hrun

theorem geP_koerper_haupt : KoerperGutG geP 0 geHaupt := by
  intro O' _ _ R _ hOV σ ρ _
  refine ⟨fun _ _ _ => rfl, fun g hrun => ?_⟩
  have hr : geP.rumpf geHaupt = geRumpfHaupt := rfl
  rw [hr] at hrun
  rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, _, h1⟩
  · simp only [execStmt, geTor] at h1
    split at h1
    · cases h1
    · rename_i r _
      exact nomatch r
    · rename_i e hR
      cases h1
      exact hOV _ _ _ _ hR g rfl
    · cases h1
  · simp only [execEnd] at h1
    cases h1

theorem geP_koerper_schreiber : KoerperGutG geP 0 geSchreiber := by
  intro O' _ _ R _ _ σ ρ _
  refine ⟨fun _ _ _ => rfl, fun g hrun => ?_⟩
  have hr : geP.rumpf geSchreiber = geRumpfSchreiber := rfl
  rw [hr] at hrun
  simp only [geRumpfSchreiber, execEnd, execStmt] at hrun
  cases hrun

theorem geP_koerper_ruhe : KoerperGutG geP 0 geRuhe := by
  intro O' _ _ R _ _ σ ρ _
  refine ⟨fun _ _ _ => rfl, fun g hrun => ?_⟩
  have hr : geP.rumpf geRuhe = geRumpfRuhe := rfl
  rw [hr] at hrun
  simp only [geRumpfRuhe, execEnd] at hrun
  cases hrun

theorem geP_koerper : ∀ f, KoerperGutG geP 0 f := by
  intro f
  cases f
  · exact geP_koerper_haupt
  · exact geP_koerper_leser
  · exact geP_koerper_schreiber
  · exact geP_koerper_ruhe

/-- An event of the declaration (a release of `lg`). -/
def geE0 : Ereignis geD := .gibt GeLock.lg

/-- **All premises of `ziel_ort_geraet` hold jointly on `geP`.** -/
theorem geP_vertragAmOrt : ∀ M : RufMaschineG geD,
    RufErreichbarG geP geO 0 (RufStartG geP geSp geInit) M → VertragAmOrtG geP M :=
  ziel_ort_geraet geP geO 0 geFs geSp geInit geE0 geO_gut geO_lokal geFs_voll geP_fragment
    geP_fuss geP_koerper geP_start geInit_exklusiv

/-! ## 3. The run -/

def geZ0 : RufFadenG geD :=
  ⟨[], ⟨geHaupt, .nil, geSp.welt [], ⟨false, [], geLg, .nil, .ende geRumpfHaupt⟩⟩,
    startSpur geHaupt, [RufEreignisF.eintritt geHaupt .nil (geSp.welt [])]⟩

def geZ1 : RufFadenG geD :=
  ⟨[], ⟨geSchreiber, .nil, geSp.welt [], ⟨false, [], geLt, .nil, .ende geRumpfSchreiber⟩⟩,
    startSpur geSchreiber, [RufEreignisF.eintritt geSchreiber .nil (geSp.welt [])]⟩

theorem geM0_faden0 : (RufStartG geP geSp geInit).faeden 0 = geZ0 := by rfl

theorem geM0_faden1 : (RufStartG geP geSp geInit).faeden 1 = geZ1 := by rfl

theorem geHgLg {s : List (Ereignis geD)} (h : offen s = [GeLock.lg]) :
    HeldGenau geLg (offen s) := by
  rw [h]
  intro L
  cases L
  · exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩
  · exact ⟨fun h => absurd (List.mem_singleton.mp h) geHeld_ne,
      fun h => absurd (List.mem_singleton.mp h) geLock_ne⟩

end Gabbro.Grammatik
