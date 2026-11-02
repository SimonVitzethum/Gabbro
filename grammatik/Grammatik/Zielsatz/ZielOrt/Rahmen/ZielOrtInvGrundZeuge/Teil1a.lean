module

public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtInvGrund
public import Grammatik.Proben.InvZeuge
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtInvGrundZeuge.Teil1
@[expose] public section


namespace Gabbro.Grammatik
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
    (∃ σ1 r1, R igSetze (σ.lese igL []) .nil = .why σ1 r1 ∧
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
  | why σ1 r1 =>
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
    simp only [InvHaelt, World.lese, World.merke, World.schreibSlot, World.storeSlot, igIdx, igWert, List.map_append, List.append_assoc, eval, Zahl.weiter, dite_eq_ite, List.cons_append, List.nil_append, igP, igInv, Int.reduceEq, ↓reduceIte, ite_self]
    rfl
  · simp only [igErr, igH, igSchreib, execEndH, execStmtH, EndAusgang.schrumpf] at hrun
    cases hrun
    intro i _ _
    cases i
    simp only [InvHaelt, World.lese, World.merke, World.schreibSlot, World.storeSlot, igIdx, igWert, List.map_append, List.append_assoc, eval, Zahl.weiter, dite_eq_ite, List.cons_append, List.nil_append, igP, igInv, Int.reduceEq, ↓reduceIte, ite_self]
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
  simp only [InvHaelt, World.schreibSlot, World.merke, World.storeSlot, World.lese, igIdx, igWert, List.map_append, List.append_assoc, eval, Zahl.weiter, dite_eq_ite, List.cons_append, List.nil_append, igPgut, igP, igInv, Int.reduceEq, ↓reduceIte, ite_self]
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
  ziel_ort_sperre_invAlle igPgut igO 0 (axWahr igD) (SperrInv.leer igD) igFs igSp igInit
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
  ziel_ort_sperre_inv igPschlecht igO 0 (axWahr igD) (SperrInv.leer igD) igFs igSp igInit
    igO_gut igO_lokal (axVertragO_wahr igO) axEnsLokal_wahr sperrInvOk_leer igFs_voll
    igPschlecht_frag igPschlecht_fuss igPschlecht_koerper (igStart _) (fun _ => rfl)
    igInit_exklusiv igPschlecht_inv

/-- The identity environment move meets `HavocOk` of the empty family. -/
theorem ig_havoc : HavocOk (SperrInv.leer igD) (fun _ σ => σ) :=
  fun _ _ => ⟨rfl, fun c _ => traegerGleich_refl _ c, rfl⟩

end Gabbro.Grammatik
