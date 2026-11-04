/-
  File:      Grammatik/ZielOrtGrund.lean
  Subject:   A START FUNCTION ENDING IN A REASON (verdict
             `messung/URTEIL-MUSE-2026-09-14.md` §5) -- the probe, and what
             the flagship now says about every finished thread.

  `StartEndeG` checks a start function's `ensures` and owed invariants at a
  VALUE return (`RetKopf`). A start function ending in a reason
  (`retGrund`) owed nothing: probe `grP` on `vD` -- `ferr` (one reason,
  `ensures false`) is every thread's start function and its body is
  `return R` -- met every premise of the flagship as it stood, and every
  thread was finished at the START machine with nothing checked
  (`grP_alt_zertifiziert`, `grP_fertig`).

  The decision (`ZielOrtStart.lean` §2a): start functions declare no
  reasons (`StartOhneGrund`, a decidable premise of the flagship). Then
  every finished thread has an ordinary or saved VALUE completion, so
  `StartEndeG` checks EVERY completion of a start function; the probe fails
  the premise (`grP_nicht`) and the conclusion conjunct `KeinStartGrundG`
  is false on its start machine (`grP_verletzt`) -- no premises whatever
  could make the flagship certify it.
-/
module
public import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollZeuge
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 2. The probe: a start function that ends in a reason -/

def grRumpfHaupt : Endblock vD (vertragVon vD vHaupt) false [] [] := .ret .empty List.Perm.nil

def grRumpfMid : Endblock vD (vertragVon vD vMid) false [] [] := .ret .empty List.Perm.nil

/-- **The probe**: `ferr` (`ensures false`, one reason) is every thread's
    start function and its body is `return R`; `haupt` and `mid` return. -/
def grP : Programm vD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures
    | .ferr => .fls
    | .haupt => .tru
    | .mid => .tru
  rumpf
    | .haupt => grRumpfHaupt
    | .mid => grRumpfMid
    | .ferr => vRumpfErr

/-- Every thread starts in `ferr`. -/
def grInit : Faden → Σ f : vD.Fn, Env vD (vD.params f) := fun _ => ⟨vErr, .nil⟩

theorem grP_ohneLocks (f : vD.Fn) : (grP.rumpf f).ohneLocks = true := by cases f <;> rfl

/-- The obligation holds at every budget, for every family: `haupt` and
    `mid` return under `ensures true`, `ferr` never returns a value. -/
theorem grP_koerper (S : SperrInv vD) : ∀ (passes : Nat) (f : vD.Fn),
    KoerperGutS grP passes (axWahr vD) S f := by
  intro n f
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v h => ?_, fun g h => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e h => ?_⟩ <;>
    rw [Endblock.execH_ohne S O' U n _ _ (grP_ohneLocks f)] at h <;>
    cases f <;> first | rfl | cases h

theorem grP_fragmentG : programmImFragmentG grP vFs = true := by decide

theorem grP_fussS : fussSperreB grP (SperrInv.leer vD) vFs = true := by decide

theorem vO_lokal : RegLokal vO := ⟨(fun r _ _ _ => nomatch r), (fun g _ _ _ => nomatch g)⟩

theorem grInit_exklusiv : StartExklusiv (D := vD) grInit := fun _ _ _ _ h => nomatch h

/-- **Every premise of the flagship as it stood before §2a holds on the
    probe**, at every budget -- so its conclusion, `StartEndeG` included,
    holds on every reachable machine. -/
theorem grP_alt_zertifiziert : ∀ (passes : Nat) (M : RufMaschineG vD),
    RufErreichbarG grP vO passes (RufStartG grP vSp grInit) M →
      ((VertragAmOrtG grP M ∧ SperrInvG (SperrInv.leer vD) M ∧ KeinLogikHaltG vO passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG grP vO passes M t M') ∧
      InvAmOrtG grP M) ∧ StartEndeG grP M :=
  fun passes => ziel_ort_sperre_ende_bei grP vO passes (axWahr vD) (SperrInv.leer vD) vFs vSp grInit
    vO_gut vO_lokal (axVertragO_wahr vO) axEnsLokal_wahr sperrInvOk_leer vFs_voll
    grP_fragmentG grP_fussS (grP_koerper _ passes) (fun _ => rfl) (fun _ => rfl) grInit_exklusiv
    (invGutS_leer rfl)

/-- **The finding**: at the START machine every thread is finished
    (`FertigG`) -- in `ferr`, whose `ensures` is `false` -- and stands at a
    reason return, where `StartEndeG` checks nothing. -/
theorem grP_fertig (t : Faden) :
    FertigG (RufStartG grP vSp grInit) t ∧
      GrundKopf ((RufStartG grP vSp grInit).faeden t).kopf.rest.2.2.2.2 ∧
      grP.ensures vErr = .fls :=
  ⟨⟨rfl, rfl⟩, ⟨vR0, Or.inl ⟨List.Perm.nil, Or.inl rfl⟩⟩, rfl⟩

/-- **The probe fails the new premise**: its start function declares a
    reason. -/
theorem grP_nicht : ¬ StartOhneGrund (D := vD) grInit := fun h => absurd (h 0) (by decide)

/-- **And the new conclusion conjunct is false on the probe's start
    machine**: no premises whatever let the flagship certify it. -/
theorem grP_verletzt : ¬ KeinStartGrundG (RufStartG grP vSp grInit) :=
  fun h => h 0 rfl _ _ _ _ _ rfl ⟨vR0, Or.inl ⟨List.Perm.nil, Or.inl rfl⟩⟩

#print axioms Gabbro.Grammatik.grP_koerper
#print axioms Gabbro.Grammatik.grP_alt_zertifiziert
#print axioms Gabbro.Grammatik.grP_fertig
#print axioms Gabbro.Grammatik.grP_nicht
#print axioms Gabbro.Grammatik.grP_verletzt

end Gabbro.Grammatik
