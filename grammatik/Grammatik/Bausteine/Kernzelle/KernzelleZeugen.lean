module

public import Grammatik.Bausteine.Kernzelle.Zeuge
public import Grammatik.Bausteine.Kernzelle.SperrProtokoll
public import Grammatik.Bausteine.Kernzelle.ZulassungMitRuhe

@[expose] public section

namespace Gabbro.Grammatik.Kernzelle

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

/-! Witnesses reuse the admitted two-cell, two-lock unsigned `or` fixture.
The empty-list theorems already state their own empty witnesses. -/

private theorem admitted : akkuZulaessig zAP zAFs zA :=
  akkuProgramm_zeuge.1 zA (by simp)

theorem akkuNeutralBewohnt_zeuge :
    zA.lo ≤ neutralInt zA.op zA.lo zA.hi zA.breite ∧
    neutralInt zA.op zA.lo zA.hi zA.breite ≤ zA.hi :=
  akkuNeutralBewohnt zA_ok

theorem akkuZellenGetrennt_zeuge :
    (0 : Fin zA.kernZahl) = 0 :=
  akkuZellenGetrennt zA_ok (i := 0) (j := 0) rfl

theorem mitRuhe_kernZahl_zeuge : (AccumulatorDecl.mitRuhe zA).kernZahl = zA.kernZahl :=
  mitRuhe_kernZahl zA

theorem mitRuhe_zellen_zeuge : (AccumulatorDecl.mitRuhe zA).zellen = zA.zellen :=
  mitRuhe_zellen zA

theorem mitRuhe_sperren_zeuge : (AccumulatorDecl.mitRuhe zA).sperren = zA.sperren :=
  mitRuhe_sperren zA

theorem akkuZelleBewacht_zeuge : Bewacht (.inr (zA.zellen 0)) (zA.sperren 0) :=
  akkuZelleBewacht admitted 0

theorem akkuZellenBewacht_zeuge : ∃ L, Bewacht (.inr (zA.zellen 1)) L :=
  akkuZellenBewacht admitted 1

theorem akkuRennfreiAbgedeckt_zeuge : ∃ L, Bewacht (.inr (zA.zellen 0)) L :=
  akkuRennfreiAbgedeckt admitted 0

theorem akkuZellTyp_zeuge : zAD.gtyp (zA.zellen 1) = Ty.int zA.lo zA.hi :=
  akkuZellTyp zA_ok 1

theorem akkuEinzelB_iff_zeuge :
    akkuEinzelB zAP zAFs zATabs zAGlobs zAQs zA = true ↔
      (akkuZulaessig zAP zAFs zA ∧
        ∃ q ∈ zAQs, KernAbfrageVerbunden zAP zA q) :=
  akkuEinzelB_iff zAFs_voll zATabs_voll zAGlobs_voll

private theorem closed : ∀ w, AbgK zAP zAFs (reachB zAP zAFs w) := by
  intro w
  apply abgB_ok zAFs_voll
  cases w <;> decide

theorem traegerSchreibt_mitRuhe_ruhe_zeuge :
    TraegerSchreibt zAP.mitRuhe none (.inr (zA.zellen 0)) = false :=
  traegerSchreibt_mitRuhe_ruhe zAP _

theorem akkuZulaessig_mitRuhe_zeuge :
    akkuZulaessig zAP.mitRuhe (fsRuhe zAFs) (AccumulatorDecl.mitRuhe zA) :=
  akkuZulaessig_mitRuhe zAP zAFs_voll closed admitted

theorem accumulatorAdmission_mitRuhe_zeuge :
    AccumulatorAdmission zAP.mitRuhe (fsRuhe zAFs)
      ([zA].map AccumulatorDecl.mitRuhe) :=
  accumulatorAdmission_mitRuhe zAP zAFs_voll closed akkuProgramm_zeuge.1

private def startUnit : Einheit zAD where
  P := zAP
  S := ⟨fun _ => [], fun _ _ => true⟩
  Q := axWahr zAD
  starts := [⟨zAQ, .nil⟩]
  sp0 := {
    slots := fun t => nomatch t
    globs := fun _ => ⟨0, by decide, by decide⟩ }
  akku := [zA]

theorem akkuStartB_sound_zeuge : AkkuStart startUnit [zA] :=
  akkuStartB_sound (by decide)

theorem akkuStartB_vollst_zeuge : akkuStartB startUnit [zA] = true :=
  akkuStartB_vollst akkuProgramm_zeuge.1 akkuStartB_sound_zeuge

end Gabbro.Grammatik.Kernzelle
