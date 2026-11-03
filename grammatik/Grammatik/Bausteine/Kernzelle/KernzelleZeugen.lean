module

public import Grammatik.Bausteine.Kernzelle.Zeuge
public import Grammatik.Bausteine.Kernzelle.SperrProtokoll
public import Grammatik.Bausteine.Kernzelle.ZulassungMitRuhe
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

@[expose] public section

namespace Gabbro.Grammatik.Kernzelle

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

/-! Witnesses reuse the admitted two-cell, two-lock unsigned `or` fixture.
The empty-list theorems already state their own empty witnesses. -/

private theorem admitted : akkuZulaessig zAP zAFs zA :=
  akkuProgramm_zeuge.1.1 zA (by simp)

instance : NeZero zA.kernZahl := ⟨by decide +kernel⟩

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
    TraegerSchreibt (D := zAD.mitRuhe) none (.inr (zA.zellen 0)) = false :=
  traegerSchreibt_mitRuhe_ruhe zAP _

theorem akkuZulaessig_mitRuhe_zeuge :
    akkuZulaessig zAP.mitRuhe (fsRuhe zAFs) (AccumulatorDecl.mitRuhe zA) :=
  akkuZulaessig_mitRuhe zAP zAFs_voll closed admitted

theorem accumulatorAdmission_mitRuhe_zeuge :
    AccumulatorAdmission zAP.mitRuhe (fsRuhe zAFs)
      ([zA].map AccumulatorDecl.mitRuhe) :=
  accumulatorAdmission_mitRuhe zAP zAFs_voll closed akkuProgramm_zeuge.1

@[expose] public def startUnit : Einheit zAD where
  P := zAP
  S := ⟨fun _ => [], fun _ _ => true⟩
  Q := axWahr zAD
  starts := [⟨zAQ, .nil⟩]
  sp0 := {
    slots := fun t => nomatch t
    globs := fun _ => ⟨0, by decide, by decide⟩ }
  akku := [zA]

theorem akkuStartB_sound_zeuge : AkkuStart startUnit [zA] :=
  akkuStartB_sound (by decide +kernel)

theorem akkuStartB_vollst_zeuge : akkuStartB startUnit [zA] = true :=
  akkuStartB_vollst akkuProgramm_zeuge.1 akkuStartB_sound_zeuge

end Gabbro.Grammatik.Kernzelle
