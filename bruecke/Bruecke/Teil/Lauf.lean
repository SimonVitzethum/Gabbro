module
public import Bruecke.Teil.Realisierung
public import Bruecke.Kodierung.GlobSchreiben
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

/-- Only frames of carried targets are required by a carried Body execution. -/
def RahmenAlleC (u : UProg) (C : Fin u.fns.length → Prop) (ρB : Gabbro.Body.Env) : Prop :=
  ∀ n c, C c → fnSuch u n = some (fnAt u c) → Gabbro.Body.Frame ρB n (writesU (fnAt u c))

theorem reqAmEintritt_wahr_teil {P : Programm (declOf u)} (G : GesenktC u C P)
    (f : Fin u.fns.length) (hf : C f) (σ : World (declOf u))
    (ρ : Env (declOf u) ((declOf u).params f)) : ReqAmEintritt P f σ ρ := by
  unfold ReqAmEintritt
  rw [G.req f hf]
  rfl

theorem eintrag_gut_teil {P : Programm (declOf u)} (G : GesenktC u C P) (S : Getragen u C)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (hRR : RespektiertRahmen P R) (callee : Fin u.fns.length) (hc : C callee) (σr σ' : World (declOf u))
    (envA : Env (declOf u) ((declOf u).params callee)) (v : ErgVal (declOf u) ((declOf u).erg callee))
    (hR : R callee σr envA = .ok σ' v) (t : Gabbro.Body.State) (hWt : WGRel u σr t.world)
    (hLt : LRel (fnAt u callee) 0 envA t.local') (w : String) (ws : List String)
    (hw : (writesU (fnAt u callee)) = w :: ws) (n : String) (hn : fnSuch u n = some (fnAt u callee)) :
    EintragGut u ⟨n, t, antwort w σ' t (ergValOf ((declOf u).erg callee) v)⟩ := by
  intro gf hgf
  rw [hn] at hgf
  cases hgf
  constructor
  · intro _
    have hens := hRR.1 callee σr envA (reqAmEintritt_wahr_teil G callee hc σr envA) σ' v hR
    exact (post_iff_teil G callee hc (S.art callee hc) S.tab (S.frei callee hc) (S.olds callee hc) (S.post callee hc)
      (S.boolErg callee hc) S.boolTab σr σ' envA v t _ hWt hLt (wgrel_bump w (wgrel_enc u σ' t.world))).mpr hens
  · intro p hp
    have hgp : p ≠ geistOrt w := by
      intro e; subst e; apply hp; simp [geistOrt, Gabbro.Body.Place.carrier, hw]
    simp only [antwort, bump, Gabbro.Body.store, hgp, ↓reduceIte]
    cases p with
    | slot c k fld =>
      simp only [encG, enc]
      cases hsw : slotWert u σ' c k fld with
      | none => rfl
      | some val =>
        simp only [Option.getD_some]
        unfold slotWert at hsw
        split at hsw
        · rename_i t' ht'
          split at hsw
          · rename_i fh' hf'
            cases hsw
            rw [wrel_lies_k u hWt.1 c t' ht' fld fh' hf' k]
            congr 1
            have hfr := (hRR.2 callee σr envA σ' v hR).1.1 t'
            have hwf : (declOf u).schreibt callee t' = false := by
              show ((declOf u).signatur callee).schreibt t' = false
              rw [sigSchreibt_eq]
              unfold writesAt
              rw [show (tabAt u t').name = c from tabIdx_name _ _ _ ht']
              simp only [Gabbro.Body.Place.carrier] at hp
              simp only [List.any_eq_false, beq_iff_eq]
              intro x hx e
              subst e
              exact hp (List.mem_append_left _ hx)
            exact hfr hwf k fh'.idx
          · cases hsw
        · cases hsw
    | field c n => rfl
    | global n =>
      simp only [encG]
      cases hv : globWert u σ' n with
      | none => rfl
      | some v' =>
        simp only [Option.getD_some]
        have hglob : globWert u σ' n = globWert u σr n := by
          unfold globWert
          split
          · rfl
          · rename_i i hi
            have hn : (globAt u i).name = n := globIdx_name u.globs n i hi
            have hfalse : (declOf u).gschreibt callee i = false := by
              change ((declOf u).signatur callee).gschreibt i = false
              rw [sigGSchreibt_eq]
              unfold writesGAt
              rw [hn]
              simp only [List.any_eq_false, beq_iff_eq]
              intro x hx he
              subst x
              exact hp (List.mem_append_right _ hx)
            rw [(hRR.2 callee σr envA σ' v hR).1.2 i hfalse]
        exact (hWt.2 n v' (hglob.symm.trans hv)).symm

/-- A callee with neither table nor static writes preserves the whole represented world. -/
theorem wgrel_rahmen_leer (c : Fin u.fns.length) {σ σ' : World (declOf u)}
    {w : Gabbro.Body.World} (h : WGRel u σ w)
    (hf : Rahmen ((declOf u).schreibt c) ((declOf u).gschreibt c) σ σ')
    (hw : writesU (fnAt u c) = []) : WGRel u σ' w := by
  have ht : (fnAt u c).puts = [] := (List.append_eq_nil_iff.mp hw).1
  have hg : (fnAt u c).gputs = [] := (List.append_eq_nil_iff.mp hw).2
  apply wgrel_same u (h := h)
  · funext t k f
    apply hf.1 t
    refine (sigSchreibt_eq u c t).trans ?_
    simp only [writesAt, ht, List.any_nil]
  · funext g
    apply hf.2 g
    refine (sigGSchreibt_eq u c g).trans ?_
    simp only [writesGAt, hg, List.any_nil]

end Gabbro.Bruecke
