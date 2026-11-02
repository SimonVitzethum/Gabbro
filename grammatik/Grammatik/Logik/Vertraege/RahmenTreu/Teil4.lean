/- Part 4 of `RahmenTreu` (C11 scoped-return release: release-aware frame
   transport; pure move out of `Teil1.lean` to keep every file under 500 lines). -/
module

public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}

/-- Release then release is the same combined release (scopes concatenate). -/
theorem TreuRet.transRet {W G} {a b c : World D} (h1 : TreuRet W G a b)
    (h2 : TreuRet W G b c) : TreuRet W G a c := by
  obtain ⟨Ls1, hLs1⟩ := h1.2
  obtain ⟨Ls2, hLs2⟩ := h2.2
  exact ⟨h1.1.trans h2.1, ⟨Ls1 ++ Ls2, by rw [hLs2, hLs1, List.foldl_append]⟩⟩

/-- A releasing frame pulls through a sub-block: non-returns keep the release,
    returns concatenate it. -/
theorem TreuAusgang.vorRet {W G} {σ σ1 : World D} {o : Ausgang V l Γ}
    (h1 : TreuRet W G σ σ1) (h : TreuAusgang W G σ1 o) : TreuAusgang W G σ o := by
  intro σ' hs
  cases o with
  | ok _ _ => exact h1.transGut (h _ hs)
  | zurueck _ _ => exact h1.transRet (h _ hs)
  | why _ _ => exact h1.transRet (h _ hs)
  | leave _ _ _ => exact h1.transGut (h _ hs)
  | next _ _ _ => exact h1.transGut (h _ hs)
  | logik _ => cases hs
  | hardware _ => cases hs

theorem TreuEnd.vorRet {W G} {σ σ1 : World D} {o : EndAusgang V l Γ}
    (h1 : TreuRet W G σ σ1) (h : TreuEnd W G σ1 o) : TreuEnd W G σ o := by
  intro σ' hs
  cases o with
  | zurueck _ _ => exact h1.transRet (h _ hs)
  | why _ _ => exact h1.transRet (h _ hs)
  | leave _ _ _ => exact h1.transGut (h _ hs)
  | next _ _ _ => exact h1.transGut (h _ hs)
  | logik _ => cases hs
  | hardware _ => cases hs

/-- Every handler outcome keeps the frame (both `Treu` and `TreuRet` carry `Rahmen`). -/
theorem TreuR.rahmen (hR : TreuR R) {f : D.Fn} {σ : World D} {ρ : Env D (D.params f)}
    {σ' : World D} (h : (R f σ ρ).welt = some σ') :
    Rahmen (D.schreibt f) (D.gschreibt f) σ σ' := by
  have h2 := hR f σ ρ σ' h
  cases he : R f σ ρ with
  | ok _ _ => rw [he] at h2; exact h2.1
  | why _ _ => rw [he] at h2; exact h2.1
  | logik _ => simp only [RufAusgang.welt, reduceCtorEq] at h
  | hardware _ => simp only [RufAusgang.welt, reduceCtorEq] at h

end Gabbro.Grammatik
