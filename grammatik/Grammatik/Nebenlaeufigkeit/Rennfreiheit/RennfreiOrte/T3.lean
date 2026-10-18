/- Part 3 of 3 of `RennfreiOrte` (split by instrumente/teile/lean-teilen.py; the umbrella `RennfreiOrte.lean` imports all parts). -/
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiOrte.T2

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Lauf

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **A step's accesses, bounded by the acting function**: a read is on a
    footprint carrier of the acting frame's function; a write (event or
    memory change) is on a carrier that function may write. -/
theorem schritt_zugriffe (hO : GutO O) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) {M M' : RufMaschineG D} {f : Faden}
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M) (hs : RufSchrittG P O passes M f M')
    (c : D.Tab ⊕ D.Glob) :
    (ZugriffG M M' f c → c ∈ fussOrteG P (M.faeden f).kopf.f ∨
      TraegerSchreibt (M.faeden f).kopf.f c = true) ∧
    (SchreibG M M' f c → TraegerSchreibt (M.faeden f).kopf.f c = true) := by
  have hI := orteInvG_erreichbar sp init hr f _ List.mem_cons_self
  obtain ⟨X, hX, hok⟩ := schritt_ev hO hs hI
  have hmem : ¬ TraegerGleich M'.speicher M.speicher c →
      TraegerSchreibt (M.faeden f).kopf.f c = true := by
    intro hn
    cases hb : TraegerSchreibt (M.faeden f).kopf.f c
    · exact absurd (schritt_traeger hO hs c (Or.inr hb)) hn
    · rfl
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · rcases hz with ⟨w, hw⟩ | hm
    · have h := zugriffe_ev hX hok hw
      cases w
      · exact Or.inl (istIn_iff.mp (h.1 rfl))
      · exact Or.inr (h.2 rfl)
    · exact Or.inr (hmem hm)
  · rcases hz with hw | hm
    · exact (zugriffe_ev hX hok hw).2 rfl
    · exact hmem hm

/-- **Accesses stay in the call graph**: with closed per-thread call graphs
    `K` containing the start functions, every access of a step of thread
    `f` is a footprint read or a signature write of SOME function of `K f`,
    and every write is a signature write of some function of `K f`. -/
theorem zugriff_im_graph (hO : GutO O) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (K : Faden → D.Fn → Bool) (hAbg : ∀ t, AbgK P fs (K t))
    (hWurzel : ∀ t, K t (init t).1 = true) {M M' : RufMaschineG D} {f : Faden}
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M) (hs : RufSchrittG P O passes M f M')
    (c : D.Tab ⊕ D.Glob) :
    (ZugriffG M M' f c → ∃ g, K f g = true ∧
      (c ∈ fussOrteG P g ∨ TraegerSchreibt g c = true)) ∧
    (SchreibG M M' f c → ∃ g, K f g = true ∧ TraegerSchreibt g c = true) := by
  have hInv := merkInvG_erreichbar (O := O) (pa := passes) sp init (fun t g => K t g = true)
    (fun t _ => rufM fs (K t)) (fun t => merkAbg_rufM hvoll (hAbg t)) hWurzel hr
  have hK := (hInv f _ List.mem_cons_self).1
  obtain ⟨h1, h2⟩ := schritt_zugriffe hO sp init hr hs c
  exact ⟨fun hz => ⟨_, hK, h1 hz⟩, fun hz => ⟨_, hK, h2 hz⟩⟩

/-- **Write-separated over the call graphs**: if one thread's graph may
    write `c`, no OTHER thread's graph may write it or have it in a
    footprint. -/
def SchreibGetrenntK (P : Programm D) (K : Faden → D.Fn → Bool) (c : D.Tab ⊕ D.Glob) : Prop :=
  ∀ t u, t ≠ u → ∀ g, K t g = true → TraegerSchreibt g c = true →
    ∀ h, K u h = true → TraegerSchreibt h c = false ∧ c ∉ fussOrteG P h

/-- **No cross-thread pair with a write on a write-separated carrier.** On
    every run from the start, two accesses to `c` by different threads, one
    of them a write, do not exist when `c` is write-separated over closed
    call graphs that contain the start functions. -/
theorem rennfrei_ungeschuetzt (hO : GutO O) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (K : Faden → D.Fn → Bool) (hAbg : ∀ t, AbgK P fs (K t))
    (hWurzel : ∀ t, K t (init t).1 = true)
    (ms : Nat → RufMaschineG D) (ts : Nat → Faden) (n : Nat)
    (hl : LaufG P O passes (RufStartG P sp init) ms ts n) (i j : Nat) (hij : i < j)
    (hjn : j < n) (hfg : ts i ≠ ts j) (c : D.Tab ⊕ D.Glob) (hsep : SchreibGetrenntK P K c)
    (hzi : ZugriffG (ms i) (ms (i + 1)) (ts i) c) (hzj : ZugriffG (ms j) (ms (j + 1)) (ts j) c)
    (hw : SchreibG (ms i) (ms (i + 1)) (ts i) c ∨ SchreibG (ms j) (ms (j + 1)) (ts j) c) :
    False := by
  have gi := zugriff_im_graph hO hvoll sp init K hAbg hWurzel
    (laufG_erreichbar hl i (by omega)) (hl.2 i (by omega)) c
  have gj := zugriff_im_graph hO hvoll sp init K hAbg hWurzel
    (laufG_erreichbar hl j (by omega)) (hl.2 j (by omega)) c
  rcases hw with hw | hw
  · obtain ⟨g, hg, hgw⟩ := gi.2 hw
    obtain ⟨h, hh, hhz⟩ := gj.1 hzj
    obtain ⟨h1, h2⟩ := hsep _ _ hfg g hg hgw h hh
    rcases hhz with hhz | hhz
    · exact h2 hhz
    · rw [h1] at hhz; cases hhz
  · obtain ⟨g, hg, hgw⟩ := gj.2 hw
    obtain ⟨h, hh, hhz⟩ := gi.1 hzi
    obtain ⟨h1, h2⟩ := hsep _ _ (Ne.symm hfg) g hg hgw h hh
    rcases hhz with hhz | hhz
    · exact h2 hhz
    · rw [h1] at hhz; cases hhz

/-- **Race freedom for every carrier** (not atomic, not a publish payload):
    a cross-thread pair with a write on `c` is ordered through a guard lock
    of `c`. Guarded carriers: `rennfrei_g_voll`. Unguarded carriers: every
    such carrier is write-separated (`hsep`), so the pair does not exist
    (`rennfrei_ungeschuetzt`). -/
theorem rennfrei_alle (hO : GutO O) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hex : StartExklusiv init) (K : Faden → D.Fn → Bool) (hAbg : ∀ t, AbgK P fs (K t))
    (hWurzel : ∀ t, K t (init t).1 = true)
    (hsep : ∀ c, (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c → ¬ PaarungAusgenommen c →
      SchreibGetrenntK P K c) :
    ∀ (ms : Nat → RufMaschineG D) (ts : Nat → Faden) (n : Nat),
      LaufG P O passes (RufStartG P sp init) ms ts n →
      ∀ (i j : Nat) (c : D.Tab ⊕ D.Glob), i < j → j < n → ts i ≠ ts j →
        ZugriffG (ms i) (ms (i + 1)) (ts i) c → ZugriffG (ms j) (ms (j + 1)) (ts j) c →
        (SchreibG (ms i) (ms (i + 1)) (ts i) c ∨ SchreibG (ms j) (ms (j + 1)) (ts j) c) →
        ¬ AtomarAusgenommen c → ¬ PaarungAusgenommen c →
        ∃ L, Bewacht c L ∧ GeordnetG ms ts L i j := by
  intro ms ts n hl i j c hij hjn hfg hzi hzj hw hA hPa
  by_cases hB : ∃ L, Bewacht c L
  · obtain ⟨L, hL⟩ := hB
    exact ⟨L, hL, rennfrei_g_voll P O passes sp init hO hex ms ts n hl i j hij hjn hfg c L hL
      hzi hzj⟩
  · exact (rennfrei_ungeschuetzt hO hvoll sp init K hAbg hWurzel ms ts n hl i j hij hjn hfg c
      (hsep c (fun L hL => hB ⟨L, hL⟩) hA hPa) hzi hzj hw).elim

end Lauf

#print axioms Gabbro.Grammatik.schrittOrte
#print axioms Gabbro.Grammatik.orteInvG_erreichbar
#print axioms Gabbro.Grammatik.blatt_ev
#print axioms Gabbro.Grammatik.schritt_ev
#print axioms Gabbro.Grammatik.schritt_zugriffe
#print axioms Gabbro.Grammatik.zugriff_im_graph
#print axioms Gabbro.Grammatik.rennfrei_ungeschuetzt
#print axioms Gabbro.Grammatik.rennfrei_alle


end Gabbro.Grammatik
