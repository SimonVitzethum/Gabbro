module

public import Grammatik.Speichermodell.Maschine.DRF
public import Grammatik.Speichermodell.Atomar.Atomar.Teil2

@[expose] public section

namespace Gabbro.Grammatik
open Speichermodell
variable {D : Deklaration}
section Rennen
variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **Race freedom on every GA run from the start, for every non-atomic carrier**: two accesses
    by different threads, one a write, are ordered through a guard lock. Guarded carriers: the
    guard is held at both accesses (`zugriff_haeltA` on the presented steps), then
    `sperre_ordnetGA`. Unguarded non-atomic carriers are write-separated over the call graphs
    (`hsep`), so no such pair exists. -/
theorem rennfreiGA {fs : List D.Fn} (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hex : StartExklusiv init) (K : Faden → D.Fn → Bool) (hAbg : ∀ t, AbgK P fs (K t))
    (hWurzel : ∀ t, K t (init t).1 = true)
    (hsep : ∀ c, (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c → SchreibGetrenntK P K c)
    (ms : Nat → RufMaschineG D) (ts : Nat → Faden) (n : Nat)
    (hl : LaufGA P O passes (RufStartG P sp init) ms ts n)
    (i j : Nat) (c : D.Tab ⊕ D.Glob) (hij : i < j) (hjn : j < n) (hfg : ts i ≠ ts j)
    (hzi : ZugriffG (ms i) (ms (i + 1)) (ts i) c) (hzj : ZugriffG (ms j) (ms (j + 1)) (ts j) c)
    (hw : SchreibG (ms i) (ms (i + 1)) (ts i) c ∨ SchreibG (ms j) (ms (j + 1)) (ts j) c)
    (hA : ¬ AtomarAusgenommen c) : ∃ L, Bewacht c L ∧ GeordnetG ms ts L i j := by
  -- what one step of the run tells about an access
  have schritt : ∀ k, k < n → ∀ (Lk : D.Lock), Bewacht c Lk →
      ZugriffG (ms k) (ms (k + 1)) (ts k) c →
      Lk ∈ offen ((ms k).faeden (ts k)).spur ∧ Lk ∈ offen ((ms (k + 1)).faeden (ts k)).spur := by
    intro k hk Lk hB hz
    obtain ⟨σ, M'', hs, hfa, hZ, _, _⟩ := schrittGA_zerlegen (hl.2 k hk)
    have hr' := laufGA_erreichbar hl (k + 1) (by omega)
    have hSp' : SpurInv M'' := by
      have := gaInv_spur hO sp init hr'
      intro t; rw [← hfa]; exact this t
    have := zugriff_haeltA hO hs hSp' hB (hZ c hz)
    exact ⟨this.1, by rw [hfa]; exact this.2⟩
  have graph : ∀ k, k < n →
      (ZugriffG (ms k) (ms (k + 1)) (ts k) c → ∃ g, K (ts k) g = true ∧
        (c ∈ fussOrteG P g ∨ TraegerSchreibt g c = true)) ∧
      (SchreibG (ms k) (ms (k + 1)) (ts k) c → ∃ g, K (ts k) g = true ∧
        TraegerSchreibt g c = true) := by
    intro k hk
    obtain ⟨σ, M'', hs, _, hZ, hS, _⟩ := schrittGA_zerlegen (hl.2 k hk)
    have hr := laufGA_erreichbar hl k (by omega)
    have hOrte : OrteInvG P ((mitSpeicher (ms k) σ).faeden (ts k)) := gaInv_orte sp init hr (ts k)
    have hInv := gaInv_merk (P := P) (O := O) (passes := passes) sp init (fun t f => K t f = true)
      (fun t _ => rufM fs (K t)) (fun t => merkAbg_rufM hvoll (hAbg t)) hWurzel hr
    have hK : K (ts k) ((mitSpeicher (ms k) σ).faeden (ts k)).kopf.f = true :=
      (hInv (ts k) _ List.mem_cons_self).1
    have hb := schritt_zugriffeA hO hOrte hs c
    exact ⟨fun hz => ⟨_, hK, hb.1 (hZ c hz)⟩, fun hz => ⟨_, hK, hb.2 (hS c hz)⟩⟩
  by_cases hB : ∃ L, Bewacht c L
  · obtain ⟨L, hL⟩ := hB
    have hi := schritt i (by omega) L hL hzi
    have hj := schritt j hjn L hL hzj
    exact ⟨L, hL, sperre_ordnetGA sp init hO hex hl i j hij hjn hfg L hi.2 hj.1⟩
  · have hsc := hsep c (fun L h => hB ⟨L, h⟩) hA
    have gi := graph i (by omega)
    have gj := graph j hjn
    exfalso
    rcases hw with hw | hw
    · obtain ⟨g, hg, hgw⟩ := gi.2 hw
      obtain ⟨h, hh, hhz⟩ := gj.1 hzj
      obtain ⟨h1, h2⟩ := hsc _ _ hfg g hg hgw h hh
      rcases hhz with hhz | hhz
      · exact h2 hhz
      · rw [h1] at hhz; cases hhz
    · obtain ⟨g, hg, hgw⟩ := gj.2 hw
      obtain ⟨h, hh, hhz⟩ := gi.1 hzi
      obtain ⟨h1, h2⟩ := hsc _ _ (Ne.symm hfg) g hg hgw h hh
      rcases hhz with hhz | hhz
      · exact h2 hhz
      · rw [h1] at hhz; cases hhz

end Rennen

#print axioms Gabbro.Grammatik.fussSA_of_fussS
#print axioms Gabbro.Grammatik.ga_aus_g
#print axioms Gabbro.Grammatik.gaInv_exklusiv
#print axioms Gabbro.Grammatik.schritt_sichtInvA
#print axioms Gabbro.Grammatik.schwach_ist_gA
#print axioms Gabbro.Grammatik.plain_liest_neueste
#print axioms Gabbro.Grammatik.ga_aus_w
#print axioms Gabbro.Grammatik.w_spur_exklusiv
#print axioms Gabbro.Grammatik.schwach_ist_gA_vor
#print axioms Gabbro.Grammatik.schrittW_freigabe
#print axioms Gabbro.Grammatik.hb_uebergabe
#print axioms Gabbro.Grammatik.sperre_ordnetGA
#print axioms Gabbro.Grammatik.rennfreiGA

end Gabbro.Grammatik
