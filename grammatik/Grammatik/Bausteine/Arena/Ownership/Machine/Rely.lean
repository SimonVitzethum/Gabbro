import Grammatik.Bausteine.Arena.Ownership.Machine.Step
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtMehrfaden
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt.T2
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiOrte.T3
import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.T3
import Grammatik.Speichermodell.Atomar.Atomar

/-! **The rely, from the machine's own discipline.** A thread inside an
allocator form is about to write the free-list head or the counter. Its
next statement may write that word, so the word is guarded by a lock the
thread holds (and no other thread can hold), or it is unguarded and then,
by the write separation the checker demands of every unguarded non-atomic
carrier, no other thread's function may write it. Either way no step of
another thread changes it (`schritt_traeger`). -/

namespace Gabbro.Grammatik.ArenaOwnership.Machine

open Source Body

variable {D : Deklaration}

/-- What a residue about to write an allocator word says about that write. -/
theorem pendWord_spec {A : FreiForm D} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {r : GRest D V l Γ Λ} {g : D.Glob} (h : pendWord A r = some g) :
    (g = A.kopf ∨ g = A.zaehl) ∧ V.gschreibt g = true ∧ gdarf D g Λ := by
  unfold pendWord at h
  split at h
  · rename_i g' _ hw hL _ _
    split at h
    · rename_i hg; cases h; exact ⟨hg, hw, hL⟩
    · cases h
  · rename_i g' _ hw hL _ _
    split at h
    · rename_i hg; cases h; exact ⟨Or.inr hg, hw, hL⟩
    · cases h
  · cases h

/-- **The rely, from three facts about the threads**: static holdings are held, held locks are
    exclusive, and every running function lies in its thread's call graph. -/
theorem rely_core {P : Programm D} {A : FreiForm D} {O : Orakel D} {passes : Nat} (hO : GutO O)
    (K : Faden → D.Fn → Bool)
    (hsep : ∀ g, (g = A.kopf ∨ g = A.zaehl) → (∀ L, ¬ Bewacht (.inr g : D.Tab ⊕ D.Glob) L) →
      SchreibGetrenntK P K (.inr g))
    {M M' : RufMaschineG D} {u : Faden} (hHalt : ∀ t, HaeltInvG (M.faeden t)) (hExk : Exklusiv M)
    (hK : ∀ v, K v (M.faeden v).kopf.f = true) (hs : RufSchrittG P O passes M u M') :
    ∀ t, t ≠ u → ∀ g, pendWord A (M.faeden t).kopf.rest.2.2.2.2 = some g →
      M'.speicher.globs g = M.speicher.globs g := by
  intro t htu g hg
  obtain ⟨hgw, hw, hL⟩ := pendWord_spec hg
  by_cases hB : ∃ L, Bewacht (.inr g : D.Tab ⊕ D.Glob) L
  · obtain ⟨L, hBL⟩ := hB
    have hmem : Res.held L ∈ (M.faeden t).kopf.rest.2.2.1 := hL (Sum.inl L) hBL
    have hheld := (hHalt t).alle _ List.mem_cons_self L hmem
    exact schritt_traeger hO hs (.inr g) (Or.inl ⟨L, hBL, hExk t u htu L hheld⟩)
  · have hsg := hsep g hgw (fun L hL => hB ⟨L, hL⟩)
    exact schritt_traeger hO hs (.inr g) (Or.inr (hsg t u htu _ (hK t) hw _ (hK u)).1)

/-- **The rely holds on every reachable machine** whose start is lock-exclusive and whose unguarded
    allocator words are write-separated over the threads' call graphs. -/
theorem rely_of {P : Programm D} {A : FreiForm D} {O : Orakel D} {passes : Nat} (hO : GutO O)
    {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (K : Faden → D.Fn → Bool) (hAbg : ∀ t, AbgK P fs (K t))
    (hWurzel : ∀ t, K t (init t).1 = true) (hex : StartExklusiv init)
    (hsep : ∀ g, (g = A.kopf ∨ g = A.zaehl) → (∀ L, ¬ Bewacht (.inr g : D.Tab ⊕ D.Glob) L) →
      SchreibGetrenntK P K (.inr g))
    {M M' : RufMaschineG D} {u : Faden} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    (hs : RufSchrittG P O passes M u M') :
    ∀ t, t ≠ u → ∀ g, pendWord A (M.faeden t).kopf.rest.2.2.2.2 = some g →
      M'.speicher.globs g = M.speicher.globs g :=
  rely_core hO K hsep (rufG_haeltInv hO sp init hr) (exklusivG hO sp init hex hr)
    (fun v => ((merkInvG_erreichbar sp init (fun t g => K t g = true) (fun t _ => rufM fs (K t))
      (fun t => merkAbg_rufM hvoll (hAbg t)) hWurzel hr) v _ List.mem_cons_self).1) hs

end Gabbro.Grammatik.ArenaOwnership.Machine
