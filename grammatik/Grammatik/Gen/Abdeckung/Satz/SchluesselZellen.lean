/-
  File:      Grammatik/Gen/Abdeckung/Satz/SchluesselZellen.lean
  Subject:   T1: BODIES OF THE SAME SUMMARY GIVE THE SAME CELLS. Replacing every body of a program by one with the same
             `Rumpf.schluessel` leaves the cells (`gs_alleZellen`), every component of `AkzeptiertX` (`gs_komp`) and so
             the model's Bool (`gs_akzeptiertX`) unchanged. This is what lets the generator keep one body per summary
             (`Spez.tabellenD`) without losing a cell.
-/
import Grammatik.Gen.Abdeckung.Satz.Schluessel
import Grammatik.Gen.Abdeckung.Satz.ZellenUnmoeglich

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

variable {D : Deklaration} [Aufz D] [Zahlen]

set_option linter.unusedSectionVars false

@[simp] theorem mitRumpf_rumpf (P : Programm D) (r : ∀ f, Rumpf D f) (f : D.Fn) : (P.mitRumpf r).rumpf f = r f := rfl
@[simp] theorem mitRumpf_unterbricht (P : Programm D) (r : ∀ f, Rumpf D f) :
    (P.mitRumpf r).unterbricht = P.unterbricht := rfl

theorem all_mem_gleich {α : Type} {l₁ l₂ : List α} (p : α → Bool) (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) :
    l₁.all p = l₂.all p := by
  cases h1 : l₂.all p
  · cases h2 : l₁.all p
    · rfl
    · rw [List.all_eq_true] at h2
      have : l₂.all p = true := List.all_eq_true.2 fun x hx => h2 x ((h x).2 hx)
      rw [this] at h1; cases h1
  · exact List.all_eq_true.2 fun x hx => (List.all_eq_true.1 h1) x ((h x).1 hx)

section

variable (P : Programm D) (r : ∀ f, Rumpf D f) (h : ∀ f, GleicherSchluessel (r f) (P.rumpf f))
  (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock) (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn)
include h

theorem gs_gOkP (f : D.Fn) :
    ((P.mitRumpf r).rumpf f).gOk (fun _ => true) (fun _ => true) = (P.rumpf f).gOk (fun _ => true) (fun _ => true) := by
  rw [mitRumpf_rumpf]; exact gs_gOk (h f)

theorem gs_antsP (f : D.Fn) (x : D.Ax ⊕ D.Reg) :
    decide (x ∈ ((P.mitRumpf r).rumpf f).ants) = decide (x ∈ (P.rumpf f).ants) := by
  rw [mitRumpf_rumpf]; exact decide_eq_decide.2 (gs_ants (h f) x)

theorem gs_regsP (f : D.Fn) (x : D.Reg) : x ∈ ((P.mitRumpf r).rumpf f).regs ↔ x ∈ (P.rumpf f).regs := by
  rw [mitRumpf_rumpf]; exact gs_regs (h f) x

theorem gs_getrenntW (c : D.Tab ⊕ D.Glob) : getrenntW (P.mitRumpf r) fs ws c = getrenntW P fs ws c := by
  simp only [getrenntW, gs_reachB P r h, gs_istIn_fuss P r h]

theorem gs_schreibGetrenntW (c : D.Tab ⊕ D.Glob) :
    schreibGetrenntW (P.mitRumpf r) fs ws c = schreibGetrenntW P fs ws c := by
  simp only [schreibGetrenntW, gs_reachB P r h, gs_istIn_fuss P r h]

theorem gs_getrenntZellen (c : D.Tab ⊕ D.Glob) :
    getrenntZellen (P.mitRumpf r) fs ws c = getrenntZellen P fs ws c := by
  simp only [getrenntZellen, gs_reachB P r h, gs_istIn_fuss P r h]

theorem gs_schreibGetrenntZellen (c : D.Tab ⊕ D.Glob) :
    schreibGetrenntZellen (P.mitRumpf r) fs ws c = schreibGetrenntZellen P fs ws c := by
  simp only [schreibGetrenntZellen, gs_reachB P r h, gs_istIn_fuss P r h]

theorem gs_geteiltVB (c : D.Tab ⊕ D.Glob) : geteiltVB (P.mitRumpf r) fs c = geteiltVB P fs c := rfl

theorem gs_geteiltZelle (c : D.Tab ⊕ D.Glob) : geteiltZelle (P.mitRumpf r) fs c = geteiltZelle P fs c := rfl

theorem gs_vertragsOrte (g : D.Fn) : vertragsOrte (P.mitRumpf r) g = vertragsOrte P g := rfl

/-- **The cells of each component are the same** (as sets: component 2 walks the footprint and the register list,
    whose order may differ). -/
theorem gs_zellen (c : Fin 10) (x : Zelle) :
    x ∈ zellen (P.mitRumpf r) S fs ls cs ws c ↔ x ∈ zellen P S fs ls cs ws c := by
  rcases c with ⟨n, hn⟩
  match n, hn with
  | 0, _ => simp only [zellen, gs_gOkP P r h, gs_indB P r h, gs_vertragsOrte P r h, gs_istIn_fuss P r h]
  | 1, _ => simp only [zellen, gs_reachB P r h, gs_ruftB P r h]
  | 2, _ =>
    simp only [zellen, List.mem_append, List.mem_flatMap, gs_getrenntW P r h, gs_getrenntZellen P r h,
      gs_geteiltVB P r h, gs_geteiltZelle P r h, gs_fussOrte P r h, gs_regsP P r h]
  | 3, _ => simp only [zellen, gs_nimmtB P r h]
  | 4, _ => simp only [zellen]
  | 5, _ => simp only [zellen]
  | 6, _ => simp only [zellen, gs_reachB P r h]
  | 7, _ => simp only [zellen, gs_schreibGetrenntW P r h, gs_schreibGetrenntZellen P r h]
  | 8, _ => simp only [zellen, gs_antsP P r h]
  | 9, _ => simp only [zellen, mitRumpf_unterbricht, gs_reachB P r h, gs_nimmtB P r h]
  | n + 10, hn => exact absurd hn (by omega)

/-- **T1: the same cells.** -/
theorem gs_alleZellen (x : Zelle) : x ∈ alleZellen (P.mitRumpf r) S fs ls cs ws ↔ x ∈ alleZellen P S fs ls cs ws := by
  simp only [mem_alleZellen]
  constructor
  · rintro ⟨c, hc⟩; exact ⟨c, (gs_zellen P r h S fs ls cs ws c x).1 hc⟩
  · rintro ⟨c, hc⟩; exact ⟨c, (gs_zellen P r h S fs ls cs ws c x).2 hc⟩

/-- **The same components** of the model's Bool. -/
theorem gs_komp (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    (c : Fin 10) : komp (P.mitRumpf r) S fs ls cs ws c = komp P S fs ls cs ws c := by
  rw [← urteil_komp (P.mitRumpf r) S fs ls cs ws hvoll hls hcs c, ← urteil_komp P S fs ls cs ws hvoll hls hcs c]
  exact all_mem_gleich _ (gs_zellen P r h S fs ls cs ws c)

/-- **The same verdict** of the model's Bool. -/
theorem gs_akzeptiertX (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) :
    AkzeptiertX (P.mitRumpf r) S fs ls cs ws = AkzeptiertX P S fs ls cs ws := by
  cases h1 : AkzeptiertX P S fs ls cs ws
  · cases h2 : AkzeptiertX (P.mitRumpf r) S fs ls cs ws
    · rfl
    · rw [akzeptiertX_iff] at h2
      have : AkzeptiertX P S fs ls cs ws = true := (akzeptiertX_iff _ _ _ _ _ _).2 fun c => by
        rw [← gs_komp P r h S fs ls cs ws hvoll hls hcs c]; exact h2 c
      rw [this] at h1; cases h1
  · exact (akzeptiertX_iff _ _ _ _ _ _).2 fun c => by
      rw [gs_komp P r h S fs ls cs ws hvoll hls hcs c]; exact (akzeptiertX_iff _ _ _ _ _ _).1 h1 c

end

end Gabbro.Grammatik.Gen
