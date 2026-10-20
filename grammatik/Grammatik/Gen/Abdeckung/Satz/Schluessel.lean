/-
  File:      Grammatik/Gen/Abdeckung/Satz/Schluessel.lean
  Subject:   THE SUMMARY DECIDES THE ATOMS (part 1 of T1). A program `P` with its bodies replaced by bodies of the same
             summary (`Rumpf.schluessel`, `KoerperOrte.lean`), `P.mitRumpf r'`, has the same value of every atom the
             cells read: lock takes, indirect calls, calls, reachability, the fragment test, answers, registers and the
             footprint. `SchluesselZellen.lean` puts them together into the cells.
-/
import Grammatik.Gen.Abdeckung.Satz.KoerperOrte
import Grammatik.Gen.Abdeckung.Satz.MerkmalUnd

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

variable {D : Deklaration} [Aufz D] [Zahlen]

set_option linter.unusedSectionVars false

/-- The program with other bodies. -/
def _root_.Gabbro.Grammatik.Programm.mitRumpf (P : Programm D) (r : ∀ f, Rumpf D f) : Programm D := { P with rumpf := r }

/-- Two bodies with the same summary. -/
def GleicherSchluessel {f : D.Fn} (b' b : Rumpf D f) : Prop := b'.schluessel = b.schluessel

theorem map_gleich {α β : Type} {l : List α} {f g : α → β} (h : l.map f = l.map g) (hl : ∀ a, a ∈ l) (a : α) :
    f a = g a :=
  (List.map_inj_left.1 h) a (hl a)

section Teile

variable {f : D.Fn} {b' b : Rumpf D f} (h : GleicherSchluessel b' b)
include h

theorem gs_ruf (g : D.Fn) : mE (rufNur g) b' = mE (rufNur g) b := by
  have := map_gleich (congrArg (·.rufe) h) Aufz.fn_mem g
  simpa using this

theorem gs_ind (g : D.Fn) :
    mE ⟨fun _ => true, fun n => !(decide (n = D.sig g)), fun _ => true⟩ b' =
      mE ⟨fun _ => true, fun n => !(decide (n = D.sig g)), fun _ => true⟩ b := by
  have := map_gleich (congrArg (·.ind) h) Aufz.fn_mem g
  simpa using this

theorem gs_sperre (L : D.Lock) :
    mE ⟨fun _ => true, fun _ => true, fun L' => !(decide (L' = L))⟩ b' =
      mE ⟨fun _ => true, fun _ => true, fun L' => !(decide (L' = L))⟩ b := by
  have := map_gleich (congrArg (·.sperren) h) Aufz.lock_mem L
  simpa using this

theorem gs_gOk : b'.gOk (fun _ => true) (fun _ => true) = b.gOk (fun _ => true) (fun _ => true) :=
  congrArg (·.gok) h

theorem gs_ants (x : D.Ax ⊕ D.Reg) : x ∈ b'.ants ↔ x ∈ b.ants := by
  rcases x with a | r
  · have := map_gleich (congrArg (·.axAntw) h) Aufz.ax_mem a
    simpa using this
  · have := map_gleich (congrArg (·.regAntw) h) Aufz.reg_mem r
    simpa using this

theorem gs_regs (r : D.Reg) : r ∈ b'.regs ↔ r ∈ b.regs := by
  have := map_gleich (congrArg (·.regs) h) Aufz.reg_mem r
  simpa using this

theorem gs_koerper (c : D.Tab ⊕ D.Glob) : c ∈ koerperE b' ↔ c ∈ koerperE b := by
  have hm : ∀ c, c ∈ ((Aufz.tab (D := D)).map Sum.inl ++ (Aufz.glob (D := D)).map Sum.inr) := fun
    | .inl t => List.mem_append_left _ (List.mem_map.2 ⟨t, Aufz.tab_mem t, rfl⟩)
    | .inr g => List.mem_append_right _ (List.mem_map.2 ⟨g, Aufz.glob_mem g, rfl⟩)
  have := map_gleich (congrArg (·.orte) h) hm c
  rw [← istIn_iff, ← istIn_iff, this]

end Teile

/-! ## The atoms of a program with other bodies of the same summary -/

theorem ruf_zerlegt (g : D.Fn) :
    (⟨fun h => !(decide (h = g)), fun n => !(decide (n = D.sig g)), fun _ => true⟩ : Merkmal D) =
      (rufNur g).und ⟨fun _ => true, fun n => !(decide (n = D.sig g)), fun _ => true⟩ :=
  Merkmal.gleich (fun _ => by simp [rufNur]) (fun _ => by simp [rufNur]) (fun _ => by simp [rufNur])


section Atome

variable (P : Programm D) (r : ∀ f, Rumpf D f) (h : ∀ f, GleicherSchluessel (r f) (P.rumpf f))
include h

theorem gs_nimmtB (f : D.Fn) (L : D.Lock) : nimmtB (P.mitRumpf r) f L = nimmtB P f L := by
  simp only [nimmtB, Programm.mitRumpf]
  rw [gs_sperre (h f)]

theorem gs_indB (f g : D.Fn) : indB (P.mitRumpf r) f (D.sig g) = indB P f (D.sig g) := by
  simp only [indB, Programm.mitRumpf]
  rw [gs_ind (h f) g]

theorem gs_ruftB (f g : D.Fn) : ruftB (P.mitRumpf r) f g = ruftB P f g := by
  simp only [ruftB, Programm.mitRumpf]
  rw [ruf_zerlegt, mE_und, mE_und, gs_ruf (h f), gs_ind (h f)]

theorem gs_erreichB (fs : List D.Fn) (w : D.Fn) (n : Nat) : erreichB (P.mitRumpf r) fs w n = erreichB P fs w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext g
    simp only [erreichB, erreichSchritt, ih, gs_ruftB P r h]

theorem gs_reachB (fs : List D.Fn) (w f : D.Fn) : reachB (P.mitRumpf r) fs w f = reachB P fs w f := by
  simp only [reachB, gs_erreichB P r h]

theorem gs_endblockOrteP (f : D.Fn) (x : D.Tab ⊕ D.Glob) :
    x ∈ endblockOrteP (P.mitRumpf r) ((P.mitRumpf r).rumpf f) ↔ x ∈ endblockOrteP P (P.rumpf f) := by
  rw [endblockOrteP_iff, endblockOrteP_iff]
  simp only [Programm.mitRumpf, Gerufen, vOrte, gs_koerper (h f), gs_ruf (h f)]

theorem gs_fussOrte (f : D.Fn) (x : D.Tab ⊕ D.Glob) : x ∈ fussOrte (P.mitRumpf r) f ↔ x ∈ fussOrte P f := by
  simp only [fussOrte, List.mem_append]
  rw [gs_endblockOrteP P r h]
  rfl

theorem gs_fussOrteG (f : D.Fn) (x : D.Tab ⊕ D.Glob) : x ∈ fussOrteG (P.mitRumpf r) f ↔ x ∈ fussOrteG P f := by
  simp only [fussOrteG, List.mem_append, List.mem_flatMap, gs_fussOrte P r h]
  simp only [Programm.mitRumpf, gs_regs (h f)]

theorem gs_istIn_fuss (f : D.Fn) (c : D.Tab ⊕ D.Glob) :
    istIn (fussOrteG (P.mitRumpf r) f) c = istIn (fussOrteG P f) c := by
  cases h1 : istIn (fussOrteG P f) c
  · cases h2 : istIn (fussOrteG (P.mitRumpf r) f) c
    · rfl
    · rw [istIn_iff, gs_fussOrteG P r h] at h2
      rw [← istIn_iff] at h2
      rw [h2] at h1
      cases h1
  · rw [istIn_iff, ← gs_fussOrteG P r h, ← istIn_iff] at h1
    exact h1

end Atome

end Gabbro.Grammatik.Gen
