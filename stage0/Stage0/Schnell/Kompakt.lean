/-
  File:      stage0/Stage0/Schnell/Kompakt.lean
  Subject:   **The compact trace of the fast machine.** A step of the thread machine reads its thread's trace only
             through the open locks (`offen`) and prepends new events; the oracle of stage 0 reads the number of
             questions (`fremdZahl`). The fast machine keeps, per thread, a trace with the same open locks
             (`kompakt`) and counts the questions it dropped. `Schwanz c sF sM`: the fast tail `sF` stands for the
             machine's tail `sM`; `Paar sF sM σF σM`: two worlds of one step, one memory, the same new events in
             front of the two tails. Every world operation of the semantics keeps `Paar`.
-/
import Grammatik.Logik.Ruf.RufLogik
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration}

/-- The questions asked outside in a trace. -/
def fremdZahl : List (Ereignis D) → Nat
  | [] => 0
  | .fremd _ :: s => fremdZahl s + 1
  | .zugriff .. :: s => fremdZahl s
  | .gzugriff .. :: s => fremdZahl s
  | .nimmt .. :: s => fremdZahl s
  | .gibt _ :: s => fremdZahl s

theorem fremdZahl_append (a b : List (Ereignis D)) : fremdZahl (a ++ b) = fremdZahl a + fremdZahl b := by
  induction a with
  | nil => simp [fremdZahl]
  | cons e a ih => cases e <;> simp only [List.cons_append, fremdZahl, ih] <;> omega

/-- The open locks after new events depend on the tail only through its open locks. -/
theorem offen_append_kongr {s s' : List (Ereignis D)} (h : offen s = offen s') :
    ∀ a : List (Ereignis D), offen (a ++ s) = offen (a ++ s')
  | [] => h
  | e :: a => by cases e <;> simp only [List.cons_append, offen, offen_append_kongr h a]

/-- **The compact trace**: the open locks, each as one `nimmt` event. -/
def kompakt (s : List (Ereignis D)) : List (Ereignis D) := (offen s).map (fun L => .nimmt L [])

theorem offen_nimmtListe : ∀ ls : List D.Lock, offen (ls.map (fun L => Ereignis.nimmt (D := D) L [])) = ls
  | [] => rfl
  | L :: ls => by simp only [List.map_cons, offen, offen_nimmtListe ls]

theorem offen_kompakt (s : List (Ereignis D)) : offen (kompakt s) = offen s := offen_nimmtListe _

theorem fremdZahl_nimmtListe : ∀ ls : List D.Lock, fremdZahl (ls.map (fun L => Ereignis.nimmt (D := D) L [])) = 0
  | [] => rfl
  | L :: ls => by simp only [List.map_cons, fremdZahl, fremdZahl_nimmtListe ls]

theorem fremdZahl_kompakt (s : List (Ereignis D)) : fremdZahl (kompakt s) = 0 := fremdZahl_nimmtListe _

/-- **A fast tail for a machine tail**: the same open locks; the machine's has `c` questions more. -/
structure Schwanz (c : Nat) (sF sM : List (Ereignis D)) : Prop where
  offen : offen sF = offen sM
  fremd : fremdZahl sM = fremdZahl sF + c

theorem Schwanz.vor {c : Nat} {sF sM : List (Ereignis D)} (h : Schwanz c sF sM) (a : List (Ereignis D)) :
    Schwanz c (a ++ sF) (a ++ sM) :=
  ⟨offen_append_kongr h.offen a, by rw [fremdZahl_append, fremdZahl_append, h.fremd]; omega⟩

theorem Schwanz.kompakt {c : Nat} {sF sM : List (Ereignis D)} (h : Schwanz c sF sM) :
    Schwanz (c + fremdZahl sF) (Gabbro.Stage0.kompakt sF) sM :=
  ⟨by rw [offen_kompakt, h.offen], by rw [fremdZahl_kompakt, h.fremd]; omega⟩

/-- **Two worlds of one step**: one memory, the same new events in front of the tails `sF` and `sM`. -/
structure Paar (sF sM : List (Ereignis D)) (σF σM : World D) : Prop where
  slots : σF.slots = σM.slots
  globs : σF.globs = σM.globs
  neu : ∃ neu, σF.spur = neu ++ sF ∧ σM.spur = neu ++ sM

variable {c : Nat} {sF sM : List (Ereignis D)} {σF σM : World D}

theorem Paar.start (s : Speicher D) : Paar sF sM (s.welt sF) (s.welt sM) := ⟨rfl, rfl, [], rfl, rfl⟩

theorem Paar.speicher (h : Paar sF sM σF σM) : σF.speicher = σM.speicher := by
  simp only [World.speicher, h.slots, h.globs]

theorem Paar.haelt (hS : Schwanz c sF sM) (h : Paar sF sM σF σM) : σF.haelt = σM.haelt := by
  obtain ⟨neu, hF, hM⟩ := h.neu
  simp only [World.haelt, hF, hM]
  exact offen_append_kongr hS.offen neu

theorem Paar.fremd (hS : Schwanz c sF sM) (h : Paar sF sM σF σM) :
    fremdZahl σM.spur = fremdZahl σF.spur + c := by
  obtain ⟨neu, hF, hM⟩ := h.neu
  rw [hF, hM, fremdZahl_append, fremdZahl_append, hS.fremd]
  omega

theorem Paar.merke (h : Paar sF sM σF σM) (es : List (Ereignis D)) : Paar sF sM (σF.merke es) (σM.merke es) := by
  obtain ⟨neu, hF, hM⟩ := h.neu
  exact ⟨h.slots, h.globs, es ++ neu, by simp [World.merke, hF], by simp [World.merke, hM]⟩

theorem Paar.lese (hS : Schwanz c sF sM) (h : Paar sF sM σF σM) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    Paar sF sM (σF.lese Λ os) (σM.lese Λ os) := by
  unfold World.lese
  rw [h.haelt hS]
  exact h.merke _

theorem Paar.fragt (h : Paar sF sM σF σM) (q : D.Ax ⊕ D.Reg ⊕ D.Glob) : Paar sF sM (σF.fragt q) (σM.fragt q) :=
  h.merke _

theorem Paar.nimmt (hS : Schwanz c sF sM) (h : Paar sF sM σF σM) (L : D.Lock) :
    Paar sF sM (σF.nimmt L) (σM.nimmt L) := by
  obtain ⟨neu, hF, hM⟩ := h.neu
  refine ⟨h.slots, h.globs, .nimmt L σM.haelt :: neu, ?_, ?_⟩
  · simp [World.nimmt, hF, h.haelt hS]
  · simp [World.nimmt, hM]

theorem Paar.gibt (h : Paar sF sM σF σM) (L : D.Lock) : Paar sF sM (σF.gibt L) (σM.gibt L) := by
  obtain ⟨neu, hF, hM⟩ := h.neu
  exact ⟨h.slots, h.globs, .gibt L :: neu, by simp [World.gibt, hF], by simp [World.gibt, hM]⟩

theorem Paar.storeSlot (h : Paar sF sM σF σM) (t : D.Tab) (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f)) :
    Paar sF sM (σF.storeSlot t k f v) (σM.storeSlot t k f v) := by
  obtain ⟨neu, hF, hM⟩ := h.neu
  refine ⟨?_, h.globs, neu, hF, hM⟩
  simp only [World.storeSlot, h.slots]

theorem Paar.storeGlob (h : Paar sF sM σF σM) (g : D.Glob) (v : Wert D (D.gtyp g)) :
    Paar sF sM (σF.storeGlob g v) (σM.storeGlob g v) := by
  obtain ⟨neu, hF, hM⟩ := h.neu
  refine ⟨h.slots, ?_, neu, hF, hM⟩
  simp only [World.storeGlob, h.globs]

theorem Paar.schreibSlot (hS : Schwanz c sF sM) (h : Paar sF sM σF σM) (t : D.Tab) (Λ : List (Res D)) (k : Int)
    (f : D.Feld t) (v : Wert D (D.typ t f)) :
    Paar sF sM (σF.schreibSlot t Λ k f v) (σM.schreibSlot t Λ k f v) := by
  unfold World.schreibSlot
  rw [h.haelt hS]
  exact (h.storeSlot t k f v).merke _

theorem Paar.schreibGlob (hS : Schwanz c sF sM) (h : Paar sF sM σF σM) (g : D.Glob) (Λ : List (Res D))
    (v : Wert D (D.gtyp g)) : Paar sF sM (σF.schreibGlob g Λ v) (σM.schreibGlob g Λ v) := by
  unfold World.schreibGlob
  rw [h.haelt hS]
  exact (h.storeGlob g v).merke _

theorem Paar.schreibBytes (hS : Schwanz c sF sM) (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (Λ : List (Res D)) : ∀ (bs : List Byte) (k : Int) {σF σM : World D}, Paar sF sM σF σM →
      Paar sF sM (σF.schreibBytes t f hf Λ k bs) (σM.schreibBytes t f hf Λ k bs)
  | [], _, _, _, h => h
  | b :: bs, k, _, _, h => Paar.schreibBytes hS t f hf Λ bs (k + 1) (h.schreibSlot hS t Λ k f _)

/-- Expressions see the memory only. -/
theorem Paar.eval (h₀ : Paar sF sM σ₀F σ₀M) (h : Paar sF sM σF σM) {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ) (ρ : Env D Γ) : eval σ₀F e σF ρ = eval σ₀M e σM ρ :=
  eval_spurfrei e _ _ _ _ h₀.slots h₀.globs h.slots h.globs ρ

theorem Paar.evalArgs (h : Paar sF sM σF σM) {Γ : Ctx} {Λ : List (Res D)} {τs : List Ty}
    (args : Args D Γ Λ τs) (ρ : Env D Γ) : evalArgs σF args σF ρ = evalArgs σM args σM ρ := by
  induction args with
  | nil => rfl
  | cons e rest ih => simp only [Grammatik.evalArgs, h.eval h e ρ, ih]

end Gabbro.Stage0
