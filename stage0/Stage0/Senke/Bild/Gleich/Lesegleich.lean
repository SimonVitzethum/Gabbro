/-
  File:      stage0/Stage0/Senke/Bild/Gleich/Lesegleich.lean
  Subject:   **Worlds equal up to read events** (package P0 of the closed calls of the image theorem). `rufAt` reads
             the places of `requires`, `ensures` and the owed invariants into the trace, machine G does not
             (`befund_vertrag`); the two final worlds of a call agree in memory and differ only by READ events. This
             file names that agreement and its algebra; it changes no behaviour.

             FROZEN SIGNATURE (P0; P1-P4 build on it):
               `WeltGleich {D : Deklaration} (σ σ' : World D) : Prop`, a structure with the three fields
                 `slots : σ.slots = σ'.slots`, `globs : σ.globs = σ'.globs`,
                 `spur  : spurOhneLese σ.spur = spurOhneLese σ'.spur`,
               where `spurOhneLese` deletes exactly the read events (`istLeseEv`: a table or global access with
               `schreibt = false`). The erasure itself lives in the model (grammatik, Kern/Semantik/Semantik/T1/
               Lese.lean) since 2026-11-13: machine G hands the oracle the world without reads, so `≈` worlds are
               exactly the worlds with one erasure (`WeltGleich.iff_ohneLese`). Writes, `nimmt`, `gibt` and `fremd`
               (answers from outside) are KEPT: erasing an answer would equate observably different oracles
               (`weltGleich_nicht_merke`, `_nicht_fragt`, `_nicht_nimmt`, `_nicht_schreibSlot` in
               `LesegleichEig.lean`). The held locks (`offen_spurOhneLese`) and the write accesses of a trace
               (`schreib_spurOhneLese`, `LesegleichEig.lean`) are unchanged by the erasure; expressions do not see the
               trace at all (`WeltGleich.wert`, from `eval_spurfrei`).
-/
module
public import Grammatik.Logik.Ruf.RufLogik
public import Grammatik.Kern.Semantik.Maschine.T1.Teil1
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-! ## 2. The equivalence -/

/-- **Two worlds equal up to read events** (`σ ≈ σ'`): the same memory, and the same trace once every read event is
    erased. -/
structure WeltGleich (σ σ' : World D) : Prop where
  slots : σ.slots = σ'.slots
  globs : σ.globs = σ'.globs
  spur : spurOhneLese σ.spur = spurOhneLese σ'.spur

/-- **A read is invisible up to `≈`.** -/
theorem weltGleich_lese (σ : World D) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    WeltGleich σ (σ.lese Λ os) :=
  ⟨rfl, rfl, (spurOhneLese_lese σ Λ os).symm⟩

/-- A read of `n` places adds `n` events. -/
theorem lese_spur_length (σ : World D) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    (σ.lese Λ os).spur.length = os.length + σ.spur.length := by
  show (List.map _ os ++ σ.spur).length = _
  rw [List.length_append, List.length_map]

/-- **`≈` is not equality**: a read of a nonempty list of places changes the trace. -/
theorem lese_echt (σ : World D) (Λ : List (Res D)) {os : List (D.Tab ⊕ D.Glob)} (hne : os ≠ []) :
    (σ.lese Λ os).spur ≠ σ.spur := by
  intro he
  have hl := congrArg List.length he
  rw [lese_spur_length] at hl
  cases os with
  | nil => exact hne rfl
  | cons o os =>
      rw [List.length_cons] at hl
      omega

namespace WeltGleich

variable {σ σ' σ'' : World D}

theorem refl (σ : World D) : WeltGleich σ σ := ⟨rfl, rfl, rfl⟩

theorem symm (h : WeltGleich σ σ') : WeltGleich σ' σ := ⟨h.slots.symm, h.globs.symm, h.spur.symm⟩

theorem trans (h₁ : WeltGleich σ σ') (h₂ : WeltGleich σ' σ'') : WeltGleich σ σ'' :=
  ⟨h₁.slots.trans h₂.slots, h₁.globs.trans h₂.globs, h₁.spur.trans h₂.spur⟩

/-- **`≈` worlds are the worlds with one erasure**: what the oracle sees (`World.ohneLese`). -/
theorem ohneLese_eq (h : WeltGleich σ σ') : σ.ohneLese = σ'.ohneLese :=
  World.ohneLese_eq_of h.slots h.globs h.spur

theorem of_ohneLese (h : σ.ohneLese = σ'.ohneLese) : WeltGleich σ σ' :=
  ⟨World.slots_of_ohneLese h, World.globs_of_ohneLese h, World.spur_of_ohneLese h⟩

theorem iff_ohneLese : WeltGleich σ σ' ↔ σ.ohneLese = σ'.ohneLese :=
  ⟨ohneLese_eq, of_ohneLese⟩

/-- The open locks agree. -/
theorem offen_eq (h : WeltGleich σ σ') : offen σ.spur = offen σ'.spur := by
  rw [← offen_spurOhneLese σ.spur, h.spur, offen_spurOhneLese]

/-- The held locks agree. -/
theorem haelt_eq (h : WeltGleich σ σ') : σ.haelt = σ'.haelt := h.offen_eq

/-- The memories agree. -/
theorem speicher_eq (h : WeltGleich σ σ') : σ.speicher = σ'.speicher := by
  show (⟨σ.slots, σ.globs⟩ : Speicher D) = ⟨σ'.slots, σ'.globs⟩
  rw [h.slots, h.globs]

/-- The same events on top keep `≈`. -/
theorem merke (h : WeltGleich σ σ') (es : List (Ereignis D)) : WeltGleich (σ.merke es) (σ'.merke es) :=
  ⟨h.slots, h.globs, by
    show spurOhneLese (es ++ σ.spur) = spurOhneLese (es ++ σ'.spur)
    rw [spurOhneLese_append, spurOhneLese_append, h.spur]⟩

/-- The same reads keep `≈`. -/
theorem lese (h : WeltGleich σ σ') (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    WeltGleich (σ.lese Λ os) (σ'.lese Λ os) :=
  ⟨h.slots, h.globs, by rw [spurOhneLese_lese, spurOhneLese_lese]; exact h.spur⟩

/-- The same question to the outside keeps `≈`. -/
theorem fragt (h : WeltGleich σ σ') (q : D.Ax ⊕ D.Reg ⊕ D.Glob) : WeltGleich (σ.fragt q) (σ'.fragt q) :=
  h.merke [.fremd q]

/-- Taking the same lock keeps `≈` (the held sets agree). -/
theorem nimmt (h : WeltGleich σ σ') (L : D.Lock) : WeltGleich (σ.nimmt L) (σ'.nimmt L) := by
  have e : ∀ τ : World D, τ.nimmt L = τ.merke [.nimmt L τ.haelt] := fun _ => rfl
  rw [e, e, h.haelt_eq]
  exact h.merke _

/-- Giving the same lock keeps `≈`. -/
theorem gibt (h : WeltGleich σ σ') (L : D.Lock) : WeltGleich (σ.gibt L) (σ'.gibt L) := by
  have e : ∀ τ : World D, τ.gibt L = τ.merke [.gibt L] := fun _ => rfl
  rw [e, e]
  exact h.merke _

/-- Giving the same list of scopes keeps `≈`. -/
theorem gibt_foldl : ∀ (Ls : List D.Lock) {σ σ' : World D}, WeltGleich σ σ' →
    WeltGleich (Ls.foldl World.gibt σ) (Ls.foldl World.gibt σ')
  | [], _, _, h => h
  | L :: Ls, _, _, h => gibt_foldl Ls (h.gibt L)

/-- A slot store depends on the slots only. -/
theorem storeSlot_slots {σ σ' : World D} (h : σ.slots = σ'.slots) (t : D.Tab) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f)) : (σ.storeSlot t k f v).slots = (σ'.storeSlot t k f v).slots := by
  obtain ⟨s, g, sp⟩ := σ
  obtain ⟨s', g', sp'⟩ := σ'
  change s = s' at h
  subst h
  rfl

/-- A global store depends on the globals only. -/
theorem storeGlob_globs {σ σ' : World D} (h : σ.globs = σ'.globs) (g : D.Glob) (v : Wert D (D.gtyp g)) :
    (σ.storeGlob g v).globs = (σ'.storeGlob g v).globs := by
  obtain ⟨s, gl, sp⟩ := σ
  obtain ⟨s', gl', sp'⟩ := σ'
  change gl = gl' at h
  subst h
  rfl

theorem storeSlot (h : WeltGleich σ σ') (t : D.Tab) (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f)) :
    WeltGleich (σ.storeSlot t k f v) (σ'.storeSlot t k f v) :=
  ⟨storeSlot_slots h.slots t k f v, h.globs, h.spur⟩

theorem storeGlob (h : WeltGleich σ σ') (g : D.Glob) (v : Wert D (D.gtyp g)) :
    WeltGleich (σ.storeGlob g v) (σ'.storeGlob g v) :=
  ⟨h.slots, storeGlob_globs h.globs g v, h.spur⟩

/-- The same slot write keeps `≈`. -/
theorem schreibSlot (h : WeltGleich σ σ') (t : D.Tab) (Λ : List (Res D)) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f)) : WeltGleich (σ.schreibSlot t Λ k f v) (σ'.schreibSlot t Λ k f v) := by
  have e : ∀ τ : World D, τ.schreibSlot t Λ k f v =
      (τ.storeSlot t k f v).merke [.zugriff t true Λ τ.haelt] := fun _ => rfl
  rw [e, e, h.haelt_eq]
  exact (h.storeSlot t k f v).merke _

/-- The same global write keeps `≈`. -/
theorem schreibGlob (h : WeltGleich σ σ') (g : D.Glob) (Λ : List (Res D)) (v : Wert D (D.gtyp g)) :
    WeltGleich (σ.schreibGlob g Λ v) (σ'.schreibGlob g Λ v) := by
  have e : ∀ τ : World D, τ.schreibGlob g Λ v = (τ.storeGlob g v).merke [.gzugriff g true Λ τ.haelt] :=
    fun _ => rfl
  rw [e, e, h.haelt_eq]
  exact (h.storeGlob g v).merke _

/-- The same byte writes keep `≈`. -/
theorem schreibBytes (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) (Λ : List (Res D)) :
    ∀ (bs : List Gabbro.Grammatik.Byte) (k : Int) {σ σ' : World D}, WeltGleich σ σ' →
      WeltGleich (σ.schreibBytes t f hf Λ k bs) (σ'.schreibBytes t f hf Λ k bs)
  | [], _, _, _, h => h
  | _ :: bs, k, _, _, h => schreibBytes t f hf Λ bs (k + 1) (h.schreibSlot t Λ k f _)

/-! ## 3. Expressions do not see the trace -/

/-- An expression has the same value in `≈` worlds, on the `old(..)` side and on the current side. -/
theorem wert {σ₀ σ₀' : World D} (h₀ : WeltGleich σ₀ σ₀') (h : WeltGleich σ σ') {Γ : Ctx}
    {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) (ρ : Env D Γ) : eval σ₀ e σ ρ = eval σ₀' e σ' ρ :=
  eval_spurfrei e σ₀ σ₀' σ σ' h₀.slots h₀.globs h.slots h.globs ρ

/-- The form every statement uses: the same world on both sides of `eval`. -/
theorem wert' (h : WeltGleich σ σ') {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (ρ : Env D Γ) : eval σ e σ ρ = eval σ' e σ' ρ :=
  wert h h e ρ

/-- Arguments have the same values in `≈` worlds. -/
theorem werte (h : WeltGleich σ σ') {Γ : Ctx} {Λ : List (Res D)} :
    ∀ {τs : List Ty} (args : Args D Γ Λ τs) (ρ : Env D Γ), evalArgs σ args σ ρ = evalArgs σ' args σ' ρ
  | _, .nil, _ => rfl
  | _, .cons e rest, ρ => by
      show Env.cons (eval σ e σ ρ) (evalArgs σ rest σ ρ) = Env.cons (eval σ' e σ' ρ) (evalArgs σ' rest σ' ρ)
      rw [h.wert' e ρ, werte h rest ρ]

/-- A result expression has the same value in `≈` worlds. -/
theorem ergebnis (h : WeltGleich σ σ') {Γ : Ctx} {Λ : List (Res D)} {o : Option Ty} (x : ErgExpr D Γ Λ o)
    (ρ : Env D Γ) : evalErg σ x σ ρ = evalErg σ' x σ' ρ := by
  cases x with
  | empty => rfl
  | val e => exact h.wert' e ρ

end WeltGleich

end Gabbro.Stage0.Senke.BildLauf
