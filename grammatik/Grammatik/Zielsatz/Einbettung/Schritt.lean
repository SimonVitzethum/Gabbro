import Grammatik.Zielsatz.Einbettung.Auswertung
import Grammatik.Speichermodell.Atomar.AtomarRec

/-!
  File:      Grammatik/Zielsatz/Einbettung/Schritt.lean
  Subject:   One step of a run of `D` beside the run of its image in `D'` (stage E2b).

  The run of a translated body in `D'` and the run of the body in `D` keep the same memory on
  the image (`Treu`). The foreign part of a `D'`-world (the carriers outside the image and the
  trace) changes only where a foreign answer comes in -- a callee, an axiom; the `D`-run then
  puts a NEUTRAL piece `pad` on its own trace (`PadOk`: not empty, no lock opened or closed), so
  its trace grows at every such point. Every step that changes nothing foreign keeps the trace
  length of both or grows both.

  So along the run the `D`-world DETERMINES the `D'`-world: the KEYS `M` (pairs of a `D`-world
  and the `D'`-world it stood for) stay functional (`Inv`): a main key as long as the current
  trace stood for the current `D'`-world, since no step changes the `D'`-world without growing
  the trace except an atomic answer and a lock move -- and those are taken together with the
  read events and the take event around them; the atomic keys are told apart by their length.
  A CALL key records, at the world of a call, the callee `D'` really called and its arguments
  (stage E4: a head of `D` may stand for several foreign callees).
-/

namespace Gabbro.Grammatik.Einbettung

open Gabbro.Grammatik

variable {D D' : Deklaration}

namespace Einbettung

variable (E : Einbettung D D') (hZ : E.Rueck)

/-! ## Neutral trace pieces -/

/-- A piece of trace that opens and closes no lock, and is not empty. -/
structure PadOk (pad : List (Ereignis D)) : Prop where
  lang : 0 < pad.length
  offen : ∀ s, Gabbro.Grammatik.offen (pad ++ s) = Gabbro.Grammatik.offen s

/-- A declaration with a carrier or a lock has a neutral piece. -/
theorem padOk_tab (t : D.Tab) : PadOk [Ereignis.zugriff t false [] ([] : List D.Lock)] :=
  ⟨by simp, fun _ => rfl⟩

theorem padOk_glob (g : D.Glob) : PadOk [Ereignis.gzugriff g false [] ([] : List D.Lock)] :=
  ⟨by simp, fun _ => rfl⟩

theorem padOk_lock (L : D.Lock) : PadOk [Ereignis.gibt L, Ereignis.nimmt L []] :=
  ⟨by simp, fun s => by simp [Gabbro.Grammatik.offen]⟩

theorem castW_inj {τ σ : Ty} (h : τ = σ) {v w : Wert D τ} (e : castW h v = castW h w) : v = w := by
  subst h; exact e

/-! ## The keys -/

/-- **The keys of a run**: pairs of a `D`-world and the `D'`-world it stood for -- the MAIN keys
    (where a call handler, an axiom, a lock move or a register was asked) and the ATOMIC keys
    (where the atomic environment was asked). They are kept apart: an atomic answer may change the
    `D'`-world without changing the `D`-world (a function pointer swapped for another one `D`
    cannot name), and the next main key can stand at that same `D`-world. -/
structure Keys (D D' : Deklaration) where
  haupt : List (World D × World D')
  atom : List (World D × World D')
  /-- The CALL keys: where a callee was asked, the callee of `D'` and its actual arguments (a
      function pointer among them may name a function `D` cannot name). -/
  ruf : List (World D × (Σ f' : D'.Fn, Env D' (D'.params f')))

/-- No key yet. -/
def Keys.leer : Keys D D' := ⟨[], [], []⟩

/-- `M` is among the keys `M'`. -/
def Teil (M M' : Keys D D') : Prop :=
  (∀ p ∈ M.haupt, p ∈ M'.haupt) ∧ (∀ p ∈ M.atom, p ∈ M'.atom) ∧ (∀ p ∈ M.ruf, p ∈ M'.ruf)

theorem teil_refl (M : Keys D D') : Teil M M := ⟨fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem teil_trans {M M₁ M₂ : Keys D D'} (h1 : Teil M M₁) (h2 : Teil M₁ M₂) : Teil M M₂ :=
  ⟨fun p hp => h2.1 p (h1.1 p hp), fun p hp => h2.2.1 p (h1.2.1 p hp), fun p hp => h2.2.2 p (h1.2.2 p hp)⟩

/-- **The keys of a run, at the current pair `σ`, `σ'`**: every key carries its `D'`-world's
    image memory; none is longer than the current trace; a MAIN key as long as the current trace
    stood for the current `D'`-world; the main keys are functional; atomic keys of one length are
    one key. -/
structure Inv (M : Keys D D') (σ : World D) (σ' : World D') : Prop where
  treu : E.Treu hZ σ.speicher σ'
  eintrag : ∀ p ∈ M.haupt, E.Treu hZ p.1.speicher p.2
  kurz : ∀ p ∈ M.haupt, p.1.spur.length ≤ σ.spur.length
  gleich : ∀ p ∈ M.haupt, p.1.spur.length = σ.spur.length → p.2 = σ'
  funk : ∀ p ∈ M.haupt, ∀ q ∈ M.haupt, p.1 = q.1 → p.2 = q.2
  aEintrag : ∀ p ∈ M.atom, E.Treu hZ p.1.speicher p.2
  aKurz : ∀ p ∈ M.atom, p.1.spur.length ≤ σ.spur.length
  aFunk : ∀ p ∈ M.atom, ∀ q ∈ M.atom, p.1.spur.length = q.1.spur.length → p = q
  rKurz : ∀ p ∈ M.ruf, p.1.spur.length < σ.spur.length
  rFunk : ∀ p ∈ M.ruf, ∀ q ∈ M.ruf, p.1.spur.length = q.1.spur.length → p = q

/-- The keys alone: every one carries its image memory, and they are functional. -/
def KeyOk (M : Keys D D') : Prop :=
  (∀ p ∈ M.haupt, E.Treu hZ p.1.speicher p.2) ∧ (∀ p ∈ M.haupt, ∀ q ∈ M.haupt, p.1 = q.1 → p.2 = q.2) ∧
  (∀ p ∈ M.atom, E.Treu hZ p.1.speicher p.2) ∧ (∀ p ∈ M.atom, ∀ q ∈ M.atom, p.1 = q.1 → p.2 = q.2) ∧
  (∀ p ∈ M.ruf, ∀ q ∈ M.ruf, p.1 = q.1 → p.2 = q.2)

variable {hZ}

theorem Inv.keyOk {M : Keys D D'} {σ : World D} {σ' : World D'}
    (h : E.Inv hZ M σ σ') : E.KeyOk hZ M :=
  ⟨h.eintrag, h.funk, h.aEintrag, fun p hp q hq he => by rw [h.aFunk p hp q hq (by rw [he])],
    fun p hp q hq he => by rw [h.rFunk p hp q hq (by rw [he])]⟩

/-- **The current pair as a main key.** -/
theorem Inv.merke {M : Keys D D'} {σ : World D} {σ' : World D'}
    (h : E.Inv hZ M σ σ') : E.Inv hZ ⟨(σ, σ') :: M.haupt, M.atom, M.ruf⟩ σ σ' := by
  have neu : ∀ p ∈ M.haupt, p.1 = σ → p.2 = σ' := fun p hp he => h.gleich p hp (by rw [he])
  refine ⟨h.treu, ?_, ?_, ?_, ?_, h.aEintrag, h.aKurz, h.aFunk, h.rKurz, h.rFunk⟩
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.treu
    · exact h.eintrag p hp
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Nat.le_refl _
    · exact h.kurz p hp
  · intro p hp hl
    rcases List.mem_cons.mp hp with rfl | hp
    · rfl
    · exact h.gleich p hp hl
  · intro p hp q hq he
    rcases List.mem_cons.mp hp with rfl | hp <;> rcases List.mem_cons.mp hq with rfl | hq
    · rfl
    · exact (neu q hq he.symm).symm
    · exact neu p hp he
    · exact h.funk p hp q hq he

/-- **A longer trace**: every key is now strictly shorter. -/
theorem Inv.wachs {M : Keys D D'} {σ τ : World D} {σ' τ' : World D'}
    (h : E.Inv hZ M σ σ') (hl : σ.spur.length < τ.spur.length) (ht : E.Treu hZ τ.speicher τ') :
    E.Inv hZ M τ τ' :=
  ⟨ht, h.eintrag, fun p hp => Nat.le_of_lt (Nat.lt_of_le_of_lt (h.kurz p hp) hl),
    fun p hp he => absurd he (Nat.ne_of_lt (Nat.lt_of_le_of_lt (h.kurz p hp) hl)), h.funk,
    h.aEintrag, fun p hp => Nat.le_of_lt (Nat.lt_of_le_of_lt (h.aKurz p hp) hl), h.aFunk,
    fun p hp => Nat.lt_trans (h.rKurz p hp) hl, h.rFunk⟩

/-- **A question to the outside on both sides** (`Ereignis.fremd`): the trace grows, no memory moves. -/
theorem Inv.fragt {M : Keys D D'} {σ : World D} {σ' : World D'} (h : E.Inv hZ M σ σ')
    (q : D.Ax ⊕ D.Reg ⊕ D.Glob) (q' : D'.Ax ⊕ D'.Reg ⊕ D'.Glob) : E.Inv hZ M (σ.fragt q) (σ'.fragt q') :=
  h.wachs E (Nat.lt_succ_self _) h.treu

/-- **The current pair as an atomic key**, every earlier key strictly shorter. -/
theorem Inv.merkeA {M : Keys D D'} {σ : World D} {σ' : World D'}
    (h : E.Inv hZ M σ σ') (hk : ∀ p ∈ M.atom, p.1.spur.length < σ.spur.length) :
    E.Inv hZ ⟨M.haupt, (σ, σ') :: M.atom, M.ruf⟩ σ σ' := by
  refine ⟨h.treu, h.eintrag, h.kurz, h.gleich, h.funk, ?_, ?_, ?_, h.rKurz, h.rFunk⟩
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.treu
    · exact h.aEintrag p hp
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Nat.le_refl _
    · exact h.aKurz p hp
  · intro p hp q hq he
    rcases List.mem_cons.mp hp with rfl | hp <;> rcases List.mem_cons.mp hq with rfl | hq
    · rfl
    · exact absurd he.symm (Nat.ne_of_lt (hk q hq))
    · exact absurd he (Nat.ne_of_lt (hk p hp))
    · exact h.aFunk p hp q hq he

/-- More keys that the run reached before. -/
theorem Inv.teil {M M' : Keys D D'} {σ : World D} {σ' : World D'}
    (h : E.Inv hZ M' σ σ') (hs : Teil M M') : E.Inv hZ M σ σ' :=
  ⟨h.treu, fun p hp => h.eintrag p (hs.1 p hp), fun p hp => h.kurz p (hs.1 p hp),
    fun p hp => h.gleich p (hs.1 p hp), fun p hp q hq => h.funk p (hs.1 p hp) q (hs.1 q hq),
    fun p hp => h.aEintrag p (hs.2.1 p hp), fun p hp => h.aKurz p (hs.2.1 p hp),
    fun p hp q hq => h.aFunk p (hs.2.1 p hp) q (hs.2.1 q hq),
    fun p hp => h.rKurz p (hs.2.2 p hp), fun p hp q hq => h.rFunk p (hs.2.2 p hp) q (hs.2.2 q hq)⟩

/-- **A call key, and the answer's longer trace**: the pair where the callee was asked, with the
    callee of `D'` and its arguments, and the world after the answer. -/
theorem Inv.merkeRuf {M : Keys D D'} {σ τ : World D} {σ' τ' : World D'}
    (h : E.Inv hZ M σ σ') (r : Σ f' : D'.Fn, Env D' (D'.params f'))
    (hl : σ.spur.length < τ.spur.length) (ht : E.Treu hZ τ.speicher τ') :
    E.Inv hZ ⟨M.haupt, M.atom, (σ, r) :: M.ruf⟩ τ τ' := by
  have hw := h.wachs E hl ht
  refine ⟨ht, hw.eintrag, hw.kurz, hw.gleich, hw.funk, hw.aEintrag, hw.aKurz, hw.aFunk, ?_, ?_⟩
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hl
    · exact hw.rKurz p hp
  · intro p hp q hq he
    rcases List.mem_cons.mp hp with rfl | hp <;> rcases List.mem_cons.mp hq with rfl | hq
    · rfl
    · exact absurd he.symm (Nat.ne_of_lt (h.rKurz q hq))
    · exact absurd he (Nat.ne_of_lt (h.rKurz p hp))
    · exact h.rFunk p hp q hq he

/-! ## Reads and writes -/

/-- The events of a read: one per carrier. -/
theorem lese_laenge (σ : World D) (Λ : List (Res D)) (X : List (D.Tab ⊕ D.Glob)) :
    (σ.lese Λ X).spur.length = X.length + σ.spur.length := by
  simp [World.lese, World.merke]

theorem lese_speicher (σ : World D) (Λ : List (Res D)) (X : List (D.Tab ⊕ D.Glob)) :
    (σ.lese Λ X).speicher = σ.speicher := rfl

/-- **A read on both sides.** -/
theorem Inv.lese {M : Keys D D'} {σ : World D} {σ' : World D'} (h : E.Inv hZ M σ σ')
    (Λ : List (Res D)) (Λ' : List (Res D')) (X : List (D.Tab ⊕ D.Glob)) :
    E.Inv hZ M (σ.lese Λ X) (σ'.lese Λ' (X.map E.ortE)) := by
  cases X with
  | nil => simp only [List.map_nil]; rw [lese_nil, lese_nil]; exact h
  | cons x X =>
      refine h.wachs E ?_ h.treu
      rw [lese_laenge]; simp

theorem treu_storeSlot {s : Speicher D} {σ' : World D'} (h : E.Treu hZ s σ') (t : D.Tab) (k : Int)
    (f : D.Feld t) (v : Wert D (D.typ t f)) (v' : Wert D' (D'.typ (E.tab t) (E.feld t f)))
    (hv : E.VRel hZ _ v (castW (E.typ t f) v')) :
    E.Treu hZ (((s.welt []).storeSlot t k f v).speicher) (σ'.storeSlot (E.tab t) k (E.feld t f) v') := by
  refine ⟨fun t0 k0 f0 => ?_, fun g => h.2 g⟩
  show E.VRel hZ _ (((s.welt []).storeSlot t k f v).slots t0 k0 f0)
    (castW _ ((σ'.storeSlot (E.tab t) k (E.feld t f) v').slots (E.tab t0) k0 (E.feld t0 f0)))
  by_cases ht : t0 = t
  · subst ht
    by_cases hk : k0 = k
    · subst hk
      by_cases hf : f0 = f
      · subst hf
        simp only [World.storeSlot, dif_pos, if_pos]
        exact hv
      · have hf' : E.feld t0 f0 ≠ E.feld t0 f := fun e => hf (by
          have := congrArg (E.feldZ t0) e; rwa [E.feldZ_feld, E.feldZ_feld] at this)
        simp only [World.storeSlot, dif_pos, if_pos, dif_neg hf, dif_neg hf']
        exact h.1 t0 k0 f0
    · simp only [World.storeSlot, dif_pos, if_neg hk]
      exact h.1 t0 k0 f0
  · have ht' : E.tab t0 ≠ E.tab t := fun e => ht (E.tab_inj e)
    simp only [World.storeSlot, dif_neg ht, dif_neg ht']
    exact h.1 t0 k0 f0

theorem treu_storeGlob {s : Speicher D} {σ' : World D'} (h : E.Treu hZ s σ') (g : D.Glob)
    (v : Wert D (D.gtyp g)) (v' : Wert D' (D'.gtyp (E.glob g)))
    (hv : E.VRel hZ _ v (castW (E.gtyp g) v')) :
    E.Treu hZ (((s.welt []).storeGlob g v).speicher) (σ'.storeGlob (E.glob g) v') := by
  refine ⟨fun t k f => h.1 t k f, fun g0 => ?_⟩
  show E.VRel hZ _ (((s.welt []).storeGlob g v).globs g0) (castW _ ((σ'.storeGlob (E.glob g) v').globs (E.glob g0)))
  by_cases hg : g0 = g
  · subst hg
    simp only [World.storeGlob, dif_pos]
    exact hv
  · have hg' : E.glob g0 ≠ E.glob g := fun e => hg (E.glob_inj e)
    simp only [World.storeGlob, dif_neg hg, dif_neg hg']
    exact h.2 g0

theorem speicher_storeSlot (σ : World D) (t : D.Tab) (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f)) :
    (σ.storeSlot t k f v).speicher = ((σ.speicher.welt []).storeSlot t k f v).speicher := rfl

theorem speicher_storeGlob (σ : World D) (g : D.Glob) (v : Wert D (D.gtyp g)) :
    (σ.storeGlob g v).speicher = ((σ.speicher.welt []).storeGlob g v).speicher := rfl

/-- **A slot write on both sides.** -/
theorem Inv.schreibSlot {M : Keys D D'} {σ : World D} {σ' : World D'}
    (h : E.Inv hZ M σ σ') (t : D.Tab) (Λ : List (Res D)) (Λ' : List (Res D')) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f)) (v' : Wert D' (D'.typ (E.tab t) (E.feld t f)))
    (hv : E.VRel hZ _ v (castW (E.typ t f) v')) :
    E.Inv hZ M (σ.schreibSlot t Λ k f v) (σ'.schreibSlot (E.tab t) Λ' k (E.feld t f) v') := by
  refine h.wachs E (by simp [World.schreibSlot, World.merke, World.storeSlot]) ?_
  show E.Treu hZ (σ.storeSlot t k f v).speicher ((σ'.storeSlot (E.tab t) k (E.feld t f) v').merke _)
  rw [speicher_storeSlot]
  exact E.treu_storeSlot h.treu t k f v v' hv

/-- **A global write on both sides.** -/
theorem Inv.schreibGlob {M : Keys D D'} {σ : World D} {σ' : World D'}
    (h : E.Inv hZ M σ σ') (g : D.Glob) (Λ : List (Res D)) (Λ' : List (Res D')) (v : Wert D (D.gtyp g))
    (v' : Wert D' (D'.gtyp (E.glob g))) (hv : E.VRel hZ _ v (castW (E.gtyp g) v')) :
    E.Inv hZ M (σ.schreibGlob g Λ v) (σ'.schreibGlob (E.glob g) Λ' v') := by
  refine h.wachs E (by simp [World.schreibGlob, World.merke, World.storeGlob]) ?_
  show E.Treu hZ (σ.storeGlob g v).speicher ((σ'.storeGlob (E.glob g) v').merke _)
  rw [speicher_storeGlob]
  exact E.treu_storeGlob h.treu g v v' hv

theorem byte_cast {T T' : Ty} (hf : T = .int 0 255) (hf' : T' = .int 0 255) (e : T' = E.tyE T)
    (b : Byte) :
    E.VRel hZ T (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))
      (castW e (cast (congrArg (Wert D') hf').symm (b : Wert D' (.int 0 255)))) := by
  subst hf; subst hf'; rfl

/-- **Byte writes on both sides**: the same bytes, one slot write each. -/
theorem Inv.schreibBytes {M : Keys D D'} {σ : World D} {σ' : World D'}
    (h : E.Inv hZ M σ σ') (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (hf' : D'.typ (E.tab t) (E.feld t f) = .int 0 255) (Λ : List (Res D)) (Λ' : List (Res D'))
    (k : Int) (bs : List Byte) :
    E.Inv hZ M (σ.schreibBytes t f hf Λ k bs) (σ'.schreibBytes (E.tab t) (E.feld t f) hf' Λ' k bs) := by
  induction bs generalizing σ σ' k with
  | nil => exact h
  | cons b bs ih =>
      simp only [World.schreibBytes]
      apply ih
      exact h.schreibSlot E t Λ Λ' k f _ _ (E.byte_cast (hZ := hZ) hf hf' (E.typ t f) b)

/-- The trace of a lock take and release grows by one on both sides. -/
theorem Inv.nimmt {M : Keys D D'} {σ : World D} {σ' : World D'}
    (h : E.Inv hZ M σ σ') (L : D.Lock) (L' : D'.Lock) : E.Inv hZ M (σ.nimmt L) (σ'.nimmt L') :=
  h.wachs E (by simp [World.nimmt]) h.treu

theorem Inv.gibt {M : Keys D D'} {σ : World D} {σ' : World D'}
    (h : E.Inv hZ M σ σ') (L : D.Lock) (L' : D'.Lock) : E.Inv hZ M (σ.gibt L) (σ'.gibt L') :=
  h.wachs E (by simp [World.gibt]) h.treu

end Einbettung

end Gabbro.Grammatik.Einbettung
