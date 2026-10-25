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
  and the `D'`-world it stood for) stay functional (`Inv`): an earlier key as long as the
  current trace agrees with the current `D'`-world outside the image (`Fremd`), and on the
  image both agree with the `D`-memory, so the two `D'`-worlds are equal (`eq_of_treu`).
-/

namespace Gabbro.Grammatik.Einbettung

open Gabbro.Grammatik

variable {D D' : Deklaration}

namespace Einbettung

variable (E : Einbettung D D')

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

/-! ## Agreement outside the image -/

/-- Two `D'`-worlds agree outside the image: foreign carriers and trace. -/
def Fremd (a b : World D') : Prop :=
  (∀ t', E.tabZ t' = none → a.slots t' = b.slots t') ∧
  (∀ g', E.globZ g' = none → a.globs g' = b.globs g') ∧ a.spur = b.spur

theorem fremd_refl (a : World D') : E.Fremd a a := ⟨fun _ _ => rfl, fun _ _ => rfl, rfl⟩

theorem fremd_trans {a b c : World D'} (h1 : E.Fremd a b) (h2 : E.Fremd b c) : E.Fremd a c :=
  ⟨fun t h => (h1.1 t h).trans (h2.1 t h), fun g h => (h1.2.1 g h).trans (h2.2.1 g h),
    h1.2.2.trans h2.2.2⟩

theorem castW_inj {τ σ : Ty} (h : τ = σ) {v w : Wert D τ} (e : castW h v = castW h w) : v = w := by
  subst h; exact e

/-- **Same memory on the image, same foreign part: the same world.** -/
theorem eq_of_treu {s : Speicher D} {a b : World D'} (ha : E.Treu s a) (hb : E.Treu s b)
    (hf : E.Fremd a b) : a = b := by
  have hsl : ∀ t (k : Int) (f : D.Feld t), a.slots (E.tab t) k (E.feld t f) = b.slots (E.tab t) k (E.feld t f) :=
    fun t k f => castW_inj (E.typ t f) ((ha.1 t k f).trans (hb.1 t k f).symm)
  have hgl : ∀ g, a.globs (E.glob g) = b.globs (E.glob g) :=
    fun g => castW_inj (E.gtyp g) ((ha.2 g).trans (hb.2 g).symm)
  cases a with
  | mk sa ga pa =>
    cases b with
    | mk sb gb pb =>
      simp only [World.mk.injEq]
      refine ⟨?_, ?_, hf.2.2⟩
      · funext t' k f'
        cases hz : E.tabZ t' with
        | none => exact congrFun (congrFun (hf.1 t' hz) k) f'
        | some t =>
            have e : E.tab t = t' := E.tab_tabZ t' t hz
            subst e
            have := hsl t k (E.feldZ t f')
            exact (E.feld_feldZ t f') ▸ this
      · funext g'
        cases hz : E.globZ g' with
        | none => exact hf.2.1 g' hz
        | some g =>
            have e : E.glob g = g' := E.glob_globZ g' g hz
            subst e
            exact hgl g

/-! ## The keys -/

/-- **The keys of a run, at the current pair `σ`, `σ'`**: every key carries its `D'`-world's
    image memory; none is longer than the current trace; one as long agrees with `σ'` outside
    the image; and the keys are functional. -/
structure Inv (M : List (World D × World D')) (σ : World D) (σ' : World D') : Prop where
  treu : E.Treu σ.speicher σ'
  eintrag : ∀ p ∈ M, E.Treu p.1.speicher p.2
  kurz : ∀ p ∈ M, p.1.spur.length ≤ σ.spur.length
  gleich : ∀ p ∈ M, p.1.spur.length = σ.spur.length → E.Fremd p.2 σ'
  funk : ∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p.2 = q.2

/-- The keys alone: every one carries its image memory, and they are functional. -/
def KeyOk (M : List (World D × World D')) : Prop :=
  (∀ p ∈ M, E.Treu p.1.speicher p.2) ∧ (∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p.2 = q.2)

theorem Inv.keyOk {M : List (World D × World D')} {σ : World D} {σ' : World D'}
    (h : E.Inv M σ σ') : E.KeyOk M := ⟨h.eintrag, h.funk⟩

/-- **The current pair is a key.** -/
theorem Inv.merke {M : List (World D × World D')} {σ : World D} {σ' : World D'}
    (h : E.Inv M σ σ') : E.Inv ((σ, σ') :: M) σ σ' := by
  have neu : ∀ p ∈ M, p.1 = σ → p.2 = σ' := fun p hp he =>
    E.eq_of_treu (s := σ.speicher) (he ▸ h.eintrag p hp) h.treu (h.gleich p hp (by rw [he]))
  refine ⟨h.treu, ?_, ?_, ?_, ?_⟩
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
    · exact E.fremd_refl _
    · exact h.gleich p hp hl
  · intro p hp q hq he
    rcases List.mem_cons.mp hp with rfl | hp <;> rcases List.mem_cons.mp hq with rfl | hq
    · rfl
    · exact (neu q hq he.symm).symm
    · exact neu p hp he
    · exact h.funk p hp q hq he

/-- **A longer trace**: every key is now strictly shorter. -/
theorem Inv.wachs {M : List (World D × World D')} {σ τ : World D} {σ' τ' : World D'}
    (h : E.Inv M σ σ') (hl : σ.spur.length < τ.spur.length) (ht : E.Treu τ.speicher τ') :
    E.Inv M τ τ' :=
  ⟨ht, h.eintrag, fun p hp => Nat.le_of_lt (Nat.lt_of_le_of_lt (h.kurz p hp) hl),
    fun p hp he => absurd he (Nat.ne_of_lt (Nat.lt_of_le_of_lt (h.kurz p hp) hl)), h.funk⟩

/-- **A question to the outside on both sides** (`Ereignis.fremd`): the trace grows, no memory moves. -/
theorem Inv.fragt {M : List (World D × World D')} {σ : World D} {σ' : World D'} (h : E.Inv M σ σ')
    (q : D.Ax ⊕ D.Reg ⊕ D.Glob) (q' : D'.Ax ⊕ D'.Reg ⊕ D'.Glob) : E.Inv M (σ.fragt q) (σ'.fragt q') :=
  h.wachs E (Nat.lt_succ_self _) h.treu

/-- **The same trace length, nothing foreign changed.** -/
theorem Inv.bleib {M : List (World D × World D')} {σ τ : World D} {σ' τ' : World D'}
    (h : E.Inv M σ σ') (hl : τ.spur.length = σ.spur.length) (ht : E.Treu τ.speicher τ')
    (hf : E.Fremd σ' τ') : E.Inv M τ τ' :=
  ⟨ht, h.eintrag, fun p hp => hl ▸ h.kurz p hp,
    fun p hp he => E.fremd_trans (h.gleich p hp (he.trans hl)) hf, h.funk⟩

/-- A longer trace or the same pair. -/
theorem Inv.wachs_le {M : List (World D × World D')} {σ τ : World D} {σ' τ' : World D'}
    (h : E.Inv M σ σ') (hl : σ.spur.length < τ.spur.length ∨ (τ = σ ∧ τ' = σ'))
    (ht : E.Treu τ.speicher τ') : E.Inv M τ τ' := by
  rcases hl with hl | ⟨rfl, rfl⟩
  · exact h.wachs E hl ht
  · exact h

/-- More keys that the run reached before. -/
theorem Inv.teil {M M' : List (World D × World D')} {σ : World D} {σ' : World D'}
    (h : E.Inv M' σ σ') (hs : ∀ p ∈ M, p ∈ M') : E.Inv M σ σ' :=
  ⟨h.treu, fun p hp => h.eintrag p (hs p hp), fun p hp => h.kurz p (hs p hp),
    fun p hp => h.gleich p (hs p hp), fun p hp q hq => h.funk p (hs p hp) q (hs q hq)⟩

/-! ## Reads and writes -/

/-- The events of a read: one per carrier. -/
theorem lese_laenge (σ : World D) (Λ : List (Res D)) (X : List (D.Tab ⊕ D.Glob)) :
    (σ.lese Λ X).spur.length = X.length + σ.spur.length := by
  simp [World.lese, World.merke]

theorem lese_speicher (σ : World D) (Λ : List (Res D)) (X : List (D.Tab ⊕ D.Glob)) :
    (σ.lese Λ X).speicher = σ.speicher := rfl

/-- **A read on both sides.** -/
theorem Inv.lese {M : List (World D × World D')} {σ : World D} {σ' : World D'} (h : E.Inv M σ σ')
    (Λ : List (Res D)) (Λ' : List (Res D')) (X : List (D.Tab ⊕ D.Glob)) :
    E.Inv M (σ.lese Λ X) (σ'.lese Λ' (X.map E.ortE)) := by
  cases X with
  | nil => simp only [List.map_nil]; rw [lese_nil, lese_nil]; exact h
  | cons x X =>
      refine h.wachs E ?_ h.treu
      rw [lese_laenge]; simp

theorem treu_storeSlot {s : Speicher D} {σ' : World D'} (h : E.Treu s σ') (t : D.Tab) (k : Int)
    (f : D.Feld t) (v : Wert D (D.typ t f)) (v' : Wert D' (D'.typ (E.tab t) (E.feld t f)))
    (hv : castW (E.typ t f) v' = E.valE _ v) :
    E.Treu (((s.welt []).storeSlot t k f v).speicher) (σ'.storeSlot (E.tab t) k (E.feld t f) v') := by
  refine ⟨fun t0 k0 f0 => ?_, fun g => h.2 g⟩
  show castW _ ((σ'.storeSlot (E.tab t) k (E.feld t f) v').slots (E.tab t0) k0 (E.feld t0 f0)) =
    E.valE _ (((s.welt []).storeSlot t k f v).slots t0 k0 f0)
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

theorem treu_storeGlob {s : Speicher D} {σ' : World D'} (h : E.Treu s σ') (g : D.Glob)
    (v : Wert D (D.gtyp g)) (v' : Wert D' (D'.gtyp (E.glob g)))
    (hv : castW (E.gtyp g) v' = E.valE _ v) :
    E.Treu (((s.welt []).storeGlob g v).speicher) (σ'.storeGlob (E.glob g) v') := by
  refine ⟨fun t k f => h.1 t k f, fun g0 => ?_⟩
  show castW _ ((σ'.storeGlob (E.glob g) v').globs (E.glob g0)) =
    E.valE _ (((s.welt []).storeGlob g v).globs g0)
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
theorem Inv.schreibSlot {M : List (World D × World D')} {σ : World D} {σ' : World D'}
    (h : E.Inv M σ σ') (t : D.Tab) (Λ : List (Res D)) (Λ' : List (Res D')) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f)) (v' : Wert D' (D'.typ (E.tab t) (E.feld t f)))
    (hv : castW (E.typ t f) v' = E.valE _ v) :
    E.Inv M (σ.schreibSlot t Λ k f v) (σ'.schreibSlot (E.tab t) Λ' k (E.feld t f) v') := by
  refine h.wachs E (by simp [World.schreibSlot, World.merke, World.storeSlot]) ?_
  show E.Treu (σ.storeSlot t k f v).speicher ((σ'.storeSlot (E.tab t) k (E.feld t f) v').merke _)
  rw [speicher_storeSlot]
  exact E.treu_storeSlot h.treu t k f v v' hv

/-- **A global write on both sides.** -/
theorem Inv.schreibGlob {M : List (World D × World D')} {σ : World D} {σ' : World D'}
    (h : E.Inv M σ σ') (g : D.Glob) (Λ : List (Res D)) (Λ' : List (Res D')) (v : Wert D (D.gtyp g))
    (v' : Wert D' (D'.gtyp (E.glob g))) (hv : castW (E.gtyp g) v' = E.valE _ v) :
    E.Inv M (σ.schreibGlob g Λ v) (σ'.schreibGlob (E.glob g) Λ' v') := by
  refine h.wachs E (by simp [World.schreibGlob, World.merke, World.storeGlob]) ?_
  show E.Treu (σ.storeGlob g v).speicher ((σ'.storeGlob (E.glob g) v').merke _)
  rw [speicher_storeGlob]
  exact E.treu_storeGlob h.treu g v v' hv

theorem byte_cast {T T' : Ty} (hf : T = .int 0 255) (hf' : T' = .int 0 255) (e : T' = E.tyE T)
    (b : Byte) :
    castW e (cast (congrArg (Wert D') hf').symm (b : Wert D' (.int 0 255))) =
      E.valE T (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255))) := by
  subst hf; subst hf'; rfl

/-- **Byte writes on both sides**: the same bytes, one slot write each. -/
theorem Inv.schreibBytes {M : List (World D × World D')} {σ : World D} {σ' : World D'}
    (h : E.Inv M σ σ') (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (hf' : D'.typ (E.tab t) (E.feld t f) = .int 0 255) (Λ : List (Res D)) (Λ' : List (Res D'))
    (k : Int) (bs : List Byte) :
    E.Inv M (σ.schreibBytes t f hf Λ k bs) (σ'.schreibBytes (E.tab t) (E.feld t f) hf' Λ' k bs) := by
  induction bs generalizing σ σ' k with
  | nil => exact h
  | cons b bs ih =>
      simp only [World.schreibBytes]
      apply ih
      exact h.schreibSlot E t Λ Λ' k f _ _ (E.byte_cast hf hf' (E.typ t f) b)

/-- The trace of a lock take and release grows by one on both sides. -/
theorem Inv.nimmt {M : List (World D × World D')} {σ : World D} {σ' : World D'}
    (h : E.Inv M σ σ') (L : D.Lock) (L' : D'.Lock) : E.Inv M (σ.nimmt L) (σ'.nimmt L') :=
  h.wachs E (by simp [World.nimmt]) h.treu

theorem Inv.gibt {M : List (World D × World D')} {σ : World D} {σ' : World D'}
    (h : E.Inv M σ σ') (L : D.Lock) (L' : D'.Lock) : E.Inv M (σ.gibt L) (σ'.gibt L') :=
  h.wachs E (by simp [World.gibt]) h.treu

end Einbettung

end Gabbro.Grammatik.Einbettung
