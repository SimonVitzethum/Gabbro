/-
   File:      Grammatik/GabbroV/GvStore.lean
   Subject:   Agent 04 task V-04: store-level bridges -- the World's table
              slots into the abstract structures the generic lemmas
              consume.

   (a) `World -> RufKette`: the tick-round shape's per-call contracts as
   `vor`/`nach` over a counter cell (`zellenLesen`), with the uniform
   contract `zahl_tick_vertrag` over `Zahl 0 255` states. (b) `World ->
   edge map`: the `kantenBild` projection (`eval .reaches`'s lambda,
   `Semantik.lean:262`) commutes with `storeSlot` (step case), generic
   over tables/fields -- the missing frame cases next to the accepted
   `seite_rahmen_fremd` (foreign table) and `schreibSlot_slots_other`
   (other slot, same field). Fixture: `kettenD` (3 slots, edge + int
   fields) with `_zeuge` and a planted failure.
-/
import Grammatik.Kern.Semantik.Semantik
import Grammatik.GabbroV.GvKetten

namespace Gabbro.Grammatik.GabbroV

open Gabbro.Grammatik

variable {D : Deklaration}

/-! ## Frames: the two missing `storeSlot` cases -/

/-- Same table, elsewhere: a store touches neither another slot nor
    another field. Beside the accepted `seite_rahmen_fremd` (foreign
    table) and `schreibSlot_slots_other` (other slot, same field, with
    trace event): this is the same-table case, both dimensions. -/
theorem storeSlot_anders (σ : World D) (t : D.Tab) (k : Int)
    (f : D.Feld t) (v : Wert D (D.typ t f)) (k' : Int) (f' : D.Feld t)
    (h : k' ≠ k ∨ f' ≠ f) :
    (σ.storeSlot t k f v).slots t k' f' = σ.slots t k' f' := by
  by_cases hkk : k' = k
  · have hff : f' ≠ f := by
      cases h with
      | inl hkk' => exact absurd hkk hkk'
      | inr hff => exact hff
    simp [World.storeSlot, hkk, hff]
  · simp [World.storeSlot, hkk]

/-- The edge map a `reaches` runs over (`eval .reaches`,
    `Semantik.lean:262`): the `option index` field read as chain edges. -/
def kantenBild (D : Deklaration) (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .opt (D.count t)) :
    Int → Option (Zahl 0 (D.count t - 1)) :=
  fun k => (hf ▸ σ.slots t k f : Wert D (.opt (D.count t)))

/-- Projection commutes with a foreign-table store, pointwise. -/
theorem kantenBild_tabelle_anders (σ : World D) (t : D.Tab) (f' : D.Feld t)
    (hf' : D.typ t f' = .opt (D.count t)) (j : Int)
    (t₀ : D.Tab) (k₀ : Int) (f₀ : D.Feld t₀) (v : Wert D (D.typ t₀ f₀))
    (h : t₀ ≠ t) :
    kantenBild D (σ.storeSlot t₀ k₀ f₀ v) t f' hf' j
      = kantenBild D σ t f' hf' j := by
  have hfr : (σ.storeSlot t₀ k₀ f₀ v).slots t j f' = σ.slots t j f' :=
    seite_rahmen_fremd σ (Ne.symm h) k₀ j f₀ v f'
  simp only [kantenBild, hfr]
  rfl

/-- Projection commutes with a same-table store elsewhere, pointwise:
    another slot, or another field at any slot. -/
theorem kantenBild_slotfeld_anders (σ : World D) (t : D.Tab) (f' : D.Feld t)
    (hf' : D.typ t f' = .opt (D.count t)) (j : Int)
    (k₀ : Int) (f₀ : D.Feld t) (v : Wert D (D.typ t f₀))
    (h : k₀ ≠ j ∨ f₀ ≠ f') :
    kantenBild D (σ.storeSlot t k₀ f₀ v) t f' hf' j
      = kantenBild D σ t f' hf' j := by
  have h' : j ≠ k₀ ∨ f' ≠ f₀ := by
    cases h with
    | inl hkj => exact Or.inl (Ne.symm hkj)
    | inr hfj => exact Or.inr (Ne.symm hfj)
  have hfr : (σ.storeSlot t k₀ f₀ v).slots t j f' = σ.slots t j f' :=
    storeSlot_anders σ t k₀ f₀ v j f' h'
  simp only [kantenBild, hfr]
  rfl

/-! ## The counter cell: `World` reads as `Zahl` states -/

/-- Read an `.int 0 255` cell as its value. The cast is the same `▸`
    idiom `eval` uses; no value is invented. -/
def zellenLesen (t_c : D.Tab) (kc : Int) (f_c : D.Feld t_c)
    (hf : D.typ t_c f_c = .int 0 255) (σ : World D) : Zahl 0 255 :=
  (hf ▸ σ.slots t_c kc f_c : Wert D (.int 0 255))

/-- Precondition map over the cell: call `k` may run while `k < 64`
    and the counter is below 16 (the unrolled tick indices). -/
def zahlVor : Nat → Zahl 0 255 → Bool
  | k, z => decide (k < 64 ∧ z.n < 16)

/-- Step map over the cell: advance modulo 16. -/
def zahlNach : Nat → Zahl 0 255 → Zahl 0 255
  | _, z =>
    have hlo := z.lo_le
    ⟨(z.n + 1) % 16, by omega, by omega⟩

/-- Invariant over the cell: the counter stays below 16. -/
def zahlInv : Zahl 0 255 → Bool
  | z => decide (z.n < 16)

/-- The step map computes what it says. -/
theorem zahlNach_wert (k : Nat) (z : Zahl 0 255) :
    (zahlNach k z).n = (z.n + 1) % 16 := by
  simp [zahlNach]

/-- Uniform tick contract over any `Zahl 0 255` state: from every state
    below 16 (`k < 64` is the tick index bound, used by `vor`) each call
    may run and the next state stays below 16. The `RufKette` instance
    at `S := Zahl 0 255` -- no duplication of the induction. -/
theorem zahl_tick_vertrag :
    ∀ k z, k < 64 → zahlInv z = true → zahlVor k z = true ∧
      zahlInv (zahlNach k z) = true := by
  intro k z hk hs
  have hslt : z.n < 16 := by simpa [zahlInv] using hs
  constructor
  · simp [zahlVor, hk, hslt]
  · have hmod : (z.n + 1) % 16 < 16 := by omega
    have e : (zahlNach k z).n = (z.n + 1) % 16 := zahlNach_wert k z
    simp [zahlInv, e, hmod]

/-! ## Fixture: three slots, one edge field, one counter field -/

/-- Two fields: the tree edge and the round counter. -/
inductive KettenFeld | Kante | Zaehler deriving DecidableEq

/-- Minimal declaration in the `swD` shape (`SyscallPaarung.lean:157`):
    one unshared table with 3 slots, an `option index` edge field and
    an int counter field; everything else empty. -/
def kettenD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 3
  Feld := fun _ => KettenFeld
  decFeld := fun _ => inferInstance
  typ := fun _ f => match f with
    | .Kante => .opt 3
    | .Zaehler => .int 0 255
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun g => nomatch g
  nutzlast := fun g => nomatch g
  atomar := fun g => nomatch g
  geteilt := fun _ => false
  ggeteilt := fun g => nomatch g
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => nomatch m
  braucht := fun _ => []
  gbraucht := fun g => nomatch g
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ =>
    { params := []
      erg := none
      gruende := 0
      haelt := []
      schreibt := fun _ => true
      gschreibt := fun g => nomatch g
      konsumiert := []
      produziert := [] }
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Unit
  aparams := fun _ => []
  aerg := fun _ => none
  aschreibt := fun _ _ => true
  agschreibt := fun _ g => nomatch g
  Reg := Empty
  rtyp := fun r => nomatch r
  rklasse := fun r => nomatch r
  spiegel := fun r => nomatch r
  rzusage := fun r => nomatch r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g => nomatch g

/-! ## Witnesses: a real chain, a real write, a refuted stale view -/

/-- The edge field reads as the chain 0 → 1 → 2; the counter is 0. -/
def kettenWelt : World kettenD :=
  { slots := fun _ k f =>
      match f with
      | .Kante =>
        match k with
        | 0 => some ⟨1, by decide, by decide⟩
        | 1 => some ⟨2, by decide, by decide⟩
        | _ => none
      | .Zaehler => ⟨0, by decide, by decide⟩
    globs := fun g => nomatch g
    spur := [] }

/-- The edge field's type equation, by computation. -/
theorem hfKante : kettenD.typ () .Kante = .opt (kettenD.count ()) := rfl

/-- Witness (non-degenerate): writing the counter at slot 1 leaves the
    edge map at slot 0 untouched -- the generic commutation at work. -/
theorem ketten_rahmen_zeuge :
    kantenBild kettenD
      (kettenWelt.storeSlot () 1 .Zaehler ⟨7, by decide, by decide⟩)
      () .Kante hfKante 0
      = kantenBild kettenD kettenWelt () .Kante hfKante 0 :=
  kantenBild_slotfeld_anders kettenWelt () .Kante hfKante 0 1 .Zaehler _
    (Or.inl (by decide))

/-- The write takes effect: clearing the edge at slot 0 empties it. -/
theorem ketten_schreibt_zeuge :
    ((kantenBild kettenD (kettenWelt.storeSlot () 0 .Kante none)
      () .Kante hfKante 0).map Zahl.n)
      = none := by
  decide

/-- Planted failure: a projection that ignores the edge-clearing write
    is refuted -- stale `some 1` against fresh `none`. -/
theorem ketten_starr_widerlegt :
    ((kantenBild kettenD kettenWelt () .Kante hfKante 0).map Zahl.n)
      ≠ ((kantenBild kettenD (kettenWelt.storeSlot () 0 .Kante none)
        () .Kante hfKante 0).map Zahl.n) := by
  decide

/-- Witness (non-degenerate, part (a) capstone): 64 ticks from counter
    0 keep the counter below 16 -- the `RufKette` instance at
    `S := Zahl 0 255`, one lemma application. -/
theorem ketten_tick_zeuge :
    zahlInv (rufLauf (⟨64, zahlVor, zahlNach⟩ : RufKette (Zahl 0 255)) 64 0
      ⟨0, by decide, by decide⟩)
      = true :=
  rufKette_invariant (S := Zahl 0 255) ⟨64, zahlVor, zahlNach⟩ zahlInv
    zahl_tick_vertrag 64 0 _ (by decide) (by decide)

/-- Witness (per-call contract on a real world): ticking the counter
    cell of `kettenWelt` keeps it below 16. -/
theorem ketten_tick_schritt_zeuge :
    decide (((kettenWelt.storeSlot () 0 .Zaehler ⟨1, by decide, by decide⟩).slots
      () 0 .Zaehler).n < 16) = true := by
  decide

/-
   CUTS: what is not proved.
   - Proved: the missing `storeSlot` frame (`storeSlot_anders`, same
     table, other slot or other field) beside the accepted
     `seite_rahmen_fremd` and `schreibSlot_slots_other`; the edge-map
     projection `kantenBild` (`eval .reaches`'s lambda) commuting with
     foreign-table and same-table-elsewhere stores, pointwise;
     the int-cell reader with the uniform Zahl tick contract
     (`zahl_tick_vertrag`, the `RufKette` instance at `Zahl 0 255`);
     the `kettenD` fixture (3 slots, edge + counter) with frame,
     write-takes-effect, stale-refuted and 64-tick witnesses.
   - Only stated: `kettenD`/`kettenWelt` as fixture shapes.
   - Not modelled: threading 64 world-steps into one world run (each
     single step is bridged; the run induction over `World`s is open);
     the full `TreeState` projection (needs a `benutzt` bool cell --
     named remainder of (b)); fuel completeness; `GvTraversal`/
     `GvSplits`/`GvParserFragment` reconciliation (not in this clone).
   - No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` anywhere; every
     premise is used; no premise has type `Prop` itself.
-/

#print axioms storeSlot_anders
#print axioms kantenBild_tabelle_anders
#print axioms kantenBild_slotfeld_anders
#print axioms zahl_tick_vertrag
#print axioms ketten_tick_zeuge

end Gabbro.Grammatik.GabbroV
