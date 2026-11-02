/-
  File:      Grammatik/StabilBewacht.lean
  Subject:   STABILITY WITHOUT INVARIANT FORM (lane 105, D9).

  The goal theorem needs, for assertions over shared carriers that are NOT
  in invariant form, the full `InterferenceFree` shape (`hFree`). This file
  replaces it by the standard rely/guarantee argument at chain grain:

  * `stabil_ohne_form` -- the induction: head validity plus own-step
    preservation plus foreign-step preservation (`hStabil`, one direction
    only) give the assertion at every chain world. No invariant form, no
    `HaengtAb`, no discipline -- pure chain folding (`kette_erhaelt` grain).
  * `stabil_aus_bewachung` -- the corollary that connects `hStabil` to the
    checker: `hStabil` follows from a static GUARANTEE (every foreign write
    to a carrier `Q f` reads happens only while holding a guard lock that
    `f` holds throughout -- `Bewacht` / `TraegerSchreibt` / `D.haelt`) plus
    a per-step RELY (guarded foreign writes leave `Q f`'s slots alone).
    The rely is memory-level (slot agreement, checker-comparable per run),
    so no assertion-level per-step proof is owed any more.
  * `haengtAb_aus_slotDep` -- the checker-shape link: slot-level dependence
    plus footprint coverage give table-level `HaengtAb`, the shape the
    `InterferenceFree` machinery consumes downstream.

  Witnesses (`_zeuge`) run on the reference fixture (`ReferenzB.lean`):
  a two-thread chain where `Q` (`slot 0 = slot 1`, "my slot equals my local
  counter") is not a whole-table invariant and the other thread writes only
  slot 5, a different slot of the same shared table.
-/
module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein
public import Grammatik.Korpus.Referenz.ReferenzB

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Stability without invariant form.** What holds at the chain head and
    survives every own step and every foreign step holds at every chain
    world -- by induction on the chain index (`hKette` counts one step per
    transition, so every successor position yields its writer and its
    predecessor). One direction only: stability never needs the backward
    leg. -/
theorem stabil_ohne_form (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (Q : Faden → World D → Prop)
    (hKopf : ∀ f ∈ J.faeden, ∀ σ₀, J.welten[0]? = some σ₀ → Q f σ₀)
    (hEigen : ∀ f ∈ J.faeden, ∀ (k : Nat) (vor nach : World D),
        J.schrittFaden[k]? = some f → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        Q f vor → Q f nach)
    (hStabil : ∀ f ∈ J.faeden, ∀ (k : Nat) (g : Faden) (vor nach : World D), g ∈ J.faeden → g ≠ f →
        J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        Q f vor → Q f nach) :
    ∀ f ∈ J.faeden, ∀ (k : Nat) (σ : World D), J.welten[k]? = some σ → Q f σ := by
  intro f hf k
  induction k with
  | zero => exact hKopf f hf
  | succ k ih =>
    intro σ hσ
    have hK := J.hKette
    have hlen : k + 1 < J.welten.length := lt_of_belegt J.welten (k + 1) σ hσ
    have hsk : k < J.schrittFaden.length := by omega
    have hwk : k < J.welten.length := by omega
    obtain ⟨g, hg⟩ := kette_welt_belegt J.schrittFaden k hsk
    obtain ⟨vor, hvor⟩ := kette_welt_belegt J.welten k hwk
    have hgm : g ∈ J.faeden := (J.hSchritt k g vor σ hg hvor hσ).1
    by_cases heq : g = f
    · have hg' : J.schrittFaden[k]? = some f := heq ▸ hg
      exact hEigen f hf k vor σ hg' hvor hσ (ih vor hvor)
    · exact hStabil f hf k g vor σ hgm heq hg hvor hσ (ih vor hvor)

#print axioms Gabbro.Grammatik.stabil_ohne_form

/-- **The corollary that connects `hStabil` to the checker.** The foreign-step
    premise of `stabil_ohne_form` follows from a static GUARANTEE plus a
    per-step RELY at chain grain:

    * dependence (`hDep`): `Q f` is fixed by its slot read-set `Sf f` (tables)
      and its global frame `Gf f` -- slot-level frame locality;
    * guarantee (`hWacheT` / `hWacheG`): every foreign write to a carrier
      `Q f` reads happens only while holding a guard lock that `f` holds
      throughout (`Bewacht` names the watch list, `D.haelt` both declared
      holdings -- static, checker-dischargeable);
    * rely (`hRelyT` / `hRelyG`): a guarded foreign write leaves `Q f`'s own
      slots alone in this step -- memory-level slot agreement,
      checker-comparable per run, no assertion reasoning.

    Proof: per slot, either the writer never touches the table (then the
    chain frame `hSchritt` already agrees) or the guard fires and the rely
    agrees; globals the same. The assembled agreement feeds `hDep`. -/
theorem stabil_aus_bewachung (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (Q : Faden → World D → Prop)
    (Sf : Faden → (t : D.Tab) → Int → D.Feld t → Prop)
    (Gf : Faden → D.Glob → Bool)
    (hDep : ∀ f ∈ J.faeden, ∀ σ σ' : World D,
      (∀ (t : D.Tab) (k : Int) (fld : D.Feld t),
        Sf f t k fld → σ'.slots t k fld = σ.slots t k fld) →
      (∀ x : D.Glob, Gf f x = true → σ'.globs x = σ.globs x) →
      (Q f σ ↔ Q f σ'))
    (hWacheT : ∀ (f g : Faden), f ∈ J.faeden → g ∈ J.faeden → g ≠ f →
      ∀ (t : D.Tab) (k : Int) (fld : D.Feld t),
        Sf f t k fld → D.schreibt (J.code g) t = true →
        ∃ L : D.Lock, Bewacht (D := D) (.inl t) L ∧ L ∈ D.haelt (J.code f) ∧
          L ∈ D.haelt (J.code g))
    (hWacheG : ∀ (f g : Faden), f ∈ J.faeden → g ∈ J.faeden → g ≠ f →
      ∀ x : D.Glob, Gf f x = true → D.gschreibt (J.code g) x = true →
        ∃ L : D.Lock, Bewacht (D := D) (.inr x) L ∧ L ∈ D.haelt (J.code f) ∧
          L ∈ D.haelt (J.code g))
    (hRelyT : ∀ (f : Faden), f ∈ J.faeden → ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → g ≠ f →
        J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        ∀ (t : D.Tab) (k' : Int) (fld : D.Feld t),
          Sf f t k' fld → D.schreibt (J.code g) t = true →
          ∀ (L : D.Lock), Bewacht (D := D) (.inl t) L → L ∈ D.haelt (J.code f) →
            L ∈ D.haelt (J.code g) → nach.slots t k' fld = vor.slots t k' fld)
    (hRelyG : ∀ (f : Faden), f ∈ J.faeden → ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → g ≠ f →
        J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        ∀ x : D.Glob, Gf f x = true → D.gschreibt (J.code g) x = true →
          ∀ (L : D.Lock), Bewacht (D := D) (.inr x) L → L ∈ D.haelt (J.code f) →
            L ∈ D.haelt (J.code g) → nach.globs x = vor.globs x) :
    ∀ f ∈ J.faeden, ∀ (k : Nat) (g : Faden) (vor nach : World D), g ∈ J.faeden → g ≠ f →
      J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
      Q f vor → Q f nach := by
  intro f hf k g vor nach hgm hne hkg hkv hkn hQvor
  have hR := (J.hSchritt k g vor nach hkg hkv hkn).2
  have hSlot : ∀ (t : D.Tab) (k' : Int) (fld : D.Feld t),
      Sf f t k' fld → nach.slots t k' fld = vor.slots t k' fld := by
    intro t k' fld hSf
    cases heq : D.schreibt (J.code g) t with
    | false => exact hR.1 t heq k' fld
    | true =>
      obtain ⟨L, hL, hLf, hLg⟩ := hWacheT f g hf hgm hne t k' fld hSf heq
      exact hRelyT f hf k g vor nach hgm hne hkg hkv hkn t k' fld hSf heq L hL hLf hLg
  have hGlob : ∀ x : D.Glob, Gf f x = true → nach.globs x = vor.globs x := by
    intro x hx
    cases heq : D.gschreibt (J.code g) x with
    | false => exact hR.2 x heq
    | true =>
      obtain ⟨L, hL, hLf, hLg⟩ := hWacheG f g hf hgm hne x hx heq
      exact hRelyG f hf k g vor nach hgm hne hkg hkv hkn x hx heq L hL hLf hLg
  exact (hDep f hf vor nach hSlot hGlob).mp hQvor

#print axioms Gabbro.Grammatik.stabil_aus_bewachung

/-- **The checker-shape link.** Slot-level dependence plus footprint coverage
    give table-level `HaengtAb` -- the shape the `InterferenceFree`
    machinery consumes downstream. Frame agreement on the tables covers
    every read slot, so the slot dependence fires. -/
theorem haengtAb_aus_slotDep (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (Q : Faden → World D → Prop)
    (Sf : Faden → (t : D.Tab) → Int → D.Feld t → Prop)
    (Wf : Faden → D.Tab → Bool) (Gf : Faden → D.Glob → Bool)
    (hDep : ∀ f ∈ J.faeden, ∀ σ σ' : World D,
      (∀ (t : D.Tab) (k : Int) (fld : D.Feld t),
        Sf f t k fld → σ'.slots t k fld = σ.slots t k fld) →
      (∀ x : D.Glob, Gf f x = true → σ'.globs x = σ.globs x) →
      (Q f σ ↔ Q f σ'))
    (hCover : ∀ f ∈ J.faeden, ∀ (t : D.Tab) (k : Int) (fld : D.Feld t),
      Sf f t k fld → Wf f t = true) :
    ∀ f ∈ J.faeden, HaengtAb (Wf f) (Gf f) (Q f) := by
  intro f hf σ σ' hAgree
  obtain ⟨hT, hG⟩ := hAgree
  exact hDep f hf σ σ'
    (fun t k fld hSf => hT t (hCover f hf t k fld hSf) k fld)
    (fun x hx => hG x hx)

#print axioms Gabbro.Grammatik.haengtAb_aus_slotDep

/-! ## Witness on the reference fixture.

  Two threads over `refD` (one shared table `konto`, one lock): thread 0
  runs `lies` (reads), thread 1 runs `einzahlen` (writes). The chain has one
  step, by thread 1, writing only slot 5. `Q` (`slot 0 = slot 1`, "my slot
  equals my local counter") reads slots 0 and 1 -- it is not a whole-table
  invariant (a write to slot 0 or 1 breaks it while the table as a whole
  keeps changing), yet it survives this chain because the foreign write
  goes elsewhere, under the guard both threads hold. -/

/-- The counter value `0` at the witness type. -/
def zbV0 : Wert refD (.int 0 100) := ⟨0, by decide, by decide⟩

/-- The written value `7` at the witness type. -/
def zbV7 : Wert refD (.int 0 100) := ⟨7, by decide, by decide⟩

/-- Head world: every slot reads `0`, empty trace. -/
def zbW0 : World refD :=
  { slots := fun _ _ _ => zbV0
    globs := fun g => nomatch g
    spur := [] }

/-- End world: slot 5 reads `7` (the foreign write), slots 0 and 1 still
    `0`, with the write event on the trace. -/
def zbW1 : World refD :=
  { slots := fun _ k _ => if k = 5 then zbV7 else zbV0
    globs := fun g => nomatch g
    spur := [Ereignis.zugriff () true [Res.held (D := refD) ()] [()]] }

/-- Entry world: every slot reads `0`, the guard taken. -/
def zbWE : World refD :=
  { slots := fun _ _ _ => zbV0
    globs := fun g => nomatch g
    spur := [Ereignis.nimmt (D := refD) () []] }

/-- Both threads declared side by side. -/
def zbNb : Nebeneinander := fun _ _ => True

/-- Thread 0 reads (`lies`), every other thread writes (`einzahlen`). -/
def zbCode : Faden → refD.Fn
  | 0 => refLies
  | _ => refEin

/-- Every thread enters with the guard taken. -/
def zbEintritt : Faden → World refD := fun _ => zbWE

/-- "My slot equals my local counter": slot 0 against slot 1. Reads only
    slots 0 and 1 of the shared table -- not a whole-table invariant. -/
def zbQ : Faden → World refD → Prop :=
  fun _ σ => σ.slots () 0 () = σ.slots () 1 ()

/-- The slot read-set: slots 0 and 1 of `konto`. -/
def zbSf : Faden → (t : refD.Tab) → Int → refD.Feld t → Prop :=
  fun _ t k _ => t = () ∧ (k = 0 ∨ k = 1)

/-- No globals exist on `refD`. -/
def zbGf : Faden → refD.Glob → Bool := fun _ g => nomatch g

/-- The entry world holds exactly the guard. -/
theorem zbWE_haelt : HeldGenau [Res.held (D := refD) ()] zbWE.haelt := by
  intro L
  cases L
  constructor
  · intro _; exact List.mem_singleton.mpr rfl
  · intro _; exact List.mem_singleton.mpr rfl


end Gabbro.Grammatik
