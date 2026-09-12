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
import Grammatik.InterferenzAllgemein
import Grammatik.ReferenzB

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

/-- The witness step stays in the writer's frame: `einzahlen` may write
    the whole table, so every successor pair agrees outside `false`. -/
theorem zbSchritt_rahmen :
    Rahmen (refD.schreibt (zbCode 1)) (refD.gschreibt (zbCode 1)) zbW0 zbW1 := by
  constructor
  · intro t ht _ _
    cases t
    have htrue : refD.schreibt (zbCode 1) () = true := rfl
    rw [htrue] at ht
    simp at ht
  · intro g
    exact nomatch g

/-- The witness chain: two threads, one step by the writer, empty run. -/
def zbJ : GemeinsamerLauf (D := refD) zbNb where
  faeden := [0, 1]
  code := zbCode
  eintritt := zbEintritt
  welten := [zbW0, zbW1]
  schrittFaden := [1]
  l := ([] : Lauf refD)
  hKette := rfl
  hSchritt := by
    intro k f' vor nach hk hv hn
    cases k with
    | zero =>
      simp at hk hv hn
      subst hk
      subst hv
      subst hn
      exact ⟨by simp, zbSchritt_rahmen⟩
    | succ k => simp at hk
  hPaar := by
    intro f' hf' g hg' hne
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hf' hg'
    rcases hf' with rfl | rfl <;> rcases hg' with rfl | rfl
    · exact absurd rfl hne
    · exact True.intro
    · exact True.intro
    · exact absurd rfl hne
  hGesittet := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro f j
      have hsp : Lauf.spur ([] : Lauf refD) f j = [] := by simp [Lauf.spur]
      rw [hsp]
      exact konsistent_nil
    · intro f j e he
      have hsp : Lauf.spur ([] : Lauf refD) f j = [] := by simp [Lauf.spur]
      rw [hsp] at he
      simp at he
    · intro j f L h hi g hne
      simp at hi
    · intro i j f g m s s' ei ej hi hj hm hm'
      simp at hi
    · intro i j f g o ei ej hi hj ht1 ht2 hu
      simp at hi
  hBeschraenkt := by
    intro i j f g ei ej hi hj hne
    simp at hi
  hEintritt := by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hf
    rcases hf with rfl | rfl
    · show EintrittPasst refLies zbWE
      show HeldGenau (Signatur.anfang refD (refD.signatur refLies)) zbWE.haelt
      rw [refLies_start]
      exact zbWE_haelt
    · show EintrittPasst refEin zbWE
      show HeldGenau (Signatur.anfang refD (refD.signatur refEin)) zbWE.haelt
      rw [refEin_start]
      exact zbWE_haelt
  hSchuld := by
    intro f hf i _
    exact nomatch i
  hInvSicht := by
    intro f hf i _
    exact nomatch i

/-- Projections of the witness chain, by computation. -/
theorem zbJ_welten : zbJ.welten = [zbW0, zbW1] := rfl

/-- Projections of the witness chain, by computation. -/
theorem zbJ_schritt : zbJ.schrittFaden = [1] := rfl

/-- Projections of the witness chain, by computation. -/
theorem zbJ_faeden : zbJ.faeden = [0, 1] := rfl

/-- `Q` holds at the head world: both read slots are `0`. -/
theorem zbQ_W0 (f : Faden) : zbQ f zbW0 := rfl

/-- `Q` holds at the end world: slots 0 and 1 are untouched by the
    slot-5 write. -/
theorem zbQ_W1 (f : Faden) : zbQ f zbW1 := by
  show (if (0 : Int) = 5 then zbV7 else zbV0) =
    (if (1 : Int) = 5 then zbV7 else zbV0)
  rw [if_neg (by decide), if_neg (by decide)]

/-- Head validity on the witness chain. -/
theorem zbKopf : ∀ f ∈ zbJ.faeden, ∀ σ₀, zbJ.welten[0]? = some σ₀ → zbQ f σ₀ := by
  intro f hf σ₀ h
  rw [zbJ_welten] at h
  simp at h
  subst h
  rw [zbJ_faeden] at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact zbQ_W0 0
  · exact zbQ_W0 1

/-- Own-step preservation on the witness chain: the only step is thread 1's
    slot-5 write, which leaves `Q`'s slots alone. (`hQvor` is carried for
    shape; the step preserves `Q` by computation.) -/
theorem zbEigen : ∀ f ∈ zbJ.faeden, ∀ (k : Nat) (vor nach : World refD),
    zbJ.schrittFaden[k]? = some f → zbJ.welten[k]? = some vor →
      zbJ.welten[k + 1]? = some nach → zbQ f vor → zbQ f nach := by
  intro f hf k vor nach hk hv hn hQvor
  rw [zbJ_schritt] at hk
  rw [zbJ_welten] at hv hn
  rw [zbJ_faeden] at hf
  cases k with
  | zero =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · simp at hk
    · simp at hk hv hn
      subst hv
      subst hn
      exact zbQ_W1 1
  | succ k => simp at hk

/-- Foreign-step preservation on the witness chain: the only foreign step
    (thread 1, seen from thread 0) is the slot-5 write. (`hQvor` is carried
    for shape; preservation is by computation.) -/
theorem zbStabil : ∀ f ∈ zbJ.faeden, ∀ (k : Nat) (g : Faden) (vor nach : World refD),
    g ∈ zbJ.faeden → g ≠ f → zbJ.schrittFaden[k]? = some g →
      zbJ.welten[k]? = some vor → zbJ.welten[k + 1]? = some nach →
      zbQ f vor → zbQ f nach := by
  intro f hf k g vor nach hgm hne hk hv hn hQvor
  rw [zbJ_schritt] at hk
  rw [zbJ_welten] at hv hn
  rw [zbJ_faeden] at hgm hf
  cases k with
  | zero =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgm hf
    rcases hgm with rfl | rfl
    · simp at hk
    · simp at hk hv hn
      subst hv
      subst hn
      rcases hf with rfl | rfl
      · exact zbQ_W1 0
      · exact absurd rfl hne
  | succ k => simp at hk

/-- Every witness thread holds exactly the guard, by computation. -/
theorem zbHaelt (f : Faden) (hf : f ∈ zbJ.faeden) :
    refD.haelt (zbCode f) = [()] := by
  rw [zbJ_faeden] at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl <;> rfl

/-- The writer writes the table; the reader writes nothing. -/
theorem zbSchreibtEin : refD.schreibt (zbCode 1) () = true := rfl

/-- The writer writes the table; the reader writes nothing. -/
theorem zbSchreibtLies : refD.schreibt (zbCode 0) () = false := rfl

/-- Slot-level dependence of `Q`: slots 0 and 1 fix both sides. (The
    global agreement is carried for shape; `refD` has no globals.) -/
theorem zbDep : ∀ f ∈ zbJ.faeden, ∀ σ σ' : World refD,
    (∀ (t : refD.Tab) (k : Int) (fld : refD.Feld t),
      zbSf f t k fld → σ'.slots t k fld = σ.slots t k fld) →
    (∀ x : refD.Glob, zbGf f x = true → σ'.globs x = σ.globs x) →
    (zbQ f σ ↔ zbQ f σ') := by
  intro f _ σ σ' hs hGlob
  constructor
  · intro h
    show σ'.slots () 0 () = σ'.slots () 1 ()
    rw [hs () 0 () ⟨rfl, Or.inl rfl⟩, hs () 1 () ⟨rfl, Or.inr rfl⟩]
    exact h
  · intro h
    show σ.slots () 0 () = σ.slots () 1 ()
    rw [← hs () 0 () ⟨rfl, Or.inl rfl⟩, ← hs () 1 () ⟨rfl, Or.inr rfl⟩]
    exact h

/-- The table footprint: the whole shared table. -/
def zbWf : Faden → refD.Tab → Bool := fun _ _ => true

/-- Every read slot lies in the footprint table. -/
theorem zbCover : ∀ f ∈ zbJ.faeden, ∀ (t : refD.Tab) (k : Int) (fld : refD.Feld t),
    zbSf f t k fld → zbWf f t = true := by
  intro f _ t k fld _
  rfl

/-- Static guarantee on the witness chain: the only writer of `Q`'s
    table is thread 1, writing under the guard both threads hold. (The
    disequality and the slot index are carried for shape.) -/
theorem zbWacheT : ∀ (f g : Faden), f ∈ zbJ.faeden → g ∈ zbJ.faeden → g ≠ f →
    ∀ (t : refD.Tab) (k : Int) (fld : refD.Feld t),
      zbSf f t k fld → refD.schreibt (zbCode g) t = true →
      ∃ L : refD.Lock, Bewacht (D := refD) (.inl t) L ∧ L ∈ refD.haelt (zbCode f) ∧
        L ∈ refD.haelt (zbCode g) := by
  intro f g hf hg hne t k fld hSf hwrite
  rw [zbJ_faeden] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · cases t
    rw [zbSchreibtLies] at hwrite
    simp at hwrite
  · obtain ⟨rfl, _⟩ := hSf
    refine ⟨(), List.Mem.head _, ?_, ?_⟩
    · rw [zbHaelt f hf]
      exact List.mem_singleton.mpr rfl
    · have hg1 : (1 : Faden) ∈ zbJ.faeden := by simp [zbJ_faeden]
      rw [zbHaelt 1 hg1]
      exact List.mem_singleton.mpr rfl

/-- No globals exist, so the global guard holds vacuously. (Premises
    carried for shape.) -/
theorem zbWacheG : ∀ (f g : Faden), f ∈ zbJ.faeden → g ∈ zbJ.faeden → g ≠ f →
    ∀ x : refD.Glob, zbGf f x = true → refD.gschreibt (zbCode g) x = true →
      ∃ L : refD.Lock, Bewacht (D := refD) (.inr x) L ∧ L ∈ refD.haelt (zbCode f) ∧
        L ∈ refD.haelt (zbCode g) := by
  intro f hf g hg hne x hx hwrite
  exact nomatch x

/-- Per-step rely on the witness chain: the guarded slot-5 write leaves
    `Q`'s slots 0 and 1 alone. (Guard, holdings, and disequality carried
    for shape; agreement is by computation.) -/
theorem zbRelyT : ∀ (f : Faden), f ∈ zbJ.faeden → ∀ (k : Nat) (g : Faden) (vor nach : World refD),
    g ∈ zbJ.faeden → g ≠ f → zbJ.schrittFaden[k]? = some g →
      zbJ.welten[k]? = some vor → zbJ.welten[k + 1]? = some nach →
      ∀ (t : refD.Tab) (k' : Int) (fld : refD.Feld t),
        zbSf f t k' fld → refD.schreibt (zbCode g) t = true →
        ∀ (L : refD.Lock), Bewacht (D := refD) (.inl t) L → L ∈ refD.haelt (zbCode f) →
          L ∈ refD.haelt (zbCode g) → nach.slots t k' fld = vor.slots t k' fld := by
  intro f hf k g vor nach hgm hne hk hv hn t k' fld hSf hwrite L hL hLf hLg
  rw [zbJ_schritt] at hk
  rw [zbJ_welten] at hv hn
  cases k with
  | zero =>
    simp at hk hv hn
    subst hv
    subst hn
    obtain ⟨rfl, hk' | hk'⟩ := hSf
    · subst hk'
      show (if (0 : Int) = 5 then zbV7 else zbV0) = zbV0
      rw [if_neg (by decide)]
    · subst hk'
      show (if (1 : Int) = 5 then zbV7 else zbV0) = zbV0
      rw [if_neg (by decide)]
  | succ k => simp at hk

/-- No globals exist, so the global rely holds vacuously. (Premises
    carried for shape.) -/
theorem zbRelyG : ∀ (f : Faden), f ∈ zbJ.faeden → ∀ (k : Nat) (g : Faden) (vor nach : World refD),
    g ∈ zbJ.faeden → g ≠ f → zbJ.schrittFaden[k]? = some g →
      zbJ.welten[k]? = some vor → zbJ.welten[k + 1]? = some nach →
      ∀ x : refD.Glob, zbGf f x = true → refD.gschreibt (zbCode g) x = true →
        ∀ (L : refD.Lock), Bewacht (D := refD) (.inr x) L → L ∈ refD.haelt (zbCode f) →
          L ∈ refD.haelt (zbCode g) → nach.globs x = vor.globs x := by
  intro f hf k g vor nach hgm hne hk hv hn x hx hwrite L hL hLf hLg
  exact nomatch x

/-- The witness step really wrote slot 5. -/
theorem zbW1_slot5 : zbW1.slots () 5 () = zbV7 := by
  show (if (5 : Int) = 5 then zbV7 else zbV0) = zbV7
  rw [if_pos rfl]

/-- Slot 5 was `0` at the head. -/
theorem zbW0_slot5 : zbW0.slots () 5 () = zbV0 := rfl

/-- Memory really moved: slot 5 reads `7`, the head reads `0`. -/
theorem zbMemMoved : zbW1.slots () 5 () ≠ zbW0.slots () 5 () := by
  intro hcon
  rw [zbW1_slot5, zbW0_slot5] at hcon
  have hn := congrArg Zahl.n hcon
  simp [zbV7, zbV0] at hn

/-- A function of the witness writes the shared table. -/
theorem zbSchreibt : TraegerSchreibt (zbCode 1) (.inl ()) = true :=
  zbSchreibtEin

/-- **Inhabitation for `stabil_ohne_form`.** All premises hold jointly on
    the two-thread witness chain: head validity, own-step and foreign-step
    preservation of `slot 0 = slot 1` -- plus non-degeneracy (a function
    writes the shared table; the step moves slot 5). -/
theorem stabil_ohne_form_zeuge :
    (∀ f ∈ zbJ.faeden, ∀ (k : Nat) (σ : World refD),
      zbJ.welten[k]? = some σ → zbQ f σ) ∧
    TraegerSchreibt (zbCode 1) (.inl ()) = true ∧
    zbW1.slots () 5 () ≠ zbW0.slots () 5 () :=
  ⟨stabil_ohne_form zbNb zbJ zbQ zbKopf zbEigen zbStabil,
    zbSchreibt, zbMemMoved⟩

/-- **Inhabitation for `stabil_aus_bewachung`.** All premises hold jointly
    on the witness chain: slot dependence, the static guard guarantee, the
    per-step rely -- plus the derived checker shape (`HaengtAb`) and
    non-degeneracy (a function writes the shared table; the step moves
    slot 5 while `Q` reads slots 0 and 1). -/
theorem stabil_aus_bewachung_zeuge :
    (∀ f ∈ zbJ.faeden, ∀ (k : Nat) (g : Faden) (vor nach : World refD),
      g ∈ zbJ.faeden → g ≠ f → zbJ.schrittFaden[k]? = some g →
        zbJ.welten[k]? = some vor → zbJ.welten[k + 1]? = some nach →
        zbQ f vor → zbQ f nach) ∧
    (∀ f ∈ zbJ.faeden, HaengtAb (zbWf f) (zbGf f) (zbQ f)) ∧
    TraegerSchreibt (zbCode 1) (.inl ()) = true ∧
    zbW1.slots () 5 () ≠ zbW0.slots () 5 () :=
  ⟨stabil_aus_bewachung zbNb zbJ zbQ zbSf zbGf zbDep zbWacheT zbWacheG zbRelyT zbRelyG,
    haengtAb_aus_slotDep zbNb zbJ zbQ zbSf zbWf zbGf zbDep zbCover,
    zbSchreibt, zbMemMoved⟩

/-! ## CUTS: what is not proved here

  (S1) Table-level `HaengtAb` alone does not suffice for `hStabil`, and is
    therefore not the working premise: a foreign write to another slot of
    the same table breaks table-level frame agreement while preserving `Q`,
    so no theorem from table-level `HaengtAb` plus the guard story alone can
    conclude foreign-step preservation without slot information. The slot
    read-set `Sf` (checker-computable in principle, like `orte`) and the
    slot-level dependence/rely are the unavoidable extra premises; table
    `HaengtAb` is derived (`haengtAb_aus_slotDep`), not assumed.
  (S2) No mutual exclusion is derived: the rely (a guarded foreign write
    leaves `Q`'s slots alone in this step) arrives per step and is not
    proved from the guard -- the model has no mutual-exclusion theorem over
    `haelt` lists (`LesenStabil` L1 carries over). The guarantee (foreign
    writes only under a co-held guard) is static and checker-dischargeable;
    the rely is memory-level slot agreement, checker-comparable per run.
    What the theorems remove is assertion-level per-step reasoning.
  (S3) One direction only: stability never concludes the backward leg, so
    break-and-restore across a step stays excluded by shape (the `hBlattAll`
    B5 boundary).
  (S4) Own-step preservation (`hEigen`) is assumed, not executed (G7
    carries over): sequential-logic adequacy belongs to another lane.
  (S5) The witness is a single-step two-thread chain; `Q` (`slot 0 =
    slot 1`) stands for "my slot equals my local counter". That `Q` is not
    of invariant form is documented by shape (it constrains two slots while
    the table keeps changing elsewhere), not proved as a negation over all
    `TraegerInv`. The witness `Q`-assumptions are carried for exact shape
    match and discharged by computation on concrete worlds.
-/

#print axioms Gabbro.Grammatik.stabil_ohne_form_zeuge
#print axioms Gabbro.Grammatik.stabil_aus_bewachung_zeuge

end Gabbro.Grammatik
