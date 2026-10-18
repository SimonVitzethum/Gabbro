import Grammatik.Code.Conc.Shared
import Grammatik.Code.Conc.Witness

/-
  File:      Grammatik/Code/Conc/SharedWitness.lean
  Subject:   TRACK L, PHASE L3 -- WITNESSES that the relaxed representation and the GX interface are not vacuous.

  On the declaration of `Conc/Witness.lean` (one table, ONE atomic global holding a machine word) at the 64-bit target:
    * `cLayOk` -- the layout assumptions hold, with the global SHARED (`shAtomic` needs it atomic: it is);
    * `rep_free_witness` -- a world in which the shared global holds 5 and a memory in which its cell holds 0 satisfy
      `Rep`: the relaxation is real, not an empty hypothesis;
    * `rep_strong_fails` -- the same pair does NOT satisfy `Rep` once the global is not shared: the cell is tied there;
    * `shared_read_refused` -- a plain read of a shared global is refused by `lowerE` (only `await` reads it);
    * `sees_shared_witness` -- the interface answers a value the memory does not hold.
-/

namespace Gabbro.Code.Lower.WitC

open Gabbro.Grammatik

section C64

local instance confS64 : Conf := ⟨64, false, Or.inr rfl⟩

/-- The same layout with the global NOT shared. -/
def cLayN : Layout cD := { cLay with shared := fun _ => false }

theorem cLayOk : LayoutOk cLay where
  tab := fun _ => rfl
  fld := fun t f _ => by cases t; cases f; exact ⟨0, by decide +kernel⟩
  inj := fun _ _ _ _ _ _ => rfl
  tinj := fun _ _ _ => rfl
  gdis := fun t g => by cases t; cases g; decide
  ginj := fun _ _ _ => rfl
  shAtomic := fun _ _ => rfl
  fsm := fun _ _ => Nat.two_pow_pos _

/-- The table block (one byte) and the word cell of the global, both zero. -/
def mem0 : Mem := ((Mem.alloc ⟨fun _ => none, 0⟩ 1 true).1.alloc 8 true).1

/-- Every slot `0`, the global `5`. -/
def wld5 : World cD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun _ => ⟨5, by decide, by decide⟩, []⟩

theorem rep_free_witness : Rep cLay wld5 mem0 := by
  refine ⟨?_, ?_⟩
  · intro t k f hs h0 h1
    have hk : k = 0 := by
      have : k < 1 := h1
      omega
    subst hk
    cases t
    cases f
    decide +kernel
  · intro g hs
    cases g
    exact ⟨⟨Val.ofInt 64 0, by decide +kernel⟩, fun h => absurd h (by decide)⟩

theorem rep_strong_fails : ¬ Rep cLayN wld5 mem0 := by
  intro h
  have := (h.2 () (by decide)).2 rfl
  revert this
  decide +kernel

theorem shared_read_refused :
    lowerE cLay [] (Gabbro.Grammatik.Expr.glob (D := cD) (Γ := []) (Λ := []) () (fun w hw => absurd hw List.not_mem_nil)) 0
      = none := by
  decide +kernel

theorem sees_shared_witness :
    Sees.shared cLay mem0 (cLay.ggblk ()) 0 (memTy (cD.gtyp ())) .acq (encM cLay (cD.gtyp ()) (wld5.globs ())) ∧
      mem0.load (cLay.ggblk ()) 0 (memTy (cD.gtyp ())) ≠ some (encM cLay (cD.gtyp ()) (wld5.globs ())) :=
  ⟨sees_shared_at cLay mem0 () rfl .acq _ (by decide), by decide +kernel⟩

/-! ## The `await` of a shared atomic, instantiated -/

/-- The oracle: every `await` sees the publication; nothing else is used. -/
def cO : Orakel cD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun _ _ => true

/-- The lowering of `let x = g awaits {..}; <nothing>` (entry label 1, continuation 2, counters `0`, `3`). -/
def cLow : Option (List Block × St) := lowerAwait cLay [] (0, 0) () awRest 1 2 ⟨0, 3⟩

def cBlks : List Block := (cLow.map Prod.fst).getD []

def cSt : St := (cLow.map Prod.snd).getD ⟨0, 0⟩

theorem cLow_eq : cLow = some (cBlks, cSt) := rfl

/-- The module: an entry block (label 0), the lowered blocks, the continuation (label 2, a `ret`). -/
def cMod : Modl := ⟨[], [⟨"f", [], .void, ⟨0, [], [], .jmp 1⟩ :: cBlks ++ [⟨2, [], [], .ret none⟩]⟩]⟩

theorem cBlks_length : cBlks.length = 2 := by decide +kernel

theorem cIn : InM cMod 0 cBlks := by
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
  have h2 : i = 0 ∨ i = 1 := by
    have := cBlks_length
    omega
  rcases h2 with rfl | rfl <;> rfl

theorem cFn : FnOk cLay cMod := fun f =>
  ⟨fun τ hτ => absurd hτ List.not_mem_nil, _, _, rfl, rfl, rfl, rfl, rfl⟩

/-- The calls of the program are answered by a hardware-free stop: the premise of `CallRef` is empty, the
    refinement of the `await` is what is tested. -/
def cR : (f : cD.Fn) → World cD → Env cD (cD.params f) → RufAusgang f := fun _ _ _ => RufAusgang.logik .schleife

theorem cCall : CallRef cLay cMod (Sees.shared cLay) cR :=
  ⟨fun _ _ _ _ _ h => (nomatch h), fun _ _ _ _ _ h => (nomatch h)⟩

theorem cMem_wf : WfL cLay mem0 := by
  refine ⟨?_, fun t => ?_, fun g => ?_⟩
  · intro b hb
    by_cases h1 : b = 1
    · subst h1; decide
    · by_cases h0 : b = 0
      · subst h0; decide
      · simp [mem0, Mem.alloc, Mem.setBlk, h1, h0] at hb
  · cases t; decide
  · cases g; decide

/-- **`await` of a shared atomic, instantiated.** The memory holds `0` at the cell, the world `5`, and the thread
    reads `7` (an answer of the GX interface): the lowered `await` runs from its entry label to the continuation, in a
    memory that represents the world `σ[g := 7]` after the read, with `Post` and the frame of the run. -/
theorem await_shared_zeuge :
    ∃ m' rs', Reach cMod (Sees.shared cLay) (.run mem0 ⟨0, 1, 0, fun _ => none, none⟩ [])
        (.run m' ⟨0, 2, 0, rs', none⟩ []) := by
  have h := (await_ok_shared cLay cLayOk [] (0, 0) cO 0 cR () [] rfl (fun w hw => absurd hw List.not_mem_nil)
    awRest 1 2 ⟨0, 3⟩ cSt cBlks cLow_eq rfl cMod 0 cIn ⟨_, rfl, rfl⟩ ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩ cFn cCall
    wld5 ⟨7, by decide, by decide⟩ .nil mem0 (fun _ => none) [] none rep_free_witness trivial cMem_wf
    (fun x hx => absurd hx List.not_mem_nil)).2
  simp only [execBlock, cO, if_true] at h
  obtain ⟨m', rs', hr, _⟩ := h
  exact ⟨m', rs', hr⟩

end C64

end Gabbro.Code.Lower.WitC
