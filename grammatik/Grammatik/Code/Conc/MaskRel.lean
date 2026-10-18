import Grammatik.Code.Conc.MaskNeed
import Grammatik.Zielsatz.Eigenschaften.KernMaske

/-
  File:      Grammatik/Code/Conc/MaskRel.lean
  Subject:   TRACK L, PHASE L3 -- THE MASKED LOCK AGAINST MACHINE G'S MASK STATE: the invariant `MaskCells`, the steps
             that preserve it, and the refinement of the entry guard of an interrupt handler.

  Machine G's mask state is `MaskeKern D` (`Zielsatz/Eigenschaften/KernMaske.lean`): per core, the (thread, lock) pairs
  that mask it. The IR keeps ONE word per core, the mask word `mb c` (`Conc/Mask.lean`). The relation is a COVER, not an
  equality: **whenever G calls core `c` masked, the word of `c` is nonzero** (`MaskCells`). It is not an equality
  because the spin of an acquisition runs masked before G takes the lock (the word is set first), and because the
  restore of an outer section happens after G has released the inner lock; the hardware is only ever MORE masked than
  G, never less.

  THE STEPS (each a run of ONE thread, `treach_solo`; the other threads and the G machine are untouched):
    * `mask_on_step`  -- the word becomes `1`, the old word is saved (G silent);
    * the ticket steps of `Conc/LockRel.lean` store only into the lock cells, which are no mask cell (`MaskDisj`):
      `maskCells_ticket`;
    * `maskCells_nach` -- G's `nimmt`/`gibt` change its mask list; the cover survives when the thread has masked first
      (the new entries need a nonzero word);
    * `mask_off_step` -- the saved word comes back; the cover holds when G's list after the release is empty or the
      saved word was nonzero.
  THE GUARD: `irq_guard` -- with `MaskHw` (H1, H2), a handler entry on core `c` happens only where `mk c = []`: the
  premise `eintritt` of `KernSchritt`, so the hardware's handler entries are steps G's guarded machine allows.

  NOT CLAIMED: the composition of these steps with the interleaving of ALL threads of a core (H3 is what would discharge
  the "no other thread of the core moved between acquisition and release" premise of the restore); a Rust emitter.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration Faden Ereignis)
open Gabbro.Grammatik.Zielsatz (MaskeKern maskeNach maskEintr)

variable {D : Deklaration}

/-- **The cover**: every core's mask word exists, and is nonzero whenever G's list for that core is not empty. -/
def MaskCells (mb : Nat → Nat) (m : Mem) (mk : MaskeKern D) : Prop :=
  ∀ c, ∃ x, m.load (mb c) 0 lw = some x ∧ (mk c ≠ [] → x ≠ tk 0)

/-- The mask words are distinct blocks of their own: no lock cell, no table, no global, one per core. -/
structure MaskDisj (lay : Layout D) (mb : Nat → Nat) : Prop where
  lk : ∀ c L, mb c ≠ lay.lblk L ∧ mb c ≠ lay.lsrv L
  tab : ∀ c t, mb c ≠ lay.gblk t
  glob : ∀ c g, mb c ≠ lay.ggblk g
  inj : ∀ c c', mb c = mb c' → c = c'

/-- A store into a block that is no mask word leaves the cover alone. -/
theorem maskCells_store_other {mb : Nat → Nat} {m m' : Mem} {mk : MaskeKern D} {b : Nat} {o : Int} {t : Ty}
    {v : Val} (hc : MaskCells mb m mk) (hs : m.store b o t v = some m') (hb : ∀ c, mb c ≠ b) :
    MaskCells mb m' mk := by
  intro c
  obtain ⟨x, hx, hcov⟩ := hc c
  exact ⟨x, by rw [load_store_other hs (Or.inl (hb c))]; exact hx, hcov⟩

/-- **The ticket steps keep the cover**: their stores go to a next-ticket or serving cell. -/
theorem maskCells_ticket {lay : Layout D} {mb : Nat → Nat} {m m' : Mem} {mk : MaskeKern D} {L : D.Lock}
    {b : Nat} {o : Int} {t : Ty} {v : Val} (hd : MaskDisj lay mb) (hc : MaskCells mb m mk)
    (hb : b = lay.lblk L ∨ b = lay.lsrv L) (hs : m.store b o t v = some m') : MaskCells mb m' mk :=
  maskCells_store_other hc hs (fun c e => by
    rcases hb with rfl | rfl
    · exact (hd.lk c L).1 e
    · exact (hd.lk c L).2 e)

/-- **Mask** (G silent): the word of core `c` becomes `1` and the old word is saved; the cover holds. -/
theorem mask_on_step {mb : Nat → Nat} {mk : MaskeKern D} {T : TM} (hinj : ∀ c c', mb c = mb c' → c = c')
    (hc : MaskCells mb T.m mk) (c : Nat) {rm : Reg} {S : Sees} {Mod : Modl} {fn : Nat} {lb k : Lbl} {bk : Block}
    (hb : Mod.blk fn lb = some (maskOn (mb c) rm lb k)) (hk : Mod.blk fn k = some bk) (hkp : bk.phis = [])
    (u : Faden) {rs : Regs} {ks : List Frame} {dst : Option Reg} (hth : AtB T u fn lb rs ks dst) :
    ∃ (T' : TM) (x : Val), TReach Mod S T T' ∧ AtB T' u fn k (rs.set rm x) ks dst ∧
      (∀ v, v ≠ u → T'.th v = T.th v) ∧ T.m.load (mb c) 0 lw = some x ∧
      T'.m.load (mb c) 0 lw = some (tk 1) ∧ MaskCells mb T'.m mk := by
  obtain ⟨x, hx, _⟩ := hc c
  obtain ⟨m', hm'⟩ := store_of_load hx (tk_ty 1)
  have hreach := maskOn_run (S := S) hb hk hkp (rs := rs) (ks := ks) (dst := dst) hx hm'
  refine ⟨T.upd u (.run m' ⟨fn, k, 0, rs.set rm x, dst⟩ ks), x, treach_solo hreach T (cfg_of_atB hth),
    by simp [AtB, TM.upd], fun v hv => upd_other T _ hv, hx, ?_, ?_⟩
  · exact load_store_of hm' (dec_enc_tk 1)
  · intro c'
    by_cases hcc : c' = c
    · subst hcc
      exact ⟨tk 1, load_store_of hm' (dec_enc_tk 1), fun _ => tk_one_ne⟩
    · obtain ⟨y, hy, hcov⟩ := hc c'
      exact ⟨y, by
      show m'.load (mb c') 0 lw = some y
      rw [load_store_other hm' (Or.inl (fun e => hcc (hinj _ _ e)))]
      exact hy, hcov⟩

/-- **G's `nimmt`/`gibt` on the mask list keep the cover** when the new entries of the acting thread find the word of
    its core nonzero (it masked before it took the lock): the entries a step adds need a set word, the ones it removes
    only shrink the list. -/
theorem maskCells_nach {mb : Nat → Nat} {m : Mem} {mk : MaskeKern D} (hc : MaskCells mb m mk)
    (kern : Faden → Nat) (u : Faden) (s : List (Ereignis D))
    (hnew : maskEintr u s ≠ [] → ∃ x, m.load (mb (kern u)) 0 lw = some x ∧ x ≠ tk 0) :
    MaskCells mb m (maskeNach kern mk u s) := by
  intro c
  obtain ⟨x, hx, hcov⟩ := hc c
  refine ⟨x, hx, fun hne => ?_⟩
  unfold maskeNach at hne
  by_cases hcu : c = kern u
  · rw [if_pos hcu] at hne
    by_cases hn : maskEintr u s = []
    · rw [hn, List.append_nil] at hne
      apply hcov
      intro hnil
      apply hne
      rw [hnil]
      rfl
    · obtain ⟨x', hx', hne'⟩ := hnew hn
      rw [← hcu] at hx'
      rw [hx] at hx'
      rw [Option.some.inj hx']
      exact hne'
  · rw [if_neg hcu] at hne
    exact hcov hne

/-- **Restore** (the saved word comes back): the cover holds for G's list after the release `mk'` when that list is
    empty on the core or the saved word is nonzero. -/
theorem mask_off_step {mb : Nat → Nat} {mk' : MaskeKern D} {T : TM} (hinj : ∀ c c', mb c = mb c' → c = c')
    (hc : MaskCells mb T.m mk') (c : Nat) {rm rx : Reg} {S : Sees} {Mod : Modl} {fn : Nat} {lb k : Lbl}
    {bk : Block} (hb : Mod.blk fn lb = some (maskOff (mb c) rm rx lb k)) (hk : Mod.blk fn k = some bk)
    (hkp : bk.phis = []) (u : Faden) {rs : Regs} {ks : List Frame} {dst : Option Reg} {x : Val}
    (hth : AtB T u fn lb rs ks dst) (hrm : rs rm = some x) (hxw : x.ty = lw)
    (hx : mk' c ≠ [] → x ≠ tk 0) :
    ∃ (T' : TM) (y : Val), TReach Mod S T T' ∧ AtB T' u fn k (rs.set rx y) ks dst ∧
      (∀ v, v ≠ u → T'.th v = T.th v) ∧ T.m.load (mb c) 0 lw = some y ∧
      T'.m.load (mb c) 0 lw = some x ∧ MaskCells mb T'.m mk' := by
  obtain ⟨y, hy, _⟩ := hc c
  obtain ⟨m', hm'⟩ := store_of_load hy hxw
  have hreach := maskOff_run (S := S) hb hk hkp (rs := rs) (ks := ks) (dst := dst) hrm hy hm'
  have hdec : lw.dec x.enc = some x := by
    cases x with
    | int w v =>
        have hw : w = Conf.wbits := by simpa [Val.ty, lw] using hxw
        subst hw
        exact dec_enc_int _ _
    | _ => simp [Val.ty, lw] at hxw
  refine ⟨T.upd u (.run m' ⟨fn, k, 0, rs.set rx y, dst⟩ ks), y, treach_solo hreach T (cfg_of_atB hth),
    by simp [AtB, TM.upd], fun v hv => upd_other T _ hv, hy, load_store_of hm' hdec, ?_⟩
  intro c'
  by_cases hcc : c' = c
  · subst hcc
    exact ⟨x, load_store_of hm' hdec, hx⟩
  · obtain ⟨z, hz, hcov⟩ := hc c'
    exact ⟨z, by
    show m'.load (mb c') 0 lw = some z
    rw [load_store_other hm' (Or.inl (fun e => hcc (hinj _ _ e)))]
    exact hz, hcov⟩

/-- **THE ENTRY GUARD, REFINED**: on a CPU that meets `MaskHw`, a handler entry on core `c` happens only where G's mask
    list of `c` is empty -- the premise `eintritt` of `KernSchritt` (`Z.mask (kern f) = []`). -/
theorem irq_guard {Mach : Type} {Rel : Mem → Regs → Mach → Prop} {mb : Nat → Nat}
    {Masked : Nat → Mach → Prop} {Irq Switch : Nat → Mach → Mach → Prop}
    (hw : MaskHw Mach Rel mb Masked Irq Switch) {m : Mem} {rs : Regs} {x y : Mach} {mk : MaskeKern D} {c : Nat}
    (hrel : Rel m rs x) (hc : MaskCells mb m mk) (hirq : Irq c x y) : mk c = [] := by
  by_cases h : mk c = []
  · exact h
  · obtain ⟨v, hv, hcov⟩ := hc c
    exact absurd (hw.masked_of_cell c m rs x v hrel hv (hcov h)) (hw.irq_unmasked c x y hirq)

end Gabbro.Code.Lower
