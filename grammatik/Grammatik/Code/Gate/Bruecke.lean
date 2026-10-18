import Grammatik.Code.Gate.Provider
import Grammatik.Hardware.Anbieter.Arena

/-
  File:      Grammatik/Code/Gate/Bruecke.lean
  Subject:   TRACK L -- THE BRIDGE between the provider's ADDRESS-level contract
             (`Hardware/Anbieter/Region.lean`) and the BLOCK-level gate contracts of `Code`
             (`Provider.lean`).  PLAN-HARDWARE.md section 16.6.

  `Code` memory has no addresses: a region answer is a fresh block, and "two allocations never alias"
  is built into the block structure. The provider has addresses, and "never alias" is its FRESHNESS
  contract. The relation `Entspricht s m rho` says they describe one world: every live block `b` of `m`
  sits at the live reservation `[rho b, rho b + size)` of the provider state `s`, blocks are non-empty,
  and `rho` is injective on live blocks.

  Proved: the three Code-level roles preserve the correspondence together with their provider
  counterparts (`entspricht_hole`, `entspricht_gib`, `entspricht_ram`), and consequently two distinct
  live Code blocks have DISJOINT address ranges (`entspricht_getrennt`) -- the block-level fact the
  `Code` memory builds in is, for a program whose memory comes from a provider, a CONSEQUENCE of the
  provider's freshness contract and not an extra assumption about the machine. The witness reserves
  two blocks and shows their ranges disjoint; the planted defect is an aliasing assignment.

  No `sorry`, no `native_decide`, no new axiom.
-/

namespace Gabbro.Code

variable [Conf]

open Gabbro.Grammatik.Anbieter

/-- Every live block of `m` sits at a live reservation of `s`; blocks are non-empty; `rho` is injective
    on live blocks. -/
structure Entspricht (s : Zust) (m : Mem) (rho : Nat → Nat) : Prop where
  lebt : ∀ b blk, m.blks b = some blk → (⟨rho b, rho b + blk.size⟩ : Strecke) ∈ s.lebend
  gross : ∀ b blk, m.blks b = some blk → 0 < blk.size
  eind : ∀ b b' blk blk', m.blks b = some blk → m.blks b' = some blk' → rho b = rho b' → b = b'

/-- **Distinct live blocks have disjoint address ranges.** -/
theorem entspricht_getrennt {s : Zust} {m : Mem} {rho : Nat → Nat} (hg : Gut s)
    (hE : Entspricht s m rho) {b b' : Nat} {blk blk' : Blk} (hb : m.blks b = some blk)
    (hb' : m.blks b' = some blk') (hne : b ≠ b') :
    Strecke.getrennt ⟨rho b, rho b + blk.size⟩ ⟨rho b', rho b' + blk'.size⟩ := by
  have hr := paar_aus hg.getrennt (hE.lebt b blk hb) (hE.lebt b' blk' hb') (by
    intro h
    have := congrArg Strecke.von h
    exact hne (hE.eind b b' blk blk' hb hb' this))
  exact hr

/-- **A reserve on both sides.** The provider hands out the range `[a, a+n)` (fresh); the `Code`
    memory allocates the block `m.next`; the new block sits at `a`. -/
theorem entspricht_hole {g n a : Nat} {s s' : Zust} {m : Mem} {rho : Nat → Nat}
    (hE : Entspricht s m rho) (hs : PStep g s (.hole n a) s') :
    Entspricht s' (m.alloc n false).1 (fun b => if b = m.next then a else rho b) := by
  cases hs with
  | hole hn hnb hb hfrisch =>
      have hnew : ∀ blk, (m.alloc n false).1.blks m.next = some blk → blk.size = n := by
        intro blk h
        have := alloc_size m n false
        have e : (m.alloc n false).2 = m.next := rfl
        rw [e, h] at this
        simpa using this
      refine ⟨?_, ?_, ?_⟩
      · intro b blk h
        by_cases e : b = m.next
        · subst e
          have := hnew blk h
          simp only [if_true, this]
          exact List.mem_cons_self ..
        · rw [alloc_blks_old m n false b e] at h
          simp only [e, if_false]
          exact List.mem_cons_of_mem _ (hE.lebt b blk h)
      · intro b blk h
        by_cases e : b = m.next
        · subst e
          rw [hnew blk h]
          exact hn
        · rw [alloc_blks_old m n false b e] at h
          exact hE.gross b blk h
      · intro b b' blk blk' h h' hr
        by_cases e : b = m.next <;> by_cases e' : b' = m.next
        · rw [e, e']
        · -- the new block at `a`, an old block at `a`: the old range is live and overlaps
          exfalso
          rw [alloc_blks_old m n false b' e'] at h'
          have hl := hE.lebt b' blk' h'
          have hf := hfrisch _ hl
          have hg := hE.gross b' blk' h'
          simp only [e, e', if_true, if_false] at hr
          unfold Strecke.getrennt at hf
          simp only at hf
          omega
        · exfalso
          rw [alloc_blks_old m n false b e] at h
          have hl := hE.lebt b blk h
          have hf := hfrisch _ hl
          have hg := hE.gross b blk h
          simp only [e, e', if_true, if_false] at hr
          unfold Strecke.getrennt at hf
          simp only at hf
          omega
        · rw [alloc_blks_old m n false b e] at h
          rw [alloc_blks_old m n false b' e'] at h'
          simp only [e, e', if_false] at hr
          exact hE.eind b b' blk blk' h h' hr

/-- **A release on both sides.** The `Code` memory removes block `b`; the provider gives back the
    reservation it sits at. The correspondence of the remaining blocks stays. -/
theorem entspricht_gib {g : Nat} {s s' : Zust} {m : Mem} {rho : Nat → Nat} {b : Nat} {blk : Blk}
    (hE : Entspricht s m rho) (hb : m.blks b = some blk)
    (hs : PStep g s (.gib ⟨rho b, rho b + blk.size⟩) s') :
    Entspricht s' (m.entfernen b) rho := by
  cases hs with
  | gib hr =>
      refine ⟨?_, ?_, ?_⟩
      · intro b' blk' h
        simp only [Mem.entfernen] at h
        by_cases e : b' = b
        · simp [e] at h
        · simp only [e, if_false] at h
          refine (List.mem_erase_of_ne ?_).2 (hE.lebt b' blk' h)
          intro h2
          have := congrArg Strecke.von h2
          exact e (hE.eind b' b blk' blk h hb this)
      · intro b' blk' h
        simp only [Mem.entfernen] at h
        by_cases e : b' = b
        · simp [e] at h
        · simp only [e, if_false] at h
          exact hE.gross b' blk' h
      · intro b1 b2 blk1 blk2 h1 h2 hr
        simp only [Mem.entfernen] at h1 h2
        by_cases e1 : b1 = b <;> by_cases e2 : b2 = b
        · simp [e1] at h1
        · simp [e1] at h1
        · simp [e2] at h2
        · simp only [e1, e2, if_false] at h1 h2
          exact hE.eind b1 b2 blk1 blk2 h1 h2 hr

/-- **A commit or a page return changes no reservation**: the correspondence survives whenever the
    block sizes do. -/
theorem entspricht_ram {s s' : Zust} {m m' : Mem} {rho : Nat → Nat} (hE : Entspricht s m rho)
    (hl : s'.lebend = s.lebend)
    (hsz : ∀ b blk', m'.blks b = some blk' → ∃ blk, m.blks b = some blk ∧ blk.size = blk'.size) :
    Entspricht s' m' rho := by
  refine ⟨?_, ?_, ?_⟩
  · intro b blk' h
    obtain ⟨blk, hb, hs⟩ := hsz b blk' h
    rw [hl, ← hs]
    exact hE.lebt b blk hb
  · intro b blk' h
    obtain ⟨blk, hb, hs⟩ := hsz b blk' h
    rw [← hs]
    exact hE.gross b blk hb
  · intro b b' blk blk' h h' hr
    obtain ⟨c, hc, -⟩ := hsz b blk h
    obtain ⟨c', hc', -⟩ := hsz b' blk' h'
    exact hE.eind b b' c c' hc hc' hr

/-- **The Code-level commit keeps every block size** (`fuell_lokal`): so a commit on both sides keeps the
    correspondence. -/
theorem fuell_groessen {m m' : Mem} {vs : List Val} {ans : Option Val}
    (h : fuellSpec.post m vs m' ans) :
    (∀ b blk', m'.blks b = some blk' → ∃ blk, m.blks b = some blk ∧ blk.size = blk'.size) ∧
    (∀ b blk, m.blks b = some blk → ∃ blk', m'.blks b = some blk' ∧ blk'.size = blk.size) := by
  obtain ⟨b0, o, n, blk0, hb0, hon, hc⟩ := (by
    obtain ⟨b, o, n, blk, -, hb, hon, hc⟩ := h
    exact ⟨b, o, n, blk, hb, hon, hc⟩ : ∃ (b o n : Nat) (blk : Blk), m.blks b = some blk ∧
      o + n ≤ blk.size ∧ ((∃ c, m' = m.setBlk b (blk.fuellen o n c) ∧ ans = some (Val.ofInt Conf.wbits 0)) ∨
        (m' = m ∧ ans = some (Val.ofInt Conf.wbits 1))))
  rcases hc with ⟨c, rfl, -⟩ | ⟨rfl, -⟩
  · constructor
    · intro b blk' h'
      by_cases e : b = b0
      · subst e
        rw [setBlk_same] at h'
        cases h'
        exact ⟨blk0, hb0, rfl⟩
      · rw [setBlk_other _ _ _ _ e] at h'
        exact ⟨blk', h', rfl⟩
    · intro b blk hb
      by_cases e : b = b0
      · subst e
        rw [hb0] at hb
        cases hb
        exact ⟨_, setBlk_same _ _ _, rfl⟩
      · exact ⟨blk, by rw [setBlk_other _ _ _ _ e]; exact hb, rfl⟩
  · exact ⟨fun b blk' h' => ⟨blk', h', rfl⟩, fun b blk hb => ⟨blk, hb, rfl⟩⟩

/-! ## Witness and planted defect (64-bit word) -/

local instance confB64 : Conf := ⟨64, false, Or.inr rfl⟩

/-- **Witness**: two reserves (page 16) -- 64 bytes at 32, then 64 bytes at 96 -- on the empty
    memory. After both, the two `Code` blocks exist, sit at 32 and 96, the correspondence holds and
    their address ranges are disjoint. -/
theorem bruecke_zeuge :
    ∃ (s2 : Zust) (m2 : Mem) (rho : Nat → Nat), Gut s2 ∧ Entspricht s2 m2 rho ∧
      rho 0 = 32 ∧ rho 1 = 96 ∧ m2.blks 0 ≠ none ∧ m2.blks 1 ≠ none ∧
      Strecke.getrennt ⟨32, 32 + 64⟩ ⟨96, 96 + 64⟩ := by
  have hE0 : Entspricht Zust.leer Mem.empty (fun _ => 0) :=
    ⟨fun b blk h => by simp [Mem.empty] at h, fun b blk h => by simp [Mem.empty] at h,
     fun b b' blk blk' h => by simp [Mem.empty] at h⟩
  have hs1 : PStep 16 Zust.leer (.hole 64 32)
      { lebend := [⟨32, 32 + 64⟩], ram := Zust.leer.ram } :=
    PStep.hole (s := Zust.leer) (by decide) (by decide) (by decide) (by simp [Zust.leer])
  have hE1 := entspricht_hole hE0 hs1
  have hg1 := gut_nach gut_leer hs1
  have hs2 : PStep 16 { lebend := [⟨32, 32 + 64⟩], ram := Zust.leer.ram } (.hole 64 96)
      { lebend := ⟨96, 96 + 64⟩ :: [⟨32, 32 + 64⟩], ram := Zust.leer.ram } :=
    PStep.hole (by decide) (by decide) (by decide) (by simp [Strecke.getrennt])
  have hE2 := entspricht_hole hE1 hs2
  have hg2 := gut_nach hg1 hs2
  refine ⟨_, _, _, hg2, hE2, rfl, ?_, ?_, ?_, ?_⟩
  · simp [Mem.alloc, Mem.setBlk, Mem.empty]
  · simp [Mem.alloc, Mem.setBlk, Mem.empty]
  · simp [Mem.alloc, Mem.setBlk, Mem.empty]
  · simp [Strecke.getrennt]

/-- **Planted defect: aliasing.** An assignment that puts two distinct live blocks at one address is no
    correspondence: injectivity is a field, not a hope. -/
theorem aliasing_verweigert {s : Zust} {m : Mem} {rho : Nat → Nat} (hE : Entspricht s m rho)
    {b b' : Nat} {blk blk' : Blk} (hb : m.blks b = some blk) (hb' : m.blks b' = some blk')
    (hne : b ≠ b') : rho b ≠ rho b' := fun h => hne (hE.eind b b' blk blk' hb hb' h)

end Gabbro.Code
