import Grammatik.Code.Gate.Provider

/-
  File:      Grammatik/Code/Gate/Zeuge.lean
  Subject:   TRACK L -- WITNESSES for `GateNeed` / `gate_verfeinert` (`Gate.lean`) over the three provider
             gates (`Provider.lean`), and a planted defect.

  The reference CPU is the abstract machine itself (`refRel` is equality, `refTrap` takes any outcome the
  contract allows): it meets `GateNeed` (`ref_need`), which shows the obligations are satisfiable and
  that the contracts of the three roles are inhabited for every precondition (`erfuellbar`). The planted
  defect is a CPU whose `get` trap answers an ALREADY EXISTING block without allocating: that violates
  the freshness half of the contract and so `GateNeed` (`schlecht_verletzt`). `tor_zeuge` runs
  `gate_verfeinert` on a module that calls the `get` gate once, ALL premises jointly.

  No `sorry`, no `native_decide`, no new axiom.
-/

namespace Gabbro.Code

variable [Conf]

/-- The gate table of the three provider roles: gate 0 `get`, 1 `fill`, 2 `drop`. -/
def tabelle : GateTab := [holeSpec, fuellSpec, gibSpec]

/-- The reference CPU: the abstract machine itself. -/
def refRel : Mem → Regs → (Mem × Regs) → Prop := fun m rs x => x = (m, rs)

/-- Its trap: any outcome the contract allows. -/
def refTrap (G : GateTab) : Nat → Option Reg → List Val → Mem × Regs → Mem × Regs → Prop :=
  fun k d vs x y => ∃ gs m' ans, G[k]? = some gs ∧ gs.post x.1 vs m' ans ∧
    y = (m', setAns d ans x.2)

/-- Every precondition of a provider gate has an outcome the contract allows. -/
theorem erfuellbar {k : Nat} {gs : GateSpec} {m : Mem} {vs : List Val}
    (hk : tabelle[k]? = some gs) (hp : gs.pre m vs) : ∃ m' ans, gs.post m vs m' ans := by
  match k, hk with
  | 0, hk =>
      cases (Option.some.inj hk)
      obtain ⟨n, rfl⟩ := hp
      exact ⟨_, _, n, rfl, rfl, rfl⟩
  | 1, hk =>
      cases (Option.some.inj hk)
      obtain ⟨b, o, n, blk, rfl, hb, hon⟩ := hp
      exact ⟨_, _, b, o, n, blk, rfl, hb, hon, Or.inl ⟨fun _ => 0, rfl, rfl⟩⟩
  | 2, hk =>
      cases (Option.some.inj hk)
      obtain ⟨b, blk, rfl, hb⟩ := hp
      exact ⟨_, _, b, blk, rfl, hb, rfl, rfl⟩
  | k + 3, hk => simp [tabelle] at hk

/-- **The reference CPU meets the obligations.** -/
theorem ref_need : GateNeed (Mem × Regs) refRel tabelle (refTrap tabelle) := by
  refine ⟨?_, ?_⟩
  · intro k gs d vs m rs x hk hp hw hr
    subst hr
    obtain ⟨m', ans, h⟩ := erfuellbar hk hp
    exact ⟨_, gs, m', ans, hk, h, rfl⟩
  · intro k gs d vs m rs x y hk hp hw hr ht
    subst hr
    obtain ⟨gs', m', ans, hk', h, rfl⟩ := ht
    rw [hk] at hk'
    cases hk'
    exact ⟨m', ans, h, rfl⟩

/-- **Planted defect**: a CPU whose `get` trap hands back an existing block and allocates nothing. -/
def schlechtTrap : Nat → Option Reg → List Val → Mem × Regs → Mem × Regs → Prop :=
  fun k _ _ x y => k = 0 ∧ y = x

/-- It violates the contract (the new block must come from `alloc`, which advances `next`), so it does
    not meet `GateNeed`. -/
theorem schlecht_verletzt : ¬ GateNeed (Mem × Regs) refRel tabelle schlechtTrap := by
  intro N
  have hpre : holeSpec.pre Mem.empty [Val.ofInt Conf.wbits 8] := ⟨8, rfl⟩
  have hw : WohlAnruf holeSpec none Mem.empty [Val.ofInt Conf.wbits 8] := by
    intro r hr
    cases hr
  obtain ⟨m', ans, hp, hr⟩ := N.erlaubt 0 holeSpec none _ Mem.empty (fun _ => none)
    (Mem.empty, fun _ => none) (Mem.empty, fun _ => none) rfl hpre hw rfl ⟨rfl, rfl⟩
  obtain ⟨n, -, rfl, -⟩ := hp
  have := congrArg (fun p : Mem × Regs => p.1.next) hr
  simp [Mem.alloc, Mem.setBlk, Mem.empty] at this

/-- **Witness for `gate_verfeinert`**, all premises jointly: a module whose only function calls the `get`
    gate (function number 1, past its single own function) with the word 64. -/
def modul : Modl :=
  ⟨[], [⟨"main", [], .void, [⟨0, [], [.call (some 0) 1 [.int Conf.wbits 64]], .ret none⟩]⟩]⟩

theorem tor_zeuge :
    ∃ (m' : Mem) (g : Frame) (y : Mem × Regs),
      GateStep modul tabelle (.run Mem.empty ⟨0, 0, 0, fun _ => none, none⟩ [])
        (.run m' g []) ∧ refRel m' g.regs y := by
  have hpre : holeSpec.pre Mem.empty [Val.ofInt Conf.wbits 64] := ⟨64, rfl⟩
  have hw : WohlAnruf holeSpec (some 0) Mem.empty [Val.ofInt Conf.wbits 64] := by
    intro r hr m' a hp
    obtain ⟨n, -, -, rfl⟩ := hp
    rfl
  obtain ⟨y, hy⟩ := gate_laeuft (d := some 0) ref_need (k := 0) (gs := holeSpec)
    (vs := [Val.ofInt Conf.wbits 64]) (m := Mem.empty) (rs := fun _ => none)
    (x := (Mem.empty, fun _ => none)) rfl hpre hw rfl
  obtain ⟨m', g, hs, hr⟩ := gate_verfeinert ref_need (M := modul)
    (f := ⟨0, 0, 0, fun _ => none, none⟩) (ks := [])
    (blk := ⟨0, [], [.call (some 0) 1 [.int Conf.wbits 64]], .ret none⟩) (d := some 0) (fi := 1)
    (args := [.int Conf.wbits 64]) (vs := [Val.ofInt Conf.wbits 64]) (gs := holeSpec)
    (x := (Mem.empty, fun _ => none)) (y := y)
    rfl rfl (by simp [modul]) rfl rfl hpre hw rfl hy
  exact ⟨m', g, y, hs, hr⟩

end Gabbro.Code
