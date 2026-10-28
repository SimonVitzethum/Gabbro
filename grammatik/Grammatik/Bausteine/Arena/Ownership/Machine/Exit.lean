import Grammatik.Bausteine.Arena.Ownership.Machine.Bind

/-! **`leave` and `next`.** An exit at the head of the residue peels outward
through blocks, shrinks, release markers and `else` continuations until it
reaches the shim of its loop; there it leaves the loop into the loop's
continuation or starts the next iteration. The exit's context exits to the
loop context (`ExitsTo`), so the loop's judgment carries on from it. -/

namespace Gabbro.Grammatik.ArenaOwnership.Machine

open Source Body

variable {D : Deklaration}

section Inv

variable {A : FreiForm D} {I : Interfaces A} {V : Vertrag D} {out : Flow.Output A V.erg}

/-- What the exit half says about a residue, by its shape. -/
def XTop (A : FreiForm D) (I : Interfaces A) {V : Vertrag D} (out : Flow.Output A V.erg) (k : Context) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop
  | _, _, _, .dann _ r => OX A I out k r
  | _, _, _, .schrumpf (Γ := Γ0) r => k.references.length ≤ Γ0.length ∧ OX A I out k r
  | _, _, _, .frei _ r => OX A I out k r
  | _, _, _, .abbruch r => OX A I out k r
  | _, Γ, _, .wiederRest _ bis body ueber r => ∃ k0 c1, checkExpression A k bis = true ∧
      OB A I out k k body c1 ∧ Weaker k c1 ∧ OB A I out k0 k ueber k ∧ k.references.length = Γ.length ∧
      k0.references.length ≤ Γ.length ∧ OR A I out k0 k r
  | _, Γ, _, .ewigRest _ _ inv body r => ∃ k0 c1, checkExpression A k inv = true ∧
      OB A I out k k body c1 ∧ Weaker k c1 ∧ k.references.length = Γ.length ∧
      k0.references.length ≤ Γ.length ∧ OR A I out k0 k r
  | _, _, _, _ => True

theorem ox_top : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {k : Context} {r : GRest D V l Γ Λ},
    OX A I out k r → XTop A I out k r
  | _, _, _, _, _, .dann _ _ hx => hx
  | _, _, _, _, _, .schrumpf _ hk hx => ⟨hk, hx⟩
  | _, _, _, _, _, .frei _ _ hx => hx
  | _, _, _, _, _, .abbruch _ hx => hx
  | _, _, _, _, _, .wiederRest _ _ _ _ _ hbis hb hback hu hlen hk hr => ⟨_, _, hbis, hb, hback, hu, hlen, hk, hr⟩
  | _, _, _, _, _, .ewigRest _ _ _ _ _ hinv hb hback hlen hk hr => ⟨_, _, hinv, hb, hback, hlen, hk, hr⟩
  | _, _, _, _, _, .travRest .. => trivial
  | _, _, _, _, _, .ende .. => trivial
  | _, _, _, _, _, .leer => trivial
  | _, _, _, _, _, .trav .. => trivial
  | _, _, _, _, _, .wieder .. => trivial
  | _, _, _, _, _, .ewig .. => trivial
  | _, _, _, _, _, .wartet .. => trivial
  | _, _, _, _, _, .wartetSonst .. => trivial

end Inv

section Step

variable {A : FreiForm D} {I : Interfaces A} {fr : Frame} {s : State}
  {f : D.Fn} {l : Bool} {Γ : Ctx} {k c : Context} {g : Ghost} {σ σ' : World D} {ρ : Env D Γ}

theorem exit_leave {Λ1 Λ' : List (Res D)} {hl : true = true}
    {rest : Block D (vertragVon D f) true Γ Λ1 Λ'} {r : GRest D (vertragVon D f) true Γ Λ'}
    (hr : OR A I (I f).output k c (.dann (.cons (.leave hl : Stmt D (vertragVon D f) true Γ Λ1 Λ1) rest) r)) :
    ExitsTo k c ∧ OX A I (I f).output k r := by
  obtain ⟨c2, hs, hc⟩ := hr.stmt trivial
  exact ⟨os_top hs, ox_top hc.exits⟩

theorem exit_next {Λ1 Λ' : List (Res D)} {hl : true = true}
    {rest : Block D (vertragVon D f) true Γ Λ1 Λ'} {r : GRest D (vertragVon D f) true Γ Λ'}
    (hr : OR A I (I f).output k c (.dann (.cons (.next hl : Stmt D (vertragVon D f) true Γ Λ1 Λ1) rest) r)) :
    ExitsTo k c ∧ OX A I (I f).output k r := by
  obtain ⟨c2, hs, hc⟩ := hr.stmt trivial
  exact ⟨os_top hs, ox_top hc.exits⟩

/-- The traverse shim behind an exit. -/
theorem travExit {Λ : List (Res D)} {kk : Context} {t : D.Tab} {inv : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true (.index (D.count t) :: Γ) Λ Λ} {is : List (Wert D (.index (D.count t)))}
    {r : GRest D (vertragVon D f) l Γ Λ} {c : Context} {i : Wert D (.index (D.count t))}
    (hf : FrameOk c g s fr (.cons i ρ)) (hx : ExitsTo kk c)
    (hX : OX A I (I f).output kk (.travRest t inv body is r)) :
    Weaker kk c.drop ∧ ∃ k0 c1, checkExpression A kk inv = true ∧ OB A I (I f).output kk (kk.bind none) body c1 ∧
      Weaker kk c1.drop ∧ k0.references.length ≤ Γ.length ∧ OR A I (I f).output k0 kk r := by
  obtain ⟨k0, c1, hinv, hb, hback, hlen, hk0, h⟩ := ox_shim hX
  have hcl : c.references.length = Γ.length + 1 := by simpa using hf.length
  refine ⟨(hx.drop (by omega)).weaker (by simp only [Context.drop, List.length_dropLast, hcl, Nat.add_one_sub_one, hlen]), k0, c1, hinv, hb, hback, hk0, h⟩

/-! ## The exit steps -/

/-- **An exit peels through** a block, a release marker or an `else` continuation. -/
theorem run_peel {Λ1 : List (Res D)} {st : Stmt D (vertragVon D f) true Γ Λ1 Λ1}
    {r : GRest D (vertragVon D f) true Γ Λ1} (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ)
    (ha : s.agrees A σ) (ho : A.FreiOk σ) (hall : OS A I (I f).output k c st (badContext Γ))
    (hX : OX A I (I f).output k r) : Next A I fr s σ σ f ⟨true, Γ, Λ1, ρ, .dann (.cons st .nil) r⟩ :=
  Next.same ha ho (.run ρ _ hk hf (OR.of_dead (.cons _ _ hall .nil) hX))

/-- **An exit peels through a shrink**, forgetting the binder. -/
theorem run_peelSchrumpf {Λ1 : List (Res D)} {τ : Ty} {v : Wert D τ} {st : Stmt D (vertragVon D f) true Γ Λ1 Λ1}
    {r : GRest D (vertragVon D f) true Γ Λ1} (hk : k.references.length ≤ Γ.length)
    (hf : FrameOk c g s fr (.cons v ρ)) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hall : OS A I (I f).output k c.drop st (badContext Γ)) (hX : OX A I (I f).output k r) :
    Next A I fr s σ σ f ⟨true, Γ, Λ1, ρ, .dann (.cons st .nil) r⟩ :=
  Next.of_holds (hf.holds ha ho).drop hk (OR.of_dead (.cons _ _ hall .nil) hX)

/-- The exit context of a shrink. -/
theorem exitsTo_shrink {τ : Ty} {v : Wert D τ} (hf : FrameOk c g s fr (.cons v ρ)) (hx : ExitsTo k c)
    (hk : k.references.length ≤ Γ.length) : ExitsTo k c.drop :=
  hx.drop (by have := hf.length; simp only [List.length_cons] at this; omega)

/-- `leave` at the traverse shim leaves the loop. -/
theorem run_leaveTrav {Λ : List (Res D)} {kk : Context} {t : D.Tab} {inv : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true (.index (D.count t) :: Γ) Λ Λ} {is : List (Wert D (.index (D.count t)))}
    {r : GRest D (vertragVon D f) l Γ Λ} {c : Context} {i : Wert D (.index (D.count t))}
    (hf : FrameOk c g s fr (.cons i ρ)) (ha : s.agrees A σ) (ho : A.FreiOk σ) (hx : ExitsTo kk c)
    (hX : OX A I (I f).output kk (.travRest t inv body is r)) (hm : MetaSame A σ σ') :
    Next A I fr s σ σ' f ⟨l, Γ, Λ, ρ, r⟩ := by
  obtain ⟨hw, k0, c1, _, _, _, hk0, h⟩ := travExit hf hx hX
  exact Next.holdsMeta hf ha ho hm (fun h' => h'.drop.weaken hw) hk0 h

/-- `next` at the traverse shim goes on with the remaining indices. -/
theorem run_nextTrav {Λ : List (Res D)} {kk : Context} {t : D.Tab} {inv : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true (.index (D.count t) :: Γ) Λ Λ} {is : List (Wert D (.index (D.count t)))}
    {r : GRest D (vertragVon D f) l Γ Λ} {c : Context} {i : Wert D (.index (D.count t))}
    (hf : FrameOk c g s fr (.cons i ρ)) (ha : s.agrees A σ) (ho : A.FreiOk σ) (hx : ExitsTo kk c)
    (hX : OX A I (I f).output kk (.travRest t inv body is r)) (hm : MetaSame A σ σ') :
    Next A I fr s σ σ' f ⟨l, Γ, Λ, ρ, .trav t inv body is r⟩ := by
  obtain ⟨hw, k0, c1, hinv, hb, hback, hk0, h⟩ := travExit hf hx hX
  exact Next.holdsMeta hf ha ho hm (fun h' => h'.drop) hk0 (.trav t inv body is r hw hinv hb hback hk0 h)

/-- `leave` at the `retry` shim leaves the loop. -/
theorem run_leaveWieder {Λ : List (Res D)} {kk : Context} {n : Nat} {bis : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true Γ Λ Λ} {ueber : Block D (vertragVon D f) l Γ Λ Λ}
    {r : GRest D (vertragVon D f) l Γ Λ}
    (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ) (hx : ExitsTo kk c)
    (hX : OX A I (I f).output kk (.wiederRest n bis body ueber r)) (hm : MetaSame A σ σ') :
    Next A I fr s σ σ' f ⟨l, Γ, Λ, ρ, r⟩ := by
  obtain ⟨k0, c1, _, _, _, _, hlen, hk0, h⟩ := ox_top hX
  exact Next.holdsMeta hf ha ho hm (fun h' => h'.weaken (hx.weaker (hf.length.trans hlen.symm))) hk0 h

/-- `next` at the `retry` shim tries again. -/
theorem run_nextWieder {Λ : List (Res D)} {kk : Context} {n : Nat} {bis : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true Γ Λ Λ} {ueber : Block D (vertragVon D f) l Γ Λ Λ}
    {r : GRest D (vertragVon D f) l Γ Λ}
    (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ) (hx : ExitsTo kk c)
    (hX : OX A I (I f).output kk (.wiederRest n bis body ueber r)) (hm : MetaSame A σ σ') :
    Next A I fr s σ σ' f ⟨l, Γ, Λ, ρ, .wieder n bis body ueber r⟩ := by
  obtain ⟨k0, c1, hbis, hb, hback, hu, hlen, hk0, h⟩ := ox_top hX
  exact Next.meta ha ho hm (.run ρ _ hk0 hf
    (.wieder n bis body ueber r (hx.weaker (hf.length.trans hlen.symm)) hbis hb hback hu hk0 h))

/-- `leave` at the `forever` shim leaves the loop. -/
theorem run_leaveEwig {Λ : List (Res D)} {kk : Context} {a : D.Annahme} {n : Nat} {inv : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true Γ Λ Λ} {r : GRest D (vertragVon D f) l Γ Λ}
    (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ) (hx : ExitsTo kk c)
    (hX : OX A I (I f).output kk (.ewigRest a n inv body r)) (hm : MetaSame A σ σ') :
    Next A I fr s σ σ' f ⟨l, Γ, Λ, ρ, r⟩ := by
  obtain ⟨k0, c1, _, _, _, hlen, hk0, h⟩ := ox_top hX
  exact Next.holdsMeta hf ha ho hm (fun h' => h'.weaken (hx.weaker (hf.length.trans hlen.symm))) hk0 h

/-- `next` at the `forever` shim goes on. -/
theorem run_nextEwig {Λ : List (Res D)} {kk : Context} {a : D.Annahme} {n : Nat} {inv : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true Γ Λ Λ} {r : GRest D (vertragVon D f) l Γ Λ}
    (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ) (hx : ExitsTo kk c)
    (hX : OX A I (I f).output kk (.ewigRest a n inv body r)) (hm : MetaSame A σ σ') :
    Next A I fr s σ σ' f ⟨l, Γ, Λ, ρ, .ewig a n inv body r⟩ := by
  obtain ⟨k0, c1, hinv, hb, hback, hlen, hk0, h⟩ := ox_top hX
  exact Next.meta ha ho hm (.run ρ _ hk0 hf
    (.ewig a n inv body r (hx.weaker (hf.length.trans hlen.symm)) hinv hb hback hk0 h))

end Step

end Gabbro.Grammatik.ArenaOwnership.Machine
