import Grammatik.Bausteine.Arena.Ownership.Machine.Alloc
import Grammatik.Bausteine.Arena.Ownership.Machine.BlockInv

/-! **The unfold steps of the running activation.** A compound statement at
the head of the residue unfolds into the residue: a branch in front of the
rest, a locked body in front of its release marker, a bounded loop with its
per-iteration shim. Its judgment gives the judgment of what it unfolds
into; the world changes only by reads, so the ledger stays. -/

namespace Gabbro.Grammatik.ArenaOwnership.Machine

open Source Body

variable {D : Deklaration}

/-- Every statement but a table store (the first statement of an executed `free`). -/
def NotStore {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Prop
  | .assignSlot .. => False
  | _ => True

section Inv

variable {A : FreiForm D} {I : Interfaces A} {V : Vertrag D} {out : Flow.Output A V.erg}

theorem Cont.bad {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {k : Context} {r : GRest D V l Γ Λ}
    (hx : OX A I out k r) : Cont A I out k (badContext Γ) r :=
  Or.inr ⟨badContext_length Γ, hx⟩

/-- **A statement in front of the rest**: judged into some context the rest continues from. -/
theorem OR.stmt {l : Bool} {Γ : Ctx} {Λ Λ1 Λ' : List (Res D)} {k c : Context} {st : Stmt D V l Γ Λ Λ1}
    {rest : Block D V l Γ Λ1 Λ'} {r : GRest D V l Γ Λ'} (hr : OR A I out k c (.dann (.cons st rest) r))
    (hst : NotStore st) : ∃ c2, OS A I out k c st c2 ∧ Cont A I out k c2 (.dann rest r) := by
  obtain ⟨c1, hb, hc⟩ := hr.dann_inv
  rcases ob_cons_inv hb rfl with ⟨c2, hs, hrest⟩ | hd | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, heq, _⟩
  · exact ⟨c2, hs, Or.inl (OR.of_cont hrest hc)⟩
  · exact ⟨_, hd _ (badContext_bounded Γ), Cont.bad (.dann rest r hc.exits)⟩
  · cases heq; exact hst.elim

/-- **A statement in front of an end block.** -/
theorem OR.stmtEnde {l : Bool} {Γ : Ctx} {Λ Λ1 : List (Res D)} {k c : Context} {st : Stmt D V l Γ Λ Λ1}
    {rest : Endblock D V l Γ Λ1} (hr : OR A I out k c (.ende (.cons st rest))) :
    ∃ c2, OS A I out k c st c2 ∧ Cont A I out k c2 (.ende rest) := by
  cases hr with
  | ende _ he =>
    rcases oe_cons_inv he rfl with ⟨c2, hs, hrest⟩ | hd
    · exact ⟨c2, hs, Or.inl (.ende rest hrest)⟩
    · exact ⟨_, hd _ (badContext_bounded Γ), Cont.bad (.ende rest)⟩

/-- A residue judged from a context that weakens a realised one. -/
theorem cont_real {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {k c : Context} {r : GRest D V l Γ Λ}
    (h : Cont A I out k c r) (hl : c.references.length = Γ.length) : OR A I out k c r := by
  rcases h with h | ⟨hu, _⟩
  · exact h
  · exact absurd hl hu

end Inv

section Step

variable {A : FreiForm D} {I : Interfaces A} {fr : Frame} {s : State}

theorem Next.meta {σ σ' : World D} {f : D.Fn} {x} (ha : s.agrees A σ) (ho : A.FreiOk σ) (hm : MetaSame A σ σ')
    (h : Head A I fr s σ' f x) : Next A I fr s σ' f x :=
  Next.same (State.agrees_meta ha hm) (freiOk_meta ho hm) h

theorem Next.holdsMeta {σ σ' : World D} {f : D.Fn} {l : Bool} {Γ Γ' : Ctx} {Λ : List (Res D)} {k c c' : Context}
    {g : Ghost} {ρ : Env D Γ} {ρ' : Env D Γ'} {r : GRest D (vertragVon D f) l Γ' Λ} (hf : FrameOk c g s fr ρ)
    (ha : s.agrees A σ) (ho : A.FreiOk σ) (hm : MetaSame A σ σ')
    (h : Holds A fr s c σ' ρ → Holds A fr s c' σ' ρ') (hk : k.references.length ≤ Γ'.length)
    (hr : OR A I (I f).output k c' r) : Next A I fr s σ' f ⟨l, Γ', Λ, ρ', r⟩ :=
  Next.of_holds (h (hf.holds (State.agrees_meta ha hm) (freiOk_meta ho hm))) hk hr

variable {f : D.Fn} {l : Bool} {Γ : Ctx} {k c : Context} {g : Ghost} {σ σ' : World D} {ρ : Env D Γ}

/-- `if` takes its branch in front of the rest. -/
theorem run_ite {Λ Λ' Λ'' : List (Res D)} {cond : Expr D Γ Λ .bool} {t e : Block D (vertragVon D f) l Γ Λ Λ'}
    {rest : Block D (vertragVon D f) l Γ Λ' Λ''} {r : GRest D (vertragVon D f) l Γ Λ''}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.cons (.ite cond t e) rest) r)) (hm : MetaSame A σ σ')
    (b : Bool) : Next A I fr s σ' f ⟨l, Γ, Λ, ρ, .dann (if b then t else e) (.dann rest r)⟩ := by
  obtain ⟨c2, hs, hc⟩ := hr.stmt trivial
  obtain ⟨_, ht, he⟩ := os_top hs
  · cases b
    · exact Next.meta ha ho hm (.run ρ _ hk hf (OR.of_cont he hc))
    · exact Next.meta ha ho hm (.run ρ _ hk hf (OR.of_cont ht hc))

/-- `match` over an option with a value binds it in front of the shrink. -/
theorem run_onOptionSome {Λ Λ' Λ'' : List (Res D)} {n : Int} {o : Expr D Γ Λ (.opt n)}
    {p : Block D (vertragVon D f) l (.index n :: Γ) Λ Λ'} {a : Block D (vertragVon D f) l Γ Λ Λ'}
    {rest : Block D (vertragVon D f) l Γ Λ' Λ''} {r : GRest D (vertragVon D f) l Γ Λ''}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.cons (.onOption o p a) rest) r)) (hm : MetaSame A σ σ')
    (v : Wert D (.index n)) :
    Next A I fr s σ' f ⟨l, .index n :: Γ, Λ, .cons v ρ, .dann p (.schrumpf (.dann rest r))⟩ := by
  obtain ⟨c2, hs, hc⟩ := hr.stmt trivial
  obtain ⟨_, ⟨_, hp, hw⟩, _⟩ := os_top hs
  · exact Next.holdsMeta hf ha ho hm (fun h => h.bindNone v) (Nat.le_succ_of_le hk)
      (OR.binder hp (Or.inr hw) hk hc)

theorem run_onOptionNone {Λ Λ' Λ'' : List (Res D)} {n : Int} {o : Expr D Γ Λ (.opt n)}
    {p : Block D (vertragVon D f) l (.index n :: Γ) Λ Λ'} {a : Block D (vertragVon D f) l Γ Λ Λ'}
    {rest : Block D (vertragVon D f) l Γ Λ' Λ''} {r : GRest D (vertragVon D f) l Γ Λ''}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.cons (.onOption o p a) rest) r)) (hm : MetaSame A σ σ') :
    Next A I fr s σ' f ⟨l, Γ, Λ, ρ, .dann a (.dann rest r)⟩ := by
  obtain ⟨c2, hs, hc⟩ := hr.stmt trivial
  obtain ⟨_, _, ha'⟩ := os_top hs
  exact Next.meta ha ho hm (.run ρ _ hk hf (OR.of_cont ha' hc))

theorem oarms_wahl {V : Vertrag D} {out : Flow.Output A V.erg} :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} {k c c' : Context}
      {arms : Arms D V l Γ Λ Λ' cs}, OArms A I out k c arms c' → ∀ v : Wert D (.sum cs),
      ∃ c1, OB A I out k (armBind c (armWahlG arms v).1) (armWahlG arms v).2.1 c1 ∧
        Weaker c' (armDrop c1 (armWahlG arms v).1)
  | _, _, _, _, _, _, _, _, _, .nil, ⟨i, _⟩ => i.elim0
  | _, _, _, _, _, _, _, _, _, .cons b rest hb hw hr, ⟨⟨0, _⟩, nutz⟩ => ⟨_, hb, hw⟩
  | _, _, _, _, _, _, _, _, _, .cons b rest hb hw hr, ⟨⟨i + 1, hi⟩, nutz⟩ => by
    simp only [armWahlG]
    exact oarms_wahl hr _

/-- `match` over a tag with a payload binds it in front of the shrink. -/
theorem run_onTagSome {Λ Λ' Λ'' : List (Res D)} {cs : List (Option (Int × Int))} {v : Expr D Γ Λ (.sum cs)}
    {arms : Arms D (vertragVon D f) l Γ Λ Λ' cs} {rest : Block D (vertragVon D f) l Γ Λ' Λ''}
    {r : GRest D (vertragVon D f) l Γ Λ''}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.cons (.onTag v arms) rest) r)) (hm : MetaSame A σ σ')
    (w : Wert D (.sum cs)) {lo hi : Int} {b : Block D (vertragVon D f) l (.int lo hi :: Γ) Λ Λ'}
    {nutz : Nutzlast (some (lo, hi))} (hw : armWahlG arms w = ⟨some (lo, hi), b, nutz⟩) :
    Next A I fr s σ' f ⟨l, .int lo hi :: Γ, Λ, armEnv nutz ρ, .dann b (.schrumpf (.dann rest r))⟩ := by
  obtain ⟨c2, hs, hc⟩ := hr.stmt trivial
  obtain ⟨_, harms⟩ := os_top hs
  · obtain ⟨c1, hb, hwk⟩ := oarms_wahl harms w
    rw [hw] at hb hwk
    exact Next.holdsMeta hf ha ho hm (fun h => h.arm (some (lo, hi)) nutz) (Nat.le_succ_of_le hk)
      (OR.binder hb (Or.inr hwk) hk hc)

theorem run_onTagNone {Λ Λ' Λ'' : List (Res D)} {cs : List (Option (Int × Int))} {v : Expr D Γ Λ (.sum cs)}
    {arms : Arms D (vertragVon D f) l Γ Λ Λ' cs} {rest : Block D (vertragVon D f) l Γ Λ' Λ''}
    {r : GRest D (vertragVon D f) l Γ Λ''}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.cons (.onTag v arms) rest) r)) (hm : MetaSame A σ σ')
    (w : Wert D (.sum cs)) {b : Block D (vertragVon D f) l Γ Λ Λ'} {nutz : Nutzlast none}
    (hw : armWahlG arms w = ⟨none, b, nutz⟩) :
    Next A I fr s σ' f ⟨l, Γ, Λ, armEnv nutz ρ, .dann b (.dann rest r)⟩ := by
  obtain ⟨c2, hs, hc⟩ := hr.stmt trivial
  obtain ⟨_, harms⟩ := os_top hs
  · obtain ⟨c1, hb, hwk⟩ := oarms_wahl harms w
    rw [hw] at hb hwk
    exact Next.holdsMeta hf ha ho hm (fun h => h.arm none nutz) hk (OR.weakened hb (Or.inr hwk) hc)

theorem ogrund_wahl {V : Vertrag D} {out : Flow.Output A V.erg} :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} {k c c' : Context}
      {arms : GrundArms D V l Γ Λ Λ' n}, OGrund A I out k c arms c' → ∀ r : Fin n,
      ∃ c1, OB A I out k c (grundWahlG arms r) c1 ∧ Weaker c' c1
  | _, _, _, _, _, _, _, _, _, .nil, r => r.elim0
  | _, _, _, _, _, _, _, _, _, .cons b rest hb hw hr, ⟨0, _⟩ => ⟨_, hb, hw⟩
  | _, _, _, _, _, _, _, _, _, .cons b rest hb hw hr, ⟨i + 1, hi⟩ => by
    simp only [grundWahlG]
    exact ogrund_wahl hr _

/-- `match` over a reason takes its arm in front of the rest. -/
theorem run_onWhy {Λ Λ' Λ'' : List (Res D)} {n : Nat} {re : Expr D Γ Λ (.why n)}
    {arms : GrundArms D (vertragVon D f) l Γ Λ Λ' n} {rest : Block D (vertragVon D f) l Γ Λ' Λ''}
    {r : GRest D (vertragVon D f) l Γ Λ''}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.cons (.onWhy re arms) rest) r)) (hm : MetaSame A σ σ')
    (w : Fin n) : Next A I fr s σ' f ⟨l, Γ, Λ, ρ, .dann (grundWahlG arms w) (.dann rest r)⟩ := by
  obtain ⟨c2, hs, hc⟩ := hr.stmt trivial
  obtain ⟨_, harms⟩ := os_top hs
  · obtain ⟨c1, hb, hwk⟩ := ogrund_wahl harms w
    exact Next.meta ha ho hm (.run ρ _ hk hf (OR.weakened hb (Or.inr hwk) hc))

/-- `breaking` runs its body in front of the rest. -/
theorem run_breaking {Λ Λ' Λ'' : List (Res D)} {i : D.Inv} {body : Block D (vertragVon D f) l Γ Λ Λ'}
    {rest : Block D (vertragVon D f) l Γ Λ' Λ''} {r : GRest D (vertragVon D f) l Γ Λ''}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.cons (.breaking i body) rest) r)) :
    Next A I fr s σ f ⟨l, Γ, Λ, ρ, .dann body (.dann rest r)⟩ := by
  obtain ⟨c2, hs, hc⟩ := hr.stmt trivial
  have hb := os_top hs
  exact Next.same ha ho (.run ρ _ hk hf (OR.of_cont hb hc))

/-- `locks` runs its body in front of the release marker. -/
theorem run_locks {Λ Λ'' : List (Res D)} {L : D.Lock} {hrk : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L}
    {body : Block D (vertragVon D f) l Γ (Res.held L :: Λ) (Res.held L :: Λ)}
    {rest : Block D (vertragVon D f) l Γ Λ Λ''} {r : GRest D (vertragVon D f) l Γ Λ''}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.cons (.locks L hrk body) rest) r)) (hm : MetaSame A σ σ') :
    Next A I fr s σ' f ⟨l, Γ, Res.held L :: Λ, ρ, .dann body (.frei L (.dann rest r))⟩ := by
  obtain ⟨c2, hs, hc⟩ := hr.stmt trivial
  have hb := os_top hs
  · rcases hc with h | ⟨hu, hx⟩
    · exact Next.meta ha ho hm (.run ρ _ hk hf (.dann _ _ hb (.frei L _ h)))
    · exact Next.meta ha ho hm (.run ρ _ hk hf (.dannDead _ _ hb hu (.frei L _ hx)))

/-- `traverse` starts its loop in front of the rest. -/
theorem run_traverse {Λ Λ'' : List (Res D)} {t : D.Tab} {inv : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true (.index (D.count t) :: Γ) Λ Λ}
    {rest : Block D (vertragVon D f) l Γ Λ Λ''} {r : GRest D (vertragVon D f) l Γ Λ''}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.cons (.traverse t inv body) rest) r))
    (ks : List (Wert D (.index (D.count t)))) :
    Next A I fr s σ f ⟨l, Γ, Λ, ρ, .trav t inv body ks (.dann rest r)⟩ := by
  obtain ⟨c2, hs, hc⟩ := hr.stmt trivial
  obtain ⟨hentry, hinv, _, hb, hback⟩ := os_top hs
  · have hl : c2.references.length = Γ.length := hentry.2.2.1.trans hf.length
    exact Next.same ha ho (.run ρ _ hk hf (.trav t inv body ks _ hentry hinv hb hback hk (cont_real hc hl)))

/-- `retry` starts its loop in front of the rest. -/
theorem run_retry {Λ Λ'' : List (Res D)} {n : Nat} {bis : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true Γ Λ Λ} {ueber : Block D (vertragVon D f) l Γ Λ Λ}
    {rest : Block D (vertragVon D f) l Γ Λ Λ''} {r : GRest D (vertragVon D f) l Γ Λ''}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.cons (.retry n bis body ueber) rest) r)) :
    Next A I fr s σ f ⟨l, Γ, Λ, ρ, .wieder n bis body ueber (.dann rest r)⟩ := by
  obtain ⟨c2, hs, hc⟩ := hr.stmt trivial
  obtain ⟨hentry, hbis, ⟨_, hb, hback⟩, hu⟩ := os_top hs
  · have hl : c2.references.length = Γ.length := hentry.2.2.1.trans hf.length
    exact Next.same ha ho (.run ρ _ hk hf (.wieder n bis body ueber _ hentry hbis hb hback hu hk (cont_real hc hl)))

/-- `forever` starts its loop in front of the rest. -/
theorem run_forever {Λ Λ'' : List (Res D)} {a : D.Annahme} {inv : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true Γ Λ Λ}
    {rest : Block D (vertragVon D f) l Γ Λ Λ''} {r : GRest D (vertragVon D f) l Γ Λ''}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.cons (.forever a inv body) rest) r)) (n : Nat) :
    Next A I fr s σ f ⟨l, Γ, Λ, ρ, .ewig a n inv body (.dann rest r)⟩ := by
  obtain ⟨c2, hs, hc⟩ := hr.stmt trivial
  obtain ⟨hentry, hinv, _, hb, hback⟩ := os_top hs
  · have hl : c2.references.length = Γ.length := hentry.2.2.1.trans hf.length
    exact Next.same ha ho (.run ρ _ hk hf (.ewig a n inv body _ hentry hinv hb hback hk (cont_real hc hl)))

/-- A compound statement in end-block position moves into block position. -/
theorem run_entf {Λ Λ' : List (Res D)} {st : Stmt D (vertragVon D f) l Γ Λ Λ'}
    {rest : Endblock D (vertragVon D f) l Γ Λ'}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.ende (.cons st rest))) :
    Next A I fr s σ f ⟨l, Γ, Λ, ρ, .dann (.cons st .nil) (.ende rest)⟩ := by
  obtain ⟨c2, hs, hc⟩ := hr.stmtEnde
  exact Next.same ha ho (.run ρ _ hk hf (OR.of_cont (.cons _ _ hs .nil) hc))

/-- An end-block former moves into block position in front of nothing. -/
theorem run_endeForm {Λ : List (Res D)} {e : Endblock D (vertragVon D f) l Γ Λ}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.ende e)) :
    Next A I fr s σ f ⟨l, Γ, Λ, ρ, .dann e.alsBlock.2 (.abbruch (Λk := Λ) .leer)⟩ := by
  cases hr with
  | ende _ he => exact Next.same ha ho (.run ρ _ hk hf (OR.sonst he .leer))

/-! ## Residue shapes -/

/-- An empty block hands over to its continuation. -/
theorem run_leer {Λ : List (Res D)} {r : GRest D (vertragVon D f) l Γ Λ}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann .nil r)) : Next A I fr s σ f ⟨l, Γ, Λ, ρ, r⟩ := by
  obtain ⟨c1, hb, hc⟩ := hr.dann_inv
  rcases ob_top hb with rfl | hw
  · exact Next.same ha ho (.run ρ r hk hf (cont_real hc hf.length))
  · exact Next.of_holds ((hf.holds ha ho).weaken hw) hk (cont_real hc (hw.2.2.1.trans hf.length))

/-- A release marker hands over to its continuation. -/
theorem run_frei {Λ : List (Res D)} {L : D.Lock} {r : GRest D (vertragVon D f) l Γ Λ}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.frei L r)) : Next A I fr s σ f ⟨l, Γ, Λ, ρ, r⟩ := by
  cases hr with
  | frei _ _ h => exact Next.same ha ho (.run ρ r hk hf h)

/-- A shrink forgets the innermost binder. -/
theorem run_schrumpf {Λ : List (Res D)} {τ : Ty} {r : GRest D (vertragVon D f) l Γ Λ} {v : Wert D τ}
    {c : Context} {ρ : Env D Γ} (hf : FrameOk c g s fr (.cons v ρ)) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.schrumpf (τ := τ) r)) : Next A I fr s σ f ⟨l, Γ, Λ, ρ, r⟩ := by
  cases hr with
  | schrumpf _ hk h => exact Next.of_holds (hf.holds ha ho).drop hk h

/-! ## The bounded loops -/

theorem run_travNext {Λ : List (Res D)} {t : D.Tab} {inv : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true (.index (D.count t) :: Γ) Λ Λ} {i : Wert D (.index (D.count t))}
    {is : List (Wert D (.index (D.count t)))} {r : GRest D (vertragVon D f) l Γ Λ}
    (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.trav t inv body (i :: is) r)) (hm : MetaSame A σ σ') :
    Next A I fr s σ' f ⟨true, .index (D.count t) :: Γ, Λ, .cons i ρ, .dann body (.travRest t inv body is r)⟩ := by
  cases hr with
  | trav _ _ _ _ _ hentry hinv hb hback hk h =>
    have hlen := hentry.2.2.1.trans hf.length
    exact Next.holdsMeta hf ha ho hm (fun h' => (h'.weaken hentry).bindNone i) (by simp; omega)
      (.dann _ _ hb (.travRest t inv body is r hback (.travRest t inv body is r hinv hb hback hlen hk h)))

theorem run_travFort {Λ : List (Res D)} {kk : Context} {t : D.Tab} {inv : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true (.index (D.count t) :: Γ) Λ Λ} {i : Wert D (.index (D.count t))}
    {is : List (Wert D (.index (D.count t)))} {r : GRest D (vertragVon D f) l Γ Λ}
    (hf : FrameOk c g s fr (.cons i ρ)) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output kk c (.travRest t inv body is r)) :
    Next A I fr s σ f ⟨l, Γ, Λ, ρ, .trav t inv body is r⟩ := by
  obtain ⟨hentry, hx⟩ := or_shim hr
  obtain ⟨k0, c1, hinv, hb, hback, _, hk, h⟩ := ox_shim hx
  exact Next.of_holds (hf.holds ha ho).drop hk (.trav t inv body is r hentry hinv hb hback hk h)

theorem run_travDone {Λ : List (Res D)} {t : D.Tab} {inv : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true (.index (D.count t) :: Γ) Λ Λ} {r : GRest D (vertragVon D f) l Γ Λ}
    (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.trav t inv body [] r)) (hm : MetaSame A σ σ') :
    Next A I fr s σ' f ⟨l, Γ, Λ, ρ, r⟩ := by
  cases hr with
  | trav _ _ _ _ _ hentry _ _ _ hk h => exact Next.holdsMeta hf ha ho hm (fun h' => h'.weaken hentry) hk h

theorem run_wiederUeber {Λ : List (Res D)} {bis : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true Γ Λ Λ} {ueber : Block D (vertragVon D f) l Γ Λ Λ}
    {r : GRest D (vertragVon D f) l Γ Λ}
    (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.wieder 0 bis body ueber r)) :
    Next A I fr s σ f ⟨l, Γ, Λ, ρ, .dann (.cons (.ite bis .nil ueber) .nil) r⟩ := by
  cases hr with
  | wieder _ _ _ _ _ hentry hbis _ _ hu hk h =>
    exact Next.of_holds ((hf.holds ha ho).weaken hentry) hk
      (.dann _ _ (.cons _ _ (.ite bis .nil ueber hbis .nil hu) .nil) h)

theorem run_wiederWeiter {Λ : List (Res D)} {n : Nat} {bis : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true Γ Λ Λ} {ueber : Block D (vertragVon D f) l Γ Λ Λ}
    {r : GRest D (vertragVon D f) l Γ Λ}
    (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.wieder (n + 1) bis body ueber r)) (hm : MetaSame A σ σ') :
    Next A I fr s σ' f ⟨l, Γ, Λ, ρ, r⟩ := by
  cases hr with
  | wieder _ _ _ _ _ hentry _ _ _ _ hk h => exact Next.holdsMeta hf ha ho hm (fun h' => h'.weaken hentry) hk h

theorem run_wiederSchritt {Λ : List (Res D)} {n : Nat} {bis : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true Γ Λ Λ} {ueber : Block D (vertragVon D f) l Γ Λ Λ}
    {r : GRest D (vertragVon D f) l Γ Λ}
    (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.wieder (n + 1) bis body ueber r)) (hm : MetaSame A σ σ') :
    Next A I fr s σ' f ⟨true, Γ, Λ, ρ, .dann body (.wiederRest n bis body ueber r)⟩ := by
  cases hr with
  | wieder _ _ _ _ _ hentry hbis hb hback hu hk h =>
    have hlen := hentry.2.2.1.trans hf.length
    exact Next.holdsMeta hf ha ho hm (fun h' => h'.weaken hentry) (Nat.le_of_eq hlen)
      (.dann _ _ hb (.wiederRest n bis body ueber r hback (.wiederRest n bis body ueber r hbis hb hback hu hlen hk h)))

theorem run_wiederFort {Λ : List (Res D)} {kk : Context} {n : Nat} {bis : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true Γ Λ Λ} {ueber : Block D (vertragVon D f) l Γ Λ Λ}
    {r : GRest D (vertragVon D f) l Γ Λ}
    (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output kk c (.wiederRest n bis body ueber r)) :
    Next A I fr s σ f ⟨l, Γ, Λ, ρ, .wieder n bis body ueber r⟩ := by
  cases hr with
  | wiederRest _ _ _ _ _ hentry hx =>
    cases hx with
    | wiederRest _ _ _ _ _ hbis hb hback hu _ hk h =>
      exact Next.same ha ho (.run ρ _ hk hf (.wieder n bis body ueber r hentry hbis hb hback hu hk h))

theorem run_ewigWeiter {Λ : List (Res D)} {a : D.Annahme} {n : Nat} {inv : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true Γ Λ Λ} {r : GRest D (vertragVon D f) l Γ Λ}
    (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.ewig a (n + 1) inv body r)) (hm : MetaSame A σ σ') :
    Next A I fr s σ' f ⟨true, Γ, Λ, ρ, .dann body (.ewigRest a n inv body r)⟩ := by
  cases hr with
  | ewig _ _ _ _ _ hentry hinv hb hback hk h =>
    have hlen := hentry.2.2.1.trans hf.length
    exact Next.holdsMeta hf ha ho hm (fun h' => h'.weaken hentry) (Nat.le_of_eq hlen)
      (.dann _ _ hb (.ewigRest a n inv body r hback (.ewigRest a n inv body r hinv hb hback hlen hk h)))

theorem run_ewigFort {Λ : List (Res D)} {kk : Context} {a : D.Annahme} {n : Nat} {inv : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true Γ Λ Λ} {r : GRest D (vertragVon D f) l Γ Λ}
    (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output kk c (.ewigRest a n inv body r)) :
    Next A I fr s σ f ⟨l, Γ, Λ, ρ, .ewig a n inv body r⟩ := by
  cases hr with
  | ewigRest _ _ _ _ _ hentry hx =>
    cases hx with
    | ewigRest _ _ _ _ _ hinv hb hback _ hk h =>
      exact Next.same ha ho (.run ρ _ hk hf (.ewig a n inv body r hentry hinv hb hback hk h))

end Step

end Gabbro.Grammatik.ArenaOwnership.Machine
