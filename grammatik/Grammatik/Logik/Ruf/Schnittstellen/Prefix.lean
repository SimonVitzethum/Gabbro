module

public import Grammatik.Logik.Ruf.Schnittstellen.Rufstelle
public import Grammatik.Logik.Ruf.Schnittstellen.Lokal

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {n : Nat}

/-- The interface pre replays across worlds that agree on its footprint.
    This is the prefix step for indirect call sites: a havoc or environment
    move that preserves the pre carriers preserves the caller duty. -/
theorem ptrPre_prefix (P : Programm D) (s0 s0' : World D)
    (ρ : Env D (D.sigNr n).params)
    (h : (P.ptrVertrag n).preHolds s0 ρ)
    (hag : GleichAuf (P.ptrVertrag n).pre.orte s0 s0') :
    (P.ptrVertrag n).preHolds s0' ρ := by
  have hiff := CallContract.pre_congr (P.ptrVertrag n) hag ρ
  unfold CallContract.preHolds at h hiff ⊢
  rw [hiff] at h
  exact h

/-- The interface post replays with separate entry/current agreements.
    The old-state discipline is preserved: agreement only in the current
    world cannot rewrite `old` reads from the entry world. -/
theorem ptrPost_prefix (P : Programm D) (s0 s0' s1 s1' : World D)
    (ρ : Env D (D.sigNr n).params) (v : ErgVal D (D.sigNr n).erg)
    (h : (P.ptrVertrag n).postHolds s0 s1 ρ v)
    (h0 : GleichAuf (P.ptrVertrag n).post.orte s0 s0')
    (h1 : GleichAuf (P.ptrVertrag n).post.orte s1 s1') :
    (P.ptrVertrag n).postHolds s0' s1' ρ v := by
  have hiff := CallContract.post_congr (P.ptrVertrag n) h0 h1 ρ v
  unfold CallContract.postHolds at h hiff ⊢
  rw [hiff] at h
  exact h

/-- The local interface duty replays across a prefix that preserves the
    operand-entry footprint. The site world is the recorded operand-entry
    world `σ.lese Λ (p.orte ++ args.orte)`; a prefix move agreeing there
    keeps the duty. -/
theorem ptrPflicht_prefix (P : Programm D)
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (σ σ' : World D) (ρ : Env D Γ)
    (h : PtrRufPflicht P p args σ ρ)
    (hag : GleichAuf (P.ptrVertrag n).pre.orte
      (σ.lese Λ (p.orte ++ args.orte)) (σ'.lese Λ (p.orte ++ args.orte))) :
    PtrRufPflicht P p args σ' ρ := by
  unfold PtrRufPflicht at h ⊢
  exact ptrPre_prefix P _ _ _ h hag

/-- Full prefix transfer for a statement indirect call: the replayed
    interface duty yields the selected target's concrete requires at the
    replayed operand-entry world with the replayed arguments. -/
theorem ptrReq_prefix_stmt (hR : PtrVerfeinert P)
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (σ σ' : World D) (ρ : Env D Γ)
    (h : PtrRufPflicht P p args σ ρ)
    (hag : GleichAuf (P.ptrVertrag n).pre.orte
      (σ.lese Λ (p.orte ++ args.orte)) (σ'.lese Λ (p.orte ++ args.orte))) :
    let s0 := σ'.lese Λ (p.orte ++ args.orte)
    let target := eval s0 p s0 ρ
    ReqAmEintritt P target.val s0 (umsig target.property (evalArgs s0 args s0 ρ)) :=
  PtrRufPflicht.req hR (ptrPflicht_prefix P p args σ σ' ρ h hag)

/-- The concrete caller gate opens at the replayed site world. The selected
    handler, body and result remain unchanged; only the entry world moves
    along the prefix agreement. -/
theorem ptrTor_prefix_stmt (hR : PtrVerfeinert P)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (σ σ' : World D) (ρ : Env D Γ)
    (h : PtrRufPflicht P p args σ ρ)
    (hag : GleichAuf (P.ptrVertrag n).pre.orte
      (σ.lese Λ (p.orte ++ args.orte)) (σ'.lese Λ (p.orte ++ args.orte))) :
    let s0 := σ'.lese Λ (p.orte ++ args.orte)
    let target := eval s0 p s0 ρ
    torRuf P R target.val s0 (umsig target.property (evalArgs s0 args s0 ρ)) =
      R target.val s0 (umsig target.property (evalArgs s0 args s0 ρ)) :=
  PtrRufPflicht.torRuf hR R (ptrPflicht_prefix P p args σ σ' ρ h hag)

/-- The interface post at a normal return replays across entry/current
    agreements and projects from the concrete ensures. Reason exits supply
    no premise of this shape. -/
theorem ptrEns_prefix_stmt (hR : PtrVerfeinert P)
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (σ σ' : World D) (ρ : Env D Γ)
    (h : PtrRufPflicht P p args σ ρ)
    (hag : GleichAuf (P.ptrVertrag n).pre.orte
      (σ.lese Λ (p.orte ++ args.orte)) (σ'.lese Λ (p.orte ++ args.orte)))
    (s1 s1' : World D)
    (v : ErgVal D (D.erg (eval (σ'.lese Λ (p.orte ++ args.orte)) p
      (σ'.lese Λ (p.orte ++ args.orte)) ρ).val))
    (hv : let s0 := σ'.lese Λ (p.orte ++ args.orte)
      let target := eval s0 p s0 ρ
      EnsAmRueck P target.val s0 s1 (umsig target.property (evalArgs s0 args s0 ρ)) v)
    (h1 : GleichAuf (P.ptrVertrag n).post.orte s1 s1') :
    let s0 := σ'.lese Λ (p.orte ++ args.orte)
    let target := eval s0 p s0 ρ
    (P.ptrVertrag n).postHolds s0 s1' (evalArgs s0 args s0 ρ) (ptrResult target.property v) := by
  have hpost := PtrRufPflicht.ens hR (ptrPflicht_prefix P p args σ σ' ρ h hag) s1 v hv
  have hag0 : GleichAuf (P.ptrVertrag n).post.orte
      (σ'.lese Λ (p.orte ++ args.orte)) (σ'.lese Λ (p.orte ++ args.orte)) :=
    GleichAuf.refl _ _
  exact ptrPost_prefix P _ _ s1 s1' _ _ hpost hag0 h1

end Gabbro.Grammatik
