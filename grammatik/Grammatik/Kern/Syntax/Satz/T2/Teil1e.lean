/- Part 1e of `Satz/T2/Teil1` (C11 split; pure move): caller transport
   (`heldB_weiter`/`heldB_weiterRet`/`heldB_ruf`) and the residual-held
   invariant with the call-branch widening. -/
module

public import Grammatik.Kern.Syntax.Satz.T1
public import Grammatik.Kern.Syntax.Satz.T2.Teil1d

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-! #### The floor forms (held-set relaxation, 2026-09-13) -/

theorem heldB_weiter {W G} {bo : Option Int} {σ σ1 : World D} {Λ Λ' : List (Res D)}
    (hm : ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ) (hg : Gut W G σ σ1) (hh : HeldB bo Λ σ.haelt) :
    HeldB bo Λ' σ1.haelt := by
  rw [hg.haelt]
  exact ⟨fun L hL => hh.1 L ((hm L).mp hL), fun L hL hn => hh.2 L hL (fun h => hn ((hm L).mpr h))⟩

/-- Membership survives a release that does not name the lock. -/
theorem mem_foldl_erase (L : D.Lock) (Ks : List D.Lock) (h : List D.Lock)
    (hm : L ∈ h) (hn : L ∉ Ks) : L ∈ Ks.foldl (fun h M => h.erase M) h := by
  induction Ks generalizing h with
  | nil => exact hm
  | cons M Ms ih =>
      simp only [List.foldl_cons]
      have hne : L ≠ M := by intro e; subst e; exact hn List.mem_cons_self
      refine ih _ (List.mem_erase_of_ne hne hm) (fun hcon => hn (List.mem_cons_of_mem _ hcon))

/-- Transport through a spare+rank release: every needed lock survives. Required
    locks survive by spare; extras (held, not required) survive by rank — they
    rank below the floor (`hx`, i.e. `RufPasst.hx` at the call site) while every
    released lock ranks at or above it. Erasure only removes, so the floor part
    rides along (`BravRet.mem`). -/
theorem heldB_weiterRet {W G} {haelt : List D.Lock} {boden : Option Int} {bo : Option Int}
    {σ σ1 : World D} {Λ Λ' : List (Res D)}
    (hm : ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ)
    (hg : GutRetV W G haelt boden σ σ1) (hh : HeldB bo Λ σ.haelt)
    (hx : ∀ L, Res.held L ∈ Λ → L ∉ haelt → ∃ c, boden = some c ∧ D.rang L < c) :
    HeldB bo Λ' σ1.haelt := by
  obtain ⟨_, Ls, heq, hsp, hrk, _, _⟩ := hg
  have hsurv : ∀ L, Res.held L ∈ Λ' → L ∈ σ1.haelt := by
    intro L hL
    have hLΛ : Res.held L ∈ Λ := (hm L).mp hL
    have hLh : L ∈ σ.haelt := hh.1 L hLΛ
    have hnotin : L ∉ Ls := by
      intro hLs
      by_cases hreq : L ∈ haelt
      · exact hsp L hLs hreq
      · obtain ⟨c, hc, hlt⟩ := hx L hLΛ hreq
        have hge := hrk L hLs c hc
        omega
    rw [heq]
    exact mem_foldl_erase L Ls σ.haelt hLh hnotin
  have hbR : BravRet σ σ1 := hg.toBravRet
  exact ⟨fun L hL => hsurv L hL,
    fun L hL hn => hh.2 L (hbR.mem hL) (fun h => hn ((hm L).mpr h))⟩

/-- The callee's entry from the caller's: its signature locks are held
    (`RufPasst.hh`), a new extra lock is below its floor (`RufPasst.hx`), an
    extra lock of the caller is below the caller's floor, hence below the
    callee's (`RufPasst.hb`). -/
theorem heldB_ruf {V : Vertrag D} {S : Signatur D.Tab D.Glob D.Lock D.Marke} {Λ : List (Res D)}
    {h : List D.Lock} {b : Option Int} (hp : RufPasst D V S Λ) (hbV : BodenUnter b V.boden)
    (hh : HeldB b Λ h) : HeldB S.boden (Signatur.anfang D S) h := by
  refine ⟨fun L hL => hh.1 L (hp.hh L ((held_anfang S L).mp hL)), fun L hL hn => ?_⟩
  have hnS : L ∉ S.haelt := fun hm => hn ((held_anfang S L).mpr hm)
  by_cases hΛ : Res.held L ∈ Λ
  · exact hp.hx L hΛ hnS
  · obtain ⟨c, hc, hlt⟩ := hh.2 L hL hΛ
    obtain ⟨c', hc', hle⟩ := hbV c hc
    obtain ⟨c'', hc'', hle'⟩ := hp.hb c' hc'
    exact ⟨c'', hc'', by omega⟩

/-! #### The residual-held invariant (C11 call-branch widening)

    A releasing handler outcome (`GutRetV`) is stated over the CALLEE residual
    and floor (`S.haelt`/`S.boden`), but the caller continues over its OWN
    (`V.haelt`/`V.boden`). The widening (`widen_resid`) needs one link: every
    lock the caller residual requires is statically named in the caller frame
    (`ResidHeld`), so each released lock either hits the callee spare or is a
    caller extra below the callee floor (`hx` + rank). Established once at
    function entry (`residHeld_anfang`) and preserved over steps
    (`ResidHeld.of_iff`, via the existing `held_iff` facts). -/

/-- **The residual is held (named) in the caller frame**: every lock the
    contract residual requires (`V.haelt`) is statically named in the current
    `Λ` — hence held wherever `HeldB` holds. -/
def ResidHeld (V : Vertrag D) (Λ : List (Res D)) : Prop :=
  ∀ L ∈ V.haelt, Res.held L ∈ Λ

/-- Preservation over steps: steps keep the held set (`held_iff`), so a named
    residual stays named. -/
theorem ResidHeld.of_iff {V : Vertrag D} {Λ Λ' : List (Res D)}
    (hm : ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ) (h : ResidHeld V Λ) :
    ResidHeld V Λ' :=
  fun L hV => (hm L).mpr (h L hV)

/-- At function entry the residual is named: the entry set is exactly the
    signature locks (plus input marks). -/
theorem residHeld_anfang (S : Signatur D.Tab D.Glob D.Lock D.Marke) :
    ResidHeld (Vertrag.vonSig D S) (Signatur.anfang D S) :=
  fun L hL => (held_anfang S L).mpr hL

/-- Erasing only locks that are absent is the identity. -/
theorem foldl_erase_of_not_mem : ∀ (Ks : List D.Lock) (h : List D.Lock),
    (∀ L ∈ Ks, L ∉ h) → Ks.foldl (fun h M => h.erase M) h = h
  | [], _, _ => rfl
  | M :: Ms, h, hn => by
      simp only [List.foldl_cons]
      rw [List.erase_of_not_mem (hn M List.mem_cons_self)]
      exact foldl_erase_of_not_mem Ms _ (fun L hL => hn L (List.mem_cons_of_mem _ hL))

/-- Widen a releasing step from the callee residual/floor to the caller one.
    The floor lifts by `RufPasst.hb`, and every released lock avoids the caller
    residual: either it is required by the callee (spare) or it is a caller
    extra below the callee floor (`hx` + rank, via the residual-held
    invariant). -/
theorem GutRetV.widen_resid {S : Signatur D.Tab D.Glob D.Lock D.Marke}
    {Λ : List (Res D)} {W : D.Tab → Bool} {G : D.Glob → Bool} {σ σ1 : World D}
    (hp : RufPasst D V S Λ) (hresid : ResidHeld V Λ)
    (h : GutRetV W G S.haelt S.boden σ σ1) :
    GutRetV W G V.haelt V.boden σ σ1 := by
  obtain ⟨hr, Ls, heq, hsp, hrk, hgood, hkons⟩ := h
  refine ⟨hr, Ls, heq, ?spareV, ?rankV, hgood, hkons⟩
  · intro L hL hV
    by_cases hS : L ∈ S.haelt
    · exact absurd hS (hsp L hL)
    · obtain ⟨c, hc, hlt⟩ := hp.hx L (hresid L hV) hS
      have hge := hrk L hL c hc
      omega
  · intro L hL c hc
    obtain ⟨c', hc', hle⟩ := hp.hb c hc
    exact Int.le_trans hle (hrk L hL c' hc')

/-- A releasing step with a vacuous release is a plain step. At function entry
    (entry set `anfang`, residual `S.haelt`) the release list cannot touch what
    is held: required locks survive by spare, extras — below the floor — by
    rank. Used for the `.ok` exit of `rufAt_gut`, whose body may unwind scopes
    on the way to `.zurueck`. -/
theorem GutRetV.toGut_entry {S : Signatur D.Tab D.Glob D.Lock D.Marke}
    {W : D.Tab → Bool} {G : D.Glob → Bool} {σ σ' : World D}
    (h : GutRetV W G S.haelt S.boden σ σ')
    (hh : HeldB S.boden (Signatur.anfang D S) σ.haelt) :
    Gut W G σ σ' := by
  obtain ⟨hr, Ls, heq, hsp, hrk, hgood, hkons⟩ := h
  have hnot : ∀ L ∈ Ls, L ∉ σ.haelt := by
    intro L hL hM
    by_cases hA : Res.held L ∈ Signatur.anfang D S
    · exact hsp L hL ((held_anfang S L).mp hA)
    · obtain ⟨c, hc, hlt⟩ := hh.2 L hM hA
      have hge := hrk L hL c hc
      omega
  have heq2 : σ'.haelt = σ.haelt := heq.trans (foldl_erase_of_not_mem Ls _ hnot)
  exact ⟨hr, heq2, hgood, hkons⟩

end Gabbro.Grammatik
