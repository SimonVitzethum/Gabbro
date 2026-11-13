/-
  File:      Grammatik/Logik/Fortschritt/Halten/Nimmt.lean
  Subject:   WHERE A SECTION BEGINS: the step that takes `L` is `dannLocks` at a `locks L` head
             (`nimmt_an_sperre`), and it establishes the section invariant `SekInv` at the checked bound:
             the body's `kostenBlock ep` is at most `N L` (the walker on the head's residue at the price `ep`
             of the frame's return predicates,
             `GRest.hR`), the release costs one, the markers behind it are distinct locks of `ls`
             (`GRest.freis_nodup`), and the frame names `L` beyond its end signature (the end holdings
             are held, `L` is not).
-/
module
public import Grammatik.Logik.Fortschritt.Halten.Invariante
public import Grammatik.Logik.Fortschritt.Halten.SchrittHalt
public import Grammatik.Logik.Fortschritt.Lebendigkeit
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The walker at one section of a lock with a bound. -/
theorem haltS_locks_some (N : D.Lock → Nat) (ep : Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (L : D.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (Res.held L :: Λ) (Res.held L :: Λ)) :
    haltS (fun K => some (N K)) ep c Z pa (Stmt.locks L hr body) =
      (decide (kostenBlock ep c pa body ≤ N L) && rufeB Z (fun _ => false) true body &&
        haltB (fun K => some (N K)) ep c Z pa body) := by
  first | rfl | simp only [haltS]

section Nimmt

variable {ι : Type} (T : ι → D.Fn → Nat) (S : ι → D.Fn → Bool) {P : Programm D} {O : Orakel D}
  {pa : Nat} (N : D.Lock → Nat) (ls : List D.Lock)

/-- **A section entered by `dannLocks` satisfies `SekInv` at `haltSchranke ls N K`.** -/
theorem sekInv_locks (i : ι) (z : RufFadenG D) {M : RufMaschineG D} {u : Faden} {ep : Nat}
    {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)} {K : D.Lock}
    {hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang K}
    {body : Block D (vertragVon D (M.faeden u).kopf.f) l Γ (Res.held K :: Λ) (Res.held K :: Λ)}
    {rest : Block D (vertragVon D (M.faeden u).kopf.f) l Γ Λ Λ''}
    {k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ''} {ρ : Env D Γ}
    (hhead : (M.faeden u).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.locks K hr body) rest) k⟩)
    (hz : z.kopf = ⟨(M.faeden u).kopf.f, (M.faeden u).kopf.rho, (M.faeden u).kopf.s0,
        ⟨l, Γ, Res.held K :: Λ, ρ, .dann body (.frei K (.dann rest k))⟩⟩)
    (hH : GRest.hR (fun K' => some (N K')) ep (T i) (S i) pa (M.faeden u).kopf.rest.2.2.2.2)
    (h0 : K ∉ offen (M.faeden u).spur)
    (hstat : ∀ K', Res.held K' ∈ (M.faeden u).kopf.rest.2.2.1 → K' ∈ offen (M.faeden u).spur)
    (hbal : RestScopeBalance (M.faeden u).kopf.rest)
    (hnf : (M.faeden u).kopf.rest.2.2.2.2.freis.Nodup) (hls : ∀ K', K' ∈ ls) :
    SekInv T S pa K z (haltSchranke ls N K) := by
  have hsb : (GRest.dann (.cons (.locks K hr body) rest) k).scopeBalance := scopeBalance_von hhead hbal
  rw [hhead] at hH hnf
  have hlen : (GRest.dann rest k).freis.length ≤ ls.length :=
    List.Nodup.length_le_of_subset hnf (fun x _ => hls x)
  simp only [GRest.hR, haltB, haltS_locks_some, Bool.and_eq_true, decide_eq_true_eq] at hH
  obtain ⟨⟨⟨⟨hkb, hrb⟩, -⟩, -⟩, -⟩ := hH
  refine ⟨[], z.kopf, z.stapel, i, ep, 0, rfl, Seg.nil, ?_, ?_, ?_, ?_⟩
  · rw [hz]
    show (rufeB (S i) (fun _ => false) true body &&
      rufeV K (S i) (fun _ => false) true (GRest.frei K (GRest.dann rest k))) = true
    simp only [rufeV_frei_gleich, hrb, Bool.and_self]
  · rw [hz]
    exact List.mem_cons_self
  · rw [hz]
    intro hm
    have h1 : 0 < (vertragVon D (M.faeden u).kopf.f).ende.count (Res.held K) := List.count_pos_iff.mpr hm
    have hc := hsb K
    apply h0
    apply hstat K
    rw [hhead]
    show Res.held K ∈ Λ
    exact List.count_pos_iff.mp (by omega)
  · rw [hz]
    show 0 + (kostenBlock ep (T i) pa body + potSek K ep (T i) pa (GRest.frei K (GRest.dann rest k))) ≤
      haltSchranke ls N K
    rw [potSek_frei_gleich]
    unfold haltSchranke
    omega

set_option maxHeartbeats 4000000 in
/-- **The acquisition step.** A step of `u` from a `locks L` head establishes `SekInv` at the
    checked hold time `haltSchranke ls N L`; every rule but `dannLocks` has a head that is no `locks`
    statement (the case analysis of `sperre_schritt`). -/
theorem sekInv_nimmt (i : ι) {M M' : RufMaschineG D} {u : Faden} {L : D.Lock} {ep : Nat}
    (hA : AnSperre M u L) (hs : RufSchrittG P O pa M u M')
    (hH : GRest.hR (fun K' => some (N K')) ep (T i) (S i) pa (M.faeden u).kopf.rest.2.2.2.2)
    (h0 : L ∉ offen (M.faeden u).spur)
    (hstat : ∀ K', Res.held K' ∈ (M.faeden u).kopf.rest.2.2.1 → K' ∈ offen (M.faeden u).spur)
    (hbal : RestScopeBalance (M.faeden u).kopf.rest)
    (hnf : (M.faeden u).kopf.rest.2.2.2.2.freis.Nodup) (hls : ∀ K', K' ∈ ls) :
    SekInv T S pa L (M'.faeden u) (haltSchranke ls N L) := by
  have hK := anSperre_kopf hA
  cases hs with
  | g1 hs =>
    cases hs with
    | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead =>
        exfalso
        rw [hhead] at hK
        simp only [GRest.kopfSperre, Block.sperreVon, Stmt.blatt_sperreVon s hleaf] at hK
        cases hK
    | _ =>
        exfalso
        rw [‹(M.faeden u).kopf.rest = _›] at hK
        simp only [GRest.kopfSperre, reduceCtorEq, Block.sperreVon, Stmt.sperreVon] at hK
  | g2 hs =>
    cases hs with
    | dannLocks l Γ Λ Λ'' L' hr body rest k ρ hhead hself hrang hfrei =>
        rw [hhead] at hK
        simp only [GRest.kopfSperre, Block.sperreVon, Stmt.sperreVon, Option.some.injEq] at hK
        subst hK
        simp only [rufUpdateG_self]
        exact sekInv_locks T S N ls i _ hhead rfl hH h0 hstat hbal hnf hls
    | _ =>
        exfalso
        rw [‹(M.faeden u).kopf.rest = _›] at hK
        simp only [GRest.kopfSperre, reduceCtorEq, Block.sperreVon, Stmt.sperreVon] at hK
  | g3 hs =>
    cases hs with
    | _ =>
        exfalso
        rw [‹(M.faeden u).kopf.rest = _›] at hK
        simp only [GRest.kopfSperre, reduceCtorEq, Block.sperreVon, Stmt.sperreVon] at hK
  | g4 hs =>
    cases hs with
    | _ =>
        exfalso
        rw [‹(M.faeden u).kopf.rest = _›] at hK
        simp only [GRest.kopfSperre, reduceCtorEq, Block.sperreVon, Stmt.sperreVon] at hK
  | g5 hs =>
    cases hs with
    | _ =>
        exfalso
        rw [‹(M.faeden u).kopf.rest = _›] at hK
        simp only [GRest.kopfSperre, reduceCtorEq, Block.sperreVon, Stmt.sperreVon] at hK
  | g6 hs =>
    cases hs with
    | _ =>
        exfalso
        rw [‹(M.faeden u).kopf.rest = _›] at hK
        simp only [GRest.kopfSperre, reduceCtorEq, Block.sperreVon, Stmt.sperreVon] at hK
  | g7 hs =>
    cases hs with
    | rueckScopedWert ρ r e R hhead hret
    | rueckScopedWertDirekt ρ r e R hhead hret =>
      exfalso
      rcases GRest.scopedWert_faelle hret with he | ⟨rest, he⟩ | ⟨Λ', rest, k, he⟩ <;> subst r <;>
        rw [hhead] at hK <;> simp only [GRest.kopfSperre, Block.sperreVon, Stmt.sperreVon,
          Bool.false_eq_true, reduceCtorEq] at hK
    | rueckScopedGrund ρ r grund R hhead hret
    | rueckScopedGrundDirekt ρ r grund R hhead hret =>
      exfalso
      rcases GRest.scopedGrund_faelle hret with he | ⟨rest, he⟩ | ⟨Λ', rest, k, he⟩ <;> subst r <;>
        rw [hhead] at hK <;> simp only [GRest.kopfSperre, Block.sperreVon, Stmt.sperreVon,
          Bool.false_eq_true, reduceCtorEq] at hK
    | _ =>
        exfalso
        rw [‹(M.faeden u).kopf.rest = _›] at hK
        simp only [GRest.kopfSperre, reduceCtorEq, Block.sperreVon, Stmt.sperreVon] at hK

end Nimmt

end Gabbro.Grammatik
