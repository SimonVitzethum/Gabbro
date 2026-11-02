module
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreBeweis.T1
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

section Begruendet

variable {P : Programm D} {O : Orakel D} {passes : Nat} {S : SperrInv D}

/-- **Two justified answers with one key are equal** (no event): the
    determinism of the calls of machine G in such a declaration. -/
theorem begruendet_eindeutig (hE : ¬ Nonempty (Ereignis D)) {e : EintragV D}
    (h : Begruendet P O passes S e) :
    ∀ a', Begruendet P O passes S ⟨e.1, e.2.1, e.2.2.1, a'⟩ → e.2.2.2 = a' := by
  induction h with
  | mk g κ ρ a H hf _ hpred ih =>
    intro a' h2
    cases h2 with
    | mk _ _ _ _ H2 hf2 hB2 hpred2 =>
      have hfun : FunkV (H ++ H2) := by
        intro g' σ ρ' b b' m1 m2
        rcases List.mem_append.mp m1 with m1 | m1 <;> rcases List.mem_append.mp m2 with m2 | m2
        · exact hf _ _ _ _ _ m1 m2
        · exact ih _ m1 b' (hB2 _ m2)
        · exact (ih _ m2 b (hB2 _ m1)).symm
        · exact hf2 _ _ _ _ _ m1 m2
      have hp := rufAusV_passt hfun
      exact antwortet_eindeutig hE
        (hpred (rufAusV (H ++ H2)) (fun _ σ => σ)
          (fun g σ ρ a hm => hp g σ ρ a (List.mem_append_left _ hm)))
        (hpred2 (rufAusV (H ++ H2)) (fun _ σ => σ)
          (fun g σ ρ a hm => hp g σ ρ a (List.mem_append_right _ hm)))

end Begruendet
/-- Without an event there is no lock: every acquire record fits every move. -/
theorem passtU_leer (hE : ¬ Nonempty (Ereignis D)) (S : SperrInv D) (U : Umwelt D)
    (HU : List (UEintrag D)) : PasstU S U HU :=
  fun L _ _ _ => absurd ⟨.gibt L⟩ hE

theorem funkA_of_passtA {O : Orakel D} {HA : List (AxEintrag D)} (h : PasstA O HA) : FunkA HA :=
  fun a σ ρ x x' h1 h2 => (h a σ ρ x h1).symm.trans (h a σ ρ x' h2)

/-- The freshness side of a call record: every key below `N` when the
    declaration has an event; every answer justified when it has none. -/
def KurzVB (P : Programm D) (O : Orakel D) (passes : Nat) (S : SperrInv D) (N : Nat)
    (H : List (EintragV D)) : Prop :=
  (Nonempty (Ereignis D) → KurzV N H) ∧
    (¬ Nonempty (Ereignis D) → ∀ e ∈ H, Begruendet P O passes S e)

/-- The freshness side of an axiom record: every key below `N` with an
    event; the machine oracle's own answers without one. -/
def KurzAB (O : Orakel D) (N : Nat) (HA : List (AxEintrag D)) : Prop :=
  (Nonempty (Ereignis D) → KurzA N HA) ∧ (¬ Nonempty (Ereignis D) → PasstA O HA)

/-- The freshness side of an acquire record (without an event there is no
    lock and no acquire). -/
def KurzUB (N : Nat) (HU : List (UEintrag D)) : Prop :=
  Nonempty (Ereignis D) → KurzU N HU

section Kurz

variable {P : Programm D} {O : Orakel D} {passes : Nat} {S : SperrInv D}

theorem kurzVB_nil (N : Nat) : KurzVB P O passes S N ([] : List (EintragV D)) :=
  ⟨fun _ => kurzV_nil N, fun _ _ h => absurd h List.not_mem_nil⟩

theorem kurzAB_nil (N : Nat) : KurzAB O N ([] : List (AxEintrag D)) :=
  ⟨fun _ => kurzA_nil N, fun _ _ _ _ _ h => absurd h List.not_mem_nil⟩

theorem kurzUB_nil (N : Nat) : KurzUB N ([] : List (UEintrag D)) := fun _ => kurzU_nil N

theorem kurzVB_mono {N N' : Nat} {H : List (EintragV D)} (h : KurzVB P O passes S N H)
    (hN : N ≤ N') : KurzVB P O passes S N' H :=
  ⟨fun hE => kurzV_mono (h.1 hE) hN, h.2⟩

theorem kurzAB_mono {N N' : Nat} {HA : List (AxEintrag D)} (h : KurzAB O N HA) (hN : N ≤ N') :
    KurzAB O N' HA :=
  ⟨fun hE => kurzA_mono (h.1 hE) hN, h.2⟩

theorem kurzUB_mono {N N' : Nat} {HU : List (UEintrag D)} (h : KurzUB N HU) (hN : N ≤ N') :
    KurzUB N' HU :=
  fun hE => kurzU_mono (h hE) hN

/-- **A new call answer keeps the record functional**: fresh when the
    declaration has an event, justified when it has none. -/
theorem funkV_appendB {N : Nat} {H : List (EintragV D)} (hf : FunkV H)
    (hk : KurzVB P O passes S N H) (e : EintragV D)
    (he : Nonempty (Ereignis D) → N ≤ e.2.1.spur.length)
    (hb : ¬ Nonempty (Ereignis D) → Begruendet P O passes S e) : FunkV (H ++ [e]) := by
  by_cases hN : Nonempty (Ereignis D)
  · exact funkV_append hf (hk.1 hN) e (he hN)
  · intro g σ ρ a a' k1 k2
    rcases List.mem_append.mp k1 with h1 | h1 <;> rcases List.mem_append.mp k2 with h2 | h2
    · exact hf g σ ρ a a' h1 h2
    · rw [List.mem_singleton] at h2
      subst h2
      exact begruendet_eindeutig hN (e := ⟨g, σ, ρ, a⟩) (hk.2 hN _ h1) a' (hb hN)
    · rw [List.mem_singleton] at h1
      subst h1
      exact (begruendet_eindeutig hN (e := ⟨g, σ, ρ, a'⟩) (hk.2 hN _ h2) a (hb hN)).symm
    · rw [List.mem_singleton] at h1 h2
      rw [← h1] at h2
      have e2 := eq_of_heq (Sigma.mk.inj h2).2
      simp only [Prod.mk.injEq] at e2
      exact e2.2.2.symm

end Kurz
/-! ## 1. The replay invariants -/

section Inv

variable (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D) (S : SperrInv D)
  (lok : D.Tab ⊕ D.Glob → Bool)

/-- How a suspended frame continues once its pending call is answered (as
    `FortV`), over the semantics with lock invariants. -/
def FortS (F : RufRahmenG D) (g : D.Fn) (X : ZErgG (vertragVon D F.f))
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D) (U : Umwelt D) :
    RufAusgang g → Prop
  | .ok σa v =>
      (F.wartend = false → X.folgt (semH S O' U passes R F.rest.2.2.2.2 σa F.rest.2.2.2.1)) ∧
      (∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
          (restb : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ')
          (k : GRest D (vertragVon D F.f) l Γ Λ') (ρc : Env D Γ),
        (F.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ ∨
          ∃ (n : Nat) (err : Endblock D (vertragVon D F.f) l (.why n :: Γ) Λ),
            F.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩) →
        ∀ he : D.erg g = some τ,
          X.folgt (semH S O' U passes R (.dann restb (.schrumpf k)) σa (.cons (ergWert he v) ρc)))
  | .why σa r =>
      ∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty) (n : Nat)
        (err : Endblock D (vertragVon D F.f) l (.why n :: Γ) Λ)
        (restb : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ')
        (k : GRest D (vertragVon D F.f) l Γ Λ') (ρc : Env D Γ),
        F.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩ →
        ∀ hn : D.gruende g = n,
          X.folgt (semH S O' U passes R (.dann err.alsBlock.2 (.abbruch (.schrumpf k))) σa
            (.cons (Fin.cast hn r) ρc))
  | _ => True

/-- **The replay of a head frame** `F` whose thread world is `W`, with lock
    invariants. -/
def KopfS (F : RufRahmenG D) (W : World D) : Prop :=
  ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (HU : List (UEintrag D)) (σ : World D),
    ReqAmEintritt P F.f F.s0 F.rho ∧ FunkV H ∧ VertraegeOkR P H ∧
    KurzVB P O passes S σ.spur.length H ∧
    FunkA HA ∧ RahmenA HA ∧ VertragA O.zeiger Q HA ∧ KurzAB O σ.spur.length HA ∧
    FunkU HU ∧ InvU S HU ∧ KurzUB σ.spur.length HU ∧
    GleichAuf (stabilS P S lok F.f F.rest.2.2.1) σ W ∧
    F.rest.2.2.2.2.okS P (fussOrteG P F.f) (sicher P lok F.f) ∧
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (U : Umwelt D),
      PasstV R H → PasstA O' HA → PasstU S U HU → GleichRS O O' →
      (zErgG (execEndH (V := vertragVon D F.f) S O' U passes R (P.rumpf F.f) F.s0 F.rho)).folgt
        (semH S O' U passes R F.rest.2.2.2.2 σ F.rest.2.2.2.1)

/-- **The replay of a suspended frame** `F` waiting for the callee with key
    `G`. The key world agrees with the callee's machine entry world on the
    frame's stable carriers at its holdings, which contain the callee's
    contract carriers. -/
def WarteS (F : RufRahmenG D) (G : Σ f : D.Fn, Env D (D.params f) × World D) : Prop :=
  ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (HU : List (UEintrag D)) (κ : World D),
    ReqAmEintritt P F.f F.s0 F.rho ∧ FunkV H ∧ VertraegeOkR P H ∧
    KurzVB P O passes S κ.spur.length H ∧
    FunkA HA ∧ RahmenA HA ∧ VertragA O.zeiger Q HA ∧ KurzAB O κ.spur.length HA ∧
    FunkU HU ∧ InvU S HU ∧ KurzUB κ.spur.length HU ∧
    F.rest.2.2.2.2.okS P (fussOrteG P F.f) (sicher P lok F.f) ∧
    ReqAmEintritt P G.1 κ G.2.1 ∧
    (GleichAuf ((P.requires G.1).orte ++ (P.ensures G.1).orte) κ G.2.2 ∧
      (P.requires G.1).orte ++ (P.ensures G.1).orte ⊆ stabilS P S lok F.f F.rest.2.2.1 ∧
      GleichAuf (stabilS P S lok F.f F.rest.2.2.1) κ G.2.2) ∧
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (U : Umwelt D),
      PasstV R H → PasstA O' HA → PasstU S U HU → GleichRS O O' →
      FortS passes S F G.1
        (zErgG (execEndH (V := vertragVon D F.f) S O' U passes R (P.rumpf F.f) F.s0 F.rho)) R O' U
        (R G.1 κ G.2.1)

def StapelS : (Σ f : D.Fn, Env D (D.params f) × World D) → List (RufRahmenG D) → Prop
  | _, [] => True
  | G, F :: rest => WarteS P O passes Q S lok F G ∧ StapelS (RufSchluesselG F) rest

def FadenS (z : RufFadenG D) (W : World D) : Prop :=
  KopfS P O passes Q S lok z.kopf W ∧ StapelS P O passes Q S lok (RufSchluesselG z.kopf) z.stapel

def ZielInvS (M : RufMaschineG D) : Prop :=
  (∀ t, FadenS P O passes Q S lok (M.faeden t) (M.weltVon t)) ∧ ∀ t, LogOk P (M.faeden t).log

end Inv
/-- `FortS` is monotone in the predicted result. -/
theorem fortS_mono {passes : Nat} {S : SperrInv D} {F : RufRahmenG D} {g : D.Fn}
    {X Y : ZErgG (vertragVon D F.f)}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f} {O' : Orakel D} {U : Umwelt D}
    (hXY : X.folgt Y) :
    ∀ {a : RufAusgang g}, FortS passes S F g Y R O' U a → FortS passes S F g X R O' U a
  | .ok _ _, h => ⟨fun hw => ZErgG.folgt_trans hXY (h.1 hw),
      fun l Γ Λ Λ' τ restb k ρc hc he => ZErgG.folgt_trans hXY (h.2 l Γ Λ Λ' τ restb k ρc hc he)⟩
  | .why _ _, h => fun l Γ Λ Λ' τ n err restb k ρc hc hn =>
      ZErgG.folgt_trans hXY (h l Γ Λ Λ' τ n err restb k ρc hc hn)
  | .logik _, _ => trivial
  | .hardware _, _ => trivial

/-! ## 2. The steps of the replay -/


end Gabbro.Grammatik
