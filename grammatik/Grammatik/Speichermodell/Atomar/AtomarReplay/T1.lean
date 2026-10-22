/-
  File:      Grammatik/Speichermodell/AtomarReplay.lean
  Subject:   THE REPLAY WITH THE ATOMIC RELY, part 2: the footprint property with shared
             atomics, the replay invariant `KopfSA` ... `ZielInvSA` (SperreBeweis.lean with one
             more record, `HX`, the atomic reads) and its generic steps. Opus lane O25b,
             2026-09-26, OFFEN O25. Standalone.

  `Tg` is the set of SHARED atomics of the run: carriers another thread may change with nothing
  in the program ordering it. What the footprint property `FussSX` demands of them: nothing at a
  body read (that is the exemption), and that they occur in NO contract (`VertragsFrei`:
  no `requires`, `ensures` or owed invariant reads them) -- a contract over a value that races
  would be a claim about a moment nobody can name. So every contract carrier stays STABLE, as
  in `ziel_ort_sperre`, and only body reads may see the rely.
-/
import Grammatik.Speichermodell.Atomar.AtomarRec

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The footprint property with shared atomics -/

/-- `c` occurs in no contract of the program: no `requires`, no `ensures`, no owed invariant. -/
def VertragsFrei (P : Programm D) (c : D.Tab ⊕ D.Glob) : Prop :=
  ∀ g, c ∉ (P.requires g).orte ∧ c ∉ (P.ensures g).orte ∧ c ∉ invOrteP P g

/-- **The footprint property with shared atomics**: `FussS` with one more disjunct at a
    footprint carrier, "the carrier is a shared atomic" (`Tg c`). Device carriers unchanged. -/
def FussSX (P : Programm D) (S : SperrInv D) (lok : D.Tab ⊕ D.Glob → Bool)
    (Tg : D.Tab ⊕ D.Glob → Prop) (f : D.Fn) : Prop :=
  (∀ c ∈ fussOrte P f, (sigB f c || lok c) = true ∨ (∃ L, Bewacht c L ∧ c ∈ S.orte L) ∨ Tg c) ∧
  (∀ c ∈ (P.rumpf f).regs.flatMap D.rtraeger, (sigB f c || lok c) = true)

theorem fussSX_of_fussS {P : Programm D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool}
    {Tg : D.Tab ⊕ D.Glob → Prop} {f : D.Fn} (h : FussS P S lok f) : FussSX P S lok Tg f :=
  ⟨fun c hc => (h.1 c hc).elim Or.inl (fun h => Or.inr (Or.inl h)), h.2⟩

section Stabil

variable {P : Programm D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool}
  {Tg : D.Tab ⊕ D.Glob → Prop} {f : D.Fn}

/-- A footprint carrier whose guards are held is stable or a shared atomic. -/
theorem stabil_of_fussX (hF : FussSX P S lok Tg f) {Λ : List (Res D)} {c : D.Tab ⊕ D.Glob}
    (hc : c ∈ fussOrteG P f) (hw : ∀ L, Bewacht c L → Res.held L ∈ Λ) :
    c ∈ stabilS P S lok f Λ ∨ Tg c := by
  rcases List.mem_append.mp hc with hc1 | hc2
  · rcases hF.1 c hc1 with h | ⟨L, hB, hL⟩ | h
    · exact Or.inl (stabilS_mem.mpr (Or.inl (sicher_mem.mpr ⟨hc, h⟩)))
    · exact Or.inl (stabilS_mem.mpr (Or.inr ⟨L, hw L hB, hL⟩))
    · exact Or.inr h
  · exact Or.inl (stabilS_mem.mpr (Or.inl (sicher_mem.mpr ⟨hc, hF.2 c hc2⟩)))

/-- **The carriers a read touches are stable or shared atomics.** -/
theorem orte_stabilX (hF : FussSX P S lok Tg f) {os : List (D.Tab ⊕ D.Glob)}
    {Λ : List (Res D)} (hd : ∀ o ∈ os, OrtDarf Λ o) (h : os ⊆ fussOrteG P f) :
    ∀ c ∈ os, c ∈ stabilS P S lok f Λ ∨ Tg c :=
  fun _ ho => stabil_of_fussX hF (h ho) fun _ hB => bewacht_held (hd _ ho) hB

theorem expr_stabilX (hF : FussSX P S lok Tg f) {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ) (h : e.orte ⊆ fussOrteG P f) :
    ∀ c ∈ e.orte, c ∈ stabilS P S lok f Λ ∨ Tg c :=
  orte_stabilX hF e.orte_darf h

theorem args_stabilX (hF : FussSX P S lok Tg f) {Γ : Ctx} {Λ : List (Res D)} {τs : List Ty}
    (a : Args D Γ Λ τs) (h : a.orte ⊆ fussOrteG P f) :
    ∀ c ∈ a.orte, c ∈ stabilS P S lok f Λ ∨ Tg c :=
  orte_stabilX hF a.orte_darf h

theorem erg_stabilX (hF : FussSX P S lok Tg f) {Γ : Ctx} {Λ : List (Res D)} {τ : Option Ty}
    (e : ErgExpr D Γ Λ τ) (h : e.orte ⊆ fussOrteG P f) :
    ∀ c ∈ e.orte, c ∈ stabilS P S lok f Λ ∨ Tg c :=
  orte_stabilX hF e.orte_darf h

/-- **A callee's contract carriers are stable at the call** (shared atomics are in no
    contract). -/
theorem vertrag_stabilX (hF : FussSX P S lok Tg f) (hTV : ∀ c, Tg c → VertragsFrei P c)
    {V : Vertrag D} {Λ : List (Res D)} (g : D.Fn) (hp : RufPasst D V (D.signatur g) Λ)
    (h : (P.requires g).orte ++ (P.ensures g).orte ⊆ fussOrteG P f) :
    (P.requires g).orte ++ (P.ensures g).orte ⊆ stabilS P S lok f Λ := by
  intro o ho
  rcases stabil_of_fussX hF (h ho) (fun L hB => hp.hh L (vertrag_darf P g _ ho L hB)) with h' | h'
  · exact h'
  · exfalso
    rcases List.mem_append.mp ho with ho | ho
    · exact (hTV o h' g).1 ho
    · exact (hTV o h' g).2.1 ho

theorem vertrag_stabilX_ind (hF : FussSX P S lok Tg f) (hTV : ∀ c, Tg c → VertragsFrei P c)
    {V : Vertrag D} {Λ : List (Res D)} {n : Nat} (g : D.Fn) (hg : D.passt g n = true)
    (hp : RufPasst D V (D.sigNr n) Λ)
    (h : (P.requires g).orte ++ (P.ensures g).orte ⊆ fussOrteG P f) :
    (P.requires g).orte ++ (P.ensures g).orte ⊆ stabilS P S lok f Λ := by
  replace hp := RufPasst.vonPasst (D.passt_sig hg) hp
  exact vertrag_stabilX hF hTV g hp h

/-- **The own `ensures` carriers are stable at a return.** -/
theorem ens_stabilX (hF : FussSX P S lok Tg f) (hTV : ∀ c, Tg c → VertragsFrei P c)
    {Λ : List (Res D)} (hperm : Λ.Perm (vertragVon D f).ende) :
    (P.ensures f).orte ⊆ stabilS P S lok f Λ := by
  intro o ho
  rcases stabil_of_fussX hF (fuss_ensG P f ho) (fun _ hB =>
    hperm.symm.mem_iff.mp (bewacht_held ((P.ensures f).orte_darf _ ho) hB)) with h | h
  · exact h
  · exact absurd ho (hTV o h f).2.1

end Stabil
/-! ## 2. Justified answers over `execStmtHA` (declarations without an event) -/

section Begruendet

variable (P : Programm D) (O : Orakel D) (passes : Nat) (S : SperrInv D)

/-- **A justified call answer** over the semantics with the atomic rely (as `Begruendet`). -/
inductive BegruendetA : EintragV D → Prop
  | mk (g : D.Fn) (κ : World D) (ρ : Env D (D.params g)) (a : RufAusgang g)
      (H : List (EintragV D)) :
      FunkV H → (∀ e ∈ H, BegruendetA e) →
      (∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (U : Umwelt D)
        (A : AUmwelt D), PasstV R H →
          Antwortet (execEndHA (V := vertragVon D g) S O U A passes R (P.rumpf g) κ ρ) a) →
      BegruendetA ⟨g, κ, ρ, a⟩

variable {P O passes S}

theorem begruendetA_eindeutig (hE : ¬ Nonempty (Ereignis D)) {e : EintragV D}
    (h : BegruendetA P O passes S e) :
    ∀ a', BegruendetA P O passes S ⟨e.1, e.2.1, e.2.2.1, a'⟩ → e.2.2.2 = a' := by
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
        (hpred (rufAusV (H ++ H2)) (fun _ σ => σ) idA
          (fun g σ ρ a hm => hp g σ ρ a (List.mem_append_left _ hm)))
        (hpred2 (rufAusV (H ++ H2)) (fun _ σ => σ) idA
          (fun g σ ρ a hm => hp g σ ρ a (List.mem_append_right _ hm)))

/-- The freshness side of a call record over the new semantics. -/
def KurzVBA (N : Nat) (H : List (EintragV D)) : Prop :=
  (Nonempty (Ereignis D) → KurzV N H) ∧
    (¬ Nonempty (Ereignis D) → ∀ e ∈ H, BegruendetA P O passes S e)

theorem kurzVBA_nil (N : Nat) : KurzVBA (P := P) (O := O) (passes := passes) (S := S) N
    ([] : List (EintragV D)) :=
  ⟨fun _ => kurzV_nil N, fun _ _ h => absurd h List.not_mem_nil⟩

theorem kurzVBA_mono {N N' : Nat} {H : List (EintragV D)}
    (h : KurzVBA (P := P) (O := O) (passes := passes) (S := S) N H) (hN : N ≤ N') :
    KurzVBA (P := P) (O := O) (passes := passes) (S := S) N' H :=
  ⟨fun hE => kurzV_mono (h.1 hE) hN, h.2⟩

theorem funkV_appendBA {N : Nat} {H : List (EintragV D)} (hf : FunkV H)
    (hk : KurzVBA (P := P) (O := O) (passes := passes) (S := S) N H) (e : EintragV D)
    (he : Nonempty (Ereignis D) → N ≤ e.2.1.spur.length)
    (hb : ¬ Nonempty (Ereignis D) → BegruendetA P O passes S e) : FunkV (H ++ [e]) := by
  by_cases hN : Nonempty (Ereignis D)
  · exact funkV_append hf (hk.1 hN) e (he hN)
  · intro g σ ρ a a' k1 k2
    rcases List.mem_append.mp k1 with h1 | h1 <;> rcases List.mem_append.mp k2 with h2 | h2
    · exact hf g σ ρ a a' h1 h2
    · rw [List.mem_singleton] at h2
      subst h2
      exact begruendetA_eindeutig hN (e := ⟨g, σ, ρ, a⟩) (hk.2 hN _ h1) a' (hb hN)
    · rw [List.mem_singleton] at h1
      subst h1
      exact (begruendetA_eindeutig hN (e := ⟨g, σ, ρ, a'⟩) (hk.2 hN _ h2) a (hb hN)).symm
    · rw [List.mem_singleton] at h1 h2
      rw [← h1] at h2
      have e2 := eq_of_heq (Sigma.mk.inj h2).2
      simp only [Prod.mk.injEq] at e2
      exact e2.2.2.symm

end Begruendet
/-- Without an event every environment is the identity and every record fits. -/
theorem havocA_leer (hE : ¬ Nonempty (Ereignis D)) (T : D.Tab ⊕ D.Glob → Prop) (A : AUmwelt D) :
    HavocA T A :=
  fun X σ => ⟨by rw [welt_eq hE (A X σ) σ], fun c _ => by
    rw [welt_eq hE (A X σ) σ]; exact traegerGleich_refl _ c⟩

theorem passtX_leer (hE : ¬ Nonempty (Ereignis D)) (T : D.Tab ⊕ D.Glob → Prop) (A : AUmwelt D)
    (HX : List (XEintrag D)) : PasstX T A HX :=
  fun _ _ _ _ => welt_eq hE _ _

/-! ## 3. The replay invariants -/

section Inv

variable (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D) (S : SperrInv D)
  (lok : D.Tab ⊕ D.Glob → Bool) (Tg : D.Tab ⊕ D.Glob → Prop)

/-- How a suspended frame continues once its pending call is answered (as `FortS`). -/
def FortSA (F : RufRahmenG D) (g : D.Fn) (X : ZErgG (vertragVon D F.f))
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D) (U : Umwelt D)
    (A : AUmwelt D) : RufAusgang g → Prop
  | .ok σa v =>
      (F.wartend = false → X.folgt (semHA S O' U A passes R F.rest.2.2.2.2 σa F.rest.2.2.2.1)) ∧
      (∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
          (restb : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ')
          (k : GRest D (vertragVon D F.f) l Γ Λ') (ρc : Env D Γ),
        (F.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ ∨
          ∃ (n : Nat) (err : Endblock D (vertragVon D F.f) l (.why n :: Γ) Λ),
            F.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩) →
        ∀ he : D.erg g = some τ,
          X.folgt (semHA S O' U A passes R (.dann restb (.schrumpf k)) σa (.cons (ergWert he v) ρc)))
  | .why σa r =>
      ∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty) (n : Nat)
        (err : Endblock D (vertragVon D F.f) l (.why n :: Γ) Λ)
        (restb : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ')
        (k : GRest D (vertragVon D F.f) l Γ Λ') (ρc : Env D Γ),
        F.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩ →
        ∀ hn : D.gruende g = n,
          X.folgt (semHA S O' U A passes R (.dann err.alsBlock.2 (.abbruch (.schrumpf k))) σa
            (.cons (Fin.cast hn r) ρc))
  | _ => True

/-- **The replay of a head frame** with the atomic rely: `KopfS` with the record `HX` of atomic
    reads, and every prediction for every environment in the class repeating it. -/
def KopfSA (F : RufRahmenG D) (W : World D) : Prop :=
  ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (HU : List (UEintrag D))
    (HX : List (XEintrag D)) (σ : World D),
    ReqAmEintritt P F.f F.s0 F.rho ∧ FunkV H ∧ VertraegeOkR P H ∧
    KurzVBA (P := P) (O := O) (passes := passes) (S := S) σ.spur.length H ∧
    FunkA HA ∧ RahmenA HA ∧ VertragA O.zeiger Q HA ∧ KurzAB O σ.spur.length HA ∧
    FunkU HU ∧ InvU S HU ∧ KurzUB σ.spur.length HU ∧
    (FunkX HX ∧ KurzX σ.spur.length HX) ∧
    GleichAuf (stabilS P S lok F.f F.rest.2.2.1) σ W ∧
    F.rest.2.2.2.2.okS P (fussOrteG P F.f) (sicher P lok F.f) ∧
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (U : Umwelt D) (A : AUmwelt D),
      PasstV R H → PasstA O' HA → PasstU S U HU → PasstX Tg A HX → HavocA Tg A → GleichRS O O' →
      (zErgG (execEndHA (V := vertragVon D F.f) S O' U A passes R (P.rumpf F.f) F.s0 F.rho)).folgt
        (semHA S O' U A passes R F.rest.2.2.2.2 σ F.rest.2.2.2.1)

/-- **The replay of a suspended frame** with the atomic rely. -/
def WarteSA (F : RufRahmenG D) (G : Σ f : D.Fn, Env D (D.params f) × World D) : Prop :=
  ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (HU : List (UEintrag D))
    (HX : List (XEintrag D)) (κ : World D),
    ReqAmEintritt P F.f F.s0 F.rho ∧ FunkV H ∧ VertraegeOkR P H ∧
    KurzVBA (P := P) (O := O) (passes := passes) (S := S) κ.spur.length H ∧
    FunkA HA ∧ RahmenA HA ∧ VertragA O.zeiger Q HA ∧ KurzAB O κ.spur.length HA ∧
    FunkU HU ∧ InvU S HU ∧ KurzUB κ.spur.length HU ∧
    (FunkX HX ∧ KurzX κ.spur.length HX) ∧
    F.rest.2.2.2.2.okS P (fussOrteG P F.f) (sicher P lok F.f) ∧
    ReqAmEintritt P G.1 κ G.2.1 ∧
    (GleichAuf ((P.requires G.1).orte ++ (P.ensures G.1).orte) κ G.2.2 ∧
      (P.requires G.1).orte ++ (P.ensures G.1).orte ⊆ stabilS P S lok F.f F.rest.2.2.1 ∧
      GleichAuf (stabilS P S lok F.f F.rest.2.2.1) κ G.2.2) ∧
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (U : Umwelt D) (A : AUmwelt D),
      PasstV R H → PasstA O' HA → PasstU S U HU → PasstX Tg A HX → HavocA Tg A → GleichRS O O' →
      FortSA passes S F G.1
        (zErgG (execEndHA (V := vertragVon D F.f) S O' U A passes R (P.rumpf F.f) F.s0 F.rho)) R O'
        U A (R G.1 κ G.2.1)

def StapelSA : (Σ f : D.Fn, Env D (D.params f) × World D) → List (RufRahmenG D) → Prop
  | _, [] => True
  | G, F :: rest => WarteSA P O passes Q S lok Tg F G ∧ StapelSA (RufSchluesselG F) rest

def FadenSA (z : RufFadenG D) (W : World D) : Prop :=
  KopfSA P O passes Q S lok Tg z.kopf W ∧ StapelSA P O passes Q S lok Tg (RufSchluesselG z.kopf) z.stapel

def ZielInvSA (M : RufMaschineG D) : Prop :=
  (∀ t, FadenSA P O passes Q S lok Tg (M.faeden t) (M.weltVon t)) ∧ ∀ t, LogOk P (M.faeden t).log

end Inv
/-- `FortSA` is monotone in the predicted result. -/
theorem fortSA_mono {passes : Nat} {S : SperrInv D} {F : RufRahmenG D} {g : D.Fn}
    {X Y : ZErgG (vertragVon D F.f)}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f} {O' : Orakel D} {U : Umwelt D}
    {A : AUmwelt D} (hXY : X.folgt Y) :
    ∀ {a : RufAusgang g}, FortSA passes S F g Y R O' U A a → FortSA passes S F g X R O' U A a
  | .ok _ _, h => ⟨fun hw => ZErgG.folgt_trans hXY (h.1 hw),
      fun l Γ Λ Λ' τ restb k ρc hc he => ZErgG.folgt_trans hXY (h.2 l Γ Λ Λ' τ restb k ρc hc he)⟩
  | .why _ _, h => fun l Γ Λ Λ' τ n err restb k ρc hc hn =>
      ZErgG.folgt_trans hXY (h l Γ Λ Λ' τ n err restb k ρc hc hn)
  | .logik _, _ => trivial
  | .hardware _, _ => trivial

/-! ## 4. The generic steps -/


end Gabbro.Grammatik
