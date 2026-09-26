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
import Grammatik.Speichermodell.AtomarRec

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
    {V : Vertrag D} {Λ : List (Res D)} {n : Nat} (g : D.Fn) (hg : D.sig g = n)
    (hp : RufPasst D V (D.sigNr n) Λ)
    (h : (P.requires g).orte ++ (P.ensures g).orte ⊆ fussOrteG P f) :
    (P.requires g).orte ++ (P.ensures g).orte ⊆ stabilS P S lok f Λ := by
  subst hg
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
          ∃ (n : Nat) (err : Endblock D (vertragVon D F.f) l (.grund n :: Γ) Λ),
            F.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩) →
        ∀ he : D.erg g = some τ,
          X.folgt (semHA S O' U A passes R (.dann restb (.schrumpf k)) σa (.cons (ergWert he v) ρc)))
  | .grund σa r =>
      ∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty) (n : Nat)
        (err : Endblock D (vertragVon D F.f) l (.grund n :: Γ) Λ)
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
  | .grund _ _, h => fun l Γ Λ Λ' τ n err restb k ρc hc hn =>
      ZErgG.folgt_trans hXY (h l Γ Λ Λ' τ n err restb k ρc hc hn)
  | .logik _, _ => trivial
  | .hardware _, _ => trivial

/-! ## 4. The generic steps -/

section Schritte

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop}

theorem kopfSA_okS {F : RufRahmenG D} {W : World D} (h : KopfSA P O passes Q S lok Tg F W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D F.f) l Γ Λ} (hr : F.rest = ⟨l, Γ, Λ, ρ, r⟩) :
    r.okS P (fussOrteG P F.f) (sicher P lok F.f) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hok, _⟩ := h
  rw [hr] at hok
  exact hok

/-- **A head-local step** (as `fadenS_lokalQ`): the step may extend the record of atomic reads
    (a read of a shared atomic), and its residue semantics is followed for every environment
    repeating the extended record. -/
theorem fadenSA_lokalQ {z : RufFadenG D} {W W' : World D}
    (hF : FadenSA P O passes Q S lok Tg z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (hstep : ∀ (σ : World D) (HX : List (XEintrag D)), FunkX HX → KurzX σ.spur.length HX →
      GleichAuf (stabilS P S lok z.kopf.f Λ) σ W →
      r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      ∃ (σ' : World D) (HX' : List (XEintrag D)), FunkX HX' ∧ KurzX σ'.spur.length HX' ∧
        (∀ e ∈ HX, e ∈ HX') ∧
        σ.spur.length ≤ σ'.spur.length ∧ GleichAuf (stabilS P S lok z.kopf.f Λ') σ' W' ∧
        r'.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) ∧
        ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
          (U : Umwelt D) (A : AUmwelt D), PasstX Tg A HX' → HavocA Tg A → GleichRS O O' →
          (semHA S O' U A passes R r σ ρ).folgt (semHA S O' U A passes R r' σ' ρ')) :
    FadenSA P O passes Q S lok Tg
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩ W' := by
  obtain ⟨⟨H, HA, HU, HX, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, ⟨hfx, hkx⟩, hg,
    hok, heq⟩, hS⟩ := hF
  have hok' : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) := by rw [hr] at hok; exact hok
  have hg0 : GleichAuf (stabilS P S lok z.kopf.f Λ) σ W := by rw [hr] at hg; exact hg
  obtain ⟨σ', HX', hfx', hkx', hsub, hl, hg', hok'', hsem⟩ := hstep σ HX hfx hkx hg0 hok'
  refine ⟨⟨H, HA, HU, HX', σ', hreq, hf, hv, kurzVBA_mono hk hl, hfa, hra, hqa, kurzAB_mono hka hl,
    hfu, hiu, kurzUB_mono hku hl, ⟨hfx', hkx'⟩, hg', hok'', fun R O' U A hR hA hU hX hHA hQ => ?_⟩,
    hS⟩
  have h1 := heq R O' U A hR hA hU (passtX_teil hsub hX) hHA hQ
  rw [hr] at h1
  exact ZErgG.folgt_trans h1 (hsem R O' U A hX hHA hQ)

/-- A head-local step with no read of a shared atomic and a semantics that holds for every
    oracle and environment (the record stays). -/
theorem fadenSA_lokal {z : RufFadenG D} {W W' : World D}
    (hF : FadenSA P O passes Q S lok Tg z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (hstep : ∀ σ : World D, GleichAuf (stabilS P S lok z.kopf.f Λ) σ W →
      r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      σ.spur.length = σ.spur.length ∧ GleichAuf (stabilS P S lok z.kopf.f Λ') σ W' ∧
        r'.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) ∧
        ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
          (U : Umwelt D) (A : AUmwelt D),
          (semHA S O' U A passes R r σ ρ).folgt (semHA S O' U A passes R r' σ ρ')) :
    FadenSA P O passes Q S lok Tg
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩ W' :=
  fadenSA_lokalQ hF hr ρ' r' spur' fun σ HX hfx hkx hg hok => by
    obtain ⟨_, hg', hok', hsem⟩ := hstep σ hg hok
    exact ⟨σ, HX, hfx, hkx, fun _ h => h, Nat.le_refl _, hg', hok',
      fun R O' U A _ _ _ => hsem R O' U A⟩

/-- **A head-local step that READS the list `X`** (every carrier of it stable or a shared
    atomic): the read is recorded, the sequential world after it holds the machine's presented
    values at the read shared atomics (`mischT`), and the step continues from there. -/
theorem fadenSA_lese {z : RufFadenG D} {W W' : World D}
    (hF : FadenSA P O passes Q S lok Tg z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (Λr : List (Res D)) (X : List (D.Tab ⊕ D.Glob))
    (hX : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      ∀ c ∈ X, c ∈ stabilS P S lok z.kopf.f Λ ∨ Tg c)
    (hstep : ∀ σ : World D, GleichAuf (stabilS P S lok z.kopf.f Λ ++ X) σ (W.lese Λr X) →
      r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      ∃ σ' : World D, σ.spur.length ≤ σ'.spur.length ∧
        GleichAuf (stabilS P S lok z.kopf.f Λ') σ' W' ∧
        r'.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) ∧
        ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
          (U : Umwelt D) (A : AUmwelt D) (σ0 : World D), GleichRS O O' →
          GleichAuf (stabilS P S lok z.kopf.f Λ) σ0 W → leseA A σ0 Λr X = σ →
          (semHA S O' U A passes R r σ0 ρ).folgt (semHA S O' U A passes R r' σ' ρ')) :
    FadenSA P O passes Q S lok Tg
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩ W' := by
  refine fadenSA_lokalQ hF hr ρ' r' spur' fun σ HX hfx hkx hg hok => ?_
  obtain ⟨HX', hfx', hkx', hsub, hrec⟩ := lese_schritt Tg hfx hkx Λr X W.speicher
  have hgX := mischT_gleichAuf hg (hX hok) Λr Λr
  obtain ⟨σ', hl, hg', hok', hsem⟩ := hstep _ hgX hok
  refine ⟨σ', HX', hfx', kurzX_mono hkx' hl, hsub, Nat.le_trans (lese_laenge σ Λr X) hl, hg', hok',
    fun R O' U A hPX hHA hQ => hsem R O' U A σ hQ hg (hrec A hPX hHA)⟩

/-- Memory moved outside the head's stable carriers keeps the replay. -/
theorem fadenSA_speicher {z : RufFadenG D} {W W' : World D}
    (hF : FadenSA P O passes Q S lok Tg z W)
    (hw : ∀ c ∈ stabilS P S lok z.kopf.f z.kopf.rest.2.2.1,
      TraegerGleich W'.speicher W.speicher c) :
    FadenSA P O passes Q S lok Tg z W' := by
  obtain ⟨⟨H, HA, HU, HX, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, hx, hg, hok,
    heq⟩, hS⟩ := hF
  refine ⟨⟨H, HA, HU, HX, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, hx,
    ⟨fun t ht => ?_, fun g hg' => ?_⟩, hok, heq⟩, hS⟩
  · exact (hg.1 t ht).trans (hw (.inl t) ht).symm
  · exact (hg.2 g hg').trans (hw (.inr g) hg').symm

/-- **The return leg** (as `popS_ens`): the returned expression may read shared atomics; the
    read is answered by a record made here. -/
theorem popSA_ens (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f) {G : RufRahmenG D}
    {W : World D} (hG : KopfSA P O passes Q S lok Tg G W) {lr : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {ρ : Env D Γ} {r : GRest D (vertragVon D G.f) lr Γ Λ}
    (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩)
    (e : ErgExpr D Γ Λ (vertragVon D G.f).erg)
    (he : ∀ c ∈ e.orte, c ∈ stabilS P S lok G.f Λ ∨ Tg c)
    (hens : (P.ensures G.f).orte ⊆ stabilS P S lok G.f Λ)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (A : AUmwelt D) (σ : World D), (semHA S O' U A passes R r σ ρ).gleich
        (.zurueck (leseA A σ Λ e.orte) (evalErg (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ))) :
    EnsAmRueck P G.f G.s0 (W.lese Λ e.orte) G.rho
      (evalErg (W.lese Λ e.orte) e (W.lese Λ e.orte) ρ) := by
  obtain ⟨H, HA, HU, HX, σ, hreq, hf, hv, _, hfa, hra, hqa, _, hfu, hiu, _, ⟨hfx, hkx⟩, hg, _,
    heq⟩ := hG
  obtain ⟨HX', hfx', _, hsub, hrec⟩ := lese_schritt Tg hfx hkx Λ e.orte W.speicher
  have hPX := umweltAusA_passt Tg hfx'
  have hHA := umweltAusA_ok Tg HX'
  have h1 := heq (rufAusV H) (orakelAus O HA) (umweltAus S sp HU) (umweltAusA Tg HX')
    (rufAusV_passt hf) (orakelAus_passt O hfa) (umweltAus_passt S sp hfu) (passtX_teil hsub hPX)
    hHA (gleichRS_orakelAus O HA)
  rw [hr] at h1 hg
  simp only at h1 hg
  have h2 := ZErgG.folgt_zurueck (ZErgG.folgt_trans h1
    (ZErgG.folgt_of_gleich (hsem _ _ _ (umweltAusA Tg HX') σ)))
  obtain ⟨σ'', hex, hsg⟩ := zErgG_gleich_zurueck h2
  have hE := ((hK G.f).1 (orakelAus O HA) (orakelAus_rahmen hO hra) (regLokal_orakelAus hRL HA)
    (orakelAus_vertrag hQ hqa) (umweltAus S sp HU) (umweltAus_ok hS hsp hiu) (umweltAusA Tg HX')
    hHA (rufAusV H) (rufAusV_rahmen hv) (rufAusV_ohneVorbedingung hv.1) G.s0 G.rho hreq).1 σ'' _ hex
  rw [hrec _ hPX hHA] at hE hsg
  have hgl := mischT_gleichAuf hg he Λ Λ
  rw [evalErg_gleichAuf e (fun _ h => List.mem_append_right _ h) hgl ρ] at hE
  exact ens_transfer hE (GleichAuf.refl _ _)
    (GleichAuf.mono (fun _ h => List.mem_append_left _ (hens h)) ((gleichAuf_SG hsg).trans hgl))

/-- **The call leg** (as `pushS_req`), for a caller whose record repeats `HX`. -/
theorem pushSA_req (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f) {F : RufRahmenG D}
    {H : List (EintragV D)} {HA : List (AxEintrag D)} {HU : List (UEintrag D)}
    {HX : List (XEintrag D)} {σ : World D}
    (hreq : ReqAmEintritt P F.f F.s0 F.rho) (hf : FunkV H) (hv : VertraegeOkR P H)
    (hfa : FunkA HA) (hra : RahmenA HA) (hqa : VertragA O.zeiger Q HA) (hfu : FunkU HU)
    (hiu : InvU S HU) (hfx : FunkX HX)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    (r : GRest D (vertragVon D F.f) l Γ Λ)
    (heq : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (U : Umwelt D) (A : AUmwelt D), PasstV R H → PasstA O' HA → PasstU S U HU →
      PasstX Tg A HX → HavocA Tg A → GleichRS O O' →
      (zErgG (execEndHA (V := vertragVon D F.f) S O' U A passes R (P.rumpf F.f) F.s0 F.rho)).folgt
        (semHA S O' U A passes R r σ ρ))
    (g : D.Fn) (κ : World D) (ρk : Env D (D.params g))
    (hlogik : ∀ (O' : Orakel D) (U : Umwelt D) (A : AUmwelt D) R (e : Logik D),
      PasstX Tg A HX → HavocA Tg A → R g κ ρk = .logik e →
      semHA S O' U A passes R r σ ρ = .logik e) :
    ReqAmEintritt P g κ ρk := by
  cases hq : wahr? (eval κ (P.requires g) κ ρk) with
  | true => exact hq
  | false =>
      exfalso
      have htor : torRuf P (rufAusV H) g κ ρk = .logik (.vorbedingung g) := by
        simp only [torRuf, hq]
        rfl
      have hPX := umweltAusA_passt Tg hfx
      have hHA := umweltAusA_ok Tg HX
      have h1 := heq _ (orakelAus O HA) (umweltAus S sp HU) (umweltAusA Tg HX)
        (torRuf_passtV (rufAusV_passt hf) hv.1) (orakelAus_passt O hfa) (umweltAus_passt S sp hfu)
        hPX hHA (gleichRS_orakelAus O HA)
      rw [hlogik _ _ _ _ _ hPX hHA htor] at h1
      have hex := zErgG_gleich_logik (ZErgG.folgt_logik h1)
      exact ((hK F.f).1 (orakelAus O HA) (orakelAus_rahmen hO hra) (regLokal_orakelAus hRL HA)
        (orakelAus_vertrag hQ hqa) (umweltAus S sp HU) (umweltAus_ok hS hsp hiu)
        (umweltAusA Tg HX) hHA (rufAusV H) (rufAusV_rahmen hv) (rufAusV_ohneVorbedingung hv.1)
        F.s0 F.rho hreq).2 g hex

/-- **A returning head justifies its answer** (no event, as `popS_begr_ok`). -/
theorem popSA_begr_ok (hE : ¬ Nonempty (Ereignis D)) {G : RufRahmenG D} {W : World D}
    (hG : KopfSA P O passes Q S lok Tg G W) {lr : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D G.f) lr Γ Λ} (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩)
    (e : ErgExpr D Γ Λ (vertragVon D G.f).erg)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (A : AUmwelt D) (σ : World D), (semHA S O' U A passes R r σ ρ).gleich
        (.zurueck (leseA A σ Λ e.orte) (evalErg (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ))) :
    BegruendetA P O passes S
      ⟨G.f, G.s0, G.rho, .ok G.s0 (evalErg (W.lese Λ e.orte) e (W.lese Λ e.orte) ρ)⟩ := by
  obtain ⟨H, HA, HU, HX, σ, _, hf, _, hk, _, _, _, hka, _, _, _, _, _, _, heq⟩ := hG
  obtain rfl : σ = W := welt_eq hE σ W
  refine .mk _ _ _ _ H hf (hk.2 hE) (fun R U A hR => ?_)
  have h1 := heq R O U A hR (hka.2 hE) (passtU_leer hE S U HU) (passtX_leer hE Tg A HX)
    (havocA_leer hE Tg A) ⟨rfl, rfl, rfl⟩
  rw [hr] at h1
  simp only at h1
  have h2 := ZErgG.folgt_zurueck (ZErgG.folgt_trans h1 (ZErgG.folgt_of_gleich (hsem _ _ _ A σ)))
  obtain ⟨σ'', hex, _⟩ := zErgG_gleich_zurueck h2
  have e1 : leseA A σ Λ e.orte = σ.lese Λ e.orte := welt_eq hE _ _
  rw [e1] at hex
  exact ⟨σ'', hex⟩

/-- The same for a head at a REASON return. -/
theorem popSA_begr_grund (hE : ¬ Nonempty (Ereignis D)) {G : RufRahmenG D} {W : World D}
    (hG : KopfSA P O passes Q S lok Tg G W) {lr : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D G.f) lr Γ Λ} (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩)
    (rg : Fin (vertragVon D G.f).gruende)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (A : AUmwelt D) (σ : World D),
      (semHA S O' U A passes R r σ ρ).gleich (.grund σ rg)) :
    BegruendetA P O passes S ⟨G.f, G.s0, G.rho, .grund G.s0 rg⟩ := by
  obtain ⟨H, HA, HU, HX, σ, _, hf, _, hk, _, _, _, hka, _, _, _, _, _, _, heq⟩ := hG
  refine .mk _ _ _ _ H hf (hk.2 hE) (fun R U A hR => ?_)
  have h1 := heq R O U A hR (hka.2 hE) (passtU_leer hE S U HU) (passtX_leer hE Tg A HX)
    (havocA_leer hE Tg A) ⟨rfl, rfl, rfl⟩
  rw [hr] at h1
  simp only at h1
  have h2 := ZErgG.folgt_grund (ZErgG.folgt_trans h1 (ZErgG.folgt_of_gleich (hsem _ _ _ A σ)))
  obtain ⟨σ'', hex, _⟩ := zErgG_gleich_grund h2
  exact ⟨σ'', hex⟩

/-- **The caller resumes** (as `popS_kopf`). -/
theorem popSA_kopf {F : RufRahmenG D}
    {G : Σ f : D.Fn, Env D (D.params f) × World D}
    (hW : WarteSA P O passes Q S lok Tg F G) (s1 : World D) (mk : World D → RufAusgang G.1)
    (hmk : (∃ v, (∀ σa, mk σa = .ok σa v) ∧ EnsAmRueck P G.1 G.2.2 s1 G.2.1 v) ∨
      (∃ r, ∀ σa, mk σa = .grund σa r))
    (hb : ¬ Nonempty (Ereignis D) → BegruendetA P O passes S ⟨G.1, G.2.2, G.2.1, mk G.2.2⟩)
    (hRah : GleichOhne G.1 (stabilS P S lok F.f F.rest.2.2.1) G.2.2 s1)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ' : Env D Γ) (r' : GRest D (vertragVon D F.f) l Γ Λ)
    (hΛ : ∀ L, Res.held L ∈ Λ → Res.held L ∈ F.rest.2.2.1)
    (hok' : F.rest.2.2.2.2.okS P (fussOrteG P F.f) (sicher P lok F.f) →
      r'.okS P (fussOrteG P F.f) (sicher P lok F.f))
    (hwahl : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (U : Umwelt D) (A : AUmwelt D) (σa : World D) (X : ZErgG (vertragVon D F.f)),
      FortSA passes S F G.1 X R O' U A (mk σa) → X.folgt (semHA S O' U A passes R r' σa ρ'))
    (W' : World D) (hW' : W'.slots = s1.slots ∧ W'.globs = s1.globs) :
    KopfSA P O passes Q S lok Tg ⟨F.f, F.rho, F.s0, ⟨l, Γ, Λ, ρ', r'⟩⟩ W' := by
  obtain ⟨H, HA, HU, HX, κ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, ⟨hfx, hkx⟩, hok,
    hreqκ, ⟨hglκ, hsub, hfussκ⟩, hcont⟩ := hW
  have hσa : GleichAuf (stabilS P S lok F.f F.rest.2.2.1) (rahmenWeltF G.1 κ s1) s1 :=
    rahmenWeltF_gleichAuf G.1 hfussκ hRah
  have hlen := rahmenWeltF_laenge G.1 κ s1
  have hlt : Nonempty (Ereignis D) → κ.spur.length < (rahmenWeltF G.1 κ s1).spur.length :=
    fun hN => frischSpur_laenge hN κ.spur
  have hbe : ¬ Nonempty (Ereignis D) →
      BegruendetA P O passes S ⟨G.1, κ, G.2.1, mk (rahmenWeltF G.1 κ s1)⟩ := by
    intro hN
    rw [welt_eq hN (rahmenWeltF G.1 κ s1) G.2.2, welt_eq hN κ G.2.2]
    exact hb hN
  have hmem : (⟨G.1, κ, G.2.1, mk (rahmenWeltF G.1 κ s1)⟩ : EintragV D) ∈
      H ++ [⟨G.1, κ, G.2.1, mk (rahmenWeltF G.1 κ s1)⟩] :=
    List.mem_append_right _ List.mem_cons_self
  refine ⟨H ++ [⟨G.1, κ, G.2.1, mk (rahmenWeltF G.1 κ s1)⟩], HA, HU, HX, rahmenWeltF G.1 κ s1,
    hreq, funkV_appendBA hf hk _ (fun _ => Nat.le_refl _) hbe, ⟨?_, ?_⟩, ?_, hfa, hra, hqa,
    kurzAB_mono hka hlen, hfu, hiu, kurzUB_mono hku hlen, ⟨hfx, kurzX_mono hkx hlen⟩, ?_,
    hok' hok, ?_⟩
  · intro g σ ρ a hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hv.1 g σ ρ a hm
    · rw [List.mem_singleton] at hm
      cases hm
      refine ⟨hreqκ, ?_, ?_⟩
      · intro σa w hw
        rcases hmk with ⟨v, hv', hens⟩ | ⟨rr, hr'⟩
        · rw [hv'] at hw
          cases hw
          refine ens_transfer hens ?_ ?_
          · exact GleichAuf.mono (fun _ h => List.mem_append_right _ h) hglκ.symm
          · exact (GleichAuf.mono (fun _ h => hsub (List.mem_append_right _ h)) hσa).symm
        · rw [hr'] at hw
          cases hw
      · intro e he
        rcases hmk with ⟨v, hv', _⟩ | ⟨rr, hr'⟩
        · rw [hv'] at he; cases he
        · rw [hr'] at he; cases he
  · intro g σ ρ a hm σ' w hw
    rcases List.mem_append.mp hm with hm | hm
    · exact hv.2 g σ ρ a hm σ' w hw
    · rw [List.mem_singleton] at hm
      cases hm
      have e : σ' = rahmenWeltF G.1 κ s1 := by
        rcases hmk with ⟨v, hv', _⟩ | ⟨rr, hr'⟩
        · rw [hv'] at hw; cases hw; rfl
        · rw [hr'] at hw; cases hw
      subst e
      exact ⟨rahmenWeltF_rahmen G.1 κ s1, rahmenWeltF_offen G.1 κ s1⟩
  · refine ⟨fun hN e hm => ?_, fun hN e hm => ?_⟩
    · rcases List.mem_append.mp hm with hm | hm
      · exact Nat.lt_trans (hk.1 hN e hm) (hlt hN)
      · rw [List.mem_singleton] at hm
        subst hm
        exact hlt hN
    · rcases List.mem_append.mp hm with hm | hm
      · exact hk.2 hN e hm
      · rw [List.mem_singleton] at hm
        subst hm
        exact hbe hN
  · refine GleichAuf.mono (fun _ h => stabilS_mono hΛ h) ?_
    exact ⟨fun t ht => (hσa.1 t ht).trans (congrFun hW'.1.symm t),
      fun g hg => (hσa.2 g hg).trans (congrFun hW'.2.symm g)⟩
  · intro R O' U A hR hA hU hX hHA hQ
    have hans := hR _ _ _ _ hmem
    have hc := hcont R O' U A (passtV_append hR) hA hU hX hHA hQ
    rw [hans] at hc
    exact hwahl R O' U A _ _ hc


/-- **A push through a read set `os`** (as `pushS_gen`): the read is recorded; the callee's key
    world is the sequential world after the read (it agrees with the machine's entry world on
    the caller's stable carriers and on `os`). -/
theorem pushSA_gen (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    {z : RufFadenG D} {W : World D} (hF : FadenSA P O passes Q S lok Tg z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (os : List (D.Tab ⊕ D.Glob)) (g : D.Fn) (rhoF : World D → Env D (D.params g))
    (hX : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      ∀ c ∈ os, c ∈ stabilS P S lok z.kopf.f Λ ∨ Tg c)
    (hSt : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      (P.requires g).orte ++ (P.ensures g).orte ⊆ stabilS P S lok z.kopf.f Λ)
    (hrho : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) → ∀ σ : World D,
      GleichAuf (stabilS P S lok z.kopf.f Λ ++ os) σ (W.lese Λ os) → rhoF σ = rhoF (W.lese Λ os))
    {lc : Bool} {Γc : Ctx} {Λc : List (Res D)} (ρc : Env D Γc)
    (rc : GRest D (vertragVon D z.kopf.f) lc Γc Λc)
    (hΛc : ∀ L, Res.held L ∈ Λc ↔ Res.held L ∈ Λ)
    (hrc : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      rc.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f))
    (hlogik : ∀ (O' : Orakel D) (U : Umwelt D) (A : AUmwelt D) R (σ0 κ : World D) (e : Logik D),
      GleichAuf (stabilS P S lok z.kopf.f Λ ++ os) κ (W.lese Λ os) →
      leseA A σ0 Λ os = κ → R g κ (rhoF κ) = .logik e → semHA S O' U A passes R r σ0 ρ = .logik e)
    (hweiter : ∀ (O' : Orakel D) (U : Umwelt D) (A : AUmwelt D) R (σ0 κ : World D),
      GleichAuf (stabilS P S lok z.kopf.f Λ ++ os) κ (W.lese Λ os) →
      leseA A σ0 Λ os = κ →
      FortSA passes S ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩ g
        (semHA S O' U A passes R r σ0 ρ) R O' U A (R g κ (rhoF κ))) :
    FadenSA P O passes Q S lok Tg
      ⟨⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩ :: z.stapel,
        ⟨g, rhoF (W.lese Λ os), W.lese Λ os,
          ⟨false, D.params g, Signatur.anfang D (D.signatur g), rhoF (W.lese Λ os),
            .ende (P.rumpf g)⟩⟩,
        (W.lese Λ os).spur,
        RufEreignisF.eintritt g (rhoF (W.lese Λ os)) (W.lese Λ os) :: z.log⟩
      (W.lese Λ os) ∧
    ReqAmEintritt P g (W.lese Λ os) (rhoF (W.lese Λ os)) := by
  obtain ⟨⟨H, HA, HU, HX, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, ⟨hfx, hkx⟩, hg,
    hok, heq⟩, hSt'⟩ := hF
  have hok' : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) := by rw [hr] at hok; exact hok
  have hg0 : GleichAuf (stabilS P S lok z.kopf.f Λ) σ W := by rw [hr] at hg; exact hg
  obtain ⟨HX', hfx', hkx', hsub, hrec⟩ := lese_schritt Tg hfx hkx Λ os W.speicher
  have hgκ := mischT_gleichAuf hg0 (hX hok') Λ Λ
  have hρk := hrho hok' _ hgκ
  have heq' : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (U : Umwelt D) (A : AUmwelt D), PasstV R H → PasstA O' HA → PasstU S U HU →
      PasstX Tg A HX' → HavocA Tg A → GleichRS O O' →
      (zErgG (execEndHA (V := vertragVon D z.kopf.f) S O' U A passes R (P.rumpf z.kopf.f) z.kopf.s0
        z.kopf.rho)).folgt (semHA S O' U A passes R r σ ρ) := by
    intro R O' U A hR hA hU hX hHA hQ
    have := heq R O' U A hR hA hU (passtX_teil hsub hX) hHA hQ
    rw [hr] at this
    exact this
  have hctr := hSt hok'
  have hreqκ := pushSA_req hO hRL hQ hS hsp hK hreq hf hv hfa hra hqa hfu hiu hfx' r heq' g
    (mischT Tg os (σ.lese Λ os) W.speicher) (rhoF (mischT Tg os (σ.lese Λ os) W.speicher))
    (fun O' U A R e hPX hHA h => hlogik O' U A R σ _ e hgκ (hrec A hPX hHA) h)
  rw [hρk] at hreqκ
  have hctrκ : GleichAuf ((P.requires g).orte ++ (P.ensures g).orte)
      (mischT Tg os (σ.lese Λ os) W.speicher) (W.lese Λ os) :=
    GleichAuf.mono (fun _ h => List.mem_append_left _ (hctr h)) hgκ
  have hreq0 := req_transfer hreqκ
    (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hctrκ)
  have hsubc : (P.requires g).orte ++ (P.ensures g).orte ⊆ stabilS P S lok z.kopf.f Λc :=
    fun _ h => stabilS_iff (fun L => (hΛc L).symm) (hctr h)
  have hlen : σ.spur.length ≤ (mischT Tg os (σ.lese Λ os) W.speicher).spur.length :=
    lese_laenge _ _ _
  refine ⟨⟨⟨[], [], [], [], W.lese Λ os, hreq0, funkV_nil, vertraegeOkR_nil P, kurzVBA_nil _,
    funkA_nil, rahmenA_nil, vertragA_nil _ Q, kurzAB_nil _, funkU_nil, invU_nil S, kurzUB_nil _,
    ⟨funkX_nil, kurzX_nil _⟩, GleichAuf.refl _ _, ⟨hFragS g, fuss_rumpfG P g⟩,
    fun R O' U A _ _ _ _ _ _ => ZErgG.folgt_refl _⟩,
    ⟨H, HA, HU, HX', mischT Tg os (σ.lese Λ os) W.speicher, hreq, hf, hv, kurzVBA_mono hk hlen,
      hfa, hra, hqa, kurzAB_mono hka hlen, hfu, hiu, kurzUB_mono hku hlen, ⟨hfx', hkx'⟩, hrc hok',
      hreqκ, ⟨hctrκ, hsubc, gleichAuf_stabil_iff hΛc
        (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hgκ)⟩, ?_⟩, hSt'⟩, hreq0⟩
  intro R O' U A hR hA hU hX hHA hQ
  have hw := hweiter O' U A R σ _ hgκ (hrec A hX hHA)
  rw [hρk] at hw
  exact fortSA_mono (F := ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩)
    (heq' R O' U A hR hA hU hX hHA hQ) hw

/-- **An axiom step keeps the replay** (as `fadenS_ax`): its argument read is recorded. -/
theorem fadenSA_ax {z : RufFadenG D} {W : World D}
    (hF : FadenSA P O passes Q S lok Tg z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (hΛ' : ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ)
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (hX : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      ∀ c ∈ args.orte, c ∈ stabilS P S lok z.kopf.f Λ ∨ Tg c)
    (hok : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      r'.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f))
    (xm : World D × Int) (hxm : Rahmen (D.aschreibt a) (D.agschreibt a) (W.lese Λ args.orte) xm.1)
    (hxO : ¬ Nonempty (Ereignis D) →
      xm.2 = (O.wirkt a (W.lese Λ args.orte) (evalArgs (W.lese Λ args.orte) args
        (W.lese Λ args.orte) ρ)).2)
    (hlok : AxEnsLokal Q)
    (hxq : ∀ v : ErgVal D (D.aerg a), einpassenErg O.zeiger (D.aerg a) xm.2 = some v →
      Q a xm.1 v = true)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (A : AUmwelt D) (σ0 κ : World D), ZeigerGleich O O' →
      leseA A σ0 Λ args.orte = κ →
      O'.wirkt a κ (evalArgs κ args κ ρ) = (axWeltF a κ xm.1, xm.2) →
      (semHA S O' U A passes R r σ0 ρ).folgt
        (semHA S O' U A passes R r' (axWeltF a κ xm.1) ρ')) :
    FadenSA P O passes Q S lok Tg
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩
      (xm.1.speicher.welt spur') := by
  obtain ⟨⟨H, HA, HU, HX, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, ⟨hfx, hkx⟩, hg,
    hok0, heq⟩, hS⟩ := hF
  have hok' : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) := by
    rw [hr] at hok0; exact hok0
  have hg0 : GleichAuf (stabilS P S lok z.kopf.f Λ) σ W := by rw [hr] at hg; exact hg
  obtain ⟨HX', hfx', hkx', hsub, hrec⟩ := lese_schritt Tg hfx hkx Λ args.orte W.speicher
  have hgκ := mischT_gleichAuf hg0 (hX hok') Λ Λ
  have hlen : σ.spur.length ≤ (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher).spur.length :=
    lese_laenge _ _ _
  have hlen2 : σ.spur.length ≤
      (axWeltF a (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) xm.1).spur.length :=
    Nat.le_trans hlen (axWeltF_laenge _ _ _)
  have hlen3 : (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher).spur.length ≤
      (axWeltF a (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) xm.1).spur.length :=
    axWeltF_laenge _ _ _
  have hlt : Nonempty (Ereignis D) →
      (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher).spur.length <
      (axWeltF a (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) xm.1).spur.length :=
    fun hN => frischSpur_laenge hN _
  have hpa : ¬ Nonempty (Ereignis D) → PasstA O (HA ++ [⟨a,
      mischT Tg args.orte (σ.lese Λ args.orte) W.speicher,
      evalArgs (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) args
        (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) ρ,
      (axWeltF a (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) xm.1, xm.2)⟩]) := by
    intro hN a' σk ρk x hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hka.2 hN a' σk ρk x hm
    · rw [List.mem_singleton] at hm
      cases hm
      rw [hxO hN, welt_eq hN (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher)
        (W.lese Λ args.orte)]
      exact Prod.ext (welt_eq hN _ _) rfl
  refine ⟨⟨H, HA ++ [⟨a, mischT Tg args.orte (σ.lese Λ args.orte) W.speicher,
      evalArgs (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) args
        (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) ρ,
      (axWeltF a (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) xm.1, xm.2)⟩], HU, HX',
    axWeltF a (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) xm.1, hreq, hf, hv,
    kurzVBA_mono hk hlen2, ?_, ?_, ?_, ?_,
    hfu, hiu, kurzUB_mono hku hlen2, ⟨hfx', kurzX_mono hkx' hlen3⟩, ?_, hok hok', ?_⟩, hS⟩
  · by_cases hN : Nonempty (Ereignis D)
    · exact funkA_append hfa (hka.1 hN) _ hlen
    · exact funkA_of_passtA (hpa hN)
  · intro a' σk ρk x hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hra a' σk ρk x hm
    · rw [List.mem_singleton] at hm
      cases hm
      exact axWeltF_rahmen a _ _
  · intro a' σk ρk x hm v hv
    rcases List.mem_append.mp hm with hm | hm
    · exact hqa a' σk ρk x hm v hv
    · rw [List.mem_singleton] at hm
      cases hm
      exact axWeltF_vertrag hlok a _ _ v (hxq v hv)
  · refine ⟨fun hN e hm => ?_, hpa⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact Nat.lt_of_lt_of_le (hka.1 hN e hm) hlen2
    · rw [List.mem_singleton] at hm
      subst hm
      exact hlt hN
  · have h1 := axWeltF_gleichAuf a
      (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hgκ) hxm
    exact gleichAuf_stabil_iff hΛ' ⟨fun t ht => h1.1 t ht, fun g hg' => h1.2 g hg'⟩
  · intro R O' U A hR hA hU hXA hHA hQ
    have h1 := heq R O' U A hR (passtA_append hA) hU (passtX_teil hsub hXA) hHA hQ
    rw [hr] at h1
    exact ZErgG.folgt_trans h1
      (hsem O' R U A σ _ hQ.2.2 (hrec A hXA hHA)
        (hA _ _ _ _ (List.mem_append_right _ List.mem_cons_self)))


/-- **A leaf's outcome world extends the world after its reads** (non-axiom leaves). -/
theorem blatt_lese_laenge (P : Programm D) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (hb : s.istBlatt = true)
    (ha : s.istAxiom = false) {σ : World D} {ρ : Env D Γ} {σ' : World D} {ρ' : Env D Γ}
    (h : execStmt O passes R s σ ρ = .ok σ' ρ') :
    (σ.lese Λ (stmtOrteP P s)).spur.length ≤ σ'.spur.length := by
  cases s with
  | assignSlot t f i e hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact spur_laenge_erw (Erw.schreibSlot _ _ _ _ _ _)
  | assignDurch p t ht f i e hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact spur_laenge_erw (Erw.schreibSlot _ _ _ _ _ _)
  | assignGlob g e hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact spur_laenge_erw (Erw.schreibGlob _ _ _ _)
  | schreibBytes t f hf n i hlo hhi e hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact spur_laenge_erw (Erw.schreibBytes _ _ _ _ _ _ _)
  | assignVar x e =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Nat.le_refl _
  | uebergang t f hτ i von nach hn he hw hL =>
      simp only [execStmt] at h
      split at h
      · simp only [Ausgang.ok.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact spur_laenge_erw (Erw.schreibSlot _ _ _ _ _ _)
      · cases h
  | regSchreib r hk e =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Nat.le_refl _
  | transition r hk m hm hmk maske bits =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [stmtOrteP, lese_nil]
      exact Nat.le_refl _
  | publish g e payload hp hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact spur_laenge_erw (Erw.schreibGlob _ _ _ _)
  | advances =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [stmtOrteP, lese_nil]
      exact Nat.le_refl _
  | retires =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [stmtOrteP, lese_nil]
      exact Nat.le_refl _
  | axiomCall => simp [Stmt.istAxiom] at ha
  | ret e hp => simp [execStmt] at h
  | retGrund r hp => simp [execStmt] at h
  | leave hl => simp [execStmt] at h
  | next hl => simp [execStmt] at h
  | _ => simp [Stmt.istBlatt] at hb

theorem vorA_eq {A : AUmwelt D} {σ w : World D} {Λ : List (Res D)} {X : List (D.Tab ⊕ D.Glob)}
    (h : leseA A σ Λ X = w) : vorA A σ Λ X = ⟨w.slots, w.globs, σ.spur⟩ := by
  unfold vorA
  unfold leseA at h
  rw [h]

/-- **A leaf step keeps the replay** (as `fadenS_blatt`): its reads are recorded; a non-axiom
    leaf by leaf locality over the stable carriers AND the read list, an axiom call by recording
    its answer. -/
theorem fadenSA_blatt (hO : GutO O) (hQ : AxVertragO Q O)
    (hlok : AxEnsLokal Q) (hFS : ∀ f, FussSX P S lok Tg f) {z : RufFadenG D} {W : World D}
    (hF : FadenSA P O passes Q S lok Tg z W) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (s : Stmt D (vertragVon D z.kopf.f) l Γ Λ Λ') (K : GRest D (vertragVon D z.kopf.f) l Γ Λ')
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (A : AUmwelt D) (σ : World D),
      semHA S O' U A passes R r σ ρ = weiterHA S O' U A passes R K (execStmtHA S O' U A passes R s σ ρ))
    (hok : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      stmtOrteP P s ⊆ fussOrteG P z.kopf.f ∧ K.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f))
    (hleaf : s.istBlatt = true) (σ' : World D) (ρ' : Env D Γ)
    (hstep : execStmt O passes keinRuf s W ρ = .ok σ' ρ') :
    FadenSA P O passes Q S lok Tg
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, Λ', ρ', K⟩⟩, σ'.spur, z.log⟩
      (σ'.speicher.welt σ'.spur) := by
  have hΛ' : ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ := s.held_iff
  cases hax : s.istAxiom with
  | false =>
      refine fadenSA_lokalQ hF hr ρ' K σ'.spur (fun σ HX hfx hkx hg hok' => ?_)
      obtain ⟨hs, hK⟩ := hok hok'
      have hXs := orte_stabilX (hFS _) (s.blatt_darf P hleaf) hs
      obtain ⟨HX', hfx', hkx', hsub, hrec⟩ :=
        lese_schritt Tg hfx hkx Λ (stmtOrteP P s) W.speicher
      have hgX := mischT_gleichAuf hg hXs Λ Λ
      have hĝ : GleichAuf (stabilS P S lok z.kopf.f Λ ++ stmtOrteP P s)
          (⟨(mischT Tg (stmtOrteP P s) (σ.lese Λ (stmtOrteP P s)) W.speicher).slots,
            (mischT Tg (stmtOrteP P s) (σ.lese Λ (stmtOrteP P s)) W.speicher).globs, σ.spur⟩ :
            World D) W := hgX
      obtain ⟨σs, hes, hgs, _⟩ := blatt_lokalV P O passes s hleaf hax
        (fun _ h => List.mem_append_right _ h) hĝ hstep
      have hl := blatt_lese_laenge P O passes keinRuf s hleaf hax (hes O keinRuf)
      refine ⟨σs, HX', hfx', kurzX_mono hkx' hl, hsub, Nat.le_trans (lese_laenge σ Λ _) hl,
        gleichAuf_stabil_iff hΛ' (GleichAuf.mono (fun _ h => List.mem_append_left _ h)
          ⟨fun t ht => hgs.1 t ht, fun g hg' => hgs.2 g hg'⟩),
        hK, fun R O' U A hPX hHA _ => ?_⟩
      rw [hsem, execStmtHA_blatt P S O' U hHA passes R s hleaf, vorA_eq (hrec A hPX hHA), hes]
      exact ZErgG.folgt_refl _
  | true =>
      cases s with
      | axiomCall a args h hw hg hd hgd =>
          obtain ⟨e1, e2, u, hu⟩ := axiomCall_ok_inv O passes keinRuf a args h hw hg hd hgd W ρ σ' ρ'
            hstep
          subst e2
          have hfr := (hO a (W.lese Λ args.orte)
            (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ')).1
          rw [← e1] at hfr
          refine fadenSA_ax hF hr ρ' K σ'.spur hΛ' a args
            (fun h' => orte_stabilX (hFS _) args.orte_darf (hok h').1) (fun h' => (hok h').2)
            (σ', (O.wirkt a (W.lese Λ args.orte)
              (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ')).2) hfr (fun _ => rfl)
            hlok
            (fun v hv => by
              rw [e1]
              exact hQ a _ _ v hv) ?_
          intro O' R U A σ0 κ hz hκ hw
          rw [hsem]
          apply ZErgG.folgt_of_eq
          simp only [execStmtHA, axiomAntwort, hκ, hw]
          simp only [(show O'.zeiger = O.zeiger from hz), hu]
          rfl
      | _ => simp [Stmt.istAxiom] at hax

/-- **The acquire keeps the replay** (as `fadenS_locks`). -/
theorem fadenSA_locks {z : RufFadenG D} {W : World D} (hF : FadenSA P O passes Q S lok Tg z W)
    {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)} (L : D.Lock)
    (hrL : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D (vertragVon D z.kopf.f) l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.locks L hrL body) rest) k⟩)
    (hinv : S.inv L W.speicher = true) (spur' : List (Ereignis D)) :
    FadenSA P O passes Q S lok Tg
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
        ⟨l, Γ, Res.held L :: Λ, ρ, .dann body (.frei L (.dann rest k))⟩⟩, spur', z.log⟩
      (W.speicher.welt spur') := by
  obtain ⟨⟨H, HA, HU, HX, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, ⟨hfx, hkx⟩, hg,
    hok, heq⟩, hS⟩ := hF
  rw [hr] at hg hok
  simp only at hg hok
  obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
  have hlen : σ.spur.length < ((mischU S L σ W.speicher).nimmt L).spur.length := by
    show σ.spur.length < (Ereignis.nimmt L _ :: σ.spur).length
    exact Nat.lt_succ_self _
  refine ⟨⟨H, HA, HU ++ [(L, σ, W.speicher)], HX, (mischU S L σ W.speicher).nimmt L, hreq, hf, hv,
    kurzVBA_mono hk (Nat.le_of_lt hlen), hfa, hra, hqa, kurzAB_mono hka (Nat.le_of_lt hlen),
    funkU_append hfu (hku ⟨.gibt L⟩) _ (Nat.le_refl _), invU_append hiu L σ W.speicher hinv, ?_,
    ⟨hfx, kurzX_mono hkx (Nat.le_of_lt hlen)⟩, ?_, ⟨hks, hss, hrest⟩, ?_⟩, hS⟩
  · intro hN e he
    rcases List.mem_append.mp he with he | he
    · exact Nat.lt_trans (hku hN e he) hlen
    · rw [List.mem_singleton] at he
      subst he
      exact hlen
  · have key : ∀ c ∈ stabilS P S lok z.kopf.f (Res.held L :: Λ),
        TraegerGleich ((mischU S L σ W.speicher).nimmt L).speicher W.speicher c := by
      intro c hc
      by_cases hcL : c ∈ S.orte L
      · exact mischU_innen S L σ W.speicher c hcL
      · have hc' : c ∈ stabilS P S lok z.kopf.f Λ := by
          rcases stabilS_mem.mp hc with hc | ⟨K, hK, hcK⟩
          · exact stabilS_mem.mpr (Or.inl hc)
          · rcases List.mem_cons.mp hK with hK | hK
            · cases hK
              exact absurd hcK hcL
            · exact stabilS_mem.mpr (Or.inr ⟨K, hK, hcK⟩)
        refine traegerGleich_trans (mischU_aussen S L σ W.speicher c hcL) ?_
        cases c with
        | inl t => exact hg.1 t hc'
        | inr g => exact hg.2 g hc'
    exact ⟨fun t ht => key (.inl t) ht, fun g hg' => key (.inr g) hg'⟩
  · intro R O' U A hR hA hU hX hHA hQ
    have h1 := heq R O' U A hR hA (passtU_append hU) hX hHA hQ
    rw [hr] at h1
    simp only at h1
    refine ZErgG.folgt_trans h1 (ZErgG.folgt_of_eq ?_)
    rw [semHA_locks S O' U A passes R L hrL body rest k σ ρ,
      hU L σ W.speicher (List.mem_append_right _ List.mem_cons_self)]

end Schritte

/-! ## 5. The head never predicts a `logik` outcome; the release steps -/

section Frei

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop}

/-- **The head's prediction is never a `logik` outcome** (as `kopfS_keineLogik`), against the
    record handler, oracle, lock move and atomic environment. -/
theorem kopfSA_keineLogik (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f) {F : RufRahmenG D} {W : World D}
    (hG : KopfSA P O passes Q S lok Tg F W) :
    ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (HU : List (UEintrag D))
      (HX : List (XEintrag D)) (σ : World D),
      FunkX HX ∧ KurzX σ.spur.length HX ∧
      GleichAuf (stabilS P S lok F.f F.rest.2.2.1) σ W ∧
      F.rest.2.2.2.2.okS P (fussOrteG P F.f) (sicher P lok F.f) ∧
      ∀ (A : AUmwelt D), PasstX Tg A HX → HavocA Tg A → ∀ e : Logik D,
        semHA S (orakelAus O HA) (umweltAus S sp HU) A passes (rufAusL H) F.rest.2.2.2.2 σ
          F.rest.2.2.2.1 ≠ .logik e := by
  obtain ⟨H, HA, HU, HX, σ, hreq, hf, hv, _, hfa, hra, hqa, _, hfu, hiu, _, ⟨hfx, hkx⟩, hg, hok,
    heq⟩ := hG
  refine ⟨H, HA, HU, HX, σ, hfx, hkx, hg, hok, fun A hPX hHA e he => ?_⟩
  have h1 := heq (rufAusL H) (orakelAus O HA) (umweltAus S sp HU) A (rufAusL_passt hf)
    (orakelAus_passt O hfa) (umweltAus_passt S sp hfu) hPX hHA (gleichRS_orakelAus O HA)
  rw [he] at h1
  exact (hK F.f).2 (orakelAus O HA) (orakelAus_rahmen hO hra) (regLokal_orakelAus hRL HA)
    (orakelAus_vertrag hQ hqa) (umweltAus S sp HU) (umweltAus_ok hS hsp hiu) A hHA (rufAusL H)
    (rufAusL_rahmen hv) (rufAusL_ohneLogik hv.1) F.s0 F.rho hreq e
    (zErgG_gleich_logik (ZErgG.folgt_logik h1))

/-- The same, for a residue named by its shape. -/
theorem kopfSA_keineLogik' (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f) {F : RufRahmenG D} {W : World D}
    (hG : KopfSA P O passes Q S lok Tg F W) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D F.f) l Γ Λ} (hr : F.rest = ⟨l, Γ, Λ, ρ, r⟩) :
    ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (HU : List (UEintrag D))
      (HX : List (XEintrag D)) (σ : World D),
      FunkX HX ∧ KurzX σ.spur.length HX ∧
      GleichAuf (stabilS P S lok F.f Λ) σ W ∧ r.okS P (fussOrteG P F.f) (sicher P lok F.f) ∧
      ∀ (A : AUmwelt D), PasstX Tg A HX → HavocA Tg A → ∀ e : Logik D,
        semHA S (orakelAus O HA) (umweltAus S sp HU) A passes (rufAusL H) r σ ρ ≠ .logik e := by
  obtain ⟨H, HA, HU, HX, σ, hfx, hkx, hg, hok, hno⟩ := kopfSA_keineLogik hO hRL hQ hS hsp hK hG
  rw [hr] at hok hno hg
  exact ⟨H, HA, HU, HX, σ, hfx, hkx, hg, hok, hno⟩

/-- **At a release the invariant holds in the machine** (as `kopfS_frei_inv`). -/
theorem kopfSA_frei_inv (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f) {F : RufRahmenG D} {W : World D}
    (hG : KopfSA P O passes Q S lok Tg F W) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} (L : D.Lock) (hL : Res.held L ∈ Λ) {r : GRest D (vertragVon D F.f) l Γ Λ}
    (hr : F.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (hlog : ∀ (O' : Orakel D) (U : Umwelt D) (A : AUmwelt D) R (σ : World D),
      S.inv L σ.speicher = false → semHA S O' U A passes R r σ ρ = .logik .schleife) :
    S.inv L W.speicher = true := by
  obtain ⟨H, HA, HU, HX, σ, hfx, _, hg, _, hno⟩ := kopfSA_keineLogik' hO hRL hQ hS hsp hK hG hr
  have hi : S.inv L σ.speicher = true := by
    cases h : S.inv L σ.speicher with
    | true => rfl
    | false => exact absurd (hlog (orakelAus O HA) (umweltAus S sp HU) (umweltAusA Tg HX)
        (rufAusL H) σ h) (hno _ (umweltAusA_passt Tg hfx) (umweltAusA_ok Tg HX) .schleife)
  rw [← hi]
  refine hS.2 L _ _ fun c hc => ?_
  have hcs : c ∈ stabilS P S lok F.f Λ := stabilS_mem.mpr (Or.inr ⟨L, hL, hc⟩)
  cases c with
  | inl t => exact (hg.1 t hcs).symm
  | inr g => exact (hg.2 g hcs).symm

/-- **The release after the body keeps the replay** (`freiGib`). -/
theorem fadenSA_frei (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f) {z : RufFadenG D} {W : World D}
    (hF : FadenSA P O passes Q S lok Tg z W) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (L : D.Lock)
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hr : z.kopf.rest = ⟨l, Γ, Res.held L :: Λ, ρ, .frei L k⟩) (spur' : List (Ereignis D)) :
    FadenSA P O passes Q S lok Tg
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, Λ, ρ, k⟩⟩, spur', z.log⟩
      (W.speicher.welt spur') := by
  have hW := kopfSA_frei_inv hO hRL hQ hS hsp hK hF.1 L List.mem_cons_self hr
    (fun O' U A R σ h => semHA_frei_falsch S O' U A passes R L k σ ρ h)
  refine fadenSA_lokalQ hF hr ρ k spur' (fun σ HX hfx hkx hg hok => ?_)
  have hiσ : S.inv L σ.speicher = true := (inv_gleich hS List.mem_cons_self hg).trans hW
  exact ⟨σ.gibt L, HX, hfx, kurzX_mono hkx (Nat.le_succ _), fun _ h => h, Nat.le_succ _,
    gleichAuf_frei hg spur', hok,
    fun R O' U A _ _ _ => ZErgG.folgt_of_eq (semHA_frei S O' U A passes R L k σ ρ hiσ)⟩

/-- **A `leave`/`next` out of a `locks` body keeps the replay**. -/
theorem fadenSA_peelFrei (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f) {z : RufFadenG D} {W : World D}
    (hF : FadenSA P O passes Q S lok Tg z W) {Γ : Ctx} {Λ Λ1 : List (Res D)} (L : D.Lock)
    (rest : Block D (vertragVon D z.kopf.f) true Γ Λ (Res.held L :: Λ1))
    (k : GRest D (vertragVon D z.kopf.f) true Γ Λ1) (ρ : Env D Γ) (h : true = true) (x : Bool)
    (hr : z.kopf.rest =
      ⟨true, Γ, Λ, ρ, .dann (.cons (if x then .leave h else .next h) rest) (.frei L k)⟩)
    (spur' : List (Ereignis D)) :
    FadenSA P O passes Q S lok Tg
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
        ⟨true, Γ, Λ1, ρ, .dann (.cons (if x then .leave h else .next h) .nil) k⟩⟩, spur', z.log⟩
      (W.speicher.welt spur') := by
  have hLΛ : Res.held L ∈ Λ := (Block.held_iff rest L).mp List.mem_cons_self
  have hΛ1 : ∀ M, Res.held M ∈ Λ1 → Res.held M ∈ Λ :=
    fun M hM => (Block.held_iff rest M).mp (List.mem_cons_of_mem _ hM)
  have hW := kopfSA_frei_inv hO hRL hQ hS hsp hK hF.1 L hLΛ hr
    (fun O' U A R σ hi => semHA_peelFrei_falsch S O' U A passes R L rest k σ ρ h x hi)
  refine fadenSA_lokalQ hF hr ρ _ spur' (fun σ HX hfx hkx hg hok => ?_)
  have hiσ : S.inv L σ.speicher = true := (inv_gleich hS hLΛ hg).trans hW
  obtain ⟨_, _, hk⟩ := hok
  refine ⟨σ.gibt L, HX, hfx, kurzX_mono hkx (Nat.le_succ _), fun _ h => h, Nat.le_succ _,
    GleichAuf.mono (fun _ hc => stabilS_mono hΛ1 hc) ⟨fun t ht => hg.1 t ht, fun g hg' => hg.2 g hg'⟩,
    ⟨by cases x <;> rfl, fun _ hc => by cases x <;> simp [blockOrteP, stmtOrteP] at hc, hk⟩,
    fun R O' U A _ _ _ => ZErgG.folgt_of_eq (semHA_peelFrei S O' U A passes R L rest k σ ρ h x hiσ)⟩

end Frei

end Gabbro.Grammatik
