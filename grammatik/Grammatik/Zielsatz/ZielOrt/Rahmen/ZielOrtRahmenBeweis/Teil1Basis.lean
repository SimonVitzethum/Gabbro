module

public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmenSem
public import Grammatik.Logik.Vertraege.AxiomVertrag

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 0. The obligation over the oracles that also meet declared axiom ensures

  The replay below is generic in a declared axiom ensures `Q` (as the replay
  of `ziel_ort_voll_ax`, `ZielOrtAxBeweis.lean`): the records keep
  `VertragA O.zeiger Q HA`, so the record oracle meets `Q` (`orakelAus_vertrag`) and
  the obligation may quantify over the oracles that meet it. With the
  trivial ensures `axWahr` every oracle meets it, and the obligation is
  `KoerperGutR` (`koerperGutRQ_of_R`). -/

/-- **The user obligation against frame-respecting handlers and the
    oracles that meet the declared axiom ensures `Q`.** `KoerperGutR` with
    one more oracle condition (`AxVertragOP (PreQ P) Q O'`): fewer oracles, so it is
    weaker than `KoerperGutR` (`koerperGutRQ_of_R`) and than `KoerperGutA`
    (`koerperGutRQ_of_A`). -/
def KoerperGutRQ (P : Programm D) (passes : Nat) (Q : AxEns D) (f : D.Fn) : Prop :=
  ∀ O' : Orakel D, RahmenO O' → RegLokal O' → AxVertragOP (PreQ P) Q O' →
  ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
    RespektiertRahmen P R → OhneVorbedingung R →
    ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ →
      (∀ (σ' : World D) (v : ErgVal D (D.erg f)),
        execEnd (V := vertragVon D f) O' passes R (P.rumpf f) σ ρ = EndAusgang.zurueck σ' v →
          EnsAmRueck P f σ σ' ρ v) ∧
      (∀ g : D.Fn,
        execEnd (V := vertragVon D f) O' passes (torRuf P R) (P.rumpf f) σ ρ ≠
          EndAusgang.logik (Logik.vorbedingung g))

theorem koerperGutRQ_of_R {P : Programm D} {passes : Nat} (Q : AxEns D) {f : D.Fn}
    (h : KoerperGutR P passes f) : KoerperGutRQ P passes Q f :=
  fun O' hr hl _ R hR hOV σ ρ hreq => h O' hr hl R hR hOV σ ρ hreq

/-- `KoerperGutA` (the obligation of `ziel_ort_voll_ax`) gives the new one:
    fewer oracles (register-local ones) and fewer handlers (frame-respecting
    ones). -/
theorem koerperGutRQ_of_A {P : Programm D} {passes : Nat} {Q : AxEns D} {f : D.Fn}
    (h : KoerperGutA P passes Q f) : KoerperGutRQ P passes Q f :=
  fun O' hr _ hq R hR hOV σ ρ hreq => h O' hr hq R hR.1 hOV σ ρ hreq

/-- The trivial declared ensures: every answer meets it. -/
def axWahr (D : Deklaration) : AxEns D := fun _ _ _ => true

theorem axVertragO_wahr (O : Orakel D) : AxVertragO (axWahr D) O := fun _ _ _ _ _ => rfl

theorem axEnsLokal_wahr : AxEnsLokal (axWahr D) := fun _ _ _ _ _ _ => rfl

/-- Over the trivial ensures the new obligation IS `KoerperGutR`. -/
theorem koerperGutR_of_RQ_wahr {P : Programm D} {passes : Nat} {f : D.Fn}
    (h : KoerperGutRQ P passes (axWahr D) f) : KoerperGutR P passes f :=
  fun O' hr hl R hR hOV σ ρ hreq => h O' hr hl (axVertragOP_of_O _ (axVertragO_wahr O')) R hR hOV σ ρ hreq

/-! ## 1. The replay invariants -/

section Inv

variable (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)

/-- **The replay of a head frame** `F` whose thread world is `W` (as
    `KopfV`): the sequential oracles are those that repeat the recorded
    axiom answers AND give the machine oracle's register and visibility
    answers. -/
def KopfR (F : RufRahmenG D) (W : World D) : Prop :=
  ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (σ : World D),
    ReqAmEintritt P F.f F.s0 F.rho ∧ FunkV H ∧ VertraegeOkR P H ∧ KurzV σ.rang H ∧
    FunkA HA ∧ RahmenA HA ∧ VertragA O.zeiger Q HA ∧ KurzA σ.rang HA ∧
    GleichAuf (fussOrteG P F.f) σ W ∧ F.rest.2.2.2.2.okG P (fussOrteG P F.f) ∧
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
      PasstV R H → PasstA O' HA → GleichRS O O' →
      (zErg (execEnd (V := vertragVon D F.f) O' passes R (P.rumpf F.f) F.s0 F.rho)).folgt
        (semV O' passes R F.rest.2.2.2.2 σ F.rest.2.2.2.1)

/-- **The replay of a suspended frame** (as `WarteV`), over the same class
    of sequential oracles. -/
def WarteR (F : RufRahmenG D) (G : Σ f : D.Fn, Env D (D.params f) × World D) : Prop :=
  ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (κ : World D),
    ReqAmEintritt P F.f F.s0 F.rho ∧ FunkV H ∧ VertraegeOkR P H ∧ KurzV κ.rang H ∧
    FunkA HA ∧ RahmenA HA ∧ VertragA O.zeiger Q HA ∧ KurzA κ.rang HA ∧
    F.rest.2.2.2.2.okG P (fussOrteG P F.f) ∧
    ReqAmEintritt P G.1 κ G.2.1 ∧
    (GleichAuf ((P.requires G.1).orte ++ (P.ensures G.1).orte) κ G.2.2 ∧
      (P.requires G.1).orte ++ (P.ensures G.1).orte ⊆ fussOrteG P F.f ∧
      GleichAuf (fussOrteG P F.f) κ G.2.2) ∧
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
      PasstV R H → PasstA O' HA → GleichRS O O' →
      FortV passes F G.1
        (zErg (execEnd (V := vertragVon D F.f) O' passes R (P.rumpf F.f) F.s0 F.rho)) R O'
        (R G.1 κ G.2.1)

def StapelR : (Σ f : D.Fn, Env D (D.params f) × World D) → List (RufRahmenG D) → Prop
  | _, [] => True
  | G, F :: rest => WarteR P O passes Q F G ∧ StapelR (RufSchluesselG F) rest

def FadenR (z : RufFadenG D) (W : World D) : Prop :=
  KopfR P O passes Q z.kopf W ∧ StapelR P O passes Q (RufSchluesselG z.kopf) z.stapel

def ZielInvR (M : RufMaschineG D) : Prop :=
  (∀ t, FadenR P O passes Q (M.faeden t) (M.weltVon t)) ∧ ∀ t, LogOk P (M.faeden t).log

end Inv


end Gabbro.Grammatik
