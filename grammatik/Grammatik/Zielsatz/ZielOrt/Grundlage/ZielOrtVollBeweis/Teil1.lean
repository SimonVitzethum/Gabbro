module
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis.Teil1Basis
import all Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis.Teil1Basis

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollSem
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}
/-! ## 3. The replay invariants -/

section Inv

variable (P : Programm D) (O : Orakel D) (passes : Nat)

/-- **The replay of a head frame** `F` whose thread world is `W`: records of
    its calls `H` and its axiom calls `HA` (functions of their keys, keys
    below the sequential trace, call answers respecting the callees'
    contracts, axiom answers inside their frames), a sequential world `σ`
    agreeing with `W` on the footprint, the residue in the fragment; and
    for ANY handler and ANY oracle repeating the records, the residue run
    from `σ` predicts the body's result. -/
def KopfV (F : RufRahmenG D) (W : World D) : Prop :=
  ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (σ : World D),
    ReqAmEintritt P F.f F.s0 F.rho ∧ FunkV H ∧ VertraegeOkV P H ∧ KurzV σ.spur.length H ∧
    FunkA HA ∧ RahmenA HA ∧ KurzA σ.spur.length HA ∧
    GleichAuf (fussOrte P F.f) σ W ∧ F.rest.2.2.2.2.okV P (fussOrte P F.f) ∧
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
      PasstV R H → PasstA O' HA → ZeigerGleich O O' →
      (zErg (execEnd (V := vertragVon D F.f) O' passes R (P.rumpf F.f) F.s0 F.rho)).folgt
        (semV O' passes R F.rest.2.2.2.2 σ F.rest.2.2.2.1)

/-- How a suspended frame `F` continues once its pending call to `g` is
    answered with `a`, predicted for the body's result `X`: a normal answer
    resumes the frame (plain call) or binds the value (`let`, with or
    without `else`); a reason answer runs the `else` block with the reason
    bound. -/
def FortV (F : RufRahmenG D) (g : D.Fn) (X : ZErg (vertragVon D F.f))
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D) :
    RufAusgang g → Prop
  | .ok σa v =>
      (F.wartend = false → X.folgt (semV O' passes R F.rest.2.2.2.2 σa F.rest.2.2.2.1)) ∧
      (∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
          (restb : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ')
          (k : GRest D (vertragVon D F.f) l Γ Λ') (ρc : Env D Γ),
        (F.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ ∨
          ∃ (n : Nat) (err : Endblock D (vertragVon D F.f) l (.why n :: Γ) Λ),
            F.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩) →
        ∀ he : D.erg g = some τ,
          X.folgt (semV O' passes R (.dann restb (.schrumpf k)) σa (.cons (ergWert he v) ρc)))
  | .why σa r =>
      ∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty) (n : Nat)
        (err : Endblock D (vertragVon D F.f) l (.why n :: Γ) Λ)
        (restb : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ')
        (k : GRest D (vertragVon D F.f) l Γ Λ') (ρc : Env D Γ),
        F.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩ →
        ∀ hn : D.gruende g = n,
          X.folgt (semV O' passes R (.dann err.alsBlock.2 (.abbruch (.schrumpf k))) σa
            (.cons (Fin.cast hn r) ρc))
  | _ => True

/-- **The replay of a suspended frame** `F` waiting for the callee with key
    `G`: records, the sequential key world `κ` of the pending call (the
    callee's `requires` holds there; it agrees with the callee's machine
    entry world on the callee's contract carriers), and for any handler and
    oracle repeating the records, the continuation after the handler's
    answer to the pending call predicts the body's result. -/
def WarteV (F : RufRahmenG D) (G : Σ f : D.Fn, Env D (D.params f) × World D) : Prop :=
  ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (κ : World D),
    ReqAmEintritt P F.f F.s0 F.rho ∧ FunkV H ∧ VertraegeOkV P H ∧ KurzV κ.spur.length H ∧
    FunkA HA ∧ RahmenA HA ∧ KurzA κ.spur.length HA ∧
    F.rest.2.2.2.2.okV P (fussOrte P F.f) ∧
    ReqAmEintritt P G.1 κ G.2.1 ∧
    GleichAuf ((P.requires G.1).orte ++ (P.ensures G.1).orte) κ G.2.2 ∧
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
      PasstV R H → PasstA O' HA → ZeigerGleich O O' →
      FortV passes F G.1
        (zErg (execEnd (V := vertragVon D F.f) O' passes R (P.rumpf F.f) F.s0 F.rho)) R O'
        (R G.1 κ G.2.1)

def StapelV : (Σ f : D.Fn, Env D (D.params f) × World D) → List (RufRahmenG D) → Prop
  | _, [] => True
  | G, F :: rest => WarteV P O passes F G ∧ StapelV (RufSchluesselG F) rest

def FadenV (z : RufFadenG D) (W : World D) : Prop :=
  KopfV P O passes z.kopf W ∧ StapelV P O passes (RufSchluesselG z.kopf) z.stapel

def ZielInvV (M : RufMaschineG D) : Prop :=
  (∀ t, FadenV P O passes (M.faeden t) (M.weltVon t)) ∧ ∀ t, LogOk P (M.faeden t).log

end Inv

theorem logOk_grund {P : Programm D} {log : List (RufEreignisF D)} (h : LogOk P log)
    {g : D.Fn} {rho : Env D (D.params g)} {r : Fin (D.gruende g)} {s0 s1 : World D} :
    LogOk P (RufEreignisF.why g rho r s0 s1 :: log) := by
  intro ev hev
  rcases List.mem_cons.mp hev with rfl | hev
  · refine ⟨fun g' rho' s0' h' => ?_, fun g' rho' v' s0' s1' h' => ?_⟩ <;> cases h'
  · exact h ev hev

/-- `FortV` is monotone in the predicted result. -/
theorem fortV_mono {passes : Nat} {F : RufRahmenG D} {g : D.Fn} {X Y : ZErg (vertragVon D F.f)}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f} {O' : Orakel D}
    (hXY : X.folgt Y) : ∀ {a : RufAusgang g}, FortV passes F g Y R O' a → FortV passes F g X R O' a
  | .ok _ _, h => ⟨fun hw => ZErg.folgt_trans hXY (h.1 hw),
      fun l Γ Λ Λ' τ restb k ρc hc he => ZErg.folgt_trans hXY (h.2 l Γ Λ Λ' τ restb k ρc hc he)⟩
  | .why _ _, h => fun l Γ Λ Λ' τ n err restb k ρc hc hn =>
      ZErg.folgt_trans hXY (h l Γ Λ Λ' τ n err restb k ρc hc hn)
  | .logik _, _ => trivial
  | .hardware _, _ => trivial

/-! ## 4. The steps of the replay -/

section Schritte

variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem kopfV_okV {F : RufRahmenG D} {W : World D} (h : KopfV P O passes F W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D F.f) l Γ Λ} (hr : F.rest = ⟨l, Γ, Λ, ρ, r⟩) :
    r.okV P (fussOrte P F.f) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hok, _⟩ := h
  rw [hr] at hok
  exact hok

/-- **A head-local step without a new record** keeps the replay: the
    residue moves by a step of the frame semantics whose new prediction
    refines the old one. -/
theorem fadenV_lokal {z : RufFadenG D} {W W' : World D} (hF : FadenV P O passes z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (hstep : ∀ σ : World D, GleichAuf (fussOrte P z.kopf.f) σ W →
      r.okV P (fussOrte P z.kopf.f) →
      ∃ σ', σ.spur.length ≤ σ'.spur.length ∧ GleichAuf (fussOrte P z.kopf.f) σ' W' ∧
        r'.okV P (fussOrte P z.kopf.f) ∧
        ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
          (semV O' passes R r σ ρ).folgt (semV O' passes R r' σ' ρ')) :
    FadenV P O passes
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩ W' := by
  obtain ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hka, hg, hok, heq⟩, hS⟩ := hF
  have hok' : r.okV P (fussOrte P z.kopf.f) := by rw [hr] at hok; exact hok
  obtain ⟨σ', hl, hg', hok'', hsem⟩ := hstep σ hg hok'
  refine ⟨⟨H, HA, σ', hreq, hf, hv, kurzV_mono hk hl, hfa, hra, kurzA_mono hka hl, hg', hok'',
    fun R O' hR hA hz => ?_⟩, hS⟩
  have h1 := heq R O' hR hA hz
  rw [hr] at h1
  exact ZErg.folgt_trans h1 (hsem R O')

/-- Memory moved outside the head's footprint keeps the replay. -/
theorem fadenV_speicher {z : RufFadenG D} {W W' : World D} (hF : FadenV P O passes z W)
    (hw : ∀ c ∈ fussOrte P z.kopf.f, TraegerGleich W'.speicher W.speicher c) :
    FadenV P O passes z W' := by
  obtain ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hka, hg, hok, heq⟩, hS⟩ := hF
  refine ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hka, ⟨fun t ht => ?_, fun g hg' => ?_⟩, hok,
    heq⟩, hS⟩
  · exact (hg.1 t ht).trans (hw (.inl t) ht).symm
  · exact (hg.2 g hg').trans (hw (.inr g) hg').symm

/-- **The return leg.** -/
theorem popV_ens (hO : GutO O) (hK : ∀ f, KoerperGutV P passes f) {G : RufRahmenG D}
    {W : World D} (hG : KopfV P O passes G W) {lr : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D G.f) lr Γ Λ} (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩)
    (e : ErgExpr D Γ Λ (vertragVon D G.f).erg) (he : e.orte ⊆ fussOrte P G.f)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (σ : World D), (semV O' passes R r σ ρ).gleich
        (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ))) :
    EnsAmRueck P G.f G.s0 (W.lese Λ e.orte) G.rho
      (evalErg (W.lese Λ e.orte) e (W.lese Λ e.orte) ρ) := by
  obtain ⟨H, HA, σ, hreq, hf, hv, _, hfa, hra, _, hg, _, heq⟩ := hG
  have h1 := heq (rufAusV H) (orakelAus O HA) (rufAusV_passt hf) (orakelAus_passt O hfa) rfl
  rw [hr] at h1
  simp only at h1
  have h2 := ZErg.folgt_zurueck (ZErg.folgt_trans h1 (ZErg.folgt_of_gleich (hsem _ _ σ)))
  obtain ⟨σ'', hex, hsg⟩ := zErg_gleich_zurueck h2
  have hE := (hK G.f (orakelAus O HA) (orakelAus_rahmen hO hra) (rufAusV H)
    (rufAusV_respektiert hv) (rufAusV_ohneVorbedingung hv) G.s0 G.rho hreq).1 σ'' _ hex
  have hgl : GleichAuf (fussOrte P G.f) (σ.lese Λ e.orte) (W.lese Λ e.orte) :=
    hg.lese Λ Λ e.orte e.orte
  rw [evalErg_gleichAuf e (fun _ h => he h) hgl ρ] at hE
  exact ens_transfer hE (GleichAuf.refl _ _)
    (GleichAuf.mono (fun _ h => fuss_ens P G.f h) ((gleichAuf_SG hsg).trans hgl))

end Schritte
end Gabbro.Grammatik
