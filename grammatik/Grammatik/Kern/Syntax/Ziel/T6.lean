/- Part 6 of 6 of `Ziel` (split by instrumente/teile/lean-teilen.py; the umbrella `Ziel.lean` imports all parts). -/
import Grammatik.Kern.Syntax.Ziel.T5

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}
variable {D : Deklaration}
variable {D : Deklaration}

/-- **The witnessed chain from the whole run, closed.** The exact
    `kette_aus_lauf_bezeugt` premises minus `hWitSchritt`, with the exact
    `kette_aus_lauf_bezeugt` conclusion: chain identification (worlds and run
    by construction) with the unconditional table link plus the guard. The
    open step premise vanishes into one positional application of the §11
    glue (`hwitschritt_kleber_voll`, read-only reuse), which has exactly the
    `hWitSchritt` shape. The narrowing rides along openly: single-thread
    frame-covered runs over one table carrier under guard. Every premise is
    load-bearing. -/
theorem kette_aus_lauf_bezeugt_closed
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (Nb : Nebeneinander)
    (prog : PCProg D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc)
    (f : Faden) (code : Faden → D.Fn)
    (t₀ : D.Tab) (L : D.Lock)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (hCov : TraegerSchreibt (code f) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i)
    (hsingle_prog : ∀ g, g ≠ f → prog g = [])
    (hsingle_run : ∀ s ∈ M.lauf, s.faden = f)
    (hRahmen : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ'), s.istBlatt = true →
      (∀ t, V.schreibt t = true → D.schreibt (code f) t = true) ∧
      (∀ g, V.gschreibt g = true → D.gschreibt (code f) g = true))
    (hEintritt : EintrittPasst (code f) (GenStart sp).start)
    (hSchuld : SchuldnerHaelt (code f))
    (hInvSicht : InvSichtHaelt (code f) (GenStart sp).start)
    (hwit_leaf : ∀ (Mx : GenMaschine D) (V : Vertrag D) (l : Bool) (Γ : Ctx)
      (Λ Λ' : List (Res D)) (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
      (_hΛ : HeldGenau Λ (offen (Mx.spuren f))) (σ' : World D) (neu : List (Ereignis D))
      (_hstep : (execStmt O passes keinRuf s (Mx.weltVon f) ρ).welt = some σ'),
      TraegerSchreibt (code f) (.inl t₀) = true →
      ∃ (w : Bool) (Λw : List (Res D)) (hwL : List D.Lock),
        Ereignis.zugriff t₀ w Λw hwL ∈ neu)
    (hwit_lock : ∀ (Mx : GenMaschine D) (pcx : PCStand),
      PCReach P O passes prog (GenStart sp) Mx pcx →
      TraegerSchreibt (code f) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        Mx.lauf[j]? = some (Schritt.mk f (.zugriff t₀ w Λe he))) :
    ∃ J : GemeinsamerLauf (D := D) Nb,
      J.welten = M.welten ∧
      J.l = M.lauf ∧
      f ∈ J.faeden ∧
      SerialLink Nb J M.lauf t₀ ∧
      (∀ (g : Faden), g ∈ J.faeden → TraegerSchreibt (J.code g) (.inl t₀) = true →
        L ∈ D.haelt (J.code g)) := by
  exact kette_aus_lauf_bezeugt P O passes hO sp Nb prog M pc h f code t₀ L hGuardT hCov
    hsingle_prog hsingle_run hRahmen hEintritt hSchuld hInvSicht hwit_leaf hwit_lock
    (fun Mx Mx' hReach hReach' V l Γ Λ Λ' s ρ hΛ σ' neu hstep hM'l hM'w J hJw hmem hW hG
      hsingle hGuardT hCov hwit_old hneu_wit =>
      hwitschritt_kleber_voll P O passes hO sp Nb Mx Mx' f hReach hReach' V l Γ Λ Λ' s ρ
        hΛ σ' neu hstep hM'l hM'w J hJw hmem hW hG hsingle t₀ L hGuardT hCov hwit_old hneu_wit)

#print axioms Gabbro.Grammatik.kette_aus_lauf_bezeugt_closed

end Gabbro.Grammatik

/-! ## 13. The Q-binder corollary: the stabil variant at `QRequires` / `QEnsures` (s01, 2026-09-12)

    FINDING (rank HIGH, two checkers): the Q-binder is missing -- no theorem
    applies the variant `ziel_nutzer_last_aus_pc_stabil` (§9b continued, same
    file) at `Pre := QRequires P`, `Post := QEnsures P`.

    What this section wires in (read-only reuse; this file only appends):

    * `ziel_nutzer_last_aus_pc_Q` concludes the exact variant conclusion at
      the Q-instantiation, by one positional application of
      `ziel_nutzer_last_aus_pc_stabil` at `Pre := Extraktion.QRequires P`,
      `Post := Extraktion.QEnsures P`.
    * `hMemAll` arrives via `Extraktion.speicherVertrag_aus_Q` (premise-free:
      the Q-contracts read only live memory at every function).
    * `hAb` arrives via `Extraktion.haengtAb_vertrag_gesamt` at each member
      thread's function. The narrowing it needs -- both contract footprints
      inside the signature frame -- rides along openly as four per-member
      premises (`hReqTAll`, `hReqGAll`, `hEnsTAll`, `hEnsGAll`), not hidden.
    * Every premise is load-bearing: each feeds the variant application or
      the footprint fold, so deleting any premise breaks elaboration. There
      is no `have _ :=` discard, no `sorry`/`admit`/`axiom`, and no bare
      `Prop` slot that `False` could inhabit (the run is owed as
      `PCReach`/`PCSpur`, the wiring as equations over them).

    Remainder (booked, not hidden): discharging the four footprint premises
    per program (checker footprint duty); the `hJw`/`hJsf` wiring, `hBlattAll`
    per leaf, and head validity from thread entry -- exactly as the variant
    books them.
-/

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-- The goal from PC runs at Q-contracts (Q-binder corollary): the
    `ziel_nutzer_last_aus_pc` conclusion with `Pre := QRequires P` and
    `Post := QEnsures P`, the posited `hSpec` replaced by the run premises
    exactly as the stabil variant replaces it, and the two contract-side
    premises discharged by read-only reuse (`speicherVertrag_aus_Q` for the
    memory leg, `haengtAb_vertrag_gesamt` for the frame leg over four
    explicit per-member footprint premises). Every premise is load-bearing. -/
theorem ziel_nutzer_last_aus_pc_Q (o : Ausgang V l Γ)
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (fcode : Faden → D.Fn) (tabs : List D.Tab) (globs : List D.Glob)
    (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp) M pc)
    (code : D.Marke → Nat)
    (hMSep : PCMarkSep code (Extraktion.progAus P fcode tabs globs))
    (hCSep : PCUnsharedSep (Extraktion.progAus P fcode tabs globs))
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D))
    (Wc : (c : D.Tab ⊕ D.Glob) → D.Tab → Bool)
    (Gc : (c : D.Tab ⊕ D.Glob) → D.Glob → Bool)
    (hAbD : ∀ c, HaengtAb (Wc c) (Gc c) (I.inv c))
    (hFrameTD : ∀ (c : D.Tab ⊕ D.Glob) (t : D.Tab), Wc c t = true → c = .inl t)
    (hFrameGD : ∀ (c : D.Tab ⊕ D.Glob) (x : D.Glob), Gc c x = true → c = .inr x)
    (hGuardEx : ∀ c : D.Tab ⊕ D.Glob, ∃ L : D.Lock, Bewacht (D := D) c L)
    (hEntry : ∀ (c : D.Tab ⊕ D.Glob) (σ₀ : World D),
      J.welten[0]? = some σ₀ → I.inv c σ₀)
    (hReturn : ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock) (k : Nat) (g : Faden)
      (vor nach : World D),
      Bewacht (D := D) c L → g ∈ J.faeden → J.schrittFaden[k]? = some g →
        J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          TraegerSchreibt (J.code g) c = true → L ∈ D.haelt (J.code g) → I.inv c nach)
    (hWatch : ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock) (k : Nat) (g : Faden)
      (vor nach : World D),
      Bewacht (D := D) c L → g ∈ J.faeden → J.schrittFaden[k]? = some g →
        J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          TraegerSchreibt (J.code g) c = true → L ∈ D.haelt (J.code g))
    (hDeck : GeteiltGedeckt Nb J)
    (hReqTAll : ∀ (g : Faden), g ∈ J.faeden → ∀ t : D.Tab,
      .inl t ∈ (P.requires (J.code g)).orte → D.schreibt (J.code g) t = true)
    (hReqGAll : ∀ (g : Faden), g ∈ J.faeden → ∀ x : D.Glob,
      .inr x ∈ (P.requires (J.code g)).orte → D.gschreibt (J.code g) x = true)
    (hEnsTAll : ∀ (g : Faden), g ∈ J.faeden → ∀ t : D.Tab,
      .inl t ∈ (P.ensures (J.code g)).orte → D.schreibt (J.code g) t = true)
    (hEnsGAll : ∀ (g : Faden), g ∈ J.faeden → ∀ x : D.Glob,
      .inr x ∈ (P.ensures (J.code g)).orte → D.gschreibt (J.code g) x = true)
    (hForm : InvariantForm Nb J I
      (SpecQ (Extraktion.QRequires P) (Extraktion.QEnsures P) Nb J))
    (tr : List Faden)
    (htr : PCSpur P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp) M pc tr)
    (hJw : J.welten = M.welten)
    (hJsf : J.schrittFaden = tr)
    (hSeedAll : ∀ (g : Faden), g ∈ J.faeden →
      (∀ σ₀ : World D, (GenStart sp).welten[0]? = some σ₀ →
        Extraktion.QRequires P (J.code g) σ₀) ∧
      (∀ σ₀ : World D, (GenStart sp).welten[0]? = some σ₀ →
        Extraktion.QEnsures P (J.code g) σ₀))
    (hBlattAll : ∀ (g : Faden), g ∈ J.faeden → ∀ (M₀ : GenMaschine D) (pc₀ : PCStand),
      PCReach P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp) M₀ pc₀ →
      ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ),
      s.istBlatt = true → HeldGenau Λ (offen (M₀.spuren g)) →
      ∀ (σ' : World D) (neu : List (Ereignis D)),
      (execStmt O passes keinRuf s (M₀.weltVon g) ρ).welt = some σ' →
      σ'.spur = neu ++ M₀.spuren g →
      (∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) →
      (Extraktion.QRequires P (J.code g) (M₀.weltVon g) ↔
        Extraktion.QRequires P (J.code g) σ') ∧
        (Extraktion.QEnsures P (J.code g) (M₀.weltVon g) ↔
          Extraktion.QEnsures P (J.code g) σ'))
    (t₀ : D.Tab) (g₁ g₂ : Faden) (hne : g₁ ≠ g₂)
    (j₁ j₂ : Nat) (w₁ w₂ : Bool) (Λ₁ Λ₂ : List (Res D)) (h₁ h₂ : List D.Lock)
    (hw₁ : M.lauf[j₁]? = some (Schritt.mk g₁ (.zugriff t₀ w₁ Λ₁ h₁)))
    (hw₂ : M.lauf[j₂]? = some (Schritt.mk g₂ (.zugriff t₀ w₂ Λ₂ h₂)))
    (S : Nat) (c : TickClock S) (hstart : c.tick 0 ≤ S)
    (p : PruefPaar) (fr : Frist D) (d : Moment)
    (hpd : p.pruef < d) (hdl : d < p.lauf)
    (hspace : deadlineSpacing S p d)
    (hLowering : Absenkung) :
    (Gesittet M.lauf)
    ∧ ((∀ f j, Konsistent (M.lauf.spur f j)) ∧
      ∀ f j (e : Ereignis D), e ∈ M.lauf.spur f j → e.gut)
    ∧ (∀ (σ : World D), J.welten.getLast? = some σ →
      ∀ (f : Faden), f ∈ J.faeden →
        SpecQ (Extraktion.QRequires P) (Extraktion.QEnsures P) Nb J f σ)
    ∧ (∃ n, d ≤ c.tick n ∧ c.tick n ≤ p.lauf ∧
      fristErgebnis (fristlauf p fr (some d)) = some (.fortschritt fr.annahme))
    ∧ (hLowering.proPrimitiv ≤ 18)
    ∧ ((∃ σ ρ, o = .ok σ ρ) ∨ (∃ σ v, o = .zurueck σ v) ∨ (∃ σ r, o = .why σ r) ∨
      (∃ h σ ρ, o = .leave h σ ρ) ∨ (∃ h σ ρ, o = .next h σ ρ) ∨
      (∃ e : Logik D, o = .logik e) ∨ (∃ e : Hardware D, o = .hardware e))
    ∧ (Marken.Einfaedig (laufProj code M.lauf))
    ∧ (∀ (i j : Nat) (f g : Faden) (carr : D.Tab ⊕ D.Glob) (ei ej : Ereignis D),
      M.lauf[i]? = some (Schritt.mk f ei) → M.lauf[j]? = some (Schritt.mk g ej) →
      (match carr with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) →
      ei.traeger = some carr → ej.traeger = some carr → f = g)
    ∧ (M.welten.length = M.tiefe + 1)
    ∧ (∀ W ∈ M.welten, ∀ e ∈ W.spur, e.gut)
    ∧ (∃ f, M.welten.getLast? = some (M.speicher.welt (M.spuren f)))
    ∧ (HB M.lauf j₁ j₂ ∨ HB M.lauf j₂ j₁) := by
  have hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f))
        (SpecQ (Extraktion.QRequires P) (Extraktion.QEnsures P) Nb J f) :=
    fun f hf => Extraktion.haengtAb_vertrag_gesamt P (J.code f)
      (hReqTAll f hf) (hReqGAll f hf) (hEnsTAll f hf) (hEnsGAll f hf)
  have hMemAll : ∀ (g : Faden), g ∈ J.faeden →
      SpeicherVertrag (Extraktion.QRequires P) (Extraktion.QEnsures P) (J.code g) :=
    fun g _ => Extraktion.speicherVertrag_aus_Q P (J.code g)
  exact ziel_nutzer_last_aus_pc_stabil o P O passes hO fcode tabs globs sp M pc h
    code hMSep hCSep Nb J I _ _ Wc Gc hAbD hFrameTD hFrameGD hGuardEx hEntry hReturn
    hWatch hDeck hAb hForm tr htr hJw hJsf hMemAll hSeedAll hBlattAll t₀ g₁ g₂ hne
    j₁ j₂ w₁ w₂ Λ₁ Λ₂ h₁ h₂ hw₁ hw₂ S c hstart p fr d hpd hdl hspace hLowering

#print axioms Gabbro.Grammatik.ziel_nutzer_last_aus_pc_Q


end Gabbro.Grammatik
