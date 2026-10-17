/- Part 5 of 6 of `Ziel` (split by instrumente/teile/lean-teilen.py; the umbrella `Ziel.lean` imports all parts). -/
import Grammatik.Kern.Syntax.Ziel.T4

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}
variable {D : Deklaration}

/-- **The witnessed step over the computed program, `axiomCall` leaves under
    `GutO`.** The firing data of an oracle leaf builds the covered PC step
    through `pcSchritt_blatt_progAus_axiomCall` under the oracle bound
    (`hO` feeds the lifter, the frame, and the projection lemmas -- GutO
    oracles only, with recorded write events), while the SAME `neu` feeds the witnessed chain extension
    (`kette_mit_zeugen_schritt`) with the frame wiring (`hW`/`hG`), the
    prefix witness duty (`hwit_old`), and the step witness (`hneu_wit`).
    The conclusion carries the extended chain, its member, the unconditional
    table link, the guard, and the covered run. Every premise is
    load-bearing. -/
theorem kette_mit_zeugen_orakel
    (O : Orakel D) (passes : Nat) (hO : GutO O)
    (P : Programm D) (fcode : Faden → D.Fn)
    (tabs : List D.Tab) (globs : List D.Glob)
    (M : GenMaschine D) (pc : PCStand) (f : Faden)
    (sp : Speicher D)
    (h : PCReach P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp) M pc)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ : List (Res D))
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (hh : D.aerg a = none)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (hct : ∀ t, D.aschreibt a t = true → t ∈ tabs)
    (hcg : ∀ g, D.agschreibt a g = true → g ∈ globs)
    (ρ : Env D Γ)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf
      (Stmt.axiomCall a args hh hw hg hd hgd : Stmt D V l Γ Λ Λ) (M.weltVon f) ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ M.spuren f)
    (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
    (Λa : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
    (hpc : (Extraktion.progAus P fcode tabs globs f)[pc f]? = some (PCAtom.leaf Λa cs))
    (hΛa : Λa = Λ)
    (hcs : cs = Extraktion.stmtTraeger tabs globs
      (Stmt.axiomCall a args hh hw hg hd hgd : Stmt D V l Γ Λ Λ) ++
      Extraktion.stmtOrte
        (Stmt.axiomCall a args hh hw hg hd hgd : Stmt D V l Γ Λ Λ))
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (hJw : J.welten = M.welten)
    (hmem : f ∈ J.faeden)
    (hW : ∀ t, V.schreibt t = true → D.schreibt (J.code f) t = true)
    (hG : ∀ g, V.gschreibt g = true → D.gschreibt (J.code f) g = true)
    (hsingle : ∀ st ∈ M.lauf, st.faden = f)
    (t₀ : D.Tab) (L : D.Lock)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (hCov : ∀ (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i)
    (hwit_old : ∀ (k : Nat) (g : Faden), J.schrittFaden[k]? = some g →
      TraegerSchreibt (J.code g) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        M.lauf[j]? = some (Schritt.mk g (.zugriff t₀ w Λe he)))
    (hneu_wit : TraegerSchreibt (J.code f) (.inl t₀) = true →
      ∃ (w : Bool) (Λw : List (Res D)) (hwL : List D.Lock),
        Ereignis.zugriff t₀ w Λw hwL ∈ neu) :
    ∃ (J' : GemeinsamerLauf (D := D) Nb) (M' : GenMaschine D) (pc' : PCStand),
      J'.welten = M'.welten ∧
      J'.l = M'.lauf ∧
      f ∈ J'.faeden ∧
      SerialLink Nb J' M'.lauf t₀ ∧
      (∀ (g : Faden), g ∈ J'.faeden → TraegerSchreibt (J'.code g) (.inl t₀) = true →
        L ∈ D.haelt (J'.code g)) ∧
      PCReach P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp) M' pc' := by
  have hSchritt : PCSchritt P O passes (Extraktion.progAus P fcode tabs globs) M pc f
      ⟨σ'.speicher, genUpdate M.spuren f σ'.spur,
       M.lauf ++ genEigen f neu, M.start, M.welten ++ [σ'], M.tiefe + 1⟩
      (pcAdvance pc f) :=
    pcSchritt_blatt_progAus_axiomCall O passes hO P fcode tabs globs M pc f V l Γ Λ
      a args hh hw hg hd hgd hct hcg ρ hΛ σ' neu hstep hneu hkein_nimmt Λa cs hpc hΛa hcs
  have hReach : GenErreichbar P O passes (GenStart sp) M :=
    pcReach_gen P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp) M pc h
  have hPC' : PCReach P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp)
      ⟨σ'.speicher, genUpdate M.spuren f σ'.spur,
       M.lauf ++ genEigen f neu, M.start, M.welten ++ [σ'], M.tiefe + 1⟩
      (pcAdvance pc f) :=
    PCReach.step _ _ _ _ f h hSchritt
  have hReach' : GenErreichbar P O passes (GenStart sp)
      ⟨σ'.speicher, genUpdate M.spuren f σ'.spur,
       M.lauf ++ genEigen f neu, M.start, M.welten ++ [σ'], M.tiefe + 1⟩ :=
    pcReach_gen P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp) _ _ hPC'
  obtain ⟨J', hJ'w, hJ'l, hmem', hLink', hGuard'⟩ :=
    kette_mit_zeugen_schritt P O passes hO sp Nb M _ f hReach hReach' V l Γ Λ Λ
      (Stmt.axiomCall a args hh hw hg hd hgd : Stmt D V l Γ Λ Λ) ρ
      hΛ σ' neu hstep rfl rfl J hJw hmem hW hG hsingle t₀ L hGuardT hCov hwit_old hneu_wit
  exact ⟨J', _, _, hJ'w, hJ'l, hmem', hLink', hGuard', hPC'⟩

#print axioms Gabbro.Grammatik.kette_mit_zeugen_orakel

/-! ## 11. The hWitSchritt glue: reuse leg closed, identities open (d01, 2026-09-12);
    full replay closed (f01, 2026-09-12)

    BEFUND (rank HOCH): `kette_mit_zeugen_schritt` (§10 above) concludes 5
    conjuncts, but `kette_aus_lauf_bezeugt`'s `hWitSchritt`
    (`MaschinenKette.lean:1450-58`) needs 7 -- plus the `faeden`/`code`
    construction identities, which hold `by rfl` AT THE LITERAL
    (`Ziel.lean:1466`: `faeden := J.faeden, code := J.code`).

    MISSION was `hWitSchritt := kette_mit_zeugen_schritt + identities`.
    RESULT (measured, not assumed): 5 of 7 close by read-only reuse
    (`hwitschritt_kleber_reuse` below: every §10 premise forwarded in one
    application, so every premise is load-bearing); the 2 identities do NOT
    close from the obtained witness. After `obtain`, `J'` is an opaque
    variable: the literal stays hidden behind the existential elimination,
    and the 5 obtained hypotheses say nothing about `J'.faeden`/`J'.code`.
    Both `rfl` attempts fail definitionally (checked against these exact
    premises, witness obtained from the §10 step):

    - `J'.faeden = J.faeden`: tactic `rfl` failed, LHS not definitionally
      equal to RHS.
    - `J'.code = J.code`: tactic `rfl` failed, LHS not definitionally equal
      to RHS.

    So `∃ J', P5 J'` does not entail the identities; only the premises entail
    the 7-conjunct statement, via the construction. Full discharge needs the
    construction replayed (the literal plus its proof fields, §10 body),
    which §11 does not duplicate (`MaschinenKette.lean:1051`: the step proof
    is never duplicated).

    f01 RESULT: `hwitschritt_kleber_voll` below replays the §10 construction
    (literal `Ziel.lean:1466` plus its proof fields) inside the §11 glue, so
    all 7 `hWitSchritt` conjuncts conclude genuinely: worlds and run by
    construction, member, both identities by `rfl` at the replayed literal,
    the unconditional table link, and the guard. Each replay step cites its
    §10 source line; the §10 text itself is untouched.

    Remainder (booked, not hidden): `J'.faeden = J.faeden` and
    `J'.code = J.code` over the §10 premises -- the two `hWitSchritt`
    conjuncts `MaschinenKette.lean:1454-55` -- CLOSED by `hwitschritt_kleber_voll`;
    no open remainder on this glue.
-/

/-- **The hWitSchritt reuse leg (5 of 7 conjuncts).** The exact §10 step
    premises forwarded in one application to `kette_mit_zeugen_schritt`
    (read-only reuse, same file): worlds and run by construction, member,
    the unconditional table link, and the guard. Every premise is
    load-bearing: each is passed to the step, so deleting any premise breaks
    elaboration. The 2 construction identities (`J'.faeden`/`J'.code`) are
    NOT concluded here -- they do not follow from the obtained witness (see
    §11 header for the measured `rfl` failures); they stay open as remainder.
    -/
theorem hwitschritt_kleber_reuse
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (Nb : Nebeneinander)
    (M M' : GenMaschine D) (f : Faden)
    (hReach : GenErreichbar P O passes (GenStart sp) M)
    (hReach' : GenErreichbar P O passes (GenStart sp) M')
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
    (hM'l : M'.lauf = M.lauf ++ genEigen f neu)
    (hM'w : M'.welten = M.welten ++ [σ'])
    (J : GemeinsamerLauf (D := D) Nb)
    (hJw : J.welten = M.welten)
    (hmem : f ∈ J.faeden)
    (hW : ∀ t, V.schreibt t = true → D.schreibt (J.code f) t = true)
    (hG : ∀ g, V.gschreibt g = true → D.gschreibt (J.code f) g = true)
    (hsingle : ∀ st ∈ M.lauf, st.faden = f)
    (t₀ : D.Tab) (L : D.Lock)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (hCov : ∀ (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i)
    (hwit_old : ∀ (k : Nat) (g : Faden), J.schrittFaden[k]? = some g →
      TraegerSchreibt (J.code g) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        M.lauf[j]? = some (Schritt.mk g (.zugriff t₀ w Λe he)))
    (hneu_wit : TraegerSchreibt (J.code f) (.inl t₀) = true →
      ∃ (w : Bool) (Λw : List (Res D)) (hwL : List D.Lock),
        Ereignis.zugriff t₀ w Λw hwL ∈ neu) :
    ∃ J' : GemeinsamerLauf (D := D) Nb,
      J'.welten = M'.welten ∧
      J'.l = M'.lauf ∧
      f ∈ J'.faeden ∧
      SerialLink Nb J' M'.lauf t₀ ∧
      (∀ (g : Faden), g ∈ J'.faeden → TraegerSchreibt (J'.code g) (.inl t₀) = true →
        L ∈ D.haelt (J'.code g)) :=
  kette_mit_zeugen_schritt P O passes hO sp Nb M M' f hReach hReach' V l Γ Λ Λ' s ρ
    hΛ σ' neu hstep hM'l hM'w J hJw hmem hW hG hsingle t₀ L hGuardT hCov hwit_old hneu_wit

#print axioms Gabbro.Grammatik.hwitschritt_kleber_reuse

/-- **The hWitSchritt full glue (7 of 7 conjuncts, f01).** Same premises as
    the §10 step `kette_mit_zeugen_schritt` (same types, same order), but the
    conclusion carries the full `hWitSchritt` shape from
    `kette_aus_lauf_bezeugt` (`MaschinenKette.lean:1450-58`): worlds and run
    by construction, member, BOTH construction identities, the unconditional
    table link, and the guard. The proof replays the §10 construction -- the
    literal (`Ziel.lean:1466`: `faeden := J.faeden, code := J.code`) plus its
    proof fields -- so the 2 identities conclude genuinely by `rfl` at the
    replayed literal instead of being reused from an opaque witness. Every
    premise is load-bearing exactly as in §10: each feeds the lifter, the
    frame, the transport, or the package, so deleting any premise breaks
    elaboration. There is no `have _ :=` discard, and no
    `sorry`/`admit`/`axiom`. -/
theorem hwitschritt_kleber_voll
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (Nb : Nebeneinander)
    (M M' : GenMaschine D) (f : Faden)
    (hReach : GenErreichbar P O passes (GenStart sp) M)
    (hReach' : GenErreichbar P O passes (GenStart sp) M')
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
    (hM'l : M'.lauf = M.lauf ++ genEigen f neu)
    (hM'w : M'.welten = M.welten ++ [σ'])
    (J : GemeinsamerLauf (D := D) Nb)
    (hJw : J.welten = M.welten)
    (hmem : f ∈ J.faeden)
    (hW : ∀ t, V.schreibt t = true → D.schreibt (J.code f) t = true)
    (hG : ∀ g, V.gschreibt g = true → D.gschreibt (J.code f) g = true)
    (hsingle : ∀ st ∈ M.lauf, st.faden = f)
    (t₀ : D.Tab) (L : D.Lock)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (hCov : ∀ (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i)
    (hwit_old : ∀ (k : Nat) (g : Faden), J.schrittFaden[k]? = some g →
      TraegerSchreibt (J.code g) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        M.lauf[j]? = some (Schritt.mk g (.zugriff t₀ w Λe he)))
    (hneu_wit : TraegerSchreibt (J.code f) (.inl t₀) = true →
      ∃ (w : Bool) (Λw : List (Res D)) (hwL : List D.Lock),
        Ereignis.zugriff t₀ w Λw hwL ∈ neu) :
    ∃ J' : GemeinsamerLauf (D := D) Nb,
      J'.welten = M'.welten ∧
      J'.l = M'.lauf ∧
      f ∈ J'.faeden ∧
      J'.faeden = J.faeden ∧
      J'.code = J.code ∧
      SerialLink Nb J' M'.lauf t₀ ∧
      (∀ (g : Faden), g ∈ J'.faeden → TraegerSchreibt (J'.code g) (.inl t₀) = true →
        L ∈ D.haelt (J'.code g)) := by
  -- Source §10 Ziel.lean:1357-1361: the old-run link and guard arrive via the
  -- e02 table package over the prefix witness duty, not as assumed premises.
  have hLinkOld : SerialLink Nb J M.lauf t₀ :=
    (serialLink_zeuge_tabelle Nb J M.lauf t₀ L hGuardT hCov hwit_old).1
  have hGuardOld : ∀ (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → L ∈ D.haelt (J.code g) :=
    (serialLink_zeuge_tabelle Nb J M.lauf t₀ L hGuardT hCov hwit_old).2
  -- Source §10 Ziel.lean:1362-1364: chain length routing through the old chain.
  have hlen : M.welten.length = J.schrittFaden.length + 1 := by
    rw [← hJw]
    exact J.hKette
  -- Source §10 Ziel.lean:1365: the last old world is a stored world.
  obtain ⟨f0, hlast⟩ := genWelten_letzte P O passes hO sp M hReach
  -- Source §10 Ziel.lean:1366-1373: index form of the last-world fact.
  have hLastIdx : M.welten[J.schrittFaden.length]? =
      some (M.speicher.welt (M.spuren f0)) := by
    have hget : M.welten.getLast? = M.welten[M.welten.length - 1]? :=
      List.getLast?_eq_getElem?
    have hn : M.welten.length - 1 = J.schrittFaden.length := by omega
    rw [hn] at hget
    rw [hlast] at hget
    exact hget.symm
  -- Source §10 Ziel.lean:1374-1383: every extended-run step is by `f` -- old
  -- steps via the single-thread premise, new steps via `genEigen` shape.
  have hfaden : ∀ (i : Nat) (g : Faden) (ei : Ereignis D),
      M'.lauf[i]? = some (Schritt.mk g ei) → g = f := by
    intro i g ei hi
    rw [hM'l] at hi
    by_cases hlt : i < M.lauf.length
    · rw [List.getElem?_append_left hlt] at hi
      exact hsingle _ (List.mem_of_getElem? hi)
    · have hle : M.lauf.length ≤ i := by omega
      rw [List.getElem?_append_right hle] at hi
      exact (gen_eigen_getElem f neu _ _ _ hi).1
  -- Source §10 Ziel.lean:1384-1395: the extended run is well-behaved, from the
  -- reachability projections plus single-thread collapse.
  have hGes' : Gesittet M'.lauf := by
    refine ⟨gen_konsistent P O passes hO sp M' hReach',
            gen_gut_obs P O passes hO sp M' hReach',
            gen_ausschluss P O passes hO sp M' hReach', ?_, ?_⟩
    · intro i j g1 g2 m s s' e1 e2 hi hj _ _
      have h1 := hfaden i g1 e1 hi
      have h2 := hfaden j g2 e2 hj
      exact h1.trans h2.symm
    · intro i j g1 g2 o e1 e2 hi hj _ _ _
      have h1 := hfaden i g1 e1 hi
      have h2 := hfaden j g2 e2 hj
      exact h1.trans h2.symm
  -- Source §10 Ziel.lean:1396-1400: bounded interleaving collapses the same way.
  have hBeschr' : BeschraenkteVerschraenkung (D := D) Nb M'.lauf := by
    intro i j g1 g2 e1 e2 hi hj hne
    have h1 := hfaden i g1 e1 hi
    have h2 := hfaden j g2 e2 hj
    exact absurd (h1.trans h2.symm) hne
  -- Source §10 Ziel.lean:1401-1404: extended chain length from the run extension.
  have hKette' : M'.welten.length = (J.schrittFaden ++ [f]).length + 1 := by
    have h1 : (J.schrittFaden ++ [f]).length = J.schrittFaden.length + 1 := by simp
    have h2 : M'.welten.length = M.welten.length + 1 := by rw [hM'w]; simp
    omega
  -- Source §10 Ziel.lean:1405-1462: the extended step proof -- old steps replay
  -- the old chain, the new step runs the frame; single new thread only.
  have hSchritt' : ∀ (k : Nat) (g0 : Faden) (vor nach0 : World D),
      (J.schrittFaden ++ [f])[k]? = some g0 → M'.welten[k]? = some vor →
      M'.welten[k + 1]? = some nach0 →
      g0 ∈ J.faeden ∧
        Rahmen (D.schreibt (J.code g0)) (D.gschreibt (J.code g0)) vor nach0 := by
    intro k g0 vor nach0 hk hkv hkn
    rw [hM'w] at hkv hkn
    by_cases hlt : k < J.schrittFaden.length
    · have e1 : (J.schrittFaden ++ [f])[k]? = J.schrittFaden[k]? :=
        List.getElem?_append_left hlt
      rw [e1] at hk
      have hltM : k < M.welten.length := by omega
      have e2 : (M.welten ++ [σ'])[k]? = M.welten[k]? :=
        List.getElem?_append_left hltM
      rw [e2] at hkv
      have hJkv : J.welten[k]? = some vor := by rw [hJw]; exact hkv
      have hltM1 : k + 1 < M.welten.length := by omega
      have e3 : (M.welten ++ [σ'])[k + 1]? = M.welten[k + 1]? :=
        List.getElem?_append_left hltM1
      rw [e3] at hkn
      have hJkn : J.welten[k + 1]? = some nach0 := by rw [hJw]; exact hkn
      exact J.hSchritt k g0 vor nach0 hk hJkv hJkn
    · by_cases heq : k = J.schrittFaden.length
      · subst heq
        have eNew : (J.schrittFaden ++ [f])[J.schrittFaden.length]? = some f := by
          rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        rw [eNew] at hk
        have hg0 : g0 = f := (Option.some_inj.mp hk).symm
        have eW : (M.welten ++ [σ'])[J.schrittFaden.length]? =
            M.welten[J.schrittFaden.length]? :=
          List.getElem?_append_left (by omega)
        rw [eW, hLastIdx] at hkv
        have hvor : vor = M.speicher.welt (M.spuren f0) :=
          Option.some_inj.mp hkv.symm
        have eW2 : (M.welten ++ [σ'])[J.schrittFaden.length + 1]? = some σ' := by
          have hle2 : M.welten.length ≤ J.schrittFaden.length + 1 := by omega
          rw [List.getElem?_append_right hle2]
          have hsub : J.schrittFaden.length + 1 - M.welten.length = 0 := by omega
          rw [hsub]
          rfl
        rw [eW2] at hkn
        have hnach0 : σ' = nach0 := Option.some_inj.mp hkn
        rw [hg0, hvor, ← hnach0]
        have hR := blatt_rahmen_schritt O passes hO M f V l Γ Λ Λ' s ρ hΛ σ' hstep
          J.code hW hG
        refine ⟨hmem, ?_, ?_⟩
        · intro t ht k2 fld
          exact hR.1 t ht k2 fld
        · intro g hg
          exact hR.2 g hg
      · have hle : J.schrittFaden.length ≤ k := by omega
        have eNone : (J.schrittFaden ++ [f])[k]? = none := by
          rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
            List.length_singleton]
          omega
        rw [eNone] at hk
        simp at hk
  -- Source §10 Ziel.lean:1466-1471: the replayed literal -- member and code
  -- kept by construction. The 2 identities below close by `rfl` AT THIS
  -- LITERAL (not from an opaque witness): this is the step the reuse leg
  -- (`hwitschritt_kleber_reuse`) cannot take.
  refine ⟨{ faeden := J.faeden, code := J.code, eintritt := J.eintritt,
            welten := M'.welten, schrittFaden := J.schrittFaden ++ [f], l := M'.lauf,
            hKette := hKette', hSchritt := hSchritt', hPaar := J.hPaar,
            hGesittet := hGes', hBeschraenkt := hBeschr',
            hEintritt := J.hEintritt, hSchuld := J.hSchuld, hInvSicht := J.hInvSicht },
          rfl, rfl, hmem, rfl, rfl, ?_, ?_⟩
  -- Source §10 Ziel.lean:1472-1513: the unconditional link -- old steps inherit
  -- from the packaged link, the new writing step owns the fired leaf witness
  -- transported from `neu` into the extended run.
  · intro k0 g0 hk0 hwr
    have hk0' : (J.schrittFaden ++ [f])[k0]? = some g0 := hk0
    have hwr0 : TraegerSchreibt (J.code g0) (.inl t₀) = true := hwr
    by_cases hlt : k0 < J.schrittFaden.length
    · have eOld : (J.schrittFaden ++ [f])[k0]? = J.schrittFaden[k0]? :=
        List.getElem?_append_left hlt
      rw [eOld] at hk0'
      obtain ⟨j, w, Λe, he, hw⟩ := hLinkOld k0 g0 hk0' hwr0
      have hjlt : j < M.lauf.length := by
        by_cases h : j < M.lauf.length
        · exact h
        · have hle : M.lauf.length ≤ j := by omega
          rw [List.getElem?_eq_none hle] at hw
          simp at hw
      have hw' : M'.lauf[j]? = some (Schritt.mk g0 (.zugriff t₀ w Λe he)) := by
        rw [hM'l, List.getElem?_append_left hjlt]
        exact hw
      exact ⟨j, w, Λe, he, hw'⟩
    · by_cases heq : k0 = J.schrittFaden.length
      · subst heq
        have hg0 : g0 = f := by
          have eNew : (J.schrittFaden ++ [f])[J.schrittFaden.length]? = some f := by
            rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
            rfl
          rw [eNew] at hk0'
          exact (Option.some_inj.mp hk0').symm
        rw [hg0] at hwr
        obtain ⟨w, Λw, hwL, hmem_neu⟩ := hneu_wit hwr
        obtain ⟨j, hj⟩ := genEigen_wit_index M.lauf f neu _ hmem_neu
        refine ⟨j, w, Λw, hwL, ?_⟩
        rw [hg0, hM'l]
        exact hj
      · have hle : J.schrittFaden.length ≤ k0 := by omega
        have eNone : (J.schrittFaden ++ [f])[k0]? = none := by
          rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
            List.length_singleton]
          omega
        rw [eNone] at hk0'
        simp at hk0'
  -- Source §10 Ziel.lean:1514-1515: the guard rides along from the package --
  -- definitionally over the replayed literal (`J'.faeden`/`J'.code` are `J`'s).
  · intro g hg hWr
    exact hGuardOld g hg hWr

#print axioms Gabbro.Grammatik.hwitschritt_kleber_voll

end Gabbro.Grammatik

/-! ## 12. The witnessed whole run, closed: no open step premise (i01)

    The call-site gap behind `kette_aus_lauf_bezeugt`
    (`MaschinenKette.lean`, read-only here): its concluding identification --
    a chain tracking the whole run with the unconditional table link plus the
    guard -- travels with the step hypothesis `hWitSchritt`, and no consumer
    discharges it. The discharge stands here, not there: `Ziel` imports
    `MaschinenKette` (not vice versa), so the application corollary lives in
    this file. `hwitschritt_kleber_voll` (§11, read-only reuse) has exactly the
    `hWitSchritt` shape -- same quantified machines, reachabilities, firing
    data, chain, and witness duties, over the same outer run, thread, carrier,
    and guard -- so one positional application closes every leaf of the
    whole-run induction. The corollary below takes the exact
    `kette_aus_lauf_bezeugt` premises minus `hWitSchritt` and concludes the
    exact `kette_aus_lauf_bezeugt` conclusion: worlds and run by construction,
    the member thread, the unconditional table link, and the guard, with no
    open step premise left.

    Narrowing carried explicitly, never widened: single-thread runs
    (`hsingle_prog`, `hsingle_run`), frame-covered leaves (`hRahmen`), one
    shared table carrier under guard (`t₀`, `L`, `hGuardT`, `hCov`). Witness
    duties stay posited -- per firing (`hwit_leaf`) and per prefix
    (`hwit_lock`) -- as scheduler/witness duty, exactly as the call site
    books them.

    Every premise is load-bearing: each is passed whole to the call-site
    theorem or to the glue, so deleting any premise breaks elaboration. There
    is no `have _ :=` discard, no `sorry`/`admit`/`axiom`, and no bare `Prop`
    slot.

    Remainder (booked, not hidden): globals, multi-carrier conflicts,
    multi-thread runs, and the witness duties themselves -- inherited from the
    call site unchanged. -/

namespace Gabbro.Grammatik

variable {D : Deklaration}


end Gabbro.Grammatik
