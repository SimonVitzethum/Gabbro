module

public import Grammatik.Kern.Syntax.Ziel.T3
public import Grammatik.Kern.Syntax.Ziel.T4.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-- **The witnessed step over the computed program, non-oracle leaves.**
    The firing data of a non-oracle leaf builds the covered PC step through
    `pcSchritt_blatt_progAus_ohne_axiomCall` (read-only reuse, same file --
    `hleaf`/`hax`/`hkein_nimmt`/`hpc`/`hΛa`/`hcs` feed exactly that lifter and
    its `PCReach` leg), while the SAME `neu` feeds the witnessed chain
    extension (`kette_mit_zeugen_schritt`, above) with the frame wiring
    (`hW`/`hG`), the prefix witness duty (`hwit_old`), and the step witness
    (`hneu_wit`). The conclusion carries the extended chain, its member, the
    unconditional table link, the guard, and the covered run. Every premise
    is load-bearing. -/
theorem kette_mit_zeugen
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (fcode : Faden → D.Fn) (tabs : List D.Tab) (globs : List D.Glob)
    (sp : Speicher D) (M : GenMaschine D) (pc : PCStand) (f : Faden)
    (h : PCReach P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp) M pc)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hleaf : s.istBlatt = true)
    (hax : match s with | .axiomCall _ _ _ _ _ _ _ => False | _ => True)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ M.spuren f)
    (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
    (Λa : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
    (hpc : (Extraktion.progAus P fcode tabs globs f)[pc f]? = some (PCAtom.leaf Λa cs))
    (hΛa : Λa = Λ)
    (hcs : cs = Extraktion.stmtTraeger tabs globs s ++ Extraktion.stmtOrte s)
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (hJw : J.welten = M.welten)
    (hmem : f ∈ J.faeden)
    (hW : ∀ t, V.schreibt t = true → D.schreibt (J.code f) t = true)
    (hG : ∀ g, V.gschreibt g = true → D.gschreibt (J.code f) g = true)
    (hsingle : ∀ st ∈ M.lauf, st.faden = f)
    (t₀ : D.Tab) (L : D.Lock)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (hCov : ∀ (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, Sum.inl t₀ ∈ D.traeger i)
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
    pcSchritt_blatt_progAus_ohne_axiomCall O passes P fcode tabs globs M pc f V l Γ Λ Λ'
      s ρ hleaf hax hΛ σ' neu hstep hneu hkein_nimmt Λa cs hpc hΛa hcs
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
    kette_mit_zeugen_schritt P O passes hO sp Nb M _ f hReach hReach' V l Γ Λ Λ' s ρ
      hleaf hΛ σ' neu hstep rfl rfl J hJw hmem hW hG hsingle t₀ L hGuardT hCov hwit_old hneu_wit
  exact ⟨J', _, _, hJ'w, hJ'l, hmem', hLink', hGuard', hPC'⟩

#print axioms Gabbro.Grammatik.kette_mit_zeugen


end Gabbro.Grammatik
