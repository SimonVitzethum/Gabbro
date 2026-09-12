import Grammatik.Maschine

open Gabbro.Grammatik

/-! ## Wrapper folding (pattern a): conclusion = premise under another name

`hsingle_aus_einfaedig` concludes `Gesittet M.lauf` from premises that are fed
positionally, whole, into `gen_gesittet`: `P O passes hO sp M h code hEin
hungeteilt`. The proof is a single application; nothing is derived that the
premise set does not already hand to `gen_gesittet`. Its content over
`gen_gesittet` is exactly the docstring sentence "each is passed whole to
`gen_gesittet`" -- i.e. the theorem is a renaming of one `gen_gesittet`
instance.

`blatt_rahmen_vertrag` / `blatt_rahmen_schritt`: the first is the `.1`
projection of one `stmt_gut` application; the second is `.weiter` applied to
the first. Both conclusions are a named premise-instance projection.
-/

-- Demonstration A: hsingle_aus_einfaedig is one application of gen_gesittet.
-- Any caller holding the hsingle premises already holds a gen_gesittet call.
example (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (M : GenMaschine D)
    (h : GenErreichbar P O passes (GenStart sp) M)
    (code : D.Marke → Nat) (hEin : Marken.Einfaedig (laufProj code M.lauf))
    (hungeteilt : ∀ (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob)
      (ei ej : Ereignis D),
      M.lauf[i]? = some (Schritt.mk f ei) → M.lauf[j]? = some (Schritt.mk g ej) →
      ei.traeger = some o → ej.traeger = some o →
      (match o with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) → f = g) :
    Gesittet M.lauf :=
  -- No case analysis, no computation: the conclusion IS gen_gesittet applied.
  gen_gesittet P O passes hO sp M h code hEin hungeteilt

-- Demonstration B: blatt_rahmen_vertrag is the `.1` projection of stmt_gut.
example (O : Orakel D) (passes : Nat) (hO : GutO O)
    (M : GenMaschine D) (f : Faden)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (σ' : World D)
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ') :
    Rahmen V.schreibt V.gschreibt (M.weltVon f) σ' :=
  -- The frame half was already proved in Satz.lean; this names its instance.
  ((stmt_gut O passes keinRuf keinRuf_gut hO s (M.weltVon f) ρ hΛ) σ' hstep).1

-- Demonstration C: blatt_rahmen_schritt is `.weiter` on demonstration B.
example (O : Orakel D) (passes : Nat) (hO : GutO O)
    (M : GenMaschine D) (f : Faden)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (σ' : World D)
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
    (code : Faden → D.Fn)
    (hW : ∀ t, V.schreibt t = true → D.schreibt (code f) t = true)
    (hG : ∀ g, V.gschreibt g = true → D.gschreibt (code f) g = true) :
    Rahmen (D.schreibt (code f)) (D.gschreibt (code f)) (M.weltVon f) σ' :=
  -- Widening is the only added content; the frame itself is demonstration B.
  (blatt_rahmen_vertrag O passes hO M f V l Γ Λ Λ' s ρ hΛ σ' hstep).weiter hW hG

#print axioms hsingle_aus_einfaedig
#print axioms blatt_rahmen_vertrag
#print axioms blatt_rahmen_schritt

/-!
CUTS:
- "Wrapper" here means single-application folding, not falsehood: the theorems
  are true and their docstrings describe the folding honestly. The audit point
  is progress-accounting (pattern a): each conclusion is available at its use
  site by the same one-line application, so counting them as separate results
  overstates what §19/§18 add.
- Whether `gen_gesittet`'s own premises discharge for ordinary programs (W4/W5
  side conditions) is out of scope for this file; see the report.
-/
