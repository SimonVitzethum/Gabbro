module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtSem

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- All three scoped source heads evaluate before the canonical release fold. -/
theorem semZ_scopedWert (O : Orakel D) (passes : Nat)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (r : GRest D V l Γ Λ) (e : ErgExpr D Γ Λ V.erg)
    (R : RueckRessourcen D V Λ) (h : r.scopedWert = some (e, R))
    (σ : World D) (ρ : Env D Γ) :
    semZ O passes calls r σ ρ =
      .zurueck (R.scopes.foldl World.gibt (σ.lese Λ e.orte))
        (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedWert_faelle h <;>
    subst r <;> rfl

/-- The scoped return reads only carriers included by the source footprint. -/
theorem scopedWert_orteZ {P : Programm D} {S : List (D.Tab ⊕ D.Glob)}
    {r : GRest D V l Γ Λ} {e : ErgExpr D Γ Λ V.erg}
    {R : RueckRessourcen D V Λ} (hok : r.okZ P S)
    (h : r.scopedWert = some (e, R)) : e.orte ⊆ S := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedWert_faelle h <;> subst r
  · exact hok.2
  · exact fun _ hx => hok.2 (List.mem_append_left _ hx)
  · exact fun _ hx => hok.2.1 (List.mem_append_left _ hx)

/-- A reason source head is excluded by the existing K fragment, in every position. -/
theorem scopedGrund_nicht_okZ {P : Programm D} {S : List (D.Tab ⊕ D.Glob)}
    {r : GRest D V l Γ Λ} {grund : Fin V.gruende} {R : RueckRessourcen D V Λ}
    (hok : r.okZ P S) (h : r.scopedGrund = some (grund, R)) : False := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedGrund_faelle h <;> subst r <;>
    simp only [GRest.okZ, Endblock.kOk, Block.kOk, Stmt.kOk,
      Bool.false_and, Bool.false_eq_true, false_and] at hok

/-- Value delivery preserves the K fragment for both plain and binding calls. -/
theorem antwortRestG_okZ {P : Programm D} {S : List (D.Tab ⊕ D.Glob)}
    (g : D.Fn) (v : ErgVal D (D.erg g))
    (c c' : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ)
    (hok : c.2.2.2.2.okZ P S) (ha : antwortRestG g (.inl v) c = some c') :
    c'.2.2.2.2.okZ P S := by
  obtain ⟨l, Γ, Λ, ρ, r⟩ := c
  cases r with
  | wartet rest k =>
      simp only [antwortRestG] at ha
      split at ha
      · simp only [Option.some.injEq] at ha
        subst c'
        exact hok
      · cases ha
  | wartetSonst => exact hok.elim
  | _ =>
      simp only [antwortRestG, Option.some.injEq] at ha
      subst c'
      exact hok

/-- A suspended K caller cannot accept the reason channel. -/
theorem antwortRestG_grund_nicht_okZ {P : Programm D} {S : List (D.Tab ⊕ D.Glob)}
    (g : D.Fn) (grund : Fin (vertragVon D g).gruende)
    (c c' : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ)
    (hok : c.2.2.2.2.okZ P S) (ha : antwortRestG g (.inr grund) c = some c') : False := by
  obtain ⟨l, Γ, Λ, ρ, r⟩ := c
  cases r with
  | wartetSonst => exact hok
  | _ => cases ha

/-- The source witness reads a guarded slot before releasing its lexical lock. -/
theorem semZ_scopedWert_zeuge :
    semZ adO 0 keinRuf
      (.ende (l := false) (.retScoped (.val umkehrScopedExpr) umkehrScopedR))
      umkehrScopedVor Env.nil =
      .zurueck ((umkehrScopedVor.lese adΛL umkehrScopedExpr.orte).gibt ())
        (evalErg (umkehrScopedVor.lese adΛL umkehrScopedExpr.orte) (.val umkehrScopedExpr)
          (umkehrScopedVor.lese adΛL umkehrScopedExpr.orte) Env.nil) := by
  exact semZ_scopedWert adO 0 keinRuf
    (.ende (l := false) (.retScoped (.val umkehrScopedExpr) umkehrScopedR))
    (.val umkehrScopedExpr) umkehrScopedR rfl umkehrScopedVor Env.nil

end Gabbro.Grammatik
