module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetSem
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis.Scoped

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {P : Programm D}

/-- The widened fragment contains every carrier of a scoped return expression. -/
theorem scopedWert_orteG {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {S : List (D.Tab ⊕ D.Glob)} {r : GRest D V l Γ Λ}
    {e : ErgExpr D Γ Λ V.erg} {R : RueckRessourcen D V Λ}
    (hok : r.okG P S) (h : r.scopedWert = some (e, R)) : e.orte ⊆ S := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedWert_faelle h <;> subst r
  · exact hok.2
  · exact fun _ hx => hok.2 (List.mem_append_left _ hx)
  · exact fun _ hx => hok.2.1 (List.mem_append_left _ hx)

/-- Answer delivery preserves the caller's fragment, including binding and reason continuations. -/
theorem antwortRestG_okG {V : Vertrag D} {S : List (D.Tab ⊕ D.Glob)}
    (g : D.Fn) (a : ErgVal D (vertragVon D g).erg ⊕ Fin (vertragVon D g).gruende)
    (c c' : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ)
    (hok : c.2.2.2.2.okG P S) (ha : antwortRestG g a c = some c') :
    c'.2.2.2.2.okG P S := by
  obtain ⟨l, Γ, Λ, ρ, r⟩ := c
  cases a with
  | inl v =>
      cases r with
      | wartet rest k =>
          simp only [antwortRestG] at ha
          split at ha
          · simp only [Option.some.injEq] at ha
            subst c'
            exact hok
          · cases ha
      | wartetSonst n err rest k =>
          simp only [antwortRestG] at ha
          split at ha
          · simp only [Option.some.injEq] at ha
            subst c'
            exact ⟨hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2⟩
          · cases ha
      | _ =>
          simp only [antwortRestG, Option.some.injEq] at ha
          subst c'
          exact hok
  | inr grund =>
      cases r with
      | wartetSonst n err rest k =>
          simp only [antwortRestG] at ha
          split at ha
          · simp only [Option.some.injEq] at ha
            subst c'
            exact okG_alsBlock err (.schrumpf k) rest.held_iff hok.1 hok.2.1 hok.2.2.2.2
          · cases ha
      | _ => cases ha

end Gabbro.Grammatik
