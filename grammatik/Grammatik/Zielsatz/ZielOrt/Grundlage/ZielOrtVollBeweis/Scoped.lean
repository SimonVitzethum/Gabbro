module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- The source selector also supplies the footprint of the evaluated return. -/
theorem scopedWert_orteV {P : Programm D} {S : List (D.Tab ⊕ D.Glob)}
    {r : GRest D V l Γ Λ} {e : ErgExpr D Γ Λ V.erg} {R : RueckRessourcen D V Λ}
    (hok : r.okV P S) (h : r.scopedWert = some (e, R)) : e.orte ⊆ S := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedWert_faelle h <;> subst r
  · exact hok.2
  · exact fun _ hx => hok.2 (List.mem_append_left _ hx)
  · exact fun _ hx => hok.2.1 (List.mem_append_left _ hx)

/-- Cleanup preserves memory, so the return prediction agrees with the read world. -/
theorem semV_scopedWert (O : Orakel D) (passes : Nat)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (r : GRest D V l Γ Λ) (e : ErgExpr D Γ Λ V.erg) (R : RueckRessourcen D V Λ)
    (h : r.scopedWert = some (e, R)) (σ : World D) (ρ : Env D Γ) :
    (semV O passes calls r σ ρ).gleich
      (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) := by
  have hg : SG (R.scopes.foldl World.gibt (σ.lese Λ e.orte)) (σ.lese Λ e.orte) :=
    World.gibt_foldl_speicher _ _
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedWert_faelle h <;> subst r
  · exact ⟨hg, rfl⟩
  · rw [semV_ende_cons]
    exact ⟨hg, rfl⟩
  · rw [semV_dann_cons]
    simp only [execStmt]
    exact ZErg.gleich_trans (weiterZ_zurueck O passes calls (.dann rest k) _ _) ⟨hg, rfl⟩

/-- Reasons have no normal-return prediction in the contract replay. -/
theorem semV_scopedGrund (O : Orakel D) (passes : Nat)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (r : GRest D V l Γ Λ) (grund : Fin V.gruende) (R : RueckRessourcen D V Λ)
    (h : r.scopedGrund = some (grund, R)) (σ : World D) (ρ : Env D Γ) :
    semV O passes calls r σ ρ = .sonst := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedGrund_faelle h <;> subst r
  · rfl
  · rw [semV_ende_cons]; rfl
  · rw [semV_dann_cons]
    simp only [execStmt]
    exact weiterZ_grund O passes calls (.dann rest k) _ _

/-- A successful answer selects exactly the continuation described by `FortV`. -/
theorem fortV_antwortRestG {passes : Nat} {F : RufRahmenG D} {g : D.Fn}
    {a : ErgVal D (vertragVon D g).erg ⊕ Fin (vertragVon D g).gruende}
    {c : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D (vertragVon D F.f) l Γ Λ}
    (ha : antwortRestG g a F.rest = some c)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O : Orakel D)
    (σ : World D) (X : ZErg (vertragVon D F.f))
    (h : FortV passes F g X R O (match a with | .inl v => .ok σ v | .inr r => .why σ r)) :
    X.folgt (semV O passes R c.2.2.2.2 σ c.2.2.2.1) := by
  obtain ⟨f, rho, s0, l, Γ, Λ, ρ, r⟩ := F
  cases a with
  | inl v =>
      cases r with
      | wartet rest k =>
          simp only [antwortRestG] at ha
          split at ha
          · rename_i he
            simp only [Option.some.injEq] at ha
            subst c
            exact h.2 _ _ _ _ _ rest k ρ (Or.inl rfl) he
          · cases ha
      | wartetSonst n err rest k =>
          simp only [antwortRestG] at ha
          split at ha
          · rename_i he
            simp only [Option.some.injEq] at ha
            subst c
            exact h.2 _ _ _ _ _ rest k ρ (Or.inr ⟨n, err, rfl⟩) he
          · cases ha
      | _ =>
          simp only [antwortRestG, Option.some.injEq] at ha
          subst c
          exact h.1 rfl
  | inr grund =>
      cases r with
      | wartetSonst n err rest k =>
          simp only [antwortRestG] at ha
          split at ha
          · rename_i hn
            simp only [Option.some.injEq] at ha
            subst c
            exact h _ _ _ _ _ _ err rest k ρ rfl hn
          · cases ha
      | _ => cases ha

/-- Answer delivery preserves the caller's fragment, including binding and reason continuations. -/
theorem antwortRestG_okV {P : Programm D} {V : Vertrag D} {S : List (D.Tab ⊕ D.Glob)}
    (g : D.Fn) (a : ErgVal D (vertragVon D g).erg ⊕ Fin (vertragVon D g).gruende)
    (c c' : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ)
    (hok : c.2.2.2.2.okV P S) (ha : antwortRestG g a c = some c') :
    c'.2.2.2.2.okV P S := by
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
            exact okV_alsBlock err (.schrumpf k) rest.held_iff hok.1 hok.2.1 hok.2.2.2.2
          · cases ha
      | _ => cases ha

end Gabbro.Grammatik
