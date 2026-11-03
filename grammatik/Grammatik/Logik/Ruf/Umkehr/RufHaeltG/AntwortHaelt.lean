module

public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.ScopeMarkers

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

private theorem antwortRestG_kette {V : Vertrag D} {A : List D.Lock} (g : D.Fn)
    (a : ErgVal D (vertragVon D g).erg ⊕ Fin (vertragVon D g).gruende)
    (c c' : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ)
    (hc : c.2.2.2.2.kette A) (ha : antwortRestG g a c = some c') :
    c'.2.2.2.2.kette A := by
  obtain ⟨l, Γ, Λ, ρ, r⟩ := c
  cases a with
  | inl v =>
      cases r with
      | wartet b k =>
          simp only [antwortRestG] at ha
          split at ha
          · simp only [Option.some.injEq] at ha
            subst c'
            exact ⟨hc.1, GRest.kette_top _ hc.2, hc.2⟩
          · cases ha
      | wartetSonst n err b k =>
          simp only [antwortRestG] at ha
          split at ha
          · simp only [Option.some.injEq] at ha
            subst c'
            exact ⟨hc.1, GRest.kette_top _ hc.2, hc.2⟩
          · cases ha
      | _ =>
          simp only [antwortRestG, Option.some.injEq] at ha
          subst c'
          exact hc
  | inr grund =>
      cases r with
      | wartetSonst n err b k =>
          simp only [antwortRestG] at ha
          split at ha
          · simp only [Option.some.injEq] at ha
            subst c'
            exact kette_abbruch err.alsBlock.2 hc.1 (.schrumpf k)
              ⟨GRest.kette_top _ hc.2, hc.2⟩
              (fun L hL => (Block.held_iff b L).mp hL)
          · cases ha
      | _ => simp only [antwortRestG, reduceCtorEq] at ha

private theorem antwortRestG_freis {V : Vertrag D} (g : D.Fn)
    (a : ErgVal D (vertragVon D g).erg ⊕ Fin (vertragVon D g).gruende)
    (c c' : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ)
    (ha : antwortRestG g a c = some c') : c'.2.2.2.2.freis = c.2.2.2.2.freis := by
  obtain ⟨l, Γ, Λ, ρ, r⟩ := c
  cases a <;> cases r <;> simp_all [antwortRestG, GRest.freis]
  all_goals split at ha <;> simp_all [GRest.freis]

/-- Delivering an evaluated answer preserves static holdings and caller
    protection whenever the held set of the supplied world is unchanged.
    A last release establishes this premise in an intermediate proof state;
    that proof state is not an additional machine step. -/
theorem haeltInvG_rufAntwort {z z' : RufFadenG D} {vor σ : World D}
    {a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende}
    (h : HaeltInvG z) (ho : offen σ.spur = offen z.spur)
    (ha : rufAntwortG z vor σ a = some z') : HaeltInvG z' := by
  cases hst : z.stapel with
  | nil =>
      simp only [rufAntwortG, hst, Option.some.injEq] at ha
      subst z'
      have hnew := haeltInvG_kopf (r' := GRest.zurueckgekehrt (l := false)
        (Γ := D.params z.kopf.f) ⟨a, vor⟩) (ρ' := z.kopf.rho) (spur' := σ.spur) h
        (fun K hK _ => by rw [ho]; exact hK)
        (fun _ hm => (List.not_mem_nil hm).elim)
        (fun L hL => (held_ende _ L).mpr hL)
        (fun L hL => by
          rw [ho]
          exact h.signatur _ List.mem_cons_self L ((held_ende _ L).mp hL))
      simpa only [hst] using hnew
  | cons c st =>
      obtain ⟨r, hr⟩ : ∃ r, antwortRestG z.kopf.f a c.rest = some r := by
        cases hr : antwortRestG z.kopf.f a c.rest with
        | none => simp [rufAntwortG, hst, hr] at ha
        | some r => exact ⟨r, rfl⟩
      simp [rufAntwortG, hst, hr] at ha
      subst z'
      have hc := h.2.1 c (by rw [hst]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      apply haeltInvG_pop h hst _ _ _ rfl
      · intro L hL
        change Res.held L ∈ c.rest.2.2.1
        rw [← antwortRestG_ressourcen _ _ _ _ hr]
        exact hL
      · intro L hL
        change L ∈ c.rest.2.2.2.2.freis
        rw [← antwortRestG_freis _ _ _ _ hr]
        exact hL
      · exact antwortRestG_kette _ _ _ _ hc hr
      · exact ho

end Gabbro.Grammatik
