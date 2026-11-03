module
public import Grammatik.Logik.Fortschritt.Lebendigkeit.T1.Teil1
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

section MaschineG

variable {P : Programm D} {O : Orakel D} {passes : Nat}

set_option maxHeartbeats 4000000 in
/-- **What a step does to the held set, with the `locks` head named**: the
    actor stands at a `locks` head (then `sperre_schritt` says what happens),
    or its held set is unchanged, or one lock is released. The twin of
    `offen_schrittG` (ZielOrt.lean), whose take case does not name the head. -/
theorem schritt_sperre_art (hO : GutO O) {M M' : RufMaschineG D} {f : Faden}
    (hs : RufSchrittG P O passes M f M') :
    (∃ L, AnSperre M f L) ∨ offen (M'.faeden f).spur = offen (M.faeden f).spur ∨
    (∃ Ls : List D.Lock,
      offen (M'.faeden f).spur = Ls.foldl (fun held L => held.erase L) (offen (M.faeden f).spur)) := by
  cases hs with
  | g1 hs =>
    cases hs with
    | blatt l Γ Λ Λ' s rest ρ hleaf _ hΛ σ' ρ' _ hstep =>
        simp only [rufUpdateG_self]
        exact Or.inr (Or.inl (blatt_offen hO s hleaf _ ρ hΛ σ' ρ' hstep))
    | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf _ hΛ σ' ρ' _ hstep =>
        simp only [rufUpdateG_self]
        exact Or.inr (Or.inl (blatt_offen hO s hleaf _ ρ hΛ σ' ρ' hstep))
    | endeBindAxiom l Γ Λ τ a args he hw hg hd hgd rest ρ _ σ₁ hs₁ σ₂ v hax =>
        simp only [rufUpdateG_self]
        refine Or.inr (Or.inl ?_)
        rw [axiom_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _
    | _ =>
        subst_vars
        simp only [rufUpdateG_self]
        first
          | exact Or.inr (Or.inl trivial)
          | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inl (lese_offen _ _ _))
  | g2 hs =>
    cases hs with
    | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead _ _ _ =>
        exact Or.inl ⟨L, l, Γ, Λ, Λ'', ρ, hr, body, rest, k, hhead⟩
    | freiGib l Γ Λ L k ρ hhead =>
        simp only [rufUpdateG_self]
        exact Or.inr (Or.inr ⟨[L], rfl⟩)
    | _ =>
        subst_vars
        simp only [rufUpdateG_self]
        first
          | exact Or.inr (Or.inl trivial)
          | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inl (lese_offen _ _ _))
  | g3 hs =>
    cases hs with
    | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hl _ σ' ρ' _ hstep _ _ σ₁ hs₁ =>
        simp only [rufUpdateG_self]
        refine Or.inr (Or.inl ?_)
        rw [hs₁, lese_offen, leave_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
    | dannNextTrav l Γ Λ t inv body is k rest i ρ hl _ σ' ρ' _ hstep =>
        simp only [rufUpdateG_self]
        refine Or.inr (Or.inl ?_)
        rw [next_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
    | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hl _ σ' ρ' _ hstep =>
        simp only [rufUpdateG_self]
        refine Or.inr (Or.inl ?_)
        rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
    | dannNextWieder l Γ Λ n bis body ueber k rest ρ hl _ σ' ρ' _ hstep =>
        simp only [rufUpdateG_self]
        refine Or.inr (Or.inl ?_)
        rw [next_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
    | dannLeaveEwig l Γ Λ a n inv body k rest ρ hl _ σ' ρ' _ hstep =>
        simp only [rufUpdateG_self]
        refine Or.inr (Or.inl ?_)
        rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
    | _ =>
        subst_vars
        simp only [rufUpdateG_self]
        first
          | exact Or.inr (Or.inl trivial)
          | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inl (lese_offen _ _ _))
  | g4 hs =>
    cases hs with
    | peelFreiLeave l Γ Λ L rest k ρ hl hhead =>
        simp only [rufUpdateG_self]
        exact Or.inr (Or.inr ⟨[L], rfl⟩)
    | peelFreiNext l Γ Λ L rest k ρ hl hhead =>
        simp only [rufUpdateG_self]
        exact Or.inr (Or.inr ⟨[L], rfl⟩)
    | dannNextEwig l Γ Λ a n inv body k rest ρ hl _ σ' ρ' _ hstep =>
        simp only [rufUpdateG_self]
        refine Or.inr (Or.inl ?_)
        rw [next_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
    | _ =>
        subst_vars
        simp only [rufUpdateG_self]
        first
          | exact Or.inr (Or.inl trivial)
          | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inl (lese_offen _ _ _))
  | g5 hs =>
    cases hs with
    | dannExchange _ _ l Γ Λ Λ' g neuE hw hL rest k ρ _ σ₁ hs₁ σ₂ hs₂ =>
        simp only [rufUpdateG_self]
        refine Or.inr (Or.inl ?_)
        rw [hs₂, hs₁]
        exact lese_offen _ _ _
    | dannBindAxiom _ _ l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ _ σ₁ hs₁ σ₂ v hax =>
        simp only [rufUpdateG_self]
        refine Or.inr (Or.inl ?_)
        rw [axiom_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _
    | dannBindAxiomElseOk _ _ l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ _ σ₁ hs₁ σ₂ v hax =>
        simp only [rufUpdateG_self]
        refine Or.inr (Or.inl ?_)
        rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _
    | dannBindAxiomElseGrund _ _ l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ _ σ₁ hs₁ σ₂ r hax =>
        simp only [rufUpdateG_self]
        refine Or.inr (Or.inl ?_)
        rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _
    | _ =>
        subst_vars
        simp only [rufUpdateG_self]
        first
          | exact Or.inr (Or.inl trivial)
          | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inl (lese_offen _ _ _))
  | g6 hs =>
    cases hs with
    | endeBindAxiomElseOk l Γ Λ τ a args he hr hw hg hd hgd err rest ρ _ σ₁ hs₁ σ₂ v hax =>
        simp only [rufUpdateG_self]
        refine Or.inr (Or.inl ?_)
        rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _
    | endeBindAxiomElseGrund l Γ Λ τ a args he hr hw hg hd hgd err rest ρ _ σ₁ hs₁ σ₂ r hax =>
        simp only [rufUpdateG_self]
        refine Or.inr (Or.inl ?_)
        rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _
  | g7 hs =>
    cases hs with
    | rueckScopedWert ρ r e R hhead hret hscope hΛ σ₁ hs₁ neu hneu =>
      simp only [rufUpdateG_self]
      subst σ₁
      exact Or.inr (Or.inl (lese_offen _ _ _))
    | rueckScopedGrund => exact Or.inr (Or.inl (by simp only [rufUpdateG_self]))
    | rueckFreigabe ρ a L remaining hhead =>
      simp only [rufUpdateG_self]
      exact Or.inr (Or.inr ⟨[L], rfl⟩)
    | rueckFreigabeLetzte ρ a L hhead z hantwort =>
      simp only [rufUpdateG_self, rufAntwortG_spur hantwort]
      exact Or.inr (Or.inr ⟨[L], rfl⟩)
    | rueckScopedWertDirekt ρ r e R hhead hret hscope hΛ σ₁ hs₁ neu hneu hempty z ha =>
      simp only [rufUpdateG_self, rufAntwortG_spur ha]
      subst σ₁
      exact Or.inr (Or.inl (lese_offen _ _ _))
    | rueckScopedGrundDirekt ρ r grund R hhead hret hscope hΛ hempty z ha =>
      simp only [rufUpdateG_self, rufAntwortG_spur ha]
      exact Or.inr (Or.inl rfl)
    | _ =>
        subst_vars
        simp only [rufUpdateG_self]
        first
          | exact Or.inr (Or.inl trivial)
          | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inl (lese_offen _ _ _))

/-- **A lock enters a held set only at a `locks` head of that lock.** -/
theorem nimmt_an_sperre (hO : GutO O) {M M' : RufMaschineG D} {f : Faden} {L : D.Lock}
    (hs : RufSchrittG P O passes M f M') (h0 : L ∉ offen (M.faeden f).spur)
    (h1 : L ∈ offen (M'.faeden f).spur) : AnSperre M f L := by
  rcases schritt_sperre_art hO hs with ⟨L', hA⟩ | e | ⟨L', e⟩
  · have e := (sperre_schritt hA hs).2
    rw [e] at h1
    simp only [offen, List.mem_cons] at h1
    rcases h1 with rfl | h1
    · exact hA
    · exact absurd h1 h0
  · rw [e] at h1; exact absurd h1 h0
  · rw [e] at h1; exact absurd (mem_of_mem_eraseScopes _ _ h1) h0

/-- A `locks L` head read off the residue is a `locks L` head. -/
theorem anSperre_of_kopf {M : RufMaschineG D} {t : Faden} {L : D.Lock}
    (h : (M.faeden t).kopf.rest.2.2.2.2.kopfSperre = some L) : AnSperre M t L := by
  unfold AnSperre
  generalize (M.faeden t).kopf.rest = x at h ⊢
  obtain ⟨l, Γ, Λ, ρ, r⟩ := x
  cases r with
  | dann b k =>
      cases b with
      | cons s rest =>
          cases s with
          | locks L' hr body =>
              simp only [GRest.kopfSperre, Block.sperreVon, Stmt.sperreVon,
                Option.some.injEq] at h
              subst h
              exact ⟨l, Γ, Λ, _, ρ, hr, body, rest, k, rfl⟩
          | _ => simp only [GRest.kopfSperre, Block.sperreVon, Stmt.sperreVon, reduceCtorEq] at h
      | _ => simp only [GRest.kopfSperre, Block.sperreVon, reduceCtorEq] at h
  | _ => simp only [GRest.kopfSperre, reduceCtorEq] at h

/-- A thread at `locks L` while another thread holds `L` cannot step. -/
theorem nicht_bereit_an_sperre {M : RufMaschineG D} {t u : Faden} {L : D.Lock}
    (hA : AnSperre M t L) (hu : u ≠ t) (hL : L ∈ offen (M.faeden u).spur) :
    ¬ ∃ M', RufSchrittG P O passes M t M' :=
  fun ⟨_, hs⟩ => (sperre_schritt hA hs).1 u hu hL

/-- The residue is a plain `return` end block. -/
def GRest.istEndeRet {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Bool
  | .ende (.ret ..) => true
  | _ => false

end MaschineG
end Gabbro.Grammatik
