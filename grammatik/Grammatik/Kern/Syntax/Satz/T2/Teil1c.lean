/- Part 1c of `Satz/T2/Teil1` (C11 split; pure move): the spare-and-rank
   release (`GutRetV`), its compositions and leaves, and `locks` with a
   releasing body. -/
module

public import Grammatik.Kern.Syntax.Satz.T1
public import Grammatik.Kern.Syntax.Satz.T2.Teil1b

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Release-aware frame+trace that spares the residual and respects the floor**:
    the release list avoids every required lock (`spare`) and every released lock
    ranks at or above the floor (`rank`). Callers transport their holdings through
    such a release: required locks survive by spare, extras by rank + `RufPasst.hx`. -/
def GutRetV (W : D.Tab → Bool) (G : D.Glob → Bool) (haelt : List D.Lock)
    (boden : Option Int) (σ σ' : World D) : Prop :=
  Rahmen W G σ σ' ∧ ∃ Ls : List D.Lock,
    σ'.haelt = Ls.foldl (fun h L => h.erase L) σ.haelt ∧
    (∀ L ∈ Ls, L ∉ haelt) ∧ (∀ L ∈ Ls, ∀ c, boden = some c → c ≤ D.rang L) ∧
    (∀ e ∈ σ'.spur, e ∈ σ.spur ∨ e.gut) ∧ (Konsistent σ.spur → Konsistent σ'.spur)

theorem GutRetV.toRet {W G} {haelt : List D.Lock} {boden : Option Int} {a b : World D}
    (h : GutRetV W G haelt boden a b) : GutRet W G a b := by
  obtain ⟨hr, Ls, heq, _, _, hgood, hkons⟩ := h
  exact ⟨hr, ⟨Ls, heq⟩, hgood, hkons⟩

theorem GutRetV.toBravRet {W G} {haelt : List D.Lock} {boden : Option Int} {a b : World D}
    (h : GutRetV W G haelt boden a b) : BravRet a b := by
  obtain ⟨_, Ls, heq, _, _, hgood, hkons⟩ := h
  exact ⟨⟨Ls, heq⟩, hgood, hkons⟩

/-- `Gut` is `GutRetV` with no release. -/
theorem Gut.toRetV {W G} {haelt : List D.Lock} {boden : Option Int} {a b : World D}
    (h : Gut W G a b) : GutRetV W G haelt boden a b := by
  obtain ⟨hr, heq, hgood, hkons⟩ := h
  refine ⟨hr, [], ?_, ?_, ?_, ?_, ?_⟩
  · simpa using heq
  · intro L hL; simp only [List.not_mem_nil] at hL
  · intro L hL; simp only [List.not_mem_nil] at hL
  · exact hgood
  · exact hkons

theorem Gut.transRetV {W G} {haelt : List D.Lock} {boden : Option Int} {a b c : World D}
    (h1 : Gut W G a b) (h2 : GutRetV W G haelt boden b c) :
    GutRetV W G haelt boden a c := by
  obtain ⟨hr2, Ls, heq2, hsp2, hrk2, hgood2, hkons2⟩ := h2
  obtain ⟨hr1, heq1, hgood1, hkons1⟩ := h1
  refine ⟨hr1.trans hr2, ⟨Ls, ?_, hsp2, hrk2, ?_, ?_⟩⟩
  · rw [heq2, heq1]
  · intro e he
    rcases hgood2 e he with h | h
    · rcases hgood1 e h with h' | h'
      · exact .inl h'
      · exact .inr h'
    · exact .inr h
  · intro k
    exact hkons2 (hkons1 k)

theorem GutRetV.transGut {W G} {haelt : List D.Lock} {boden : Option Int} {a b c : World D}
    (h1 : GutRetV W G haelt boden a b) (h2 : Gut W G b c) :
    GutRetV W G haelt boden a c := by
  obtain ⟨hr1, Ls, heq1, hsp1, hrk1, hgood1, hkons1⟩ := h1
  obtain ⟨hr2, heq2, hgood2, hkons2⟩ := h2
  refine ⟨hr1.trans hr2, ⟨Ls, ?_, hsp1, hrk1, ?_, ?_⟩⟩
  · rw [heq2, heq1]
  · intro e he
    rcases hgood1 e he with h | h
    · rcases hgood2 e h with h' | h'
      · exact .inl h'
      · exact .inr h'
    · exact .inr h
  · intro k
    exact hkons1 (hkons2 k)

theorem GutRetV.transRetV {W G} {haelt : List D.Lock} {boden : Option Int} {a b c : World D}
    (h1 : GutRetV W G haelt boden a b) (h2 : GutRetV W G haelt boden b c) :
    GutRetV W G haelt boden a c := by
  obtain ⟨hr1, Ls1, heq1, hsp1, hrk1, hgood1, hkons1⟩ := h1
  obtain ⟨hr2, Ls2, heq2, hsp2, hrk2, hgood2, hkons2⟩ := h2
  refine ⟨hr1.trans hr2, ⟨Ls1 ++ Ls2, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [heq2, heq1, List.foldl_append]
  · intro L hL
    simp only [List.mem_append] at hL
    rcases hL with hL | hL
    · exact hsp1 L hL
    · exact hsp2 L hL
  · intro L hL c hc
    simp only [List.mem_append] at hL
    rcases hL with hL | hL
    · exact hrk1 L hL c hc
    · exact hrk2 L hL c hc
  · intro e he
    rcases hgood2 e he with h | h
    · rcases hgood1 e h with h' | h'
      · exact .inl h'
      · exact .inr h'
    · exact .inr h
  · intro k
    exact hkons2 (hkons1 k)

/-- A read followed by scope releases is a releasing step with exactly those scopes;
    spare and rank come from the static scope check. -/
theorem gutRetV_retScoped {W G} {haelt : List D.Lock} {boden : Option Int}
    {σ σ1 : World D} (Ls : List D.Lock) (hl : Gut W G σ σ1)
    (hsp : ∀ L ∈ Ls, L ∉ haelt) (hrk : ∀ L ∈ Ls, ∀ c, boden = some c → c ≤ D.rang L) :
    GutRetV W G haelt boden σ (Ls.foldl World.gibt σ1) := by
  have hR := gutRet_retScoped (W := W) (G := G) (σ := σ) (σ1 := σ1) Ls hl
  obtain ⟨hr, ⟨_, heq⟩, hgood, hkons⟩ := hR
  exact ⟨hr, Ls, heq, hsp, hrk, hgood, hkons⟩

/-- A scope release alone is a releasing step with exactly those scopes. -/
theorem gutRetV_retWhyScoped {W G} {haelt : List D.Lock} {boden : Option Int}
    (σ : World D) (Ls : List D.Lock)
    (hsp : ∀ L ∈ Ls, L ∉ haelt) (hrk : ∀ L ∈ Ls, ∀ c, boden = some c → c ≤ D.rang L) :
    GutRetV W G haelt boden σ (Ls.foldl World.gibt σ) := by
  have hR := gutRet_retWhyScoped (W := W) (G := G) (σ := σ) Ls
  obtain ⟨hr, ⟨_, heq⟩, hgood, hkons⟩ := hR
  exact ⟨hr, Ls, heq, hsp, hrk, hgood, hkons⟩

/-- Frame widening for releasing steps (spare and rank are frame-free). -/
theorem GutRetV.weiter {W W' : D.Tab → Bool} {G G' : D.Glob → Bool}
    {haelt : List D.Lock} {boden : Option Int} {a b : World D}
    (hW : ∀ t, W t = true → W' t = true) (hG : ∀ g, G g = true → G' g = true)
    (h : GutRetV W G haelt boden a b) : GutRetV W' G' haelt boden a b := by
  obtain ⟨hr, Ls, heq, hsp, hrk, hgood, hkons⟩ := h
  exact ⟨hr.weiter hW hG, Ls, heq, hsp, hrk, hgood, hkons⟩

/-- Consistency survives scope releases (`gibt` records no constraint). -/
theorem konsistent_gibt_foldl (Ls : List D.Lock) (σ : World D) :
    (Konsistent σ.spur → Konsistent (Ls.foldl World.gibt σ).spur) := by
  induction Ls generalizing σ with
  | nil => exact id
  | cons L Ls ih =>
      intro k
      simp only [List.foldl_cons]
      exact konsistent_cons trivial (ih _ (konsistent_cons trivial k))

/-- Frame survives scope releases (memory kept). -/
theorem rahmen_gibt_foldl {W G} (σ : World D) (Ls : List D.Lock) :
    Rahmen W G σ (Ls.foldl World.gibt σ) := by
  obtain ⟨hs, hg⟩ := World.gibt_foldl_speicher σ Ls
  exact rahmen_gleich (fun _ _ _ _ => by rw [hs]) (fun _ _ => by rw [hg])

/-- A read followed by scope releases is a releasing step with exactly those scopes. -/
theorem gutRet_retScoped {W G} {σ σ1 : World D} (Ls : List D.Lock)
    (hl : Gut W G σ σ1) : GutRet W G σ (Ls.foldl World.gibt σ1) := by
  refine ⟨hl.1.trans (rahmen_gibt_foldl σ1 Ls), ⟨Ls, ?_⟩, ?_, ?_⟩
  · rw [haelt_gibt_foldl, hl.2.1]
  · intro e he
    rw [World.gibt_foldl_spur] at he
    simp only [List.mem_append] at he
    rcases he with he | he
    · simp only [List.mem_map] at he
      obtain ⟨_, _, rfl⟩ := he
      exact .inr trivial
    · rcases hl.2.2.1 e he with h1 | h1
      · exact .inl h1
      · exact .inr h1
  · intro k
    exact konsistent_gibt_foldl Ls σ1 (hl.2.2.2 k)

/-- A scope release alone is a releasing step with exactly those scopes. -/
theorem gutRet_retWhyScoped {W G} (σ : World D) (Ls : List D.Lock) :
    GutRet W G σ (Ls.foldl World.gibt σ) := by
  refine ⟨rahmen_gibt_foldl σ Ls, ⟨Ls, ?_⟩, ?_, ?_⟩
  · rw [haelt_gibt_foldl]
  · intro e he
    rw [World.gibt_foldl_spur] at he
    simp only [List.mem_append] at he
    rcases he with he | he
    · simp only [List.mem_map] at he
      obtain ⟨_, _, rfl⟩ := he
      exact .inr trivial
    · exact .inl he
  · intro k
    exact konsistent_gibt_foldl Ls σ k

/-- Erasing through a taken lock then releasing it is erasing without it,
    when the lock was free before (`locks` premise). -/
theorem erase_nimmt_gibt (L : D.Lock) (Ls : List D.Lock) (h : List D.Lock) (hn : L ∉ h) :
    (Ls.foldl (fun h M => h.erase M) (L :: h)).erase L =
      Ls.foldl (fun h M => h.erase M) h := by
  induction Ls generalizing h with
  | nil => exact List.erase_cons_head L h
  | cons M Ms ih =>
      simp only [List.foldl_cons]
      by_cases heq : M = L
      · subst heq
        simp only [List.erase_cons_head]
        have h_erase : h.erase L = h := List.erase_of_not_mem hn
        rw [h_erase]
        have h_mem : ∀ (h : List D.Lock), L ∉ h →
            L ∉ Ms.foldl (fun h M => h.erase M) h := by
          intro h hn
          induction Ms generalizing h with
          | nil => exact hn
          | cons N Ns ih2 =>
              simp only [List.foldl_cons]
              exact ih2 _ (fun hm => hn (List.mem_of_mem_erase hm))
        exact List.erase_of_not_mem (h_mem h hn)
      · simp only [List.erase_cons_tail _ (Ne.symm heq)]
        exact ih _ (fun hm => hn (List.mem_of_mem_erase hm))

/-- `locks L { … }` with a releasing body keeps the release list. -/
theorem gut_nimmt_gibtRet {W G} (σ σ1 : World D) (L : D.Lock)
    (hn : (∀ M ∈ σ.haelt, D.rang M < D.rang L) ∧ L ∉ σ.haelt)
    (h : GutRet W G (σ.nimmt L) σ1) : GutRet W G σ (σ1.gibt L) := by
  obtain ⟨Ls, hLs⟩ := h.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (rahmen_gleich (W := W) (G := G) (σ := σ) (σ' := σ.nimmt L) rfl rfl).trans
      (h.1.trans (rahmen_gleich rfl rfl))
  · refine ⟨Ls, ?_⟩
    show (offen σ1.spur).erase L = Ls.foldl (fun h M => h.erase M) (offen σ.spur)
    have e1 : σ1.haelt = Ls.foldl (fun h M => h.erase M) (L :: σ.haelt) := by
      have := hLs
      simp only [World.haelt, World.nimmt, offen] at this ⊢
      exact this
    rw [e1]
    exact erase_nimmt_gibt L Ls _ hn.2
  · intro e he
    simp only [World.gibt, List.mem_cons] at he
    rcases he with rfl | he
    · exact .inr trivial
    · rcases h.2.2.1 e he with h1 | h1
      · simp only [World.nimmt, List.mem_cons] at h1
        rcases h1 with rfl | h1
        · exact .inr ⟨hn.1, hn.2⟩
        · exact .inl h1
      · exact .inr h1
  · intro k
    exact konsistent_cons trivial (h.2.2.2 (konsistent_cons rfl k))

/-- `locks L { … }` with a releasing body, keeping spare and rank (same `Ls`). -/
theorem gut_nimmt_gibtRetV {W G} {haelt : List D.Lock} {boden : Option Int}
    (σ σ1 : World D) (L : D.Lock)
    (hn : (∀ M ∈ σ.haelt, D.rang M < D.rang L) ∧ L ∉ σ.haelt)
    (h : GutRetV W G haelt boden (σ.nimmt L) σ1) :
    GutRetV W G haelt boden σ (σ1.gibt L) := by
  obtain ⟨hr, Ls, heq, hsp, hrk, hgood, hkons⟩ := h
  have hR : GutRet W G (σ.nimmt L) σ1 := ⟨hr, ⟨Ls, heq⟩, hgood, hkons⟩
  have hG := gut_nimmt_gibtRet (W := W) (G := G) (σ := σ) (σ1 := σ1) L hn hR
  obtain ⟨hr', ⟨_, heq'⟩, hgood', hkons'⟩ := hG
  exact ⟨hr', Ls, heq', hsp, hrk, hgood', hkons'⟩

end Gabbro.Grammatik
