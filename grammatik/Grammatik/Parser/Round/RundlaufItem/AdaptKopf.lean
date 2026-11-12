module

public import Grammatik.Parser.Round.RundlaufItem.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

private theorem typFolge_parameter (z : String) (R : List Token)
    (hz : z = "," ∨ z = ")") : TypFolge (.zeichen z :: R) := by
  rcases hz with rfl | rfl <;>
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩ <;>
    intro r h <;> simp_all

private theorem adaptEinzel_druck (n : String) (t : STyp) (R : List Token) (F : Nat)
    (hT : parseTyp F (druckTyp t ++ R) = .ok (t, R)) :
    parseAdaptParamEinzel (F + 1) (nameTok n :: .zeichen ":" :: (druckTyp t ++ R)) =
      .ok (.neu n t, R) := by
  rcases nameTok_cases n with hn | hn <;> rw [hn] <;>
    simp only [parseAdaptParamEinzel, nimmName, nameText_wort, nameText_ident,
      fordereZeichen, strEq_self, ite_true, hT]

/-- The adapter parameter reader classifies every printed ordinary parameter as `neu`.
    In particular, punctuation inside a type cannot become an adapter marker. -/
theorem adaptFolge_druck : ∀ (ps : List (String × STyp)) (R : List Token) (F : Nat),
    ps ≠ [] → (∀ p ∈ ps, TypGut p.2) → 8 * (druckParams ps).length + 34 ≤ F →
    parseAdaptParamFolge F (druckParams ps ++ .zeichen ")" :: R) =
      .ok (ps.map (fun p => .neu p.1 p.2), .zeichen ")" :: R) := by
  intro ps
  induction ps with
  | nil => intro R F h; exact absurd rfl h
  | cons p ps ih =>
    intro R F _ hg hF
    obtain ⟨n, t⟩ := p
    have ht : TypGut t := hg (n, t) List.mem_cons_self
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
    cases ps with
    | nil =>
      simp only [druckParams, druckParam, List.length_append,
        List.length_cons, List.length_nil] at hF
      have hT := parse_druckTyp t ht (.zeichen ")" :: R) F'
        (typFolge_parameter ")" R (Or.inr rfl)) (by simp only [fbT]; omega)
      have hA := adaptEinzel_druck n t (.zeichen ")" :: R) F' hT
      simp only [druckParams, druckParam, List.cons_append, List.nil_append,
        List.append_assoc, parseAdaptParamFolge, hA, List.map_cons, List.map_nil]
      split <;> simp_all
    | cons q qs =>
      obtain ⟨m, u⟩ := q
      obtain ⟨Z, hZ⟩ : ∃ Z, druckParams ((m, u) :: qs) = nameTok m :: Z := by
        cases qs <;> exact ⟨_, rfl⟩
      have hd : druckParams ((n, t) :: (m, u) :: qs) ++ .zeichen ")" :: R =
          nameTok n :: .zeichen ":" ::
            (druckTyp t ++ .zeichen "," :: nameTok m :: (Z ++ .zeichen ")" :: R)) := by
        change (druckParam (n, t) ++ [Token.zeichen ","] ++
          druckParams ((m, u) :: qs)) ++ .zeichen ")" :: R = _
        rw [hZ]
        simp only [druckParam, List.cons_append, List.nil_append, List.append_assoc]
      have hlen : (druckParams ((n, t) :: (m, u) :: qs)).length =
          (druckTyp t).length + 3 + (druckParams ((m, u) :: qs)).length := by
        change (druckParam (n, t) ++ [Token.zeichen ","] ++
          druckParams ((m, u) :: qs)).length = _
        simp only [druckParam, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [hlen] at hF
      have hRec := ih R (F' + 1) (by simp) (fun x hx => hg x (List.mem_cons_of_mem _ hx))
        (by omega)
      rw [hZ] at hRec
      simp only [List.cons_append] at hRec
      have hT := parse_druckTyp t ht (.zeichen "," :: nameTok m :: (Z ++ .zeichen ")" :: R)) F'
        (typFolge_parameter "," _ (Or.inl rfl)) (by simp only [fbT]; omega)
      have hA := adaptEinzel_druck n t (.zeichen "," :: nameTok m :: (Z ++ .zeichen ")" :: R)) F' hT
      rw [hd, parseAdaptParamFolge]
      simp only [hA, List.cons.injEq, nameTok_ne_zeichen,
        false_and, imp_self, implies_true, List.map_cons]
      split <;> simp_all [nameTok_ne_zeichen]

theorem adaptParams_druck (ps : List (String × STyp)) (hg : ∀ p ∈ ps, TypGut p.2)
    (R : List Token) (F : Nat) (hF : 8 * (druckParams ps).length + 35 ≤ F) :
    parseAdaptParams F (.zeichen "(" :: (druckParams ps ++ .zeichen ")" :: R)) =
      .ok (ps.map (fun p => .neu p.1 p.2), R) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases ps with
  | nil =>
    simp only [parseAdaptParams, fordereZeichen, strEq_self, ite_true,
      druckParams, List.nil_append, List.map_nil]
  | cons p ps =>
    obtain ⟨n, t⟩ := p
    obtain ⟨Z, hZ⟩ : ∃ Z, druckParams ((n, t) :: ps) = nameTok n :: Z := by
      cases ps <;> exact ⟨_, rfl⟩
    have hL := adaptFolge_druck ((n, t) :: ps) R F' (by simp) hg (by omega)
    rw [hZ] at hL ⊢
    simp only [List.cons_append] at hL ⊢
    simp only [parseAdaptParams, fordereZeichen, strEq_self, ite_true,
      List.cons.injEq, nameTok_ne_zeichen, false_and, imp_self, implies_true, hL]

/-- A printed ordinary signature always takes the ordinary function dispatch, whatever follows it. -/
theorem istAdaptKopf_sigToks (sig : FnSig) (hs : SigGut sig) (R : List Token) (F : Nat)
    (hF : 8 * (sigToks sig).length + 35 ≤ F) :
    istAdaptKopf F (sigToks sig ++ R) = false := by
  let tail := resToks sig.res ++ fehlerToks sig.fehler ++ druckKlauseln sig.klauseln ++ R
  have hd : sigToks sig ++ R = .wort "fn" :: nameTok sig.name :: .zeichen "(" ::
      (druckParams sig.params ++ .zeichen ")" :: tail) := by
    simp only [sigToks_eq sig hs.2.2.2.2, tail, List.cons_append, List.nil_append, List.append_assoc]
  rw [sigToks_eq sig hs.2.2.2.2] at hF
  rw [hd]
  have hP := adaptParams_druck sig.params hs.2.1 tail F
    (by simp only [List.length_cons, List.length_append, List.length_nil] at hF; omega)
  simp only [istAdaptKopf, nameText_nameTok, hP]
  have h : ∀ ps : List (String × STyp),
      (ps.map (fun p => SAdaptParam.neu p.1 p.2)).any (fun p => match p with
        | .alle | .ohne _ => true
        | .neu _ _ => false) = false := by
    intro ps
    induction ps with
    | nil => rfl
    | cons p ps ih => simp only [List.map_cons, List.any_cons, ih, Bool.false_or]
  exact h sig.params

end Gabbro.Grammatik.Parser
