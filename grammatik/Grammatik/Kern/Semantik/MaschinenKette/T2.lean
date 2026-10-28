/- Part 2 of 5 of `MaschinenKette` (split by instrumente/teile/lean-teilen.py; the umbrella `MaschinenKette.lean` imports all parts). -/
import Grammatik.Kern.Semantik.MaschinenKette.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}
variable {D : Deklaration}

/-- **Corollary: the table package feeds the induction's guarded `SerialLink`
    slot.** From the per-carrier package (guard existence, coverage, witness
    events) the guarded slot closes unconditionally: the slot guard is matched
    for the consumer (`kette_aus_lauf_schritt`) but carries no content, because
    writers are covered by real witnesses. -/
theorem serialLink_zeuge_fuer_kette (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (run : Lauf D) (f : Faden)
    (hGuard : ∀ t₀ : D.Tab, ∃ L : D.Lock, Sum.inl L ∈ D.braucht t₀)
    (hCov : ∀ (t₀ : D.Tab) (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i)
    (hwit : ∀ (t₀ : D.Tab) (k : Nat) (g : Faden), J.schrittFaden[k]? = some g →
      TraegerSchreibt (J.code g) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λ : List (Res D)) (h : List D.Lock),
        run[j]? = some (Schritt.mk g (.zugriff t₀ w Λ h))) :
    ∀ t₀ : D.Tab, TraegerSchreibt (J.code f) (.inl t₀) = false →
      SerialLink Nb J run t₀ := by
  intro t₀ _
  obtain ⟨L, hL⟩ := hGuard t₀
  exact (serialLink_zeuge_tabelle Nb J run t₀ L hL (hCov t₀) (hwit t₀)).1

#print axioms Gabbro.Grammatik.serialLink_zeuge_tabelle
#print axioms Gabbro.Grammatik.serialLink_zeuge_fuer_kette

end Gabbro.Grammatik

/-! ## Whole-run chain over framed leaves: `kette_aus_lauf_gesamt`

    `kette_aus_lauf_voll` above iterates the threading step over whole `PCReach`
    runs but keeps the `hlock` premise: no `PCAtom.leaf` atom anywhere in `prog`,
    so the `blatt` case closes by contradiction and the induction covers exactly
    the steps that do nothing. Section 18 of `Maschine.lean` (e01) lifts that
    exclusion at step level -- `kette_aus_maschinenlauf_blatt` extends the
    tracking chain along a fired framed leaf -- but its conclusion drops the
    facts the NEXT iteration needs (the member thread, the code identity, the
    non-writer fact), so pure reuse cannot iterate, for the same reason the file
    header records for lock steps. This section iterates the blatt-step chain
    extension over whole runs:

    - `kette_aus_lauf_start_code`: the seed chain with code identity. The
      `kette_aus_lauf_start` construction plus `J.code = code` by construction,
      so the induction below converts the static contract-to-code covering to
      the chain-local wiring at every leaf.
    - `kette_aus_lauf_schritt_rahmen`: the threading step with a frame premise.
      The `kette_aus_lauf_schritt` construction with the same routing premises
      and the same conclusion, except the memory-preservation premises
      (`hslots` / `hglobs`) are replaced by one `Rahmen` premise over the new
      step (`hFrame`), and the code identity rides along (`hJcode` in,
      `J'.code = code` out). DELTA lines: the signature (frame premise, code
      threading, `neu` events instead of one event) and the new-step frame,
      which transfers `hFrame` across definitionally equal memories (successor
      worlds share memory by construction, as in
      `kette_aus_maschinenlauf_blatt`). Read-only reuse of e01:
      `blatt_rahmen_schritt` feeds `hFrame` at leaf steps; lock steps feed it by
      `rfl` (memory-preserving by construction).
    - `kette_aus_lauf_gesamt`: the chain from the whole run WITHOUT `hlock`.
      The `PCReach` induction of `kette_aus_lauf_voll` with the `blatt` case
      wired per step: counter routing rules out foreign steps
      (`hsingle_prog`), while `pcReach_gen` projects every prefix to
      `GenErreichbar` for the step (read-only; the reachability half of the
      `pcSchritt_gen` counter routing that `zaehler_routing_gen` lifts to
      occurring steps).

    Covered class (exactly): single-thread `PCReach` runs with frame-covered
    leaves, table-nonwriting code, and a fitting entry --

    * single-thread (`hsingle_prog`, `hsingle_run`): as in
      `kette_aus_lauf_voll`;
    * frame-covered leaves (`hRahmen`): every leaf statement's contract writes
      only where the member thread's code may write, so each fired leaf's
      post-world satisfies the chain-step `Rahmen` through
      `blatt_rahmen_schritt` (read-only); oracle leaves included (the frame is
      the same `stmt_gut` derivation under the same bound `hO`, as in e01);
    * table-nonwriting code (`hnw_code`): `code f` writes no table carrier, so
      the guarded `SerialLink` of one level discharges to the unconditional
      link the next step consumes; together with `hRahmen` this forces fired
      leaves to move table memory nowhere and globals only inside the code
      frame;
    * fitting entry (`hEintritt`, `hSchuld`, `hInvSicht`): as before.

    Remainder (booked, not hidden): non-vacuous `SerialLink` witnesses at
    `zugriff` events for writing steps (the e02 table package is not folded
    into this induction: the new-step link still closes by contradiction from
    the non-writer premise); multi-thread runs (as before); globals and
    multi-carrier conflicts (as before).
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Seed chain with code identity: the start machine carries its code.**
    The `kette_aus_lauf_start` construction with the same premises and the same
    conclusion, plus `J.code = code` by construction (`rfl` at the literal:
    the same `code` function is installed). The step below preserves this
    equation, so the whole-run induction converts the static contract-to-code
    covering (`hRahmen`, stated about `code`) to the chain-local wiring at
    every leaf. DELTA: the signature (one added conjunct) and the final tuple
    (one added `rfl`); everything else mirrors the source. -/
theorem kette_aus_lauf_start_code (Nb : Nebeneinander) (sp : Speicher D)
    (f : Faden) (code : Faden → D.Fn)
    (hnw_code : ∀ t₀ : D.Tab, TraegerSchreibt (code f) (.inl t₀) = false)
    (hEintritt : EintrittPasst (code f) (GenStart sp).start)
    (hSchuld : SchuldnerHaelt (code f))
    (hInvSicht : InvSichtHaelt (code f) (GenStart sp).start) :
    ∃ J : GemeinsamerLauf (D := D) Nb,
      J.welten = (GenStart sp).welten ∧
      J.l = (GenStart sp).lauf ∧
      f ∈ J.faeden ∧
      J.code = code ∧
      (∀ t₀ : D.Tab, TraegerSchreibt (J.code f) (.inl t₀) = false) ∧
      ∀ t₀ : D.Tab, SerialLink Nb J (GenStart sp).lauf t₀ := by
  have hGes : Gesittet ([] : Lauf D) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro f j
      have hsp : Lauf.spur ([] : Lauf D) f j = [] := by simp only [Lauf.spur, List.take_nil, List.filterMap_nil, List.reverse_nil]
      rw [hsp]
      exact konsistent_nil
    · intro f j e he
      have hsp : Lauf.spur ([] : Lauf D) f j = [] := by simp only [Lauf.spur, List.take_nil, List.filterMap_nil, List.reverse_nil]
      rw [hsp] at he
      simp only [List.not_mem_nil] at he
    · intro j f L h hi g hne
      simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at hi
    · intro i j f g m s s' ei ej hi hj hm hm'
      simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at hi
    · intro i j f g o ei ej hi hj ht1 ht2 hu
      simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at hi
  have hBeschr : BeschraenkteVerschraenkung (D := D) Nb ([] : Lauf D) := by
    intro i j f g ei ej hi hj hne
    simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at hi
  have hKette0 : (GenStart sp).welten.length = ([] : List Faden).length + 1 := by
    simp only [GenStart, List.length_cons, List.length_nil, Nat.zero_add]
  have hSchritt0 : ∀ (k : Nat) (f' : Faden) (vor nach : World D),
      ([] : List Faden)[k]? = some f' → (GenStart sp).welten[k]? = some vor →
      (GenStart sp).welten[k + 1]? = some nach →
      f' ∈ ([f] : List Faden) ∧
        Rahmen (D.schreibt (code f')) (D.gschreibt (code f')) vor nach := by
    intro k f' vor nach hk _ _
    simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at hk
  have hPaar0 : ∀ (f' : Faden), f' ∈ ([f] : List Faden) → ∀ (g : Faden),
      g ∈ ([f] : List Faden) → f' ≠ g → Nb f' g := by
    intro f' hf' g hg' hne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf' hg'
    subst hf'
    subst hg'
    exact absurd rfl hne
  have hEintritt0 : ∀ (f' : Faden), f' ∈ ([f] : List Faden) →
      EintrittPasst (code f') ((fun _ => (GenStart sp).start) f') := by
    intro f' hf'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
    subst hf'
    exact hEintritt
  have hSchuld0 : ∀ (f' : Faden), f' ∈ ([f] : List Faden) →
      SchuldnerHaelt (code f') := by
    intro f' hf'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
    subst hf'
    exact hSchuld
  have hInvSicht0 : ∀ (f' : Faden), f' ∈ ([f] : List Faden) →
      InvSichtHaelt (code f') ((fun _ => (GenStart sp).start) f') := by
    intro f' hf'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
    subst hf'
    exact hInvSicht
  have hmem0 : f ∈ ([f] : List Faden) := by simp only [List.mem_cons, List.not_mem_nil, or_false]
  -- DELTA: one added `rfl` for the code identity, proved at the literal.
  refine ⟨{ faeden := [f], code := code, eintritt := fun _ => (GenStart sp).start,
            welten := (GenStart sp).welten, schrittFaden := [], l := ([] : Lauf D),
            hKette := hKette0, hSchritt := hSchritt0, hPaar := hPaar0,
            hGesittet := hGes, hBeschraenkt := hBeschr,
            hEintritt := hEintritt0, hSchuld := hSchuld0, hInvSicht := hInvSicht0 },
          rfl, rfl, hmem0, rfl, hnw_code, ?_⟩
  intro t₀ k g hk _
  have hk' : ([] : List Faden)[k]? = some g := hk
  simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at hk'

/-- **The chain from the machine, one threading step with a frame premise.**
    Same construction as `kette_aus_lauf_schritt` (same read-only projection
    theorems, same single-thread arithmetic, same frame, same witness
    transport); DELTA: the new-step frame arrives as one `Rahmen` premise
    (`hFrame`) instead of two memory-preservation equations, the step carries
    `neu` events instead of one event, and the code identity rides along
    (`hJcode` in, `J'.code = code` out), so the conclusion feeds the next
    iteration -- worlds, run, member, code identity, non-writer fact, guarded
    link. Every premise is load-bearing: `neu` / `nach` type the successor
    equations, `hFrame` feeds the new-step frame, `code` / `hJcode` feed the
    code-identity conclusion, the routing premises feed the mirrored
    construction. -/
theorem kette_aus_lauf_schritt_rahmen
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (Nb : Nebeneinander)
    (M M' : GenMaschine D) (f : Faden)
    (hReach : GenErreichbar P O passes (GenStart sp) M)
    (hReach' : GenErreichbar P O passes (GenStart sp) M')
    (neu : List (Ereignis D)) (nach : World D)
    (hM'l : M'.lauf = M.lauf ++ genEigen f neu)
    (hM'w : M'.welten = M.welten ++ [nach])
    (J : GemeinsamerLauf (D := D) Nb)
    (code : Faden → D.Fn)
    (hJcode : J.code = code)
    (hJw : J.welten = M.welten)
    (hmem : f ∈ J.faeden)
    (hFrame : Rahmen (D.schreibt (J.code f)) (D.gschreibt (J.code f)) (M.weltVon f) nach)
    (hLink : ∀ t₀ : D.Tab, TraegerSchreibt (J.code f) (.inl t₀) = false →
      SerialLink Nb J M.lauf t₀)
    (hnwJ : ∀ t₀ : D.Tab, TraegerSchreibt (J.code f) (.inl t₀) = false)
    (hsingle : ∀ s ∈ M.lauf, s.faden = f) :
    ∃ J' : GemeinsamerLauf (D := D) Nb,
      J'.welten = M'.welten ∧
      J'.l = M'.lauf ∧
      f ∈ J'.faeden ∧
      J'.code = code ∧
      (∀ t₀ : D.Tab, TraegerSchreibt (J'.code f) (.inl t₀) = false) ∧
      (∀ t₀ : D.Tab, TraegerSchreibt (J'.code f) (.inl t₀) = false →
        SerialLink Nb J' M'.lauf t₀) := by
  -- DELTA: discharge the guarded link to the unconditional shape the witness
  -- transport below consumes; everything after this line mirrors the source
  -- except the new-step frame, which transfers `hFrame`.
  have hLinkUncond : ∀ t₀ : D.Tab, SerialLink Nb J M.lauf t₀ := by
    intro t₀
    exact hLink t₀ (hnwJ t₀)
  have hlen : M.welten.length = J.schrittFaden.length + 1 := by
    rw [← hJw]
    exact J.hKette
  obtain ⟨f0, hlast⟩ := genWelten_letzte P O passes hO sp M hReach
  have hLastIdx : M.welten[J.schrittFaden.length]? =
      some (M.speicher.welt (M.spuren f0)) := by
    have hget : M.welten.getLast? = M.welten[M.welten.length - 1]? :=
      List.getLast?_eq_getElem?
    have hn : M.welten.length - 1 = J.schrittFaden.length := by omega
    rw [hn] at hget
    rw [hlast] at hget
    exact hget.symm
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
  have hBeschr' : BeschraenkteVerschraenkung (D := D) Nb M'.lauf := by
    intro i j g1 g2 e1 e2 hi hj hne
    have h1 := hfaden i g1 e1 hi
    have h2 := hfaden j g2 e2 hj
    exact absurd (h1.trans h2.symm) hne
  have hKette' : M'.welten.length = (J.schrittFaden ++ [f]).length + 1 := by
    have h1 : (J.schrittFaden ++ [f]).length = J.schrittFaden.length + 1 := by simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_left_cancel_iff]
    have h2 : M'.welten.length = M.welten.length + 1 := by rw [hM'w]; simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_left_cancel_iff]
    omega
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
      have e2 : (M.welten ++ [nach])[k]? = M.welten[k]? :=
        List.getElem?_append_left hltM
      rw [e2] at hkv
      have hJkv : J.welten[k]? = some vor := by rw [hJw]; exact hkv
      have hltM1 : k + 1 < M.welten.length := by omega
      have e3 : (M.welten ++ [nach])[k + 1]? = M.welten[k + 1]? :=
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
        have eW : (M.welten ++ [nach])[J.schrittFaden.length]? =
            M.welten[J.schrittFaden.length]? :=
          List.getElem?_append_left (by omega)
        rw [eW, hLastIdx] at hkv
        have hvor : vor = M.speicher.welt (M.spuren f0) :=
          Option.some_inj.mp hkv.symm
        have eW2 : (M.welten ++ [nach])[J.schrittFaden.length + 1]? = some nach := by
          have hle2 : M.welten.length ≤ J.schrittFaden.length + 1 := by omega
          rw [List.getElem?_append_right hle2]
          have hsub : J.schrittFaden.length + 1 - M.welten.length = 0 := by omega
          rw [hsub]
          rfl
        rw [eW2] at hkn
        have hnach0 : nach = nach0 := Option.some_inj.mp hkn
        -- DELTA: the new-step frame transfers `hFrame` across definitionally
        -- equal memories (successor worlds share memory by construction).
        rw [hg0, hvor, ← hnach0]
        refine ⟨hmem, ?_, ?_⟩
        · intro t ht k2 fld
          exact hFrame.1 t ht k2 fld
        · intro g hg
          exact hFrame.2 g hg
      · have hle : J.schrittFaden.length ≤ k := by omega
        have eNone : (J.schrittFaden ++ [f])[k]? = none := by
          rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
            List.length_singleton]
          omega
        rw [eNone] at hk
        simp only [reduceCtorEq] at hk
  -- DELTA: the extended chain keeps member, code identity, and non-writer fact
  -- by construction (`rfl` up to the definition: same `faeden`, same `code`);
  -- the link below reads the discharged `hLinkUncond` for old steps.
  refine ⟨{ faeden := J.faeden, code := J.code, eintritt := J.eintritt,
            welten := M'.welten, schrittFaden := J.schrittFaden ++ [f], l := M'.lauf,
            hKette := hKette', hSchritt := hSchritt', hPaar := J.hPaar,
            hGesittet := hGes', hBeschraenkt := hBeschr',
            hEintritt := J.hEintritt, hSchuld := J.hSchuld, hInvSicht := J.hInvSicht },
          rfl, rfl, hmem, hJcode, hnwJ, ?_⟩
  intro t₀ hnw k0 g0 hk0 hwr
  have hk0' : (J.schrittFaden ++ [f])[k0]? = some g0 := hk0
  have hwr0 : TraegerSchreibt (J.code g0) (.inl t₀) = true := hwr
  by_cases hlt : k0 < J.schrittFaden.length
  · have eOld : (J.schrittFaden ++ [f])[k0]? = J.schrittFaden[k0]? :=
      List.getElem?_append_left hlt
    rw [eOld] at hk0'
    obtain ⟨j, w, Λ, h, hw⟩ := hLinkUncond t₀ k0 g0 hk0' hwr0
    have hjlt : j < M.lauf.length := by
      by_cases h : j < M.lauf.length
      · exact h
      · have hle : M.lauf.length ≤ j := by omega
        rw [List.getElem?_eq_none hle] at hw
        simp only [reduceCtorEq] at hw
    have hw' : M'.lauf[j]? = some (Schritt.mk g0 (.zugriff t₀ w Λ h)) := by
      rw [hM'l, List.getElem?_append_left hjlt]
      exact hw
    exact ⟨j, w, Λ, h, hw'⟩
  · by_cases heq : k0 = J.schrittFaden.length
    · subst heq
      have hg0 : g0 = f := by
        have eNew : (J.schrittFaden ++ [f])[J.schrittFaden.length]? = some f := by
          rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        rw [eNew] at hk0'
        exact (Option.some_inj.mp hk0').symm
      rw [hg0] at hwr
      have hwrF : TraegerSchreibt (J.code f) (.inl t₀) = true := hwr
      rw [hnw] at hwrF
      simp only [Bool.false_eq_true] at hwrF
    · have hle : J.schrittFaden.length ≤ k0 := by omega
      have eNone : (J.schrittFaden ++ [f])[k0]? = none := by
        rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
          List.length_singleton]
        omega
      rw [eNone] at hk0'
      simp only [reduceCtorEq] at hk0'


end Gabbro.Grammatik
