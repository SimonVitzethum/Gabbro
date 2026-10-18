/- Part 5 of 9 of `Maschine` (split by instrumente/teile/lean-teilen.py; the umbrella `Maschine.lean` imports all parts). -/
import Grammatik.Kern.Semantik.Maschine.T4

namespace Gabbro.Grammatik

variable {D : Deklaration}
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable {D : Deklaration}
variable {D : Deklaration}

/-- **The chain from the machine, zero-step base.** The start machine over
    shared memory is a chain by construction: empty thread list, empty step
    list, the generated worlds and the empty run. The identification holds by
    `rfl`; `SerialLink` holds vacuously over any carrier. -/
theorem kette_aus_maschinenlauf (Nb : Nebeneinander) (sp : Speicher D) (fn0 : D.Fn) :
    ∃ J : GemeinsamerLauf (D := D) Nb,
      J.welten = (GenStart sp).welten ∧
      J.l = (GenStart sp).lauf ∧
      ∀ t₀ : D.Tab, SerialLink Nb J (GenStart sp).lauf t₀ := by
  have hGes : Gesittet ([] : Lauf D) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro f j
      have hsp : Lauf.spur ([] : Lauf D) f j = [] := by simp [Lauf.spur]
      rw [hsp]
      exact konsistent_nil
    · intro f j e he
      have hsp : Lauf.spur ([] : Lauf D) f j = [] := by simp [Lauf.spur]
      rw [hsp] at he
      simp at he
    · intro j f L h hi g hne
      simp at hi
    · intro i j f g m s s' ei ej hi hj hm hm'
      simp at hi
    · intro i j f g o ei ej hi hj ht1 ht2 hu
      simp at hi
  have hBeschr : BeschraenkteVerschraenkung (D := D) Nb ([] : Lauf D) := by
    intro i j f g ei ej hi hj hne
    simp at hi
  have hKette0 : (GenStart sp).welten.length = ([] : List Faden).length + 1 := by
    simp [GenStart]
  have hSchritt0 : ∀ (k : Nat) (f : Faden) (vor nach : World D),
      ([] : List Faden)[k]? = some f → (GenStart sp).welten[k]? = some vor →
      (GenStart sp).welten[k + 1]? = some nach →
      f ∈ ([] : List Faden) ∧
        Rahmen (D.schreibt ((fun _ => fn0) f)) (D.gschreibt ((fun _ => fn0) f)) vor nach := by
    intro k f vor nach hk _ _
    simp at hk
  have hPaar0 : ∀ (f : Faden), f ∈ ([] : List Faden) → ∀ (g : Faden),
      g ∈ ([] : List Faden) → f ≠ g → Nb f g := by
    intro f hf
    simp at hf
  have hEintritt0 : ∀ (f : Faden), f ∈ ([] : List Faden) →
      EintrittPasst ((fun _ => fn0) f) ((fun _ => (GenStart sp).start) f) := by
    intro f hf
    simp at hf
  have hSchuld0 : ∀ (f : Faden), f ∈ ([] : List Faden) →
      SchuldnerHaelt ((fun _ => fn0) f) := by
    intro f hf
    simp at hf
  have hInvSicht0 : ∀ (f : Faden), f ∈ ([] : List Faden) →
      InvSichtHaelt ((fun _ => fn0) f) ((fun _ => (GenStart sp).start) f) := by
    intro f hf
    simp at hf
  refine ⟨{ faeden := [], code := fun _ => fn0, eintritt := fun _ => (GenStart sp).start,
            welten := (GenStart sp).welten, schrittFaden := [], l := ([] : Lauf D),
            hKette := hKette0, hSchritt := hSchritt0, hPaar := hPaar0,
            hGesittet := hGes, hBeschraenkt := hBeschr,
            hEintritt := hEintritt0, hSchuld := hSchuld0, hInvSicht := hInvSicht0 },
          rfl, rfl, ?_⟩
  intro t₀ k g hk _
  have hk' : ([] : List Faden)[k]? = some g := hk
  simp at hk'

/-- **The chain from the machine, one induction step.** A chain tracking `M`
    extends along one memory-preserving step of a member thread: worlds and
    run by construction (`rfl`), order and goodness from the read-only
    projection theorems, ownership and declaration side from the single-thread
    run, the new frame from memory preservation, `SerialLink` inherited plus
    guarded-vacuous at the new step. -/
theorem kette_aus_maschinenlauf_schritt
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (Nb : Nebeneinander)
    (M M' : GenMaschine D) (f : Faden)
    (hReach : GenErreichbar P O passes (GenStart sp) M)
    (hReach' : GenErreichbar P O passes (GenStart sp) M')
    (e : Ereignis D) (nach : World D)
    (hM'l : M'.lauf = M.lauf ++ genEigen f [e])
    (hM'w : M'.welten = M.welten ++ [nach])
    (hslots : ∀ (t : D.Tab) (k : Int) (fld : D.Feld t),
      nach.slots t k fld = M.speicher.slots t k fld)
    (hglobs : ∀ g : D.Glob, nach.globs g = M.speicher.globs g)
    (J : GemeinsamerLauf (D := D) Nb)
    (hJw : J.welten = M.welten)
    (hmem : f ∈ J.faeden)
    (hLink : ∀ t₀ : D.Tab, SerialLink Nb J M.lauf t₀)
    (hsingle : ∀ s ∈ M.lauf, s.faden = f) :
    ∃ J' : GemeinsamerLauf (D := D) Nb,
      J'.welten = M'.welten ∧
      J'.l = M'.lauf ∧
      (∀ t₀ : D.Tab, TraegerSchreibt (J.code f) (.inl t₀) = false →
        SerialLink Nb J' M'.lauf t₀) := by
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
      exact (gen_eigen_getElem f [e] _ _ _ hi).1
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
    have h1 : (J.schrittFaden ++ [f]).length = J.schrittFaden.length + 1 := by simp
    have h2 : M'.welten.length = M.welten.length + 1 := by rw [hM'w]; simp
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
        rw [hg0, hvor, ← hnach0]
        refine ⟨hmem, ?_, ?_⟩
        · intro t _ k2 fld
          exact hslots t k2 fld
        · intro g _
          exact hglobs g
      · have hle : J.schrittFaden.length ≤ k := by omega
        have eNone : (J.schrittFaden ++ [f])[k]? = none := by
          rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
            List.length_singleton]
          omega
        rw [eNone] at hk
        simp at hk
  refine ⟨{ faeden := J.faeden, code := J.code, eintritt := J.eintritt,
            welten := M'.welten, schrittFaden := J.schrittFaden ++ [f], l := M'.lauf,
            hKette := hKette', hSchritt := hSchritt', hPaar := J.hPaar,
            hGesittet := hGes', hBeschraenkt := hBeschr',
            hEintritt := J.hEintritt, hSchuld := J.hSchuld, hInvSicht := J.hInvSicht },
          rfl, rfl, ?_⟩
  intro t₀ hnw k0 g0 hk0 hwr
  have hk0' : (J.schrittFaden ++ [f])[k0]? = some g0 := hk0
  have hwr0 : TraegerSchreibt (J.code g0) (.inl t₀) = true := hwr
  by_cases hlt : k0 < J.schrittFaden.length
  · have eOld : (J.schrittFaden ++ [f])[k0]? = J.schrittFaden[k0]? :=
      List.getElem?_append_left hlt
    rw [eOld] at hk0'
    obtain ⟨j, w, Λ, h, hw⟩ := hLink t₀ k0 g0 hk0' hwr0
    have hjlt : j < M.lauf.length := by
      by_cases h : j < M.lauf.length
      · exact h
      · have hle : M.lauf.length ≤ j := by omega
        rw [List.getElem?_eq_none hle] at hw
        simp at hw
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
      simp at hwrF
    · have hle : J.schrittFaden.length ≤ k0 := by omega
      have eNone : (J.schrittFaden ++ [f])[k0]? = none := by
        rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
          List.length_singleton]
        omega
      rw [eNone] at hk0'
      simp at hk0'

/-- **The chain from the machine, lock-take instance.** A fireable `nimmt`
    step of a member thread extends a tracking chain: the successor and its
    evidence come from the `GenSchritt` constructor, the link from the
    one-step extension. -/
theorem kette_aus_maschinenlauf_nimmt
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (Nb : Nebeneinander)
    (M : GenMaschine D) (f : Faden) (L : D.Lock)
    (hself : L ∉ offen (M.spuren f))
    (hrang : ∀ K ∈ offen (M.spuren f), D.rang K < D.rang L)
    (hfrei : GenFrei M f L)
    (hReach : GenErreichbar P O passes (GenStart sp) M)
    (J : GemeinsamerLauf (D := D) Nb)
    (hJw : J.welten = M.welten)
    (hmem : f ∈ J.faeden)
    (hLink : ∀ t₀ : D.Tab, SerialLink Nb J M.lauf t₀)
    (hsingle : ∀ s ∈ M.lauf, s.faden = f) :
    ∃ M' : GenMaschine D, ∃ J' : GemeinsamerLauf (D := D) Nb,
      J'.welten = M'.welten ∧
      J'.l = M'.lauf ∧
      (∀ t₀ : D.Tab, TraegerSchreibt (J.code f) (.inl t₀) = false →
        SerialLink Nb J' M'.lauf t₀) := by
  let eN : Ereignis D := Ereignis.nimmt L (offen (M.spuren f))
  let nachN : World D := M.speicher.welt (eN :: M.spuren f)
  let M' : GenMaschine D :=
    ⟨M.speicher, genUpdate M.spuren f (eN :: M.spuren f),
     M.lauf ++ genEigen f [eN], M.start, M.welten ++ [nachN], M.tiefe + 1⟩
  have hs : GenSchritt P O passes M f M' :=
    GenSchritt.nimmt M f L hself hrang hfrei
  have hReach' : GenErreichbar P O passes (GenStart sp) M' :=
    GenErreichbar.schritt M M' f hReach hs
  have hM'l : M'.lauf = M.lauf ++ genEigen f [eN] := rfl
  have hM'w : M'.welten = M.welten ++ [nachN] := rfl
  have hslots : ∀ (t : D.Tab) (k : Int) (fld : D.Feld t),
      nachN.slots t k fld = M.speicher.slots t k fld := fun t k fld => rfl
  have hglobs : ∀ g : D.Glob, nachN.globs g = M.speicher.globs g := fun g => rfl
  refine ⟨M', ?_⟩
  exact kette_aus_maschinenlauf_schritt P O passes hO sp Nb M M' f
    hReach hReach' eN nachN hM'l hM'w hslots hglobs J hJw hmem hLink hsingle

/-- **The chain from the machine, lock-release instance.** A held `gibt`
    step of a member thread extends a tracking chain: same shape as the
    take instance, memory-preserving by the same construction. -/
theorem kette_aus_maschinenlauf_gibt
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (Nb : Nebeneinander)
    (M : GenMaschine D) (f : Faden) (L : D.Lock)
    (hhaelt : L ∈ offen (M.spuren f))
    (hReach : GenErreichbar P O passes (GenStart sp) M)
    (J : GemeinsamerLauf (D := D) Nb)
    (hJw : J.welten = M.welten)
    (hmem : f ∈ J.faeden)
    (hLink : ∀ t₀ : D.Tab, SerialLink Nb J M.lauf t₀)
    (hsingle : ∀ s ∈ M.lauf, s.faden = f) :
    ∃ M' : GenMaschine D, ∃ J' : GemeinsamerLauf (D := D) Nb,
      J'.welten = M'.welten ∧
      J'.l = M'.lauf ∧
      (∀ t₀ : D.Tab, TraegerSchreibt (J.code f) (.inl t₀) = false →
        SerialLink Nb J' M'.lauf t₀) := by
  let eG : Ereignis D := Ereignis.gibt L
  let nachG : World D := M.speicher.welt (eG :: M.spuren f)
  let M' : GenMaschine D :=
    ⟨M.speicher, genUpdate M.spuren f (eG :: M.spuren f),
     M.lauf ++ genEigen f [eG], M.start, M.welten ++ [nachG], M.tiefe + 1⟩
  have hs : GenSchritt P O passes M f M' :=
    GenSchritt.gibt M f L hhaelt
  have hReach' : GenErreichbar P O passes (GenStart sp) M' :=
    GenErreichbar.schritt M M' f hReach hs
  have hM'l : M'.lauf = M.lauf ++ genEigen f [eG] := rfl
  have hM'w : M'.welten = M.welten ++ [nachG] := rfl
  have hslots : ∀ (t : D.Tab) (k : Int) (fld : D.Feld t),
      nachG.slots t k fld = M.speicher.slots t k fld := fun t k fld => rfl
  have hglobs : ∀ g : D.Glob, nachG.globs g = M.speicher.globs g := fun g => rfl
  refine ⟨M', ?_⟩
  exact kette_aus_maschinenlauf_schritt P O passes hO sp Nb M M' f
    hReach hReach' eG nachG hM'l hM'w hslots hglobs J hJw hmem hLink hsingle

#print axioms Gabbro.Grammatik.kette_aus_maschinenlauf
#print axioms Gabbro.Grammatik.kette_aus_maschinenlauf_schritt
#print axioms Gabbro.Grammatik.kette_aus_maschinenlauf_nimmt
#print axioms Gabbro.Grammatik.kette_aus_maschinenlauf_gibt

end Gabbro.Grammatik

/-! ## 15. The scheduler atom identity (S12, slot-collapse fragment)

    What `Ziel.lean` §9b books as atom identity (S12): the scheduled counter at
    each step points at exactly the atom `stmtAtome_blatt_eq`
    (`Extraktion.lean` §14) yields for the fired statement -- per step and per
    run -- feeding the `hpc`/`hΛa`/`hcs` slots of `PCSchritt.leaf` (§12) and of
    the lifter `pcSchritt_blatt_progAus_ohne_axiomCall`.

    What closes HERE (no `sorry`, PC shapes only -- this file cannot see
    `Extraktion`: `Extraktion.lean` imports this file, so the instantiation
    `prog := Extraktion.progAus ...` with
    `cs₀ := Extraktion.stmtTraeger ... ++ Extraktion.stmtOrte ...` plus the
    `stmtAtome_blatt_eq` rewrite lives one level up, where both modules are
    visible):

    - `zaehler_zeigt_atom`: the three leaf slots collapse to one identity --
      from `hpc`/`hΛa`/`hcs` over any `prog`, the counter points at
      `leaf Λ cs₀`. Under the extraction instantiation this IS the
      `stmtAtome_blatt_eq` atom of the fired statement.
    - `hpc_hΛa_hcs_aus_zaehler`: the discharge corollary -- one posited
      identity feeds all three `PCSchritt.leaf` slots
      (`∃ Λa cs, hpc ∧ hΛa ∧ hcs`), so a witness positing the identity owes
      nothing more per leaf step.
    - `zaehler_zeigt_atom_lauf`: the per-run form -- any leaf step occurring
      anywhere in a generated run derivation (`SchrittImLauf`: the last step,
      or a step of the prefix) satisfies the same identity. The step proof
      `hs` evidences that the step fired, the membership proof that it fired
      in THIS run, the triple that it fired as this leaf.

    Remainder (booked, not hidden): deriving the identity FROM the run -- that
    a witness-built `PCReach` over `progAus` always posits the extracted atom
    -- is the scheduler-construction duty and stays open (S12); the `take`/
    `rel` bracket correspondence (`stmtAtome_locks` sides) and the `axiomCall`
    event contract (S13) likewise; calls and compounds never fire as leaves
    (`istBlatt = false`), so they owe no leaf identity. Positions stay
    derivation-external: proof irrelevance forbids computing a thread's step
    count off a `PCReach` derivation (large elimination -- measured above),
    so no endpoint-level atom identity is stated; per-run coverage IS
    per-step coverage at every occurring step.
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **The counter identity, leaf fragment.** The three `PCSchritt.leaf` counter
    slots (`hpc`: the counter points at `leaf Λa cs`; `hΛa`: that `Λa` is the
    fired footprint; `hcs`: those `cs` are the extracted carriers) collapse to
    one identity: the counter points at `leaf Λ cs₀`. Every premise is
    load-bearing: `prog`/`f`/`pc`/`Λa`/`cs` type `hpc`, `Λ`/`cs₀` type the
    rewrites and the conclusion. -/
theorem zaehler_zeigt_atom (prog : PCProg D) (f : Faden) (pc : PCStand)
    (Λ : List (Res D)) (cs₀ : List (D.Tab ⊕ D.Glob))
    (Λa : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
    (hpc : (prog f)[pc f]? = some (PCAtom.leaf Λa cs))
    (hΛa : Λa = Λ) (hcs : cs = cs₀) :
    (prog f)[pc f]? = some (PCAtom.leaf Λ cs₀) := by
  rw [hΛa, hcs] at hpc
  exact hpc

/-- **The discharge corollary: one identity feeds the three leaf slots.** A
    witness positing the counter identity owes `hpc`/`hΛa`/`hcs` of
    `PCSchritt.leaf` (and hence of the `progAus` lifter) at once: the triple
    is the unpacked existential. Every premise is load-bearing:
    `prog`/`f`/`pc`/`Λ`/`cs₀` type `hident`, `hident` is the witness. -/
theorem hpc_hΛa_hcs_aus_zaehler (prog : PCProg D) (f : Faden) (pc : PCStand)
    (Λ : List (Res D)) (cs₀ : List (D.Tab ⊕ D.Glob))
    (hident : (prog f)[pc f]? = some (PCAtom.leaf Λ cs₀)) :
    ∃ Λa : List (Res D), ∃ cs : List (D.Tab ⊕ D.Glob),
      (prog f)[pc f]? = some (PCAtom.leaf Λa cs) ∧ Λa = Λ ∧ cs = cs₀ := by
  exact ⟨Λ, cs₀, hident, rfl, rfl⟩

/-- **A generated step occurring in a generated run derivation**: the last
    step (`letzter`), or a step of the prefix (`frueher`). The step proof is
    fixed; the run varies over derivations containing it. -/
inductive SchrittImLauf (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M0 Mmid : GenMaschine D) (pcmid : PCStand) (f : Faden)
    (M' : GenMaschine D) (pc' : PCStand)
    (hs : PCSchritt P O passes prog Mmid pcmid f M' pc') :
    ∀ {M : GenMaschine D} {pc : PCStand},
    PCReach P O passes prog M0 M pc → Prop where
  | letzter (h : PCReach P O passes prog M0 Mmid pcmid) :
      SchrittImLauf P O passes prog M0 Mmid pcmid f M' pc' hs
        (PCReach.step Mmid M' pcmid pc' f h hs)
  | frueher {M'' : GenMaschine D} {pc'' : PCStand} {g : Faden}
      {M''' : GenMaschine D} {pc''' : PCStand}
      (h : PCReach P O passes prog M0 M'' pc'')
      (hs2 : PCSchritt P O passes prog M'' pc'' g M''' pc''')
      (hmem : SchrittImLauf P O passes prog M0 Mmid pcmid f M' pc' hs h) :
      SchrittImLauf P O passes prog M0 Mmid pcmid f M' pc' hs
        (PCReach.step M'' M''' pc'' pc''' g h hs2)


end Gabbro.Grammatik
