/- Part 4 of 9 of `Maschine` (split by instrumente/teile/lean-teilen.py; the umbrella `Maschine.lean` imports all parts). -/
import Grammatik.Kern.Semantik.Maschine.T3

namespace Gabbro.Grammatik

variable {D : Deklaration}
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

/-- One atom's carriers sit in its thread's program text. -/
theorem pcAtom_mem_carriers (prog : PCProg D) (f : Faden) (a : PCAtom D)
    (h : a ∈ prog f) (o : D.Tab ⊕ D.Glob) (ho : o ∈ a.carriers) :
    o ∈ prog.carriers f := by
  unfold PCProg.carriers
  rw [List.mem_flatMap]
  exact ⟨a, h, ho⟩

/-- The start machine names no marks: its run is empty. -/
theorem pcStart_markInv (prog : PCProg D) (sp : Speicher D) :
    PCMarkInv prog (GenStart sp) := by
  intro k f e hk m st hm
  have hnil : (GenStart sp).lauf = [] := rfl
  rw [hnil] at hk
  simp at hk

/-- The start machine touches no carriers: its run is empty. -/
theorem pcStart_carrierInv (prog : PCProg D) (sp : Speicher D) :
    PCCarrierInv prog (GenStart sp) := by
  intro k f e hk o ho
  have hnil : (GenStart sp).lauf = [] := rfl
  rw [hnil] at hk
  simp at hk

/-- A PC step preserves the mark invariant: old positions keep it, new positions
    carry the pointed-to atom's footprint into its thread's program text. -/
theorem pcSchritt_markInv (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M M' : GenMaschine D) (pc pc' : PCStand) (f : Faden)
    (hs : PCSchritt P O passes prog M pc f M' pc')
    (hinv : PCMarkInv prog M) : PCMarkInv prog M' := by
  rcases hs with ⟨_V, _l, _Γ, _Λ, _Λ', _s, _ρ, _hleaf, _hΛ, _σ', neu, _hstep, _hneu, _hkn, Λa, cs, hpc, _hΛa, hmark, _hcar⟩ |
    ⟨L, _hself, _hrang, _hfrei, _hpc⟩ | ⟨L, _hhaelt, _hpc⟩
  · intro k f' e hk m st hm
    have hkred : (M.lauf ++ genEigen f neu)[k]? = some (Schritt.mk f' e) := hk
    by_cases hkk : k < M.lauf.length
    · rw [List.getElem?_append_left hkk] at hkred
      exact hinv k f' e hkred m st hm
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hkk)] at hkred
      obtain ⟨rfl, hmem⟩ := gen_eigen_getElem f neu _ _ _ hkred
      have hfoot := hmark e hmem m st hm
      have ha : PCAtom.leaf Λa cs ∈ prog f' := List.mem_of_getElem? hpc
      exact pcAtom_mem_marks prog f' _ ha m hfoot
  · intro k f' e hk m st hm
    have hkred : (M.lauf ++ genEigen f [Ereignis.nimmt L (offen (M.spuren f))])[k]? =
        some (Schritt.mk f' e) := hk
    by_cases hkk : k < M.lauf.length
    · rw [List.getElem?_append_left hkk] at hkred
      exact hinv k f' e hkred m st hm
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hkk)] at hkred
      obtain ⟨rfl, hmem⟩ := gen_eigen_getElem f [_] _ _ _ hkred
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hlam : (Ereignis.nimmt L (offen (M.spuren f'))).lambda = [] := rfl
      rw [hlam] at hm
      simp at hm
  · intro k f' e hk m st hm
    have hkred : (M.lauf ++ genEigen f [Ereignis.gibt L])[k]? =
        some (Schritt.mk f' e) := hk
    by_cases hkk : k < M.lauf.length
    · rw [List.getElem?_append_left hkk] at hkred
      exact hinv k f' e hkred m st hm
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hkk)] at hkred
      obtain ⟨rfl, hmem⟩ := gen_eigen_getElem f [_] _ _ _ hkred
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hlam : (Ereignis.gibt L).lambda = [] := rfl
      rw [hlam] at hm
      simp at hm

/-- A PC step preserves the carrier invariant: old positions keep it, new
    positions carry the pointed-to atom's carrier set into its thread's text. -/
theorem pcSchritt_carrierInv (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M M' : GenMaschine D) (pc pc' : PCStand) (f : Faden)
    (hs : PCSchritt P O passes prog M pc f M' pc')
    (hinv : PCCarrierInv prog M) : PCCarrierInv prog M' := by
  rcases hs with ⟨_V, _l, _Γ, _Λ, _Λ', _s, _ρ, _hleaf, _hΛ, _σ', neu, _hstep, _hneu, _hkn, Λa, cs, hpc, _hΛa, _hmark, hcar⟩ |
    ⟨L, _hself, _hrang, _hfrei, _hpc⟩ | ⟨L, _hhaelt, _hpc⟩
  · intro k f' e hk o ho
    have hkred : (M.lauf ++ genEigen f neu)[k]? = some (Schritt.mk f' e) := hk
    by_cases hkk : k < M.lauf.length
    · rw [List.getElem?_append_left hkk] at hkred
      exact hinv k f' e hkred o ho
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hkk)] at hkred
      obtain ⟨rfl, hmem⟩ := gen_eigen_getElem f neu _ _ _ hkred
      have hfoot := hcar e hmem o ho
      have ha : PCAtom.leaf Λa cs ∈ prog f' := List.mem_of_getElem? hpc
      exact pcAtom_mem_carriers prog f' _ ha o hfoot
  · intro k f' e hk o ho
    have hkred : (M.lauf ++ genEigen f [Ereignis.nimmt L (offen (M.spuren f))])[k]? =
        some (Schritt.mk f' e) := hk
    by_cases hkk : k < M.lauf.length
    · rw [List.getElem?_append_left hkk] at hkred
      exact hinv k f' e hkred o ho
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hkk)] at hkred
      obtain ⟨rfl, hmem⟩ := gen_eigen_getElem f [_] _ _ _ hkred
      simp only [List.mem_singleton] at hmem
      cases hmem
      have htr : (Ereignis.nimmt L (offen (M.spuren f'))).traeger = none := rfl
      rw [htr] at ho
      cases ho
  · intro k f' e hk o ho
    have hkred : (M.lauf ++ genEigen f [Ereignis.gibt L])[k]? =
        some (Schritt.mk f' e) := hk
    by_cases hkk : k < M.lauf.length
    · rw [List.getElem?_append_left hkk] at hkred
      exact hinv k f' e hkred o ho
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hkk)] at hkred
      obtain ⟨rfl, hmem⟩ := gen_eigen_getElem f [_] _ _ _ hkred
      simp only [List.mem_singleton] at hmem
      cases hmem
      have htr : (Ereignis.gibt L).traeger = none := rfl
      rw [htr] at ho
      cases ho

/-- Every PC-reachable machine maintains the mark invariant. -/
theorem pcReach_markInv (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc) : PCMarkInv prog M := by
  induction h with
  | start => exact pcStart_markInv prog sp
  | step M M' pc pc' f _ hs ih =>
      exact pcSchritt_markInv P O passes prog M M' pc pc' f hs ih

/-- Every PC-reachable machine maintains the carrier invariant. -/
theorem pcReach_carrierInv (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc) : PCCarrierInv prog M := by
  induction h with
  | start => exact pcStart_carrierInv prog sp
  | step M M' pc pc' f _ hs ih =>
      exact pcSchritt_carrierInv P O passes prog M M' pc pc' f hs ih

/-- A projected mark naming comes from a program-text mark. -/
theorem markenProj_marke (code : D.Marke → Nat) (m : D.Marke) (st : Nat)
    (c s : Nat)
    (h : markenProj code (Res.marke m st) = Marken.Res.marke c s) :
    code m = c := by
  have h2 : Marken.Res.marke (code m) st = Marken.Res.marke c s := h
  cases h2
  rfl

/-- A lock naming is never a mark naming. -/
theorem markenProj_held_absurd (code : D.Marke → Nat) (L : D.Lock) (c s : Nat)
    (h : markenProj code (Res.held L) = Marken.Res.marke c s) : False := by
  have h2 : Marken.Res.held = Marken.Res.marke c s := h
  cases h2

/-- **The discharge fragment: program counters discharge `hEin`.** If no mark
    code is named by two threads' program texts, the projected run is
    single-threaded: which mark a thread holds follows from where its program
    stands (`PCMarkInv`), and separation over codes turns two namings into one
    thread. This replaces the `Einfaedig` projection premise. -/
theorem pc_discharge_einfaedig (code : D.Marke → Nat) (prog : PCProg D)
    (M : GenMaschine D)
    (hinv : PCMarkInv prog M)
    (hSep : PCMarkSep code prog) :
    Marken.Einfaedig (laufProj code M.lauf) := by
  intro i j f g c s s' ei ej hi hj hmi hmj
  unfold laufProj at hi hj
  rw [List.getElem?_map] at hi hj
  cases hxi : M.lauf[i]? with
  | none =>
      rw [hxi] at hi
      simp at hi
  | some si =>
      rw [hxi] at hi
      cases hxj : M.lauf[j]? with
      | none =>
          rw [hxj] at hj
          simp at hj
      | some sj =>
          rw [hxj] at hj
          cases si with
          | mk fi ei' =>
              cases sj with
              | mk fj ej' =>
                  have hi2 : schrittProj code (Schritt.mk fi ei') =
                      Marken.Schritt.mk f ei := by
                    simpa using hi
                  have hj2 : schrittProj code (Schritt.mk fj ej') =
                      Marken.Schritt.mk g ej := by
                    simpa using hj
                  obtain ⟨rfl, rfl⟩ := hi2
                  obtain ⟨rfl, rfl⟩ := hj2
                  have hli : (ereignisProj code ei').lambda =
                      ei'.lambda.map (markenProj code) := rfl
                  have hlj : (ereignisProj code ej').lambda =
                      ej'.lambda.map (markenProj code) := rfl
                  rw [hli] at hmi
                  rw [hlj] at hmj
                  obtain ⟨ri, hri, hreqi⟩ := List.mem_map.mp hmi
                  obtain ⟨rj, hrj, hreqj⟩ := List.mem_map.mp hmj
                  cases ri with
                  | held L =>
                      exact (markenProj_held_absurd code L c s hreqi).elim
                  | marke mi sti =>
                      cases rj with
                      | held L =>
                          exact (markenProj_held_absurd code L c s' hreqj).elim
                      | marke mj stj =>
                          have hci : code mi = c :=
                            markenProj_marke code mi sti c s hreqi
                          have hcj : code mj = c :=
                            markenProj_marke code mj stj c s' hreqj
                          have hfi : mi ∈ prog.marks fi :=
                            hinv i fi ei' hxi mi sti hri
                          have hfj : mj ∈ prog.marks fj :=
                            hinv j fj ej' hxj mj stj hrj
                          have hmemF : c ∈ (prog.marks fi).map code :=
                            List.mem_map.mpr ⟨mi, hfi, hci⟩
                          have hmemG : c ∈ (prog.marks fj).map code :=
                            List.mem_map.mpr ⟨mj, hfj, hcj⟩
                          by_cases hfg : fi = fj
                          · exact hfg
                          · exact absurd hmemG (hSep fi fj hfg c hmemF)

/-- **W4 on PC runs, same shape as `Gesittet.marke_eindeutig`.** The discharge
    fragment through the construction bridge: no projection premise. -/
theorem pc_marke_eindeutig (code : D.Marke → Nat) (prog : PCProg D)
    (M : GenMaschine D)
    (hinv : PCMarkInv prog M)
    (hSep : PCMarkSep code prog)
    (i j : Nat) (f g : Faden) (m : D.Marke) (s s' : Nat)
    (ei ej : Ereignis D)
    (hi : M.lauf[i]? = some (Schritt.mk f ei))
    (hj : M.lauf[j]? = some (Schritt.mk g ej))
    (hmi : Res.marke m s ∈ ei.lambda)
    (hmj : Res.marke m s' ∈ ej.lambda) : f = g :=
  marke_eindeutig_aus_einfaedig code M.lauf
    (pc_discharge_einfaedig code prog M hinv hSep) i j f g m s s' ei ej hi hj hmi hmj

/-- **The declaration side discharges from program text.** If an unshared
    carrier is accessed from two threads, both threads' texts reach it --
    against `PCUnsharedSep`. This replaces the `hungeteilt` declaration side.
    The shared-side hypothesis comes before the access equations: a `match` on
    `o` elaborates extra discriminants for hypotheses that already mention `o`,
    so the match must precede them to keep the `Gesittet` shape. -/
theorem pc_discharge_unshared (prog : PCProg D) (M : GenMaschine D)
    (hinv : PCCarrierInv prog M)
    (hSep : PCUnsharedSep prog)
    (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob)
    (ei ej : Ereignis D)
    (hi : M.lauf[i]? = some (Schritt.mk f ei))
    (hj : M.lauf[j]? = some (Schritt.mk g ej))
    (hsh : match o with
      | .inl t => D.geteilt t = false
      | .inr x => D.ggeteilt x = false)
    (hti : ei.traeger = some o) (htj : ej.traeger = some o) :
    f = g := by
  have hfi : o ∈ prog.carriers f := hinv i f ei hi o hti
  have hgj : o ∈ prog.carriers g := hinv j g ej hj o htj
  by_cases hfg : f = g
  · exact hfg
  · exact ((hSep f g hfg o hfi hgj) hsh).elim

/-- **W1, W2, W4 on PC runs, with no projection premise.** W1+W2 come from the
    generated side through the projection; W4 comes from the program text
    through the discharge fragment. Same triple shape as `gen_w1w2w4`. -/
theorem pc_w1w2w4 (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc)
    (code : D.Marke → Nat) (hMSep : PCMarkSep code prog) :
    (∀ f j, Konsistent (M.lauf.spur f j)) ∧
    (∀ f j (e : Ereignis D), e ∈ M.lauf.spur f j → e.gut) ∧
    (∀ (i j : Nat) (f g : Faden) (m : D.Marke) (s s' : Nat) (ei ej : Ereignis D),
      M.lauf[i]? = some (Schritt.mk f ei) → M.lauf[j]? = some (Schritt.mk g ej) →
      Res.marke m s ∈ ei.lambda → Res.marke m s' ∈ ej.lambda → f = g) := by
  refine ⟨pc_konsistent P O passes hO prog sp M pc h,
    pc_gut_obs P O passes hO prog sp M pc h, ?_⟩
  intro i j f g m s s' ei ej hi hj hmi hmj
  exact pc_marke_eindeutig code prog M
    (pcReach_markInv P O passes prog sp M pc h) hMSep
    i j f g m s s' ei ej hi hj hmi hmj

/-- **A PC run is `Gesittet`, with neither premise.** W1-W3 are generated, W4 is
    discharged from program text, W5 from carrier separation. -/
theorem pc_gesittet (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc)
    (code : D.Marke → Nat) (hMSep : PCMarkSep code prog)
    (hCSep : PCUnsharedSep prog) :
    Gesittet M.lauf :=
  gesittet_aus_einfaedig M.lauf
    (pc_konsistent P O passes hO prog sp M pc h)
    (pc_gut_obs P O passes hO prog sp M pc h)
    (pc_ausschluss P O passes hO prog sp M pc h)
    code
    (pc_discharge_einfaedig code prog M
      (pcReach_markInv P O passes prog sp M pc h) hMSep)
    (fun i j f g o ei ej hi hj hti htj hsh =>
      pc_discharge_unshared prog M
        (pcReach_carrierInv P O passes prog sp M pc h) hCSep
        i j f g o ei ej hi hj hsh hti htj)

/-- **Reduction, serial order, from a PC run (two-access single-carrier
    fragment).** Same interface as `gen_reduktion`: two conflicting accesses in
    a PC run are happens-before ordered, in one direction or the other. Closes
    via `reduktion_seriell` with `Gesittet` derived from positions. -/
theorem pc_reduktion (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc)
    (code : D.Marke → Nat) (hMSep : PCMarkSep code prog)
    (hCSep : PCUnsharedSep prog)
    (t₀ : D.Tab) (g₁ g₂ : Faden) (hne : g₁ ≠ g₂)
    (j₁ j₂ : Nat) (w₁ w₂ : Bool) (Λ₁ Λ₂ : List (Res D)) (h₁ h₂ : List D.Lock)
    (hw₁ : M.lauf[j₁]? = some (Schritt.mk g₁ (.zugriff t₀ w₁ Λ₁ h₁)))
    (hw₂ : M.lauf[j₂]? = some (Schritt.mk g₂ (.zugriff t₀ w₂ Λ₂ h₂))) :
    HB M.lauf j₁ j₂ ∨ HB M.lauf j₂ j₁ :=
  reduktion_seriell M.lauf
    (pc_gesittet P O passes hO prog sp M pc h code hMSep hCSep)
    t₀ g₁ g₂ hne j₁ j₂ w₁ w₂ Λ₁ Λ₂ h₁ h₂ hw₁ hw₂

#print axioms Gabbro.Grammatik.pcAdvance_self
#print axioms Gabbro.Grammatik.pcAdvance_noteq
#print axioms Gabbro.Grammatik.pcSchritt_gen
#print axioms Gabbro.Grammatik.pcReach_gen
#print axioms Gabbro.Grammatik.pcSchritt_eigen
#print axioms Gabbro.Grammatik.pcSchritt_fremd
#print axioms Gabbro.Grammatik.pc_konsistent
#print axioms Gabbro.Grammatik.pc_gut_obs
#print axioms Gabbro.Grammatik.pc_ausschluss
#print axioms Gabbro.Grammatik.pcAtom_mem_marks
#print axioms Gabbro.Grammatik.pcAtom_mem_carriers
#print axioms Gabbro.Grammatik.pcStart_markInv
#print axioms Gabbro.Grammatik.pcStart_carrierInv
#print axioms Gabbro.Grammatik.pcSchritt_markInv
#print axioms Gabbro.Grammatik.pcSchritt_carrierInv
#print axioms Gabbro.Grammatik.pcReach_markInv
#print axioms Gabbro.Grammatik.pcReach_carrierInv
#print axioms Gabbro.Grammatik.markenProj_marke
#print axioms Gabbro.Grammatik.markenProj_held_absurd
#print axioms Gabbro.Grammatik.pc_discharge_einfaedig
#print axioms Gabbro.Grammatik.pc_marke_eindeutig
#print axioms Gabbro.Grammatik.pc_discharge_unshared
#print axioms Gabbro.Grammatik.pc_w1w2w4
#print axioms Gabbro.Grammatik.pc_gesittet
#print axioms Gabbro.Grammatik.pc_reduktion

end Gabbro.Grammatik

/-! ## 13. The chain-machine link: generated PC worlds read as chain worlds

    `SerialLink` (§22 of `InterferenzAllgemein.lean`) is the ORDER side of the
    run-to-chain link: every writing chain step owns a witness access in the
    run. This section is the WORLD side: a generated PC run's world history
    `M.welten` read as the chain worlds `J.welten`.

    Import check (no cycle): `GemeinsamerLauf` and `SerialLink` already arrive
    through `Grammatik.InterferenzAllgemein` and `Nebeneinander` through
    `Grammatik.Wettlauf` (the two imports at the head of this file), so this
    section adds no import.

    What is proved (`kette_ist_maschinenwelt` below, no `sorry`): under the
    explicit identification `J.welten = M.welten`, the chain worlds inherit
    everything the generated side proves about its history -- the count
    (`genWelten_laenge`), good observations (`genWelten_gut`), and the live
    end-world shape (`genWelten_letzte`) -- projected through `pcReach_gen`.
    Every premise is load-bearing: `P O passes hO prog sp M pc h` feed the
    projection and the three world lemmas, `J` types the identification and the
    conclusion, and `hW` rewrites each conjunct onto the generated history.

    Coverage (exactly): boundary observations only -- length, goodness, and end
    shape of the world list. The full equivalence (deriving the identification
    itself from step correspondence: chain steps close over whole bodies via
    `exec` while machine steps close over leaf statements via `execStmt`, plus
    the `Nb`/`Gesittet` wiring and the `SerialLink` witnesses) is NOT built.

    Remainder (booked, not hidden): constructing a `GemeinsamerLauf` from a
    `PCReach` run (or the converse) without assuming `hW`; per-step `Rahmen`
    correspondence between chain steps and machine micro-steps; lifting
    `SerialLink` witnesses to that constructed chain.
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **The chain-machine link, boundary-observation fragment.** A generated PC
    run's worlds read as chain worlds: identified histories share the count,
    the observations, and the end shape. One direction only (machine to chain,
    under explicit identification); see §13 for the remainder. -/
theorem kette_ist_maschinenwelt (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc)
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (hW : J.welten = M.welten) :
    J.welten.length = M.tiefe + 1 ∧
    (∀ W ∈ J.welten, ∀ e ∈ W.spur, e.gut) ∧
    (∃ f, J.welten.getLast? = some (M.speicher.welt (M.spuren f))) := by
  have hG : GenErreichbar P O passes (GenStart sp) M :=
    pcReach_gen P O passes prog (GenStart sp) M pc h
  refine ⟨?_, ?_, ?_⟩
  · rw [hW]
    exact genWelten_laenge P O passes hO sp M hG
  · rw [hW]
    exact genWelten_gut P O passes hO sp M hG
  · rw [hW]
    exact genWelten_letzte P O passes hO sp M hG

#print axioms Gabbro.Grammatik.kette_ist_maschinenwelt

end Gabbro.Grammatik

/-! ## 14. The chain from the machine: identification by construction

    `kette_ist_maschinenwelt` (§13) reads machine worlds as chain worlds UNDER
    the assumed identification `hW : J.welten = M.welten`. This section derives
    the identification itself -- however narrow -- instead of assuming it.

    What is proved (no `sorry`):

    - `kette_aus_maschinenlauf`: the zero-step base. From shared memory `sp`
      and one function entry `fn0`, the start machine `GenStart sp` IS a
      chain: worlds, run, and `SerialLink` come along by construction, so the
      identification `J.welten = M.welten` holds by `rfl`, never assumed.
      `SerialLink` holds vacuously: a chain with no steps has no writing step
      that could owe a witness.
    - `kette_aus_maschinenlauf_schritt`: one induction step over a
      memory-preserving machine step. From a chain `J` tracking `M` (the
      world history `hJw`, a member thread `hmem`, the inherited link `hLink`)
      and a successor `M'` whose worlds append one memory-preserving world
      (`hM'w` with `hslots` / `hglobs`) and whose run appends one step of `f`
      (`hM'l`), the extended chain tracks `M'`, again by construction
      (`rfl`). `Gesittet` and the scheduler rule for the extended run come
      from the read-only projection theorems (`gen_konsistent`,
      `gen_gut_obs`, `gen_ausschluss`); ownership (`marke_eindeutig`,
      `ungeteilt`) and the declaration side (`BeschraenkteVerschraenkung`)
      come from the single-thread premise (`hsingle`): every run step is
      `f`'s, so distinct-thread conclusions close by arithmetic. The frame
      (`hSchritt`) for the new step holds for ANY writer frame because lock
      steps keep slots and globals by construction -- no `exec` / `execStmt`
      correspondence is needed at this boundary. `SerialLink` is inherited
      along the old steps (witness indices transport over the run prefix) and
      vacuous at the new step under the non-writer guard.
    - `kette_aus_maschinenlauf_nimmt` / `_gibt`: the two lock-step
      instantiations, via the `GenSchritt` constructors as evidence.

    Read-only inputs, never modified: `gen_konsistent`, `gen_gut_obs`,
    `gen_ausschluss`, `genWelten_letzte`, `gen_eigen_getElem`, `GenStart`,
    `GenSchritt.nimmt`, `GenSchritt.gibt`. Every premise is load-bearing
    (each one is consumed by its proof; the old run-link `J.l = M.lauf` is
    deliberately NOT taken as a premise because the run side rebuilds from
    the projection theorems instead of transporting).

    Coverage (exactly): the start machine, plus one single-thread lock step
    (`nimmt` / `gibt`) by a member thread, with `SerialLink` vacuous at the
    base and guarded-vacuous at the new step.

    Remainder (booked, not hidden): `blatt` steps -- the `execStmt` frame is
    for the statement's own contract, while `hSchritt` needs the code
    function's writes (`Nb` / code wiring, as §13 books it); iterating the
    step over a whole `PCReach` (counter routing via `pcSchritt_gen` /
    `pcReach_gen` stays future work); multi-thread runs (discharging
    `hsingle` needs the `Einfaedig` projection plus the declaration side, as
    `gen_gesittet` books them); non-vacuous `SerialLink` witnesses for
    writing steps; globals and multi-carrier conflicts (as before).
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}


end Gabbro.Grammatik
