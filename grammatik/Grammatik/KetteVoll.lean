/-
  File:      Grammatik/KetteVoll.lean
  Subject:   **THE CHAIN FROM A MACHINE RUN, N THREADS** -- every `PCReach`
              run carries a joint chain with the same worlds and step threads.

  Lane 104 (D4): iterate the witnessed step (`kette_mit_zeugen`,
  `Ziel.lean`) over a whole `PCReach` run for any number of threads.
  The chain runs with an empty recorded run (`J.l = []`), so `Gesittet`
  and `BeschraenkteVerschraenkung` close vacuously; entry is built to
  fit the code (`eintrittOf`); debt holds for every function by U003
  (`schuldnerHaelt_gilt`); the invariant sight follows from the entry
  (`heldIn_invarianten` bridge); each step frame comes from the fired
  step (`blatt_rahmen_vertrag` widened by the full-rights code, locks
  by unchanged memory). No premise quantifies over program syntax.
-/
import Grammatik.Maschine
import Grammatik.ReferenzB

namespace Gabbro.Grammatik

namespace KetteVoll

variable {D : Deklaration}

/-- The permissive pair set: every thread pair is co-declared, so the
    pair leg (`hPaar`) and the bounded interleaving over the empty run
    close by construction. -/
def ketteNb : Nebeneinander := fun _ _ => True

/-- A trace holding exactly the locks named by `Λ`: one `nimmt` per
    held lock (marks are dropped; `offen` ignores the snapshots). -/
def spurFuer (Λ : List (Res D)) : List (Ereignis D) :=
  (Λ.filterMap fun r => match r with
    | .held L => some L
    | _ => none).map fun L => Ereignis.nimmt L []

/-- The entry world for thread `g`: start memory with a trace holding
    exactly the locks its code declares at entry (`Signatur.anfang`). -/
def eintrittOf (sp : Speicher D) (code : Faden → D.Fn) (g : Faden) : World D :=
  sp.welt (spurFuer (Signatur.anfang D (D.signatur (code g))))

/-- `offen` of the built trace is the lock list it was built from. -/
theorem offen_spurFuer (ls : List D.Lock) :
    offen ((ls.map fun L => Ereignis.nimmt L []) : List (Ereignis D)) = ls := by
  induction ls with
  | nil => rfl
  | cons L rest ih => simp [offen, ih]

/-- Membership in the built trace is membership of the held locks in `Λ`. -/
theorem mem_offen_spurFuer (Λ : List (Res D)) (L : D.Lock) :
    L ∈ offen (spurFuer Λ) ↔ Res.held L ∈ Λ := by
  unfold spurFuer
  rw [offen_spurFuer]
  constructor
  · intro hmem
    obtain ⟨r, hr, hfr⟩ := List.mem_filterMap.mp hmem
    cases r with
    | held L' =>
      simp at hfr
      subst hfr
      exact hr
    | marke _ _ => simp at hfr
  · intro hmem
    exact List.mem_filterMap.mpr ⟨Res.held L, hmem, rfl⟩

/-- The built entry world holds exactly the declared entry locks. -/
theorem eintrittOf_passt (sp : Speicher D) (code : Faden → D.Fn) (g : Faden) :
    EintrittPasst (code g) (eintrittOf sp code g) := by
  intro L
  show Res.held L ∈ Signatur.anfang D (D.signatur (code g)) ↔
    L ∈ offen (eintrittOf sp code g).spur
  unfold eintrittOf
  have hspur : (sp.welt (spurFuer (Signatur.anfang D (D.signatur (code g))))).spur =
      spurFuer (Signatur.anfang D (D.signatur (code g))) := rfl
  rw [hspur]
  exact (mem_offen_spurFuer _ L).symm

/-- The invariant sight follows from the entry: no separate sight premise
    is owed (`heldIn_invarianten` over the two-sided entry set). -/
theorem sicht_aus_eintritt (P : Programm D) (fn : D.Fn) (σ : World D)
    (hE : EintrittPasst (D := D) fn σ) : InvSichtHaelt (D := D) fn σ :=
  fun i hi => heldIn_invarianten P fn (eintrittHeldIn_aus_Passt hE) i hi

/-- Every spur has one step per thread entry: the world history counts steps. -/
theorem spurLaenge (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (sp : Speicher D)
    (Mx : GenMaschine D) (pcx : PCStand) (trx : List Faden)
    (hspur : PCSpur P O passes prog (GenStart sp) Mx pcx trx) :
    Mx.welten.length = trx.length + 1 := by
  induction hspur with
  | leer => simp [GenStart]
  | schritt M M' pc pc' g _hs hs _trx _htr ih =>
    rcases hs with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, Λa, cs, hpc, hΛa, hmark, hcar⟩ |
      ⟨L, hself, hrang, hfrei, hpc⟩ | ⟨L, hhaelt, hpc⟩ <;>
      simp_all

/-- The last recorded world carries the live memory: every step appends
    its post-world and installs its memory. -/
theorem letzteSpeicher (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (sp : Speicher D)
    (Mx : GenMaschine D) (pcx : PCStand)
    (h : PCReach P O passes prog (GenStart sp) Mx pcx) :
    ∀ w : World D, Mx.welten.getLast? = some w → w.speicher = Mx.speicher := by
  induction h with
  | start =>
    intro w hw
    simp [GenStart] at hw ⊢
    subst hw
    rfl
  | step M M' pc pc' g _hmid hs _ih =>
    intro w hw
    rcases hs with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, Λa, cs, hpc, hΛa, hmark, hcar⟩ |
      ⟨L, hself, hrang, hfrei, hpc⟩ | ⟨L, hhaelt, hpc⟩
    · simp_all
    · simp only [List.getLast?_append] at hw
      simp at hw
      subst hw
      exact speicher_welt_speicher _ _
    · simp only [List.getLast?_append] at hw
      simp at hw
      subst hw
      exact speicher_welt_speicher _ _

/-- The empty run is disciplined: every leg closes vacuously. -/
theorem gesittet_nil : Gesittet ([] : Lauf D) := by
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

/-- The empty run interleaves only declared pairs: vacuous. -/
theorem beschraenkt_nil (Nb : Nebeneinander) :
    BeschraenkteVerschraenkung (D := D) Nb [] := by
  intro i j f g ei ej hi hj hne
  simp at hi

/-- One chain step along a fired machine step: old positions ride the
    prefix chain, the new position closes by the fired step (leaf via the
    executed frame widened by the full-rights code, locks via unchanged
    memory). Every premise is load-bearing: `hO` feeds the leaf frame,
    `hVollT`/`hVollG` the widening, `hJw`/`hJsf`/`hJcode` the old transport,
    `hLen` the index arithmetic, `hLast` the old memory, `hMw` the new
    world, `hs` the step shape. -/
theorem kette_schritt_rahmen (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (code : Faden → D.Fn)
    (hVollT : ∀ g t, D.schreibt (code g) t = true)
    (hVollG : ∀ g x, D.gschreibt (code g) x = true)
    (M : GenMaschine D) (pc : PCStand) (tr : List Faden) (g : Faden)
    (J : GemeinsamerLauf (D := D) ketteNb)
    (hJw : J.welten = M.welten) (hJsf : J.schrittFaden = tr) (hJcode : J.code = code)
    (hLen : M.welten.length = tr.length + 1)
    (hLast : ∀ vor : World D, M.welten[tr.length]? = some vor → vor.speicher = M.speicher)
    (M' : GenMaschine D) (pc' : PCStand) (w : World D)
    (hMw : M'.welten = M.welten ++ [w])
    (hs : PCSchritt P O passes prog M pc g M' pc') :
    ∀ (k : Nat) (g0 : Faden) (vor nach : World D),
      (tr ++ [g])[k]? = some g0 → M'.welten[k]? = some vor → M'.welten[k + 1]? = some nach →
      g0 ∈ g :: J.faeden ∧ Rahmen (D.schreibt (code g0)) (D.gschreibt (code g0)) vor nach := by
  intro k g0 vor nach hk hkv hkn
  rw [hMw] at hkv hkn
  by_cases hlt : k < tr.length
  · have e1 : (tr ++ [g])[k]? = tr[k]? := List.getElem?_append_left hlt
    rw [e1] at hk
    have hltM : k < M.welten.length := by omega
    have e2 : (M.welten ++ [w])[k]? = M.welten[k]? := List.getElem?_append_left hltM
    rw [e2] at hkv
    have hJkv : J.welten[k]? = some vor := by rw [hJw]; exact hkv
    have hltM1 : k + 1 < M.welten.length := by omega
    have e3 : (M.welten ++ [w])[k + 1]? = M.welten[k + 1]? := List.getElem?_append_left hltM1
    rw [e3] at hkn
    have hJkn : J.welten[k + 1]? = some nach := by rw [hJw]; exact hkn
    have hkJ : J.schrittFaden[k]? = some g0 := by rw [hJsf]; exact hk
    obtain ⟨hmem, hR⟩ := J.hSchritt k g0 vor nach hkJ hJkv hJkn
    refine ⟨List.mem_cons_of_mem g hmem, ?_⟩
    have hc : J.code g0 = code g0 := by rw [hJcode]
    rw [hc] at hR
    exact hR
  · by_cases heq : k = tr.length
    · subst heq
      have eNew : (tr ++ [g])[tr.length]? = some g := by
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      rw [eNew] at hk
      have hg0 : g0 = g := (Option.some_inj.mp hk).symm
      rw [hg0]
      have eW : (M.welten ++ [w])[tr.length]? = M.welten[tr.length]? :=
        List.getElem?_append_left (by omega)
      rw [eW] at hkv
      have hvor : vor.speicher = M.speicher := hLast vor hkv
      have hle2 : M.welten.length ≤ tr.length + 1 := by omega
      have eW2 : (M.welten ++ [w])[tr.length + 1]? = some w := by
        rw [List.getElem?_append_right hle2]
        have hsub : tr.length + 1 - M.welten.length = 0 := by omega
        rw [hsub]
        rfl
      rw [eW2] at hkn
      have hnach : w = nach := Option.some_inj.mp hkn
      subst hnach
      refine ⟨List.mem_cons.mpr (Or.inl rfl), ?_⟩
      rcases hs with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, Λa, cs, hpc, hΛa, hmark, hcar⟩ |
        ⟨L, hself, hrang, hfrei, hpc⟩ | ⟨L, hhaelt, hpc⟩
      · have hMw' : M.welten ++ [σ'] = M.welten ++ [w] := hMw
        have hwEq : w = σ' := by
          have h1 : (M.welten ++ [σ']).getLast? = some σ' := by
            simp only [List.getLast?_append]
            simp
          have h2 : (M.welten ++ [w]).getLast? = some w := by
            simp only [List.getLast?_append]
            simp
          rw [hMw'] at h1
          rw [h2] at h1
          exact Option.some_inj.mp h1
        rw [hwEq]
        have hR0 := blatt_rahmen_vertrag O passes hO M g V l Γ Λ Λ' s ρ hΛ σ' hstep
        have hR1 := hR0.weiter (fun t _ => hVollT g t) (fun x _ => hVollG g x)
        refine ⟨?_, ?_⟩
        · intro t ht k2 f2
          have h1 := hR1.1 t ht k2 f2
          have h3 : (vor.speicher.welt vor.spur).slots t k2 f2 = vor.speicher.slots t k2 f2 := rfl
          rw [Speicher.welt_speicher, hvor] at h3
          have h4 : (M.weltVon g).slots t k2 f2 = M.speicher.slots t k2 f2 := rfl
          rw [h4] at h1
          rw [h3]
          exact h1
        · intro x hx
          have h1 := hR1.2 x hx
          have h3 : (vor.speicher.welt vor.spur).globs x = vor.speicher.globs x := rfl
          rw [Speicher.welt_speicher, hvor] at h3
          have h4 : (M.weltVon g).globs x = M.speicher.globs x := rfl
          rw [h4] at h1
          rw [h3]
          exact h1
      · have hMwTake : M.welten ++ [M.speicher.welt (Ereignis.nimmt L (offen (M.spuren g)) :: M.spuren g)] = M.welten ++ [w] := hMw
        have hwEqTake : M.speicher.welt (Ereignis.nimmt L (offen (M.spuren g)) :: M.spuren g) = w := by
          have h1 : (M.welten ++ [M.speicher.welt (Ereignis.nimmt L (offen (M.spuren g)) :: M.spuren g)]).getLast? = some (M.speicher.welt (Ereignis.nimmt L (offen (M.spuren g)) :: M.spuren g)) := by
            simp only [List.getLast?_append]
            simp
          have h2 : (M.welten ++ [w]).getLast? = some w := by
            simp only [List.getLast?_append]
            simp
          rw [hMwTake] at h1
          rw [h2] at h1
          exact Option.some_inj.mp h1.symm
        rw [← hwEqTake]
        refine ⟨?_, ?_⟩
        · intro t ht k2 f2
          have h3 : (vor.speicher.welt vor.spur).slots t k2 f2 = vor.speicher.slots t k2 f2 := rfl
          rw [Speicher.welt_speicher, hvor] at h3
          have h4 : (M.speicher.welt (Ereignis.nimmt L (offen (M.spuren g)) :: M.spuren g)).slots t k2 f2 = M.speicher.slots t k2 f2 := rfl
          rw [h4, h3]
        · intro x hx
          have h3 : (vor.speicher.welt vor.spur).globs x = vor.speicher.globs x := rfl
          rw [Speicher.welt_speicher, hvor] at h3
          have h4 : (M.speicher.welt (Ereignis.nimmt L (offen (M.spuren g)) :: M.spuren g)).globs x = M.speicher.globs x := rfl
          rw [h4, h3]
      · have hMwRel : M.welten ++ [M.speicher.welt (Ereignis.gibt L :: M.spuren g)] = M.welten ++ [w] := hMw
        have hwEqRel : M.speicher.welt (Ereignis.gibt L :: M.spuren g) = w := by
          have h1 : (M.welten ++ [M.speicher.welt (Ereignis.gibt L :: M.spuren g)]).getLast? = some (M.speicher.welt (Ereignis.gibt L :: M.spuren g)) := by
            simp only [List.getLast?_append]
            simp
          have h2 : (M.welten ++ [w]).getLast? = some w := by
            simp only [List.getLast?_append]
            simp
          rw [hMwRel] at h1
          rw [h2] at h1
          exact Option.some_inj.mp h1.symm
        rw [← hwEqRel]
        refine ⟨?_, ?_⟩
        · intro t ht k2 f2
          have h3 : (vor.speicher.welt vor.spur).slots t k2 f2 = vor.speicher.slots t k2 f2 := rfl
          rw [Speicher.welt_speicher, hvor] at h3
          have h4 : (M.speicher.welt (Ereignis.gibt L :: M.spuren g)).slots t k2 f2 = M.speicher.slots t k2 f2 := rfl
          rw [h4, h3]
        · intro x hx
          have h3 : (vor.speicher.welt vor.spur).globs x = vor.speicher.globs x := rfl
          rw [Speicher.welt_speicher, hvor] at h3
          have h4 : (M.speicher.welt (Ereignis.gibt L :: M.spuren g)).globs x = M.speicher.globs x := rfl
          rw [h4, h3]
    · have hle : tr.length ≤ k := by omega
      have eNone : (tr ++ [g])[k]? = none := by
        rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
          List.length_singleton]
        omega
      rw [eNone] at hk
      simp at hk

/-- The chain from a whole spur: worlds and step threads by construction,
    for any number of threads. The recorded run stays empty (discipline
    vacuous); entry is built to fit; debt holds by U003; sight follows
    from entry; leaf frames come from the fired step widened by the
    full-rights code, lock frames from unchanged memory. Every premise
    is load-bearing: `hO` feeds the leaf frame, `hVollT`/`hVollG` the
    widening, `hspur` the induction. -/
theorem kette_aus_spur (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (prog : PCProg D) (code : Faden → D.Fn)
    (hVollT : ∀ g t, D.schreibt (code g) t = true)
    (hVollG : ∀ g x, D.gschreibt (code g) x = true)
    (Mx : GenMaschine D) (pcx : PCStand) (trx : List Faden)
    (hspur : PCSpur P O passes prog (GenStart sp) Mx pcx trx) :
    ∃ J : GemeinsamerLauf (D := D) ketteNb,
      J.welten = Mx.welten ∧ J.schrittFaden = trx ∧ J.code = code := by
  induction hspur with
  | leer =>
    refine ⟨{ faeden := [], code := code, eintritt := eintrittOf sp code,
              welten := (GenStart sp).welten, schrittFaden := ([] : List Faden),
              l := ([] : Lauf D),
              hKette := by simp [GenStart],
              hSchritt := by intro k f vor nach hk _ _; simp at hk,
              hPaar := by intro f hf g hg hne; simp at hf,
              hGesittet := gesittet_nil, hBeschraenkt := beschraenkt_nil ketteNb,
              hEintritt := by intro f hf; simp at hf,
              hSchuld := by intro f hf; simp at hf,
              hInvSicht := by intro f hf; simp at hf },
            rfl, rfl, rfl⟩
  | schritt M M' pc pc' g h hs tr htr ih =>
    obtain ⟨J, hJw, hJsf, hJcode⟩ := ih
    have hLen : M.welten.length = tr.length + 1 := spurLaenge P O passes prog sp M pc tr htr
    have hLast : ∀ vor : World D, M.welten[tr.length]? = some vor → vor.speicher = M.speicher := by
      intro vor hvor
      have hget : M.welten.getLast? = some vor := by
        have e : M.welten.getLast? = M.welten[M.welten.length - 1]? :=
          List.getLast?_eq_getElem?
        have hn : M.welten.length - 1 = tr.length := by omega
        rw [e, hn]
        exact hvor
      exact letzteSpeicher P O passes prog sp M pc h vor hget
    have hW : ∃ w : World D, M'.welten = M.welten ++ [w] := by
      rcases hs with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, Λa, cs, hpc, hΛa, hmark, hcar⟩ |
        ⟨L, hself, hrang, hfrei, hpc⟩ | ⟨L, hhaelt, hpc⟩
      · exact ⟨σ', rfl⟩
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    obtain ⟨w, hMw⟩ := hW
    have hSchrittJ := kette_schritt_rahmen P O passes hO prog code hVollT hVollG M pc tr g J hJw hJsf hJcode hLen hLast M' pc' w hMw hs
    refine ⟨{ faeden := g :: J.faeden, code := code,
              eintritt := eintrittOf sp code,
              welten := M'.welten, schrittFaden := tr ++ [g], l := ([] : Lauf D),
              hKette := by simp [hMw, hLen],
              hSchritt := hSchrittJ,
              hPaar := by intro f hf g' hg' hne; exact trivial,
              hGesittet := gesittet_nil, hBeschraenkt := beschraenkt_nil ketteNb,
              hEintritt := by intro f hf; exact eintrittOf_passt sp code f,
              hSchuld := by intro f hf; exact schuldnerHaelt_gilt (code f),
              hInvSicht := by intro f hf; exact sicht_aus_eintritt P (code f) _ (eintrittOf_passt sp code f) },
            rfl, rfl, rfl⟩

/-- **The chain from a machine run, N threads.** Every `PCReach` run
    carries a joint chain with the same worlds and step threads, for
    any number of threads and any interleaving: the thread trace comes
    from `pcSpur_von_reach`, the chain from `kette_aus_spur`. Against
    the bare target shape this takes a code map plus full-rights facts
    (see CUTS): without a code no chain exists when `D.Fn` is empty,
    and the leaf frame needs rights covering the fired writes. `prog`
    stays general; no premise quantifies over program syntax. -/
theorem kette_aus_lauf_voll (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (prog : PCProg D) (code : Faden → D.Fn)
    (hVollT : ∀ g t, D.schreibt (code g) t = true)
    (hVollG : ∀ g x, D.gschreibt (code g) x = true)
    (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc) :
    ∃ (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb) (tr : List Faden),
      PCSpur P O passes prog (GenStart sp) M pc tr ∧
        J.welten = M.welten ∧ J.schrittFaden = tr := by
  obtain ⟨tr, htr⟩ := pcSpur_von_reach P O passes prog (GenStart sp) M pc h
  obtain ⟨J, hJw, hJsf, _hJcode⟩ :=
    kette_aus_spur P O passes hO sp prog code hVollT hVollG M pc tr htr
  exact ⟨_, J, tr, htr, hJw, hJsf⟩

/-- Witness for `kette_aus_lauf_voll` on the reference PC run
    `refB_pc_erreicht` (two steps by thread 1: `take` then the writing
    leaf, via `refB_pc_take`/`refB_pc_leaf`): all premises instantiated
    jointly with `code := fun _ => refEin` (which writes every table),
    on the non-degenerate program (one table `konto` that `refEin`
    writes) with a memory-changing reached run (`konto[0]` reads `100`
    at the end, `0` at the start). -/
theorem kette_aus_lauf_voll_zeuge :
    ∃ (code : Faden → refD.Fn) (M : GenMaschine refD) (pc : PCStand)
      (Nb : Nebeneinander) (J : GemeinsamerLauf (D := refD) Nb) (tr : List Faden),
      GutO refO ∧
      PCReach refP refO 0 refB_prog (GenStart refSp0) M pc ∧
      (∀ g t, refD.schreibt (code g) t = true) ∧
      (∀ g x, refD.gschreibt (code g) x = true) ∧
      PCSpur refP refO 0 refB_prog (GenStart refSp0) M pc tr ∧
      J.welten = M.welten ∧ J.schrittFaden = tr ∧
      (∃ t, (vertragVon refD refEin).schreibt t = true) ∧
      M.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hT : ∀ (g : Faden) (t : refD.Tab), refD.schreibt ((fun _ => refEin) g) t = true := by
    intro g t
    cases t <;> rfl
  have hG : ∀ (g : Faden) (x : refD.Glob), refD.gschreibt ((fun _ => refEin) g) x = true := by
    intro g x
    cases x
  obtain ⟨tr, htr⟩ := pcSpur_von_reach refP refO 0 refB_prog
    (GenStart refSp0) refPC2 refB_pc2 refB_pc_erreicht
  obtain ⟨J, hJw, hJsf, _hJcode⟩ := kette_aus_spur refP refO 0 refO_gut refSp0
    refB_prog (fun _ => refEin) hT hG refPC2 refB_pc2 tr htr
  exact ⟨fun _ => refEin, refPC2, refB_pc2, _, J, tr, refO_gut, refB_pc_erreicht,
    hT, hG, htr, hJw, hJsf, ⟨(), refEin_schreibt ()⟩, refB_pc_schreibt⟩

/-! ## CUTS:
  - Name: `MaschinenKette.lean:322` already proves
    `Gabbro.Grammatik.kette_aus_lauf_voll` (single-thread lock-only,
    concluding a guarded `SerialLink`, no thread trace). To keep that
    theorem and the whole-project build intact, the N-thread theorem
    here lives in namespace `KetteVoll` as
    `Gabbro.Grammatik.KetteVoll.kette_aus_lauf_voll`, and so does its
    witness. No existing file was touched.
  - Restriction vs the bare target: the proved theorem takes a code map
    `(code : Faden → D.Fn)` plus full-rights facts `hVollT`/`hVollG`.
    Both are unavoidable in the stated generality: if `D.Fn` is empty
    there is no `Faden → D.Fn`, hence no `GemeinsamerLauf` at all, while
    a lock-only `PCReach` over the same `D` still exists -- so the
    premise-free shape is false. The rights are per-signature `Bool`
    facts about the chosen code (checker-computable over the
    declaration), not universals over statements, contracts, or runs;
    the leaf frame is derived from the fired step (`blatt_rahmen_vertrag`
    via `hO`), never posited.
  - The recorded run of the built chain is empty (`J.l = []`): the goal
    needs only worlds and step threads, so `Gesittet`/`hBeschraenkt`
    close vacuously instead of via mark/carrier separation. A chain
    with `J.l = M.lauf` would additionally owe `PCMarkSep`/`PCUnsharedSep`.
  - Entry worlds are built to fit (`eintrittOf`); debt holds for every
    function by U003 (`schuldnerHaelt_gilt`); sight follows from entry
    (`sicht_aus_eintritt` via `heldIn_invarianten`).
-/

#print axioms Gabbro.Grammatik.KetteVoll.kette_aus_lauf_voll
#print axioms Gabbro.Grammatik.KetteVoll.kette_aus_lauf_voll_zeuge

end KetteVoll

end Gabbro.Grammatik
