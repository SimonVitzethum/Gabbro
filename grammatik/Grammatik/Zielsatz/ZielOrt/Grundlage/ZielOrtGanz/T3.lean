/- Part 3 of 3 of `ZielOrtGanz` (split by instrumente/teile/lean-teilen.py; the umbrella `ZielOrtGanz.lean` imports all parts). -/
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz.T2

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Schritt

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **At a `logik` check whose test passes, G fires.** From `PrueftG` (the
    conclusion of the goal theorem) and `HeldGenau` of the head's static
    holdings: `travNext`/`travDone`, `ewigWeiter`, `dannLeaveTrav`, and
    `blatt`/`dannBlatt` on a `state` transition. -/
theorem schritt_an_pruefungI {M : RufMaschineG D} (t : Faden) (hP : PrueftG O passes M t)
    (hH : HeldIn (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur))
    (hA : AnPruefungG M t) : ∃ M', RufSchrittG P O passes M t M' := by
  rcases hA with ⟨l, Γ, Λ, ρ, tb, inv, body, ks, k, hr⟩ | ⟨l, Γ, Λ, ρ, a, n, inv, body, k, hr⟩ |
      ⟨l, Γ, Λ, Λx, ρ, tb, inv, body, is, k, rest, hl, i, hr⟩ |
      ⟨l, Γ, Λ, ρ, lo, hi, tb, fl, hτ, i, von, nach, hn, he, hw, hL, K, hr⟩ |
      ⟨l, Γ, Λ, Λ'', ρ, lo, hi, tb, fl, hτ, i, von, nach, hn, he, hw, hL, rst, k, hr⟩
  · have hwahr := hP.1 l Γ Λ ρ tb inv body ks k hr
    rw [hr] at hH
    cases ks with
    | nil =>
        obtain ⟨M', hs, _⟩ := w_travDone (P := P) (O := O) (passes := passes) (z := M.faeden t) rfl
          tb inv body k ρ hr hwahr hH
        exact ⟨M', hs⟩
    | cons j js =>
        obtain ⟨M', hs, _⟩ := w_travNext (P := P) (O := O) (passes := passes) (z := M.faeden t) rfl
          tb inv body j js k ρ hr hwahr hH
        exact ⟨M', hs⟩
  · have hwahr := hP.2.1 l Γ Λ ρ a n inv body k hr
    rw [hr] at hH
    obtain ⟨M', hs, _⟩ := w_ewigWeiter (P := P) (O := O) (passes := passes) (z := M.faeden t) rfl
      a n inv body k ρ hr hwahr hH
    exact ⟨M', hs⟩
  · have hwahr := hP.2.2.1 l Γ Λ Λx ρ tb inv body is k rest hl i hr
    rw [hr] at hH
    obtain ⟨M', hs, _⟩ := w_leaveTrav (P := P) (O := O) (passes := passes) (z := M.faeden t) rfl
      tb inv body is k rest i ρ hr hwahr hH
    exact ⟨M', hs⟩
  · have hno := hP.2.2.2.1 l Γ Λ Λ ρ _ K rfl hr
    rw [hr] at hH
    obtain ⟨σ', ρ', hst, herw⟩ := uebergang_ok O passes tb fl hτ i von nach hn he hw hL _ ρ hno
    obtain ⟨M', hs, _⟩ := w_blatt (P := P) (O := O) (passes := passes) (z := M.faeden t) rfl
      _ K ρ rfl hr hH σ' ρ' hst herw
    exact ⟨M', hs⟩
  · have hno := hP.2.2.2.2 l Γ Λ Λ Λ'' ρ _ rst k rfl hr
    rw [hr] at hH
    obtain ⟨σ', ρ', hst, herw⟩ := uebergang_ok O passes tb fl hτ i von nach hn he hw hL _ ρ hno
    obtain ⟨M', hs, _⟩ := w_dannBlatt (P := P) (O := O) (passes := passes) (z := M.faeden t) rfl
      _ rst k ρ rfl hr hH σ' ρ' hst herw
    exact ⟨M', hs⟩

/-- The form with the exact held set (before the held-set relaxation the
    rules demanded it; now `HeldIn` suffices, `schritt_an_pruefungI`). -/
theorem schritt_an_pruefung {M : RufMaschineG D} (t : Faden) (hP : PrueftG O passes M t)
    (hH : HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur))
    (hA : AnPruefungG M t) : ∃ M', RufSchrittG P O passes M t M' :=
  schritt_an_pruefungI t hP hH.heldIn hA

end Schritt
/-! ## 8. The goal theorem -/

/-- **ZIEL AM ORT, GANZ -- the goal theorem.** Over the repaired machine G,
    for every program in the widened fragment (`programmImFragmentG`: every
    form, indirect calls under `KandOk`, register reads under `RegLokal`)
    whose widened footprint check passes (`fussOrtGB`), from an exclusive
    start that meets the entry contracts, with an oracle that keeps the
    declared axiom frames and the held locks (`GutO`), answers registers and
    `awaits` from the declared carriers (`RegLokal`) and meets the declared
    axiom ensures `Q` (`AxVertragO Q O`, `Q` reading only the declared
    carriers, `AxEnsLokal Q`), and whose every function meets the user
    obligation `KoerperGutZ` -- the body triple and caller duty against
    frame-respecting handlers and the oracles meeting `Q`, and NO `logik`
    outcome of the body -- EVERY reachable machine satisfies
    * `VertragAmOrtG`: `requires` at every logged entry, `ensures` at every
      logged return, with the actual values; and
    * `KeinLogikHaltG`: no thread is stopped at a `logik` check of G -- every
      loop invariant G tests holds where G tests it, and every `state`
      transition finds its pre-state; and
    * progress at the checks: a thread standing at a `logik` check
      (`AnPruefungG`) whose head's static holdings are exactly its held locks
      (`HeldGenau`, the lock side condition of every reading rule) CAN STEP.
      What else can stop a thread is named in `THEOREM-MAP.md` §13.5.

    Premises, by class: (a) user logic `KoerperGutZ` (per function, over the
    SEQUENTIAL semantics), `StartGut`; (b) hardware `GutO`, `RegLokal`,
    `AxVertragO Q`; (c) decidable program facts `hvoll`, `programmImFragmentG`,
    `fussOrtGB`, `StartExklusiv` (N240 for constant starts), `AxEnsLokal Q`;
    the declaration has an event (`e0`). -/
theorem ziel_ort_ganz (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (fs : List D.Fn) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (e0 : Ereignis D) (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hlok : AxEnsLokal Q) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussOrtGB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutZ P passes Q f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M ∧ KeinLogikHaltG O passes M ∧
      ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
        AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M' := by
  intro M hr
  have hI := zielInvR_erreichbar P O passes Q fs sp init e0 hO hRL hQ hlok hvoll hFrag hFuss
    (fun f => (hK f).1) hStart hex M hr
  have hP : KeinLogikHaltG O passes M :=
    fun t => fadenR_prueft hO hRL hQ (fun f => (hK f).2) t (hI.1 t)
  exact ⟨fun t ev hev => hI.2 t ev hev, hP, fun t hH hA => schritt_an_pruefung t (hP t) hH hA⟩

/-- **The contract half alone** needs only the first conjunct of the
    obligation: `ziel_ort_rahmen` with declared axiom ensures (callee
    frames, registers, `awaits` and `Q` in one statement). -/
theorem ziel_ort_ganz_vertrag (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (fs : List D.Fn) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (e0 : Ereignis D) (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hlok : AxEnsLokal Q) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussOrtGB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutRQ P passes Q f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M := by
  intro M hr
  have hI := zielInvR_erreichbar P O passes Q fs sp init e0 hO hRL hQ hlok hvoll hFrag hFuss
    hK hStart hex M hr
  exact fun t ev hev => hI.2 t ev hev

/-- **`ziel_ort_voll_ax` on register-local oracles is a special case**:
    its fragment and footprint check give the widened ones, its obligation
    `KoerperGutA` gives `KoerperGutRQ` (`koerperGutRQ_of_A`). -/
theorem ziel_ort_voll_ax_lokal_aus_ganz (P : Programm D) (O : Orakel D) (passes : Nat)
    (Q : AxEns D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentV P fs = true) (hFuss : fussOrtB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutA P passes Q f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M :=
  ziel_ort_ganz_vertrag P O passes Q fs sp init e0 hO hRL hQ hlok hvoll
    (programmImFragmentG_of_V P fs hFrag) (fussOrtGB_of_V P fs hFrag hFuss)
    (fun f => koerperGutRQ_of_A (hK f)) hStart hex

/-- **`ziel_ort_rahmen` is the contract half at the trivial ensures.** -/
theorem ziel_ort_rahmen_aus_ganz (P : Programm D) (O : Orakel D) (passes : Nat) (fs : List D.Fn)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hRL : RegLokal O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussOrtGB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutR P passes f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M :=
  ziel_ort_ganz_vertrag P O passes (axWahr D) fs sp init e0 hO hRL (axVertragO_wahr O)
    axEnsLokal_wahr hvoll hFrag hFuss (fun f => koerperGutRQ_of_R (axWahr D) (hK f)) hStart hex

/-- **G MOVES AT EVERY `logik` CHECK -- the progress conjunct of
    `ziel_ort_ganz`, stated alone.** Under the premises of `ziel_ort_ganz`, on every reachable
    machine, a thread that stands at a `logik` check of G (`AnPruefungG`)
    and whose head's static holdings are exactly its held locks can step.
    No reachable machine is stuck at a loop invariant, a `forever`
    boundary with budget left, a `leave` out of a `traverse`, or a `state`
    transition. What else can stop a thread: `THEOREM-MAP.md` §13.5. -/
theorem ziel_ort_ganz_fortschritt (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (fs : List D.Fn) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (e0 : Ereignis D) (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hlok : AxEnsLokal Q) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussOrtGB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutZ P passes Q f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
        AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M' := by
  intro M hr
  exact (ziel_ort_ganz P O passes Q fs sp init e0 hO hRL hQ hlok hvoll hFrag hFuss hK hStart hex
    M hr).2.2

/-! ## CUTS:

  What is proved: `ziel_ort_ganz` -- over the repaired G, with callee
  frames (`KoerperGutRQ` over `RespektiertRahmen`), registers and `awaits`
  (`RegLokal`), declared axiom ensures `Q` (`AxVertragO Q O`, `AxEnsLokal Q`)
  and the new clause `KeineLogik`, every reachable machine satisfies
  `VertragAmOrtG`, `KeinLogikHaltG` (every `logik` test of G passes) and
  progress at the checks (`AnPruefungG` + `HeldGenau` gives a step).
  `ziel_ort_rahmen` and `ziel_ort_voll_ax` (register-local oracles) are
  special cases of the contract half (`ziel_ort_rahmen_aus_ganz`,
  `ziel_ort_voll_ax_lokal_aus_ganz`). A syntactic sufficient check for the
  new clause (`programmLogikFrei_ok`). Witnesses, probe A:
  `ZielOrtGanzZeuge.lean`.

  What is NOT covered:

  - Table and group invariants (`Logik.invariante`): they arise only in
    `rufAt` at a callee's return; G does not test them, `VertragAmOrtG` does
    not state them, and `KeineLogik` does not ask for them (its handlers
    answer no `logik` outcome, so a callee's owed invariants are neither
    assumed nor proved). NOT CARRIED.
  - Full progress. Proved: no reachable machine is stuck at a `logik` check,
    and at a check the rule fires given `HeldGenau`. Not proved: that every
    unfinished thread steps or waits on a lock or an `awaits`. What else can
    stop a thread (by rule): a lock held by another thread (`dannLocks`,
    `RufFreiG`); an invisible publication (`dannAwaits`, A10); a hardware
    outcome at the head (an axiom answer outside its declared type, a
    register answer outside its type or against its promise, a float result
    outside its range, a spent `forever` budget `ewig 0`); a `leave`/`next`
    inside an `else` end block that replaced the residue (the loop
    continuation is dropped by `dannNarrowElse`/`dannPruefFalsch`/
    `dannGleitNarrowElse`/`dannRegLiesElseFalsch`/the reason pops -- a
    modelling gap of G); the `HeldGenau` side condition, whose `⊇` half is
    no proved invariant; the shape of the caller at a binding or reason pop,
    no proved invariant either. A root frame at `ret`/`retGrund` is
    finished, not stuck.
  - Termination and `abstieg`: G has no depth bound; a recursion that does
    not end runs on in G, and no theorem bounds it.
  - Everything cut in `ZielOrtRahmen.lean` and `ZielOrtGeraet.lean`
    (locks-block-only readers, contracts over shared state at a lock
    boundary -- verdict probes B/C --, no-event declarations, reason answers
    without a frame, whole-carrier frames).
-/

#print axioms Gabbro.Grammatik.kopfR_keineLogik
#print axioms Gabbro.Grammatik.blatt_logik
#print axioms Gabbro.Grammatik.fadenR_prueft
#print axioms Gabbro.Grammatik.ziel_ort_ganz
#print axioms Gabbro.Grammatik.ziel_ort_ganz_vertrag
#print axioms Gabbro.Grammatik.ziel_ort_voll_ax_lokal_aus_ganz
#print axioms Gabbro.Grammatik.ziel_ort_rahmen_aus_ganz

#print axioms Gabbro.Grammatik.schritt_an_pruefung
#print axioms Gabbro.Grammatik.ziel_ort_ganz_fortschritt


end Gabbro.Grammatik
