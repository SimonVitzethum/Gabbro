/- Part 9 of 9 of `Maschine` (split by instrumente/teile/lean-teilen.py; the umbrella `Maschine.lean` imports all parts). -/
import Grammatik.Kern.Semantik.Maschine.T8

namespace Gabbro.Grammatik

variable {D : Deklaration}
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}

/-- **A foreign step preserves the thread triple.** Where a tracked chain
    meets one fired PC step of a different thread, the spec triple of `f`
    transfers to the extended chain: old positions keep the prefix triple,
    the fired position holds the other thread (so `f` owes nothing there),
    heads transfer through the world prefix. No per-firing preservation and
    no memory constancy are owed -- the firing supplies only the
    world-history shape. -/
theorem spec_aus_fuehrung_fremd
    (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D)
    (M M' : GenMaschine D) (pc pc' : PCStand) (g f : Faden)
    (hs : PCSchritt P O passes prog M pc g M' pc')
    (hne : g ≠ f)
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (hJw : J.welten = M.welten)
    (Pre Post : D.Fn → World D → Prop)
    (hSpec : SpecTriple Pre Post Nb J f)
    (J' : GemeinsamerLauf (D := D) Nb)
    (hJ'sf : J'.schrittFaden = J.schrittFaden ++ [g])
    (hJ'w : J'.welten = M'.welten)
    (hJ'code : J'.code f = J.code f) :
    SpecTriple Pre Post Nb J' f := by
  have hGen : GenSchritt P O passes M g M' :=
    pcSchritt_gen P O passes prog M M' pc pc' g hs
  have hAppend : ∃ w : World D, M'.welten = M.welten ++ [w] := by
    rcases hGen with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkein⟩ |
      ⟨L, _hself, _hrang, _hfrei⟩ | ⟨L, _hhaelt⟩
    · exact ⟨σ', rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  obtain ⟨w, hMw⟩ := hAppend
  have hW : J'.welten = M.welten ++ [w] := by
    rw [hJ'w, hMw]
  have hMlen : M.welten.length = J.schrittFaden.length + 1 := by
    rw [← hJw]
    exact J.hKette
  -- positions below the frontier read through the prefix triple
  have hPrefix : ∀ (k : Nat) (vor nach : World D),
      k < J.schrittFaden.length →
      J'.schrittFaden[k]? = some f → J'.welten[k]? = some vor →
        J'.welten[k + 1]? = some nach →
        (Pre (J'.code f) vor ↔ Pre (J'.code f) nach) ∧
          (Post (J'.code f) vor ↔ Post (J'.code f) nach) := by
    intro k vor nach hlt hkg hkv hkn
    have e1 : (J.schrittFaden ++ [g])[k]? = J.schrittFaden[k]? :=
      List.getElem?_append_left hlt
    rw [hJ'sf] at hkg
    rw [e1] at hkg
    have hltM : k < M.welten.length := by omega
    have hltM1 : k + 1 < M.welten.length := by omega
    have e2 : (M.welten ++ [w])[k]? = M.welten[k]? :=
      List.getElem?_append_left hltM
    have e3 : (M.welten ++ [w])[k + 1]? = M.welten[k + 1]? :=
      List.getElem?_append_left hltM1
    rw [hW] at hkv hkn
    rw [e2] at hkv
    rw [e3] at hkn
    have hJkv : J.welten[k]? = some vor := by
      rw [hJw]
      exact hkv
    have hJkn : J.welten[k + 1]? = some nach := by
      rw [hJw]
      exact hkn
    rw [hJ'code]
    exact ⟨hSpec.requiresEigen k vor nach hkg hJkv hJkn,
      hSpec.ensuresEigen k vor nach hkg hJkv hJkn⟩
  -- the head reads through the prefix
  have hHead : ∀ σ₀ : World D, J'.welten[0]? = some σ₀ → J.welten[0]? = some σ₀ := by
    intro σ₀ h0
    have hne0 : 0 < M.welten.length := by omega
    have e0 : (M.welten ++ [w])[0]? = M.welten[0]? :=
      List.getElem?_append_left hne0
    rw [hW, e0] at h0
    rw [hJw]
    exact h0
  -- at and beyond the frontier there is no step of `f`: the new position
  -- holds the other thread, later positions hold none
  have hNew : ∀ (k : Nat), J.schrittFaden.length ≤ k →
      J'.schrittFaden[k]? = some f → False := by
    intro k hle hkg
    by_cases heq : k = J.schrittFaden.length
    · subst heq
      have eNew : (J.schrittFaden ++ [g])[J.schrittFaden.length]? = some g := by
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      rw [hJ'sf, eNew] at hkg
      exact hne (Option.some_inj.mp hkg)
    · have hlt : J.schrittFaden.length < k := by omega
      have eNone : (J.schrittFaden ++ [g])[k]? = none := by
        rw [List.getElem?_append_right (by omega : J.schrittFaden.length ≤ k),
          List.getElem?_eq_none_iff, List.length_singleton]
        omega
      rw [hJ'sf, eNone] at hkg
      simp at hkg
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ₀ h0
    rw [hJ'code]
    exact hSpec.requiresHead σ₀ (hHead σ₀ h0)
  · intro σ₀ h0
    rw [hJ'code]
    exact hSpec.ensuresHead σ₀ (hHead σ₀ h0)
  · intro k vor nach hkg hkv hkn
    by_cases hlt : k < J.schrittFaden.length
    · exact (hPrefix k vor nach hlt hkg hkv hkn).1
    · exact (hNew k (by omega) hkg).elim
  · intro k vor nach hkg hkv hkn
    by_cases hlt : k < J.schrittFaden.length
    · exact (hPrefix k vor nach hlt hkg hkv hkn).2
    · exact (hNew k (by omega) hkg).elim

#print axioms Gabbro.Grammatik.spec_aus_fuehrung_fremd

/-- **The whole-run induction: seed triple to final chain.** For one thread
    `f`, seed heads plus a uniform per-firing preservation duty (over every
    reachable intermediate machine) plus memory-only contracts give the spec
    triple on every chain that tracks the run end. Induction is over the
    thread trace: the seed case is head validity with vacuous eigen
    obligations; each step restricts the final chain to its prefix (same
    members, code, and run -- only worlds and step list move) and either
    extends through the firing (own step, `spec_aus_fuehrung_schritt`) or
    persists (foreign step, `spec_aus_fuehrung_fremd`). -/
theorem spec_aus_lauf_voll
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (f : Faden) (fn : D.Fn)
    (Nb : Nebeneinander)
    (Pre Post : D.Fn → World D → Prop)
    (hMem : SpeicherVertrag Pre Post fn)
    (hSeedPre : ∀ σ₀ : World D, (GenStart sp).welten[0]? = some σ₀ → Pre fn σ₀)
    (hSeedPost : ∀ σ₀ : World D, (GenStart sp).welten[0]? = some σ₀ → Post fn σ₀)
    (hBlattAll : ∀ (M₀ : GenMaschine D) (pc₀ : PCStand),
      PCReach P O passes prog (GenStart sp) M₀ pc₀ →
      ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ),
      s.istBlatt = true → HeldGenau Λ (offen (M₀.spuren f)) →
      ∀ (σ' : World D) (neu : List (Ereignis D)),
      (execStmt O passes keinRuf s (M₀.weltVon f) ρ).welt = some σ' →
      σ'.spur = neu ++ M₀.spuren f →
      (∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) →
      (Pre fn (M₀.weltVon f) ↔ Pre fn σ') ∧
        (Post fn (M₀.weltVon f) ↔ Post fn σ'))
    (M : GenMaschine D) (pc : PCStand) (tr : List Faden)
    (htr : PCSpur P O passes prog (GenStart sp) M pc tr)
    (J : GemeinsamerLauf (D := D) Nb)
    (hJw : J.welten = M.welten)
    (hJsf : J.schrittFaden = tr)
    (hJcode : J.code f = fn) :
    SpecTriple Pre Post Nb J f := by
  revert hJcode hJsf hJw J
  induction htr with
  | leer =>
      intro J hJw hJsf hJcode
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro σ₀ h0
        rw [hJcode]
        exact hSeedPre σ₀ (by rw [← hJw]; exact h0)
      · intro σ₀ h0
        rw [hJcode]
        exact hSeedPost σ₀ (by rw [← hJw]; exact h0)
      · intro k vor nach hkg _ _
        rw [hJsf] at hkg
        simp at hkg
      · intro k vor nach hkg _ _
        rw [hJsf] at hkg
        simp at hkg
  | schritt M M' pc pc' g h hs tr htr ih =>
      intro J' hJ'w hJ'sf hJ'code
      have hGen : GenSchritt P O passes M g M' :=
        pcSchritt_gen P O passes prog M M' pc pc' g hs
      have hMlen' : M'.welten.length = (tr ++ [g]).length + 1 := by
        have hK := J'.hKette
        rw [hJ'sf, hJ'w] at hK
        exact hK
      have hAppend : ∃ w : World D, M'.welten = M.welten ++ [w] := by
        rcases hGen with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkein⟩ |
          ⟨L, _hself, _hrang, _hfrei⟩ | ⟨L, _hhaelt⟩
        · exact ⟨σ', rfl⟩
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
      obtain ⟨w, hMw⟩ := hAppend
      have hPreLen : M.welten.length = tr.length + 1 := by
        have h1 := hMlen'
        rw [hMw] at h1
        simp only [List.length_append, List.length_singleton] at h1 ⊢
        omega
      -- the prefix chain: same members, code, and run, restricted worlds
      -- and step list (no `Gesittet` work is owed, the run is kept whole)
      have hSchrittP : ∀ (k : Nat) (f' : Faden) (vor nach : World D),
          tr[k]? = some f' → M.welten[k]? = some vor → M.welten[k + 1]? = some nach →
          f' ∈ J'.faeden ∧ Rahmen (D.schreibt (J'.code f')) (D.gschreibt (J'.code f')) vor nach := by
        intro k f' vor nach hkg hkv hkn
        have hlt : k < tr.length := by
          by_cases hle : tr.length ≤ k
          · rw [List.getElem?_eq_none hle] at hkg
            simp at hkg
          · omega
        have hltM : k < M.welten.length := by omega
        have hltM1 : k + 1 < M.welten.length := by omega
        have e1 : (tr ++ [g])[k]? = tr[k]? :=
          List.getElem?_append_left hlt
        have e2 : (M.welten ++ [w])[k]? = M.welten[k]? :=
          List.getElem?_append_left hltM
        have e3 : (M.welten ++ [w])[k + 1]? = M.welten[k + 1]? :=
          List.getElem?_append_left hltM1
        have hkg' : J'.schrittFaden[k]? = some f' := by
          rw [hJ'sf, e1]
          exact hkg
        have hkv' : J'.welten[k]? = some vor := by
          rw [hJ'w, hMw, e2]
          exact hkv
        have hkn' : J'.welten[k + 1]? = some nach := by
          rw [hJ'w, hMw, e3]
          exact hkn
        exact J'.hSchritt k f' vor nach hkg' hkv' hkn'
      let Jpre : GemeinsamerLauf (D := D) Nb :=
        { faeden := J'.faeden, code := J'.code, eintritt := J'.eintritt,
          welten := M.welten, schrittFaden := tr, l := J'.l,
          hKette := hPreLen, hSchritt := hSchrittP, hPaar := J'.hPaar,
          hGesittet := J'.hGesittet, hBeschraenkt := J'.hBeschraenkt,
          hEintritt := J'.hEintritt, hSchuld := J'.hSchuld,
          hInvSicht := J'.hInvSicht }
      have hJprew : Jpre.welten = M.welten := rfl
      have hJpresf : Jpre.schrittFaden = tr := rfl
      have hJprecode : Jpre.code f = fn := hJ'code
      have hSpecPre : SpecTriple Pre Post Nb Jpre f :=
        ih Jpre hJprew hJpresf hJprecode
      have hCodePre : J'.code f = Jpre.code f :=
        hJ'code.trans hJprecode.symm
      by_cases heq : g = f
      · subst g
        have hMemPre : SpeicherVertrag Pre Post (Jpre.code f) := by
          rw [hJprecode]
          exact hMem
        have hBlattPre : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
            (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ),
            s.istBlatt = true → HeldGenau Λ (offen (M.spuren f)) →
            ∀ (σ' : World D) (neu : List (Ereignis D)),
            (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ' →
            σ'.spur = neu ++ M.spuren f →
            (∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) →
            (Pre (Jpre.code f) (M.weltVon f) ↔ Pre (Jpre.code f) σ') ∧
              (Post (Jpre.code f) (M.weltVon f) ↔ Post (Jpre.code f) σ') := by
          intro V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkein
          rw [hJprecode]
          exact hBlattAll M pc h V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkein
        have hExt : J'.schrittFaden = Jpre.schrittFaden ++ [f] := hJ'sf
        exact spec_aus_fuehrung_schritt P O passes hO prog sp M _ pc pc' f h hs Nb Jpre
          hJprew Pre Post hMemPre hBlattPre hSpecPre J' hExt hJ'w hCodePre
      · have hExt : J'.schrittFaden = Jpre.schrittFaden ++ [g] := hJ'sf
        exact spec_aus_fuehrung_fremd P O passes prog M _ pc pc' g f hs heq Nb Jpre
          hJprew Pre Post hSpecPre J' hExt hJ'w hCodePre

#print axioms Gabbro.Grammatik.spec_aus_lauf_voll

/-- **Executed triples feed stability.** Per-thread run triples (from
    `spec_aus_lauf_voll`, one instance per member thread) supply the
    sequential premise of `stabil_from_spec` -- read-only reuse with exact
    §19 premise shapes (`hInv` / `hDeck` / `hAb` / `hFree` untouched, that
    file not edited) -- whose one-line application closes executed contract
    assertions at the last world. -/
theorem stabil_aus_lauf
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D)
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (M : GenMaschine D) (pc : PCStand)
    (tr : List Faden)
    (htr : PCSpur P O passes prog (GenStart sp) M pc tr)
    (hJw : J.welten = M.welten)
    (hJsf : J.schrittFaden = tr)
    (Pre Post : D.Fn → World D → Prop)
    (I : TraegerInv (D := D))
    (hInv : InvariantenKontext Nb J I)
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f))
        (SpecQ Pre Post Nb J f))
    (hMemAll : ∀ (g : Faden), g ∈ J.faeden → SpeicherVertrag Pre Post (J.code g))
    (hSeedAll : ∀ (g : Faden), g ∈ J.faeden →
      (∀ σ₀ : World D, (GenStart sp).welten[0]? = some σ₀ → Pre (J.code g) σ₀) ∧
      (∀ σ₀ : World D, (GenStart sp).welten[0]? = some σ₀ → Post (J.code g) σ₀))
    (hBlattAll : ∀ (g : Faden), g ∈ J.faeden → ∀ (M₀ : GenMaschine D) (pc₀ : PCStand),
      PCReach P O passes prog (GenStart sp) M₀ pc₀ →
      ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ),
      s.istBlatt = true → HeldGenau Λ (offen (M₀.spuren g)) →
      ∀ (σ' : World D) (neu : List (Ereignis D)),
      (execStmt O passes keinRuf s (M₀.weltVon g) ρ).welt = some σ' →
      σ'.spur = neu ++ M₀.spuren g →
      (∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) →
      (Pre (J.code g) (M₀.weltVon g) ↔ Pre (J.code g) σ') ∧
        (Post (J.code g) (M₀.weltVon g) ↔ Post (J.code g) σ'))
    (hFree : InterferenceFree Nb J (SpecQ Pre Post Nb J)) :
    ∀ (σ : World D), J.welten.getLast? = some σ →
      ∀ (f : Faden), f ∈ J.faeden → SpecQ Pre Post Nb J f σ := by
  have hSpec : ∀ (f : Faden), f ∈ J.faeden → SpecTriple Pre Post Nb J f := by
    intro f hf
    exact spec_aus_lauf_voll P O passes hO prog sp f (J.code f) Nb Pre Post
      (hMemAll f hf) (hSeedAll f hf).1 (hSeedAll f hf).2
      (hBlattAll f hf) M pc tr htr J hJw hJsf rfl
  exact stabil_from_spec Nb J I Pre Post hInv hDeck hAb hSpec hFree

#print axioms Gabbro.Grammatik.stabil_aus_lauf

end Gabbro.Grammatik

/-! ## 22. The execution link, memory-preserving fragment
    (`hBlattAll_speicherfest_aus_feuerung`)

    BEFUND (rank HOCH, two checkers): `hBlattAll` per leaf (execution link) is
    open -- the uniform per-firing preservation over every reachable
    intermediate machine (the `spec_aus_lauf_voll` / `stabil_aus_lauf` premise,
    re-exported by the goal variant `ziel_nutzer_last_aus_pc_stabil`) has no
    discharger.

    What is proved (no `sorry`):

    - `Stmt.speicherfest`: the memory-preserving leaf test. The nine leaves
      whose every `some`-valued `execStmt` outcome keeps `speicher` (slots and
      globals) test true: `assignVar` and `regSchreib` (read into the
      environment / the device, trace grows, memory stands), `transition`
      (device mirror step, the world passes through untouched), `advances`
      and `retires` (mark bookkeeping, `.ok` on the input world), `ret`
      (reads only, `.zurueck` on the read world), `retGrund`, `leave`, `next`
      (pass-through outcomes on the input world). Everything else tests false:
      the four writes (`assignSlot`, `assignDurch`, `assignGlob`,
      `schreibBytes`), the conditional write (`uebergang`), the oracle answer
      (`axiomCall`), the global publish (`publish`), and all eleven compounds.
    - `speicherfest_speicher`: firing evidence for a `speicherfest` leaf keeps
      live memory. Case analysis on the statement: excluded shapes die at the
      test (`simp [Stmt.speicherfest] at hFest`); the nine included shapes
      compute through `execStmt` / `Ausgang.welt` / `Option.some.injEq` to a
      read-only or unchanged world, whose `speicher` is the input's by
      construction (`lese` / `merke` extend only the trace, §6).
    - `hBlattAll_speicherfest_aus_feuerung`: the `hBlattAll` conclusion for the
      memory-preserving fragment, uniformly over every intermediate machine,
      from firing evidence (`hstep`) plus memory-only contracts (`hMem`):
      memory constancy bridges both the `Pre` and the `Post` iff. No
      reachability is owed -- a pure `execStmt` fact holds at every machine,
      reachable or not, so the uniform shape is the easy direction: each
      `hBlattAll` application site whose fired leaf tests `speicherfest`
      discharges through this theorem instead of a posit.

    Coverage (exactly): the nine memory-preserving leaf shapes, every thread,
    every intermediate machine. Every premise is load-bearing: `O` / `passes`
    feed the firing in `hstep`; `Pre` / `Post` / `fn` name the conclusion;
    `hMem` bridges both iffs; `M₀` / `g` supply the two worlds; `s` / `ρ` /
    `hFest` select the fragment and compute; `σ'` / `hstep` carry the firing.
    Deleting any premise breaks elaboration. There is no `have _ :=`
    discard, no `sorry` / `admit` / `axiom`, and no bare `Prop` slot.

    Remainder (booked, not hidden): the seven memory-changing / oracle leaves
    (`assignSlot`, `assignDurch`, `assignGlob`, `schreibBytes`, `uebergang`,
    `axiomCall`, `publish`) stay owed per program and contract -- the
    sequential-verification duty. The full `hBlattAll` over abstract
    `Pre` / `Post` (which takes no memory hypothesis) is unprovable, not
    merely unproved: a writing leaf can break an arbitrary memory predicate,
    so no induction over `PCSpur` can conjure it. The step lemma's universal
    `hBlatt` premise still owes those seven leaves; `axiomCall` stays with
    S13 (arbitrary oracle answers); the `hMem` discharge per contract and
    head validity from thread entry stay where §21 books them.
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Memory-preserving leaves.** The nine leaves whose every `some`-valued
    `execStmt` outcome keeps `speicher`: reads and pass-through outcomes only,
    never a slot / global write and never an oracle answer. -/
def Stmt.speicherfest : Stmt D V l Γ Λ Λ' → Bool
  | .assignVar _ _ => true
  | .regWrite _ _ _ => true
  | .transition _ _ _ _ _ _ _ => true
  | .advances _ _ _ _ => true
  | .retires _ _ _ _ => true
  | .ret _ _ => true
  | .retWhy _ _ => true
  | .leave _ => true
  | .next _ => true
  | _ => false

/-- **Firing a memory-preserving leaf keeps live memory.** From the firing
    evidence alone: excluded shapes die at the `speicherfest` test, the nine
    included shapes compute to a read-only or unchanged world. -/
theorem speicherfest_speicher
    (O : Orakel D) (passes : Nat)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hFest : s.speicherfest = true)
    (σ σ' : World D)
    (hstep : (execStmt O passes keinRuf s σ ρ).welt = some σ') :
    σ'.speicher = σ.speicher := by
  cases s with
  | assignSlot t f i e hw hL =>
      simp [Stmt.speicherfest] at hFest
  | assignThru p t ht f i e hw hL =>
      simp [Stmt.speicherfest] at hFest
  | assignSlotRef r t ht ho f e hw hL =>
      simp [Stmt.speicherfest] at hFest
  | assignGlob g e hw hL =>
      simp [Stmt.speicherfest] at hFest
  | putBytes t f hf n i hlo hhi e hw hL =>
      simp [Stmt.speicherfest] at hFest
  | assignVar x e =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | shift t f hτ i von nach hn he hw hL =>
      simp [Stmt.speicherfest] at hFest
  | ite c t e =>
      simp [Stmt.speicherfest] at hFest
  | onOption o p a =>
      simp [Stmt.speicherfest] at hFest
  | onTag v arms =>
      simp [Stmt.speicherfest] at hFest
  | onWhy r arms =>
      simp [Stmt.speicherfest] at hFest
  | call f args hp hr =>
      simp [Stmt.speicherfest] at hFest
  | callInd p args hp hr =>
      simp [Stmt.speicherfest] at hFest
  | locks L hr body =>
      simp [Stmt.speicherfest] at hFest
  | breaking i body =>
      simp [Stmt.speicherfest] at hFest
  | traverse t inv body =>
      simp [Stmt.speicherfest] at hFest
  | retry n bis body ueberlauf =>
      simp [Stmt.speicherfest] at hFest
  | forever a inv body =>
      simp [Stmt.speicherfest] at hFest
  | axiomCall a args h hw hg hd hgd =>
      simp [Stmt.speicherfest] at hFest
  | regWrite r hk e =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | transition r hk m hm hl maske bits =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | publish g e payload hp hw hL =>
      simp [Stmt.speicherfest] at hFest
  | advances m a h hs =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | retires m s h a =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | ret e hΛ =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | retWhy r hΛ =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | leave h =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | next h =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl

#print axioms Gabbro.Grammatik.speicherfest_speicher

/-- **Per-firing preservation for memory-preserving leaves, uniformly over
    every intermediate machine.** The `hBlattAll` conclusion for the
    `speicherfest` fragment, from firing evidence plus memory-only contracts:
    the fired leaf keeps live memory (`speicherfest_speicher`), and contracts
    read only live memory (`hMem`), so `Pre` / `Post` survive with no user
    logic owed. -/
theorem hBlattAll_speicherfest_aus_feuerung
    (O : Orakel D) (passes : Nat)
    (Pre Post : D.Fn → World D → Prop) (fn : D.Fn)
    (hMem : SpeicherVertrag Pre Post fn)
    (M₀ : GenMaschine D) (g : Faden)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hFest : s.speicherfest = true)
    (σ' : World D)
    (hstep : (execStmt O passes keinRuf s (M₀.weltVon g) ρ).welt = some σ') :
    (Pre fn (M₀.weltVon g) ↔ Pre fn σ') ∧ (Post fn (M₀.weltVon g) ↔ Post fn σ') := by
  have hspeicher : σ'.speicher = (M₀.weltVon g).speicher :=
    speicherfest_speicher O passes V l Γ Λ Λ' s ρ hFest _ _ hstep
  exact ⟨hMem.memPre _ _ hspeicher.symm, hMem.memPost _ _ hspeicher.symm⟩

#print axioms Gabbro.Grammatik.hBlattAll_speicherfest_aus_feuerung


end Gabbro.Grammatik
