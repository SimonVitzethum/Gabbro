/- Part 8 of 9 of `Maschine` (split by instrumente/teile/lean-teilen.py; the umbrella `Maschine.lean` imports all parts). -/
import Grammatik.Kern.Semantik.Maschine.T7

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

/-- **One executed step extends the thread triple.** Where a tracked chain
    meets one fired PC step of its thread, the spec triple transfers to the
    extended chain: old positions keep the prefix triple, the fired position
    keeps the contract through the firing (leaf steps through per-firing
    preservation, lock steps through memory constancy). This is the step that
    binds spec triples to interleaved execution, so that `owickiGries_stabil`
    consumes executed triples, not posited ones. -/
theorem spec_aus_fuehrung_schritt
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D)
    (M M' : GenMaschine D) (pc pc' : PCStand) (f : Faden)
    (hReach : PCReach P O passes prog (GenStart sp) M pc)
    (hs : PCSchritt P O passes prog M pc f M' pc')
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (hJw : J.welten = M.welten)
    (Pre Post : D.Fn → World D → Prop)
    (hMem : SpeicherVertrag Pre Post (J.code f))
    (hBlatt : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ),
      s.istBlatt = true → HeldGenau Λ (offen (M.spuren f)) →
      ∀ (σ' : World D) (neu : List (Ereignis D)),
      (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ' →
      σ'.spur = neu ++ M.spuren f →
      (∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) →
      (Pre (J.code f) (M.weltVon f) ↔ Pre (J.code f) σ') ∧
        (Post (J.code f) (M.weltVon f) ↔ Post (J.code f) σ'))
    (hSpec : SpecTriple Pre Post Nb J f)
    (J' : GemeinsamerLauf (D := D) Nb)
    (hJ'sf : J'.schrittFaden = J.schrittFaden ++ [f])
    (hJ'w : J'.welten = M'.welten)
    (hJ'code : J'.code f = J.code f) :
    SpecTriple Pre Post Nb J' f := by
  have hG : GenErreichbar P O passes (GenStart sp) M :=
    pcReach_gen P O passes prog (GenStart sp) M pc hReach
  have hGen : GenSchritt P O passes M f M' :=
    pcSchritt_gen P O passes prog M M' pc pc' f hs
  obtain ⟨f0, hlast⟩ := genWelten_letzte P O passes hO sp M hG
  have hMlen : M.welten.length = J.schrittFaden.length + 1 := by
    rw [← hJw]
    exact J.hKette
  have hlastIdx : M.welten[J.schrittFaden.length]? =
      some (M.speicher.welt (M.spuren f0)) := by
    have hget : M.welten.getLast? = M.welten[M.welten.length - 1]? :=
      List.getLast?_eq_getElem?
    have hn : M.welten.length - 1 = J.schrittFaden.length := by omega
    rw [hn] at hget
    rw [hlast] at hget
    exact hget.symm
  have hwf : (M.weltVon f).speicher = M.speicher :=
    speicher_welt_speicher M.speicher (M.spuren f)
  -- positions below the frontier read through the prefix triple
  have hPrefix : ∀ (W : List (World D)), J'.welten = M.welten ++ W →
      ∀ (k : Nat) (vor nach : World D),
      k < J.schrittFaden.length →
      J'.schrittFaden[k]? = some f → J'.welten[k]? = some vor →
        J'.welten[k + 1]? = some nach →
        (Pre (J'.code f) vor ↔ Pre (J'.code f) nach) ∧
          (Post (J'.code f) vor ↔ Post (J'.code f) nach) := by
    intro W hW k vor nach hlt hkg hkv hkn
    have e1 : (J.schrittFaden ++ [f])[k]? = J.schrittFaden[k]? :=
      List.getElem?_append_left hlt
    rw [hJ'sf] at hkg
    rw [e1] at hkg
    have hltM : k < M.welten.length := by omega
    have hltM1 : k + 1 < M.welten.length := by omega
    have e2 : (M.welten ++ W)[k]? = M.welten[k]? :=
      List.getElem?_append_left hltM
    have e3 : (M.welten ++ W)[k + 1]? = M.welten[k + 1]? :=
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
  have hHead : ∀ (W : List (World D)), J'.welten = M.welten ++ W →
      ∀ σ₀ : World D, J'.welten[0]? = some σ₀ → J.welten[0]? = some σ₀ := by
    intro W hW σ₀ h0
    have hne : 0 < M.welten.length := by omega
    have e0 : (M.welten ++ W)[0]? = M.welten[0]? :=
      List.getElem?_append_left hne
    rw [hW, e0] at h0
    rw [hJw]
    exact h0
  -- the frontier world carries live memory
  have hFront : ∀ (W : List (World D)), J'.welten = M.welten ++ W →
      ∀ vor : World D, J'.welten[J.schrittFaden.length]? = some vor →
        vor.speicher = M.speicher := by
    intro W hW vor hkv
    have hltNew : J.schrittFaden.length < M.welten.length := by omega
    have eW : (M.welten ++ W)[J.schrittFaden.length]? =
        M.welten[J.schrittFaden.length]? :=
      List.getElem?_append_left hltNew
    rw [hW, eW, hlastIdx] at hkv
    have hvor : vor = M.speicher.welt (M.spuren f0) :=
      Option.some_inj.mp hkv.symm
    rw [hvor]
    exact speicher_welt_speicher _ _
  -- beyond the frontier there is no step
  have hBeyond : ∀ (k : Nat), J.schrittFaden.length < k →
      J'.schrittFaden[k]? = some f → False := by
    intro k hlt hkg
    have hle : J.schrittFaden.length ≤ k := by omega
    have eNone : (J.schrittFaden ++ [f])[k]? = none := by
      rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
        List.length_singleton]
      omega
    rw [hJ'sf] at hkg
    rw [eNone] at hkg
    simp at hkg
  rcases hGen with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkein⟩ |
    ⟨L, _hself, _hrang, _hfrei⟩ | ⟨L, _hhaelt⟩
  · -- the fired leaf appends its outcome world
    have hW : J'.welten = M.welten ++ [σ'] := hJ'w
    have eW2 : (M.welten ++ [σ'])[J.schrittFaden.length + 1]? = some σ' := by
      have hle2 : M.welten.length ≤ J.schrittFaden.length + 1 := by omega
      rw [List.getElem?_append_right hle2]
      have hsub : J.schrittFaden.length + 1 - M.welten.length = 0 := by omega
      rw [hsub]
      rfl
    have hNew : ∀ (vor nach : World D),
        J'.welten[J.schrittFaden.length]? = some vor →
        J'.welten[J.schrittFaden.length + 1]? = some nach →
        (Pre (J'.code f) vor ↔ Pre (J'.code f) nach) ∧
          (Post (J'.code f) vor ↔ Post (J'.code f) nach) := by
      intro vor nach hkv hkn
      have hvs : vor.speicher = M.speicher := hFront [σ'] hW vor hkv
      have hnach : σ' = nach := by
        rw [hW, eW2] at hkn
        exact Option.some_inj.mp hkn
      have hPre : Pre (J.code f) vor ↔ Pre (J.code f) σ' :=
        (hMem.memPre vor (M.weltVon f) (hvs.trans hwf.symm)).trans
          (hBlatt V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkein).1
      have hPost : Post (J.code f) vor ↔ Post (J.code f) σ' :=
        (hMem.memPost vor (M.weltVon f) (hvs.trans hwf.symm)).trans
          (hBlatt V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkein).2
      rw [hJ'code, ← hnach]
      exact ⟨hPre, hPost⟩
    have hReqH : ∀ σ₀ : World D, J'.welten[0]? = some σ₀ → Pre (J'.code f) σ₀ := by
      intro σ₀ h0
      rw [hJ'code]
      exact hSpec.requiresHead σ₀ (hHead [σ'] hW σ₀ h0)
    have hEnsH : ∀ σ₀ : World D, J'.welten[0]? = some σ₀ → Post (J'.code f) σ₀ := by
      intro σ₀ h0
      rw [hJ'code]
      exact hSpec.ensuresHead σ₀ (hHead [σ'] hW σ₀ h0)
    have hReqE : ∀ (k : Nat) (vor nach : World D),
        J'.schrittFaden[k]? = some f → J'.welten[k]? = some vor →
        J'.welten[k + 1]? = some nach → (Pre (J'.code f) vor ↔ Pre (J'.code f) nach) := by
      intro k vor nach hkg hkv hkn
      by_cases hlt : k < J.schrittFaden.length
      · exact (hPrefix [σ'] hW k vor nach hlt hkg hkv hkn).1
      · by_cases heq : k = J.schrittFaden.length
        · subst heq
          exact (hNew vor nach hkv hkn).1
        · exact (hBeyond k (by omega) hkg).elim
    have hEnsE : ∀ (k : Nat) (vor nach : World D),
        J'.schrittFaden[k]? = some f → J'.welten[k]? = some vor →
        J'.welten[k + 1]? = some nach → (Post (J'.code f) vor ↔ Post (J'.code f) nach) := by
      intro k vor nach hkg hkv hkn
      by_cases hlt : k < J.schrittFaden.length
      · exact (hPrefix [σ'] hW k vor nach hlt hkg hkv hkn).2
      · by_cases heq : k = J.schrittFaden.length
        · subst heq
          exact (hNew vor nach hkv hkn).2
        · exact (hBeyond k (by omega) hkg).elim
    exact ⟨hReqH, hEnsH, hReqE, hEnsE⟩
  · -- the fired take keeps live memory: contracts survive with no user logic
    have hW : J'.welten =
        M.welten ++ [M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)] :=
      hJ'w
    have eW2 : (M.welten ++
        [M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)])[J.schrittFaden.length + 1]? =
        some (M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)) := by
      have hle2 : M.welten.length ≤ J.schrittFaden.length + 1 := by omega
      rw [List.getElem?_append_right hle2]
      have hsub : J.schrittFaden.length + 1 - M.welten.length = 0 := by omega
      rw [hsub]
      rfl
    have hNew : ∀ (vor nach : World D),
        J'.welten[J.schrittFaden.length]? = some vor →
        J'.welten[J.schrittFaden.length + 1]? = some nach →
        (Pre (J'.code f) vor ↔ Pre (J'.code f) nach) ∧
          (Post (J'.code f) vor ↔ Post (J'.code f) nach) := by
      intro vor nach hkv hkn
      have hvs : vor.speicher = M.speicher :=
        hFront _ hW vor hkv
      have hnach : M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f) = nach := by
        rw [hW, eW2] at hkn
        exact Option.some_inj.mp hkn
      have hNs : (M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)).speicher =
          M.speicher :=
        speicher_welt_speicher _ _
      have hBrPre : Pre (J.code f) vor ↔
          Pre (J.code f) (M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)) :=
        hMem.memPre vor _ (hvs.trans hNs.symm)
      have hBrPost : Post (J.code f) vor ↔
          Post (J.code f) (M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)) :=
        hMem.memPost vor _ (hvs.trans hNs.symm)
      rw [hJ'code, ← hnach]
      exact ⟨hBrPre, hBrPost⟩
    have hReqH : ∀ σ₀ : World D, J'.welten[0]? = some σ₀ → Pre (J'.code f) σ₀ := by
      intro σ₀ h0
      rw [hJ'code]
      exact hSpec.requiresHead σ₀ (hHead _ hW σ₀ h0)
    have hEnsH : ∀ σ₀ : World D, J'.welten[0]? = some σ₀ → Post (J'.code f) σ₀ := by
      intro σ₀ h0
      rw [hJ'code]
      exact hSpec.ensuresHead σ₀ (hHead _ hW σ₀ h0)
    have hReqE : ∀ (k : Nat) (vor nach : World D),
        J'.schrittFaden[k]? = some f → J'.welten[k]? = some vor →
        J'.welten[k + 1]? = some nach → (Pre (J'.code f) vor ↔ Pre (J'.code f) nach) := by
      intro k vor nach hkg hkv hkn
      by_cases hlt : k < J.schrittFaden.length
      · exact (hPrefix _ hW k vor nach hlt hkg hkv hkn).1
      · by_cases heq : k = J.schrittFaden.length
        · subst heq
          exact (hNew vor nach hkv hkn).1
        · exact (hBeyond k (by omega) hkg).elim
    have hEnsE : ∀ (k : Nat) (vor nach : World D),
        J'.schrittFaden[k]? = some f → J'.welten[k]? = some vor →
        J'.welten[k + 1]? = some nach → (Post (J'.code f) vor ↔ Post (J'.code f) nach) := by
      intro k vor nach hkg hkv hkn
      by_cases hlt : k < J.schrittFaden.length
      · exact (hPrefix _ hW k vor nach hlt hkg hkv hkn).2
      · by_cases heq : k = J.schrittFaden.length
        · subst heq
          exact (hNew vor nach hkv hkn).2
        · exact (hBeyond k (by omega) hkg).elim
    exact ⟨hReqH, hEnsH, hReqE, hEnsE⟩
  · -- the fired release keeps live memory: the section end keeps the contract
    have hW : J'.welten =
        M.welten ++ [M.speicher.welt (Ereignis.gibt L :: M.spuren f)] :=
      hJ'w
    have eW2 : (M.welten ++
        [M.speicher.welt (Ereignis.gibt L :: M.spuren f)])[J.schrittFaden.length + 1]? =
        some (M.speicher.welt (Ereignis.gibt L :: M.spuren f)) := by
      have hle2 : M.welten.length ≤ J.schrittFaden.length + 1 := by omega
      rw [List.getElem?_append_right hle2]
      have hsub : J.schrittFaden.length + 1 - M.welten.length = 0 := by omega
      rw [hsub]
      rfl
    have hNew : ∀ (vor nach : World D),
        J'.welten[J.schrittFaden.length]? = some vor →
        J'.welten[J.schrittFaden.length + 1]? = some nach →
        (Pre (J'.code f) vor ↔ Pre (J'.code f) nach) ∧
          (Post (J'.code f) vor ↔ Post (J'.code f) nach) := by
      intro vor nach hkv hkn
      have hvs : vor.speicher = M.speicher :=
        hFront _ hW vor hkv
      have hnach : M.speicher.welt (Ereignis.gibt L :: M.spuren f) = nach := by
        rw [hW, eW2] at hkn
        exact Option.some_inj.mp hkn
      have hNs : (M.speicher.welt (Ereignis.gibt L :: M.spuren f)).speicher =
          M.speicher :=
        speicher_welt_speicher _ _
      have hBrPre : Pre (J.code f) vor ↔
          Pre (J.code f) (M.speicher.welt (Ereignis.gibt L :: M.spuren f)) :=
        hMem.memPre vor _ (hvs.trans hNs.symm)
      have hBrPost : Post (J.code f) vor ↔
          Post (J.code f) (M.speicher.welt (Ereignis.gibt L :: M.spuren f)) :=
        hMem.memPost vor _ (hvs.trans hNs.symm)
      rw [hJ'code, ← hnach]
      exact ⟨hBrPre, hBrPost⟩
    have hReqH : ∀ σ₀ : World D, J'.welten[0]? = some σ₀ → Pre (J'.code f) σ₀ := by
      intro σ₀ h0
      rw [hJ'code]
      exact hSpec.requiresHead σ₀ (hHead _ hW σ₀ h0)
    have hEnsH : ∀ σ₀ : World D, J'.welten[0]? = some σ₀ → Post (J'.code f) σ₀ := by
      intro σ₀ h0
      rw [hJ'code]
      exact hSpec.ensuresHead σ₀ (hHead _ hW σ₀ h0)
    have hReqE : ∀ (k : Nat) (vor nach : World D),
        J'.schrittFaden[k]? = some f → J'.welten[k]? = some vor →
        J'.welten[k + 1]? = some nach → (Pre (J'.code f) vor ↔ Pre (J'.code f) nach) := by
      intro k vor nach hkg hkv hkn
      by_cases hlt : k < J.schrittFaden.length
      · exact (hPrefix _ hW k vor nach hlt hkg hkv hkn).1
      · by_cases heq : k = J.schrittFaden.length
        · subst heq
          exact (hNew vor nach hkv hkn).1
        · exact (hBeyond k (by omega) hkg).elim
    have hEnsE : ∀ (k : Nat) (vor nach : World D),
        J'.schrittFaden[k]? = some f → J'.welten[k]? = some vor →
        J'.welten[k + 1]? = some nach → (Post (J'.code f) vor ↔ Post (J'.code f) nach) := by
      intro k vor nach hkg hkv hkn
      by_cases hlt : k < J.schrittFaden.length
      · exact (hPrefix _ hW k vor nach hlt hkg hkv hkn).2
      · by_cases heq : k = J.schrittFaden.length
        · subst heq
          exact (hNew vor nach hkv hkn).2
        · exact (hBeyond k (by omega) hkg).elim
    exact ⟨hReqH, hEnsH, hReqE, hEnsE⟩

#print axioms Gabbro.Grammatik.spec_aus_fuehrung_schritt

end Gabbro.Grammatik

/-! ## 21. The spec triple from execution: whole-run induction (`spec_aus_lauf_voll`)

    `spec_aus_fuehrung_schritt` (§20) extends one thread triple over one fired
    PC step; `owickiGries_stabil` (consumed via `stabil_from_spec`, §19 of
    `InterferenzAllgemein.lean`) needs triples over the FINAL chain. This
    section is the induction between them: a seed triple (head validity from
    the caller -- a zero-step chain carries no eigen obligation) carried over
    a whole `PCReach` run to the final chain.

    What is proved (no `sorry`):

    - `PCSpur`: the thread trace of a run -- `tr` lists the acting thread of
      every machine step, in order. Each `schritt` case carries its own
      `PCReach` evidence `h` and firing `hs`, so a spur determines the run it
      traces; `pcSpur_von_reach` shows every `PCReach` derivation has one.
      The main induction runs over the spur (not over `PCReach` directly),
      because the chain equations (`J.schrittFaden = tr`) must follow the
      acting threads step by step, and a machine state alone does not record
      how many run events each step contributed.
    - `spec_aus_fuehrung_fremd`: a foreign step preserves the thread triple.
      Where the tracked chain meets one fired PC step of a DIFFERENT thread
      (`hne`), the spec triple of `f` transfers to the extended chain with no
      sequential duty owed: old positions keep the prefix triple, the new
      position holds the other thread, heads transfer through the world
      prefix. No `hBlatt`, no `hMem`, no reachability -- the firing `hs`
      supplies only the world-history shape (`M'.welten = M.welten ++ [w]`).
    - `spec_aus_lauf_voll`: the run induction for one thread `f`. Seed heads
      plus a uniform per-firing preservation duty (`hBlattAll`, over every
      reachable intermediate machine) plus memory-only contracts (`hMem`)
      give the triple on every chain `J` that tracks the run end
      (`J.welten = M.welten`, `J.schrittFaden = tr`, stable code
      `J.code f = fn`). The seed case is head validity with vacuous eigen
      obligations; each step splits the final chain into its prefix (same
      members, code, and run -- only worlds and step list restricted, so no
      `Gesittet` work is owed) and either extends through the firing
      (`spec_aus_fuehrung_schritt`, own step) or persists
      (`spec_aus_fuehrung_fremd`, foreign step). The top-level `PCReach`
      derivation is not a premise: the spur already carries per-step
      reachability evidence, and `pcSpur_von_reach` bridges callers that hold
      only the derivation.
    - `stabil_aus_lauf`: the consumer corollary. Per-thread run triples feed
      `stabil_from_spec` (read-only reuse -- that file is not touched), whose
      one-line application closes executed contract assertions at the last
      world. `hInv` / `hDeck` / `hAb` / `hFree` keep their exact §19 shapes.

    Coverage (exactly): whole `PCReach` runs (`leaf` / `nimmt` / `gibt`
    steps, any interleaving), one thread triple per induction instance, all
    threads jointly at the consumer. Every premise is load-bearing (each is
    consumed by its proof; there is no `have _ :=` discard).

    Remainder (booked, not hidden): the per-step atom identity inside `hs`
    (S12, scheduler and witness duty); the `axiomCall` oracle-event contract
    (S13); discharging `hMem` for `QRequires` / `QEnsures` (per-expression
    induction downstream, where the contract instantiation lives); head
    validity from thread entry (caller side); discharging `hFree` per program
    (the Owicki-Gries check itself, verifier duty).
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Thread trace of a PC run.** `tr` lists the acting thread of every
    machine step, in order: empty at the start, one entry per fired step.
    Each step case carries its `PCReach` evidence and firing, so the spur
    determines the traced run. -/
inductive PCSpur (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M0 : GenMaschine D) :
    GenMaschine D → PCStand → List Faden → Prop where
  | leer : PCSpur P O passes prog M0 M0 (fun _ => 0) []
  | schritt (M M' : GenMaschine D) (pc pc' : PCStand) (g : Faden)
      (h : PCReach P O passes prog M0 M pc)
      (hs : PCSchritt P O passes prog M pc g M' pc')
      (tr : List Faden) (htr : PCSpur P O passes prog M0 M pc tr) :
      PCSpur P O passes prog M0 M' pc' (tr ++ [g])

/-- **Every reachable run has a thread trace.** By induction on the
    derivation: empty at the start, one entry per fired step. This bridges
    callers that hold only the `PCReach` derivation to the spur induction. -/
theorem pcSpur_von_reach (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M0 : GenMaschine D)
    (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog M0 M pc) :
    ∃ tr : List Faden, PCSpur P O passes prog M0 M pc tr := by
  induction h with
  | start => exact ⟨[], PCSpur.leer⟩
  | step M M' pc pc' g h hs ih =>
      obtain ⟨tr, htr⟩ := ih
      exact ⟨tr ++ [g], PCSpur.schritt M M' pc pc' g h hs tr htr⟩

#print axioms Gabbro.Grammatik.pcSpur_von_reach


end Gabbro.Grammatik
