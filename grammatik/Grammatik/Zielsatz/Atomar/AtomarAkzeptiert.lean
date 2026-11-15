module

public import Grammatik.Zielsatz.Atomar.AtomarAkzeptiertSpec

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik Speichermodell

variable {D : Deklaration}

/-! ## The Bool -/

section Bool

variable [DecidableEq D.Fn] [DecidableEq D.Ax] {P : Programm D} {S : SperrInv D} {fs : List D.Fn}
  {ls : List D.Lock} {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn}

/-- **No contract mentions `c`**: no `requires`, no `ensures`, no owed invariant of a function
    of the member list, and `c` is read by the predicate of no declared invariant (C05). -/
def vertragsFreiB (P : Programm D) (fs : List D.Fn) (c : D.Tab ⊕ D.Glob) : Bool :=
  (fs.all fun g => !(istIn (P.requires g).orte c) && !(istIn (P.ensures g).orte c) &&
    !(istIn (invOrteP P g) c)) &&
  D.invs.all fun i => !(istIn (P.invariante i).orte c)

omit [DecidableEq D.Fn] in
theorem vertragsFreiB_ok (hvoll : ∀ g : D.Fn, g ∈ fs) {c : D.Tab ⊕ D.Glob}
    (h : vertragsFreiB P fs c = true) : VertragsFrei P c := by
  simp only [vertragsFreiB, Bool.and_eq_true_iff] at h
  obtain ⟨hg, hiv⟩ := h
  refine ⟨fun g => ?_, fun i hi hc => ?_⟩
  · have h1 := (List.all_eq_true.mp hg) g (hvoll g)
    simp only [Bool.and_eq_true_iff, Bool.not_eq_true'] at h1
    obtain ⟨⟨h1, h2⟩, h3⟩ := h1
    refine ⟨fun hc => ?_, fun hc => ?_, fun hc => ?_⟩
    · rw [istIn_iff.mpr hc] at h1; cases h1
    · rw [istIn_iff.mpr hc] at h2; cases h2
    · rw [istIn_iff.mpr hc] at h3; cases h3
  · have h5 := (List.all_eq_true.mp hiv) i hi
    simp only [Bool.not_eq_true'] at h5
    rw [istIn_iff.mpr hc] at h5; cases h5

/-- **An admitted shared atomic, decided at a footprint carrier**: `atomic`, no guard lock, in
    no contract (thread-locality is the first disjunct of the footprint component). -/
def geteiltVB (P : Programm D) (fs : List D.Fn) (c : D.Tab ⊕ D.Glob) : Bool :=
  atomarB c && (waechterVon c).isEmpty && vertragsFreiB P fs c

/-- **The footprint component with the admitted shared atomics.** -/
def fussWXB (P : Programm D) (S : SperrInv D) (fs ws : List D.Fn) : Bool :=
  fs.all fun f =>
    (fussOrte P f).all (fun c =>
      sigB f c || getrenntW P fs ws c || ((waechterVon c).any fun L => istIn (S.orte L) c) ||
        geteiltVB P fs c) &&
    ((P.rumpf f).regs.flatMap D.rtraeger).all (fun c => sigB f c || getrenntW P fs ws c)

/-- The atomic-rely checker keeps the same final bounded guest admission.
    Source adapters must retain the complete descriptor list, as for Akzeptiert. -/
def AkzeptiertX (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn)
    (aks : List (Kernzelle.AccumulatorDecl D) := []) (checks : List (CheckDecl D) := [])
    (aqs : List D.Ax := []) (guests : List (GuestBoundary D) := [])
    (sources : Invarianten.Pruefer.LockSources S := fun _ => none)
    (hints : Vertraege.Pruefer.LoopHints D := fun _ => none) : Bool :=
  programmImFragmentG P fs && abgAlleB P fs && fussWXB P S fs ws && stufenB P fs &&
    sperrOrteB S ls && wurzelnB ws && einzelnPoolB P fs cs ws && rennB P fs cs ws &&
    antwortenB P fs && maskenB P fs && schnittstellenB P fs && libraryB P fs && Kernzelle.accumulatorB P fs (tabsOf cs) (globsOf cs) aqs aks && checkB P (tabsOf cs) (globsOf cs) fs checks && resetB cs && scopesOkProgB P fs && GuestBoundary.admissionB guests &&
    Invarianten.Pruefer.programInvariantsB P S fs sources {} ls &&
    Vertraege.Pruefer.KontrakteGeprueftB P S fs sources {} hints

theorem fussWXB_ok (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    (h : fussWXB P S fs ws = true) (f : D.Fn) : FussSX P S (lokW P fs ws) (GeteiltV P ws) f := by
  rw [← getrenntW_eq_lokW hvoll]
  have h1 := (List.all_eq_true.mp h) f (hvoll f)
  simp only [Bool.and_eq_true_iff] at h1
  refine ⟨fun c hc => ?_, fun c hc => (List.all_eq_true.mp h1.2) c hc⟩
  have h2 := (List.all_eq_true.mp h1.1) c hc
  simp only [Bool.or_eq_true_iff] at h2
  rcases h2 with ((h2 | h2) | h2) | h2
  · exact Or.inl (by simp only [h2, Bool.true_or])
  · exact Or.inl (by simp only [h2, Bool.or_true])
  · obtain ⟨L, hL, hc'⟩ := List.any_eq_true.mp h2
    exact Or.inr (Or.inl ⟨L, waechterVon_mem.mp hL, istIn_iff.mp hc'⟩)
  · cases hg : getrenntW P fs ws c
    · refine Or.inr (Or.inr ?_)
      simp only [geteiltVB, Bool.and_eq_true_iff] at h2
      obtain ⟨⟨ha, hw⟩, hv⟩ := h2
      refine ⟨⟨atomarB_iff.mp ha, fun L hL => ?_, fun hR => ?_⟩, vertragsFreiB_ok hvoll hv⟩
      · have := waechterVon_mem.mpr hL
        rw [List.isEmpty_iff.mp hw] at this
        exact List.not_mem_nil this
      · have := (getrenntW_iff hvoll).mpr ((getrenntR_iff hvoll hAbg c).mp hR)
        rw [hg] at this
        cases this
    · exact Or.inl (by simp only [Bool.or_true])

/-- **The Bool decides (a)**: `AkzeptiertX` gives `AkzeptiertSpecX`. The value
    carries the Bool's checks. The reverse (`akzeptiertX_of_spec` below) needs only
    `FussSX`-completeness of `fussWXB` (`fussWXB_vollstaendig`), proved here from the
    decided thread-locality, the guard table and the admitted shared atomics. -/
theorem akzeptiertSpecX_of [RootNativeFloat.Hardware]
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls)
    (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) (aks : List (Kernzelle.AccumulatorDecl D))
    {checks : List (CheckDecl D)} {sources : Invarianten.Pruefer.LockSources S}
    {hints : Vertraege.Pruefer.LoopHints D}
    (h : AkzeptiertX P S fs ls cs ws aks checks [] [] sources hints = true) :
    AkzeptiertSpecX P S fs ws [] aks := by
  have contractParts := Bool.and_eq_true_iff.mp h
  have hK := Vertraege.Pruefer.KontrakteGeprueftB_sound hvoll contractParts.2
  have h := contractParts.1
  have parts := Bool.and_eq_true_iff.mp h
  have hI := Invarianten.Pruefer.programInvariantsB_sound P S fs sources {} hvoll parts.2
  have h := parts.1
  change (programmImFragmentG P fs && abgAlleB P fs && fussWXB P S fs ws && stufenB P fs &&
    sperrOrteB S ls && wurzelnB ws && einzelnPoolB P fs cs ws && rennB P fs cs ws &&
    antwortenB P fs && maskenB P fs && schnittstellenB P fs && libraryB P fs &&
    Kernzelle.accumulatorB P fs (tabsOf cs) (globsOf cs) [] aks &&
    checkB P (tabsOf cs) (globsOf cs) fs checks && resetB cs && scopesOkProgB P fs &&
    GuestBoundary.admissionB []) = true at h
  simp only [GuestBoundary.admissionB_nil, Bool.and_true, Bool.and_eq_true_iff, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, _h16⟩ := h
  have hAbg := (abgAlleB_iff hvoll).mp h2
  exact {
    frag := h1
    abg := hAbg
    fuss := fussWXB_ok hvoll hAbg h3
    stufen := (stufenB_iff hvoll).mp h4
    sperrOrte := (sperrOrteB_iff hls).mp h5
    wurzeln := wurzelnB_iff.mp h6
    einzeln := (einzelnPoolB_iff hvoll hcs).mp h7
    renn := (rennB_iff hvoll hcs).mp h8
    antworten := (antwortenB_iff hvoll).mp h9
    masken := (maskenB_iff hvoll).mp h10
    schnittstellen := (schnittstellenB_iff hvoll).mp h11
    besitz := fun _ h => nomatch h
    worte := fun _ h => nomatch h
    bibliothek := (libraryB_iff _ _).mp h12
    akku := ((Kernzelle.accumulatorB_iff hvoll (tabsOf_voll hcs) (globsOf_voll hcs)).mp h13).1
    pruef := ⟨checks, (checkB_iff hvoll (tabsOf_voll hcs) (globsOf_voll hcs)).mp h14⟩
    reset := (resetB_iff hcs).mp h15
    invarianten := hI, kontrakte := hK }

/-- **The atomic checker establishes the scope discipline** (C11): from the
    Bool, outside `Spec` (which has no scope field). -/
theorem scopesOkProg_of_akzeptiertX (hvoll : ∀ g : D.Fn, g ∈ fs)
    {aks : List (Kernzelle.AccumulatorDecl D)} {checks : List (CheckDecl D)}
    (h : AkzeptiertX P S fs ls cs ws aks checks = true) : ScopesOkProg P := by
  have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1
  dsimp only [AkzeptiertX] at h
  simp only [GuestBoundary.admissionB_nil, Bool.and_true, Bool.and_eq_true_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩ := h
  exact (scopesOkProgB_iff hvoll).mp h16

/-- The old footprint component implies the new one. -/
theorem fussWXB_of_fussWB (h : fussWB P S fs ws = true) : fussWXB P S fs ws = true := by
  refine List.all_eq_true.mpr fun f hf => ?_
  have h1 := (List.all_eq_true.mp h) f hf
  simp only [Bool.and_eq_true_iff] at h1 ⊢
  refine ⟨List.all_eq_true.mpr fun c hc => ?_, h1.2⟩
  have h2 := (List.all_eq_true.mp h1.1) c hc
  simp only [Bool.or_eq_true_iff] at h2 ⊢
  exact Or.inl h2

/-- **EMBEDDING, as Bools: every unit the goal's checker accepts, `AkzeptiertX` accepts.** -/
theorem akzeptiertX_of_akzeptiert {aks : List (Kernzelle.AccumulatorDecl D)}
    {checks : List (CheckDecl D)} (h : Akzeptiert P S fs ls cs ws aks checks = true)
    (hK : Vertraege.Pruefer.KontrakteGeprueftB P S fs = true) :
    AkzeptiertX P S fs ls cs ws aks checks = true := by
  have invariantCheck := (Bool.and_eq_true_iff.mp h).2
  have h := (Bool.and_eq_true_iff.mp h).1
  unfold AkzeptiertX
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, hK⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, invariantCheck⟩
  dsimp only [Akzeptiert] at h
  simp only [GuestBoundary.admissionB_nil, Bool.and_true, Bool.and_eq_true_iff, and_assoc] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hSchnitt, hReset, h11, h12, h13, hS⟩ := h
  exact ⟨h1, h2, fussWXB_of_fussWB h3, h4, h5, h6, h7, h8, h9, h10,
    hSchnitt, h11, h12, h13, hReset, hS⟩

/-- A contract-free carrier decides `vertragsFreiB`: no `requires`, no `ensures`, no
    owed invariant mentions it. Needs no member list: the decided conjunction runs
    over the given one. -/
theorem vertragsFreiB_vollstaendig {c : D.Tab ⊕ D.Glob}
    (h : VertragsFrei P c) : vertragsFreiB P fs c = true := by
  unfold vertragsFreiB
  rw [Bool.and_eq_true_iff]
  refine ⟨List.all_eq_true.mpr fun g _ => ?_, List.all_eq_true.mpr fun i hi => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := h.1 g
    have e1 : !(istIn (P.requires g).orte c) = true := by
      cases he : istIn (P.requires g).orte c with
      | true => exact absurd (istIn_iff.mp he) h1
      | false => rfl
    have e2 : !(istIn (P.ensures g).orte c) = true := by
      cases he : istIn (P.ensures g).orte c with
      | true => exact absurd (istIn_iff.mp he) h2
      | false => rfl
    have e3 : !(istIn (invOrteP P g) c) = true := by
      cases he : istIn (invOrteP P g) c with
      | true => exact absurd (istIn_iff.mp he) h3
      | false => rfl
    simp only [Bool.and_eq_true_iff]
    exact ⟨⟨e1, e2⟩, e3⟩
  · cases he : istIn (P.invariante i).orte c with
    | true => exact absurd (istIn_iff.mp he) (h.2 i hi)
    | false => rfl

/-- **The footprint component with the admitted shared atomics is complete**: from
    `FussSX` over the admitted shared atomics, every footprint carrier is decided --
    signature-guarded or thread-local, lock-guarded, or an admitted shared atomic. -/
theorem fussWXB_vollstaendig (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hF : ∀ f, FussSX P S (lokW P fs ws) (GeteiltV P ws) f) : fussWXB P S fs ws = true := by
  unfold fussWXB
  refine List.all_eq_true.mpr fun f _ => ?_
  rw [Bool.and_eq_true_iff]
  have e : ∀ c : D.Tab ⊕ D.Glob, getrenntW P fs ws c = lokW P fs ws c :=
    fun c => congrFun (getrenntW_eq_lokW hvoll) c
  refine ⟨List.all_eq_true.mpr fun c hc => ?_, List.all_eq_true.mpr fun c hc => ?_⟩
  · rcases (hF f).1 c hc with h | ⟨L, hB, hL⟩ | hGt
    · rw [(e c).symm] at h
      simp only [Bool.or_eq_true_iff]
      exact Or.inl (Or.inl (by simpa only [Bool.or_eq_true_iff] using h))
    · simp only [Bool.or_eq_true_iff]
      exact Or.inl (Or.inr (List.any_eq_true.mpr ⟨L, waechterVon_mem.mpr hB, istIn_iff.mpr hL⟩))
    · obtain ⟨⟨ha, hG, _⟩, hV⟩ := hGt
      have hempty : waechterVon c = [] :=
        List.eq_nil_iff_forall_not_mem.mpr (fun L hL => hG L (waechterVon_mem.mp hL))
      have hg : geteiltVB P fs c = true := by
        unfold geteiltVB
        simp only [Bool.and_eq_true_iff]
        refine ⟨⟨atomarB_iff.mpr ha, ?_⟩, vertragsFreiB_vollstaendig hV⟩
        rw [hempty]
        rfl
      simp only [Bool.or_eq_true_iff]
      exact Or.inr hg
  · have h := (hF f).2 c hc
    rw [(e c).symm] at h
    exact h

/-- **The reverse direction**: `AkzeptiertSpecX` gives `AkzeptiertX`, at an explicitly
    admitted check list and the listed query axioms. The footprint needs exactly the completeness above; every other component
    already decides both ways. The arena fields are dropped: the Bool has none. The
    scope conjunct is derived from the floor field (`scopesOkProg_of_stufenM`),
    not taken as a premise. -/
theorem akzeptiertX_of_spec [RootNativeFloat.Hardware]
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls)
    (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) {B : List (ArenaOwnership.Body.ArenaIface D)}
    {aks : List (Kernzelle.AccumulatorDecl D)} (h : AkzeptiertSpecX P S fs ws B aks)
    (qs : List D.Ax) (hq : ∀ a ∈ aks, ∃ q ∈ qs, Kernzelle.KernAbfrageVerbunden P a q)
    {checks : List (CheckDecl D)} (hChecks : CheckAdmission P fs checks)
    (hI : Invarianten.Pruefer.programInvariantsB P S fs (fun _ => none) {} ls = true)
    (hK : Vertraege.Pruefer.KontrakteGeprueftB P S fs = true) :
    AkzeptiertX P S fs ls cs ws aks checks qs = true := by
  unfold AkzeptiertX
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, hK⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, hI⟩
  simp only [GuestBoundary.admissionB_nil, Bool.and_true, Bool.and_eq_true_iff, and_assoc]
  exact ⟨h.frag, (abgAlleB_iff hvoll).mpr h.abg, fussWXB_vollstaendig hvoll h.fuss,
    (stufenB_iff hvoll).mpr h.stufen, (sperrOrteB_iff hls).mpr h.sperrOrte,
    wurzelnB_iff.mpr h.wurzeln, (einzelnPoolB_iff hvoll hcs).mpr h.einzeln,
    (rennB_iff hvoll hcs).mpr h.renn, (antwortenB_iff hvoll).mpr h.antworten,
    (maskenB_iff hvoll).mpr h.masken, (schnittstellenB_iff hvoll).mpr h.schnittstellen,
    (libraryB_iff _ _).mpr h.bibliothek,
    (Kernzelle.accumulatorB_iff hvoll (tabsOf_voll hcs) (globsOf_voll hcs)).mpr ⟨h.akku, hq⟩,
    (checkB_iff hvoll (tabsOf_voll hcs) (globsOf_voll hcs)).mpr hChecks, (resetB_iff hcs).mpr h.reset,
    (scopesOkProgB_iff hvoll).mpr (scopesOkProg_of_stufenM h.stufen)⟩

end Bool

#print axioms Gabbro.Grammatik.Zielsatz.akzeptiertSpecX_of_spec
#print axioms Gabbro.Grammatik.Zielsatz.ziel_atomar_spec
#print axioms Gabbro.Grammatik.Zielsatz.rennfrei_atomar_spec
#print axioms Gabbro.Grammatik.Zielsatz.akzeptiertSpecX_of
#print axioms Gabbro.Grammatik.Zielsatz.akzeptiertX_of_akzeptiert

end Gabbro.Grammatik.Zielsatz
