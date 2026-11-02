module

public import Grammatik.Zielsatz.Kern.Spec
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiOrte
public import Grammatik.Logik.Vertraege.EinpassenVoll
public import Grammatik.Zielsatz.Kern.Akzeptiert.Teil1
public import Grammatik.Zielsatz.Kern.Akzeptiert.Teil3

@[expose] public section

namespace Gabbro.Grammatik
open Zielsatz
variable {D : Deklaration}
section Akzeptiert
variable [DecidableEq D.Fn]
section Komponenten
variable {P : Programm D} {S : SperrInv D} {fs : List D.Fn} {ls : List D.Lock}
  {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn}

theorem poolSicherWB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    {w : D.Fn} : poolSicherWB P fs cs w = true ↔ PoolSicherW P fs w := by
  unfold poolSicherWB PoolSicherW PoolSicher
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, fun f hf c hc => ?_⟩
    have h4 := (List.all_eq_true.mp h3) f (hvoll f)
    rw [hf] at h4
    simp only [Bool.not_true, Bool.false_or] at h4
    have h5 := (List.all_eq_true.mp h4) c (hcs c)
    rw [hc] at h5
    simp only [Bool.not_true, Bool.false_or] at h5
    cases hl : waechterVon c with
    | nil =>
        have he : (([] : List D.Lock).isEmpty) = true := rfl
        rw [hl, he] at h5
        simp only [Bool.not_true, Bool.false_or] at h5
        cases c with
        | inl _ => simp only [atomarB, Bool.false_eq_true] at h5
        | inr g => exact Or.inr ⟨g, rfl, h5⟩
    | cons L _ => exact Or.inl ⟨L, waechterVon_mem.mp (hl.symm ▸ List.mem_cons_self)⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, List.all_eq_true.mpr fun f _ => ?_⟩
    cases hf : reachB P fs w f with
    | false => rfl
    | true =>
        refine List.all_eq_true.mpr fun c _ => ?_
        cases hc : TraegerSchreibt f c with
        | false => rfl
        | true =>
            rcases h3 f hf c hc with ⟨L, hL⟩ | ⟨g, rfl, hg⟩
            · have he : (waechterVon c).isEmpty = false := by
                have hmem : L ∈ waechterVon c := waechterVon_mem.mpr hL
                cases hl : waechterVon c with
                | nil => rw [hl] at hmem; cases hmem
                | cons _ _ => rfl
              rw [he]
              rfl
            · have hag : atomarB (.inr g) = true := hg
              simp only [Bool.not_true, hag, Bool.or_true]

/-- **The start component decides its field** (`AkzeptiertSpec.einzeln`, fix lane F10). -/
theorem einzelnPoolB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) :
    einzelnPoolB P fs cs ws = true ↔ EinzelnPool P fs ws := by
  unfold einzelnPoolB EinzelnPool
  rw [List.all_eq_true]
  constructor
  · intro h w hm
    have hw : w ∈ ws := hm.subset List.mem_cons_self
    have h1 := h w hw
    rw [Bool.or_eq_true, mehrfachB_iff.mpr hm] at h1
    rcases h1 with h1 | h1
    · cases h1
    · exact (poolSicherWB_iff hvoll hcs).mp h1
  · intro h w _
    rw [Bool.or_eq_true]
    cases hm : mehrfachB ws w
    · exact Or.inl rfl
    · exact Or.inr ((poolSicherWB_iff hvoll hcs).mpr (h w (mehrfachB_iff.mp hm)))

/-- **The handler component decides its field** (`AkzeptiertSpec.masken`, Opus agent H). -/
theorem maskenB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) : maskenB P fs = true ↔ MaskenDisziplin P fs := by
  unfold maskenB maskenDisziplinB MaskenDisziplin
  constructor
  · intro h w hw f hf
    have h1 := List.all_eq_true.mp h w (hvoll w)
    rw [hw] at h1
    simp only [Bool.not_true, Bool.false_or] at h1
    have h2 := List.all_eq_true.mp h1 f (hvoll f)
    rw [hf] at h2
    simpa using h2
  · intro h
    refine List.all_eq_true.mpr fun w _ => ?_
    cases hw : P.unterbricht w
    · rfl
    · refine List.all_eq_true.mpr fun f _ => ?_
      cases hf : reachB P fs w f
      · rfl
      · simpa using h w hw f hf

/-- **No handler, no condition**: on a program that declares no function entered by hardware the
    handler component is `true` -- the Bool is the conjunction of before. -/
theorem maskenB_ohne (h : ∀ f, P.unterbricht f = false) : maskenB P fs = true :=
  List.all_eq_true.mpr fun w _ => by rw [h w]; rfl

/-- **`Akzeptiert` decides exactly `AkzeptiertSpec`** (given complete member
    lists). -/
theorem akzeptiert_iff (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls)
    (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) :
    Akzeptiert P S fs ls cs ws = true ↔ AkzeptiertSpec P S fs ws := by
  unfold Akzeptiert
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩
    exact ⟨h1, (abgAlleB_iff hvoll).mp h2, (fussWB_iff hvoll).mp h3, (stufenB_iff hvoll).mp h4,
      (sperrOrteB_iff hls).mp h5, wurzelnB_iff.mp h6, (einzelnPoolB_iff hvoll hcs).mp h7,
      (rennB_iff hvoll hcs).mp h8, (antwortenB_iff hvoll).mp h9, (maskenB_iff hvoll).mp h10,
      (resetB_iff hcs).mp h11⟩
  · intro h
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h.frag, (abgAlleB_iff hvoll).mpr h.abg⟩, (fussWB_iff hvoll).mpr h.fuss⟩,
      (stufenB_iff hvoll).mpr h.stufen⟩, (sperrOrteB_iff hls).mpr h.sperrOrte⟩,
      wurzelnB_iff.mpr h.wurzeln⟩, (einzelnPoolB_iff hvoll hcs).mpr h.einzeln⟩,
      (rennB_iff hvoll hcs).mpr h.renn⟩,
      (antwortenB_iff hvoll).mpr h.antworten⟩, (maskenB_iff hvoll).mpr h.masken⟩,
      (resetB_iff hcs).mpr h.reset⟩

theorem akzeptiertSpec_of (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls)
    (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) (h : Akzeptiert P S fs ls cs ws = true) :
    AkzeptiertSpec P S fs ws :=
  (akzeptiert_iff hvoll hls hcs).mp h

end Komponenten

end Akzeptiert

/-- **The concrete checker is a `Pruefer`**: its Bool is `Akzeptiert`, and
    its soundness obligation against `AkzeptiertSpec` is `akzeptiert_iff`. -/
def akzeptiert_pruefer : Pruefer where
  akzeptiert := fun E fs ls cs => Akzeptiert E.P E.S fs ls cs E.ws
  korrekt := fun _ fs ls cs h => akzeptiertSpec_of fs.2 ls.2 cs.2 h

section Start

variable [DecidableEq D.Fn]

/-! ## 5. The start -/

/-- **An idle start, decided**: holds no lock by signature, has no reasons,
    and every function it reaches has an empty footprint and writes no
    carrier of the list `cs`. -/
def ruheB (P : Programm D) (fs : List D.Fn) (cs : List (D.Tab ⊕ D.Glob)) (w : D.Fn) : Bool :=
  (D.haelt w).isEmpty && decide (D.gruende w = 0) && fs.all fun f => !(reachB P fs w f) ||
    ((fussOrteG P f).isEmpty && cs.all fun c => !(TraegerSchreibt f c))

theorem ruheB_iff {P : Programm D} {fs : List D.Fn} {cs : List (D.Tab ⊕ D.Glob)}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) {w : D.Fn} :
    ruheB P fs cs w = true ↔ Ruhig P fs w := by
  unfold ruheB Ruhig
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, fun f hf => ?_⟩
    have h4 := (List.all_eq_true.mp h3) f (hvoll f)
    rw [hf] at h4
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, List.isEmpty_iff] at h4
    refine ⟨h4.1, fun c => ?_⟩
    have h5 := (List.all_eq_true.mp h4.2) c (hcs c)
    simpa using h5
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, List.all_eq_true.mpr fun f _ => ?_⟩
    cases hf : reachB P fs w f
    · rfl
    · obtain ⟨h4, h5⟩ := h3 f hf
      simp only [Bool.not_true, h4, List.isEmpty_nil, h5, Bool.not_false, Bool.true_and, Bool.false_or,
  List.all_eq_true, implies_true]

/-- The call graph of thread `t`, computed from its start function. -/
def kVon (P : Programm D) (fs : List D.Fn) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (t : Faden) : D.Fn → Bool :=
  reachB P fs (init t).1

variable {P : Programm D} {S : SperrInv D} {fs : List D.Fn} {ws : List D.Fn}
  {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}

/-- The declared-start test gives thread-locality for the computed graphs
    of every admissible start. -/
theorem getrenntK_of (hZ : StartZulaessig P S fs ws sp init)
    {c : D.Tab ⊕ D.Glob} (hc : Getrennt P fs ws c) : GetrenntK P (kVon P fs init) c := by
  intro t u htu f hf hcf g hg
  by_cases hrt : Ruhig P fs (init t).1
  · rw [(hrt.2.2 f hf).1] at hcf
    exact absurd hcf List.not_mem_nil
  by_cases hru : Ruhig P fs (init u).1
  · exact (hru.2.2 g hg).2 c
  have hwt := (hZ.wurzel t).resolve_right hrt
  have hwu := (hZ.wurzel u).resolve_right hru
  have hne : (init t).1 ≠ (init u).1 ∨ Mehrfach ws (init t).1 := by
    by_cases he : (init t).1 = (init u).1
    · exact Or.inr ((hZ.einmal t u htu he).resolve_left hrt)
    · exact Or.inl he
  exact hc _ hwt _ hwu hne f g hf hcf hg

/-- The declared-start write separation gives write separation over the
    computed graphs of every admissible start: an idle thread writes
    nothing and reads nothing, two busy threads running different declared
    starts are separated by `SchreibGetrennt`, and two busy threads running
    ONE routine run a routine declared twice (`Mehrfach`), which is
    pool-safe (`EinzelnPool`) and so writes no unguarded, non-atomic carrier
    at all (fix lane F10). -/
theorem schreibGetrenntK_of (hZ : StartZulaessig P S fs ws sp init) (hP : EinzelnPool P fs ws)
    {c : D.Tab ⊕ D.Glob} (hB : ∀ L, ¬ Bewacht c L) (hAt : ¬ AtomarAusgenommen c)
    (hc : SchreibGetrennt P fs ws c) :
    SchreibGetrenntK P (kVon P fs init) c := by
  intro t u htu g hg hgw h hh
  by_cases hrt : Ruhig P fs (init t).1
  · rw [(hrt.2.2 g hg).2 c] at hgw
    cases hgw
  by_cases hru : Ruhig P fs (init u).1
  · obtain ⟨h1, h2⟩ := hru.2.2 h hh
    exact ⟨h2 c, by rw [h1]; exact List.not_mem_nil⟩
  have hwt := (hZ.wurzel t).resolve_right hrt
  have hwu := (hZ.wurzel u).resolve_right hru
  by_cases he : (init t).1 = (init u).1
  · have hpool := hP _ ((hZ.einmal t u htu he).resolve_left hrt)
    rcases hpool.2.2 g hg c hgw with ⟨L, hL⟩ | hA
    · exact absurd hL (hB L)
    · exact absurd hA hAt
  · exact hc _ hwt _ hwu he g hg hgw h hh

/-- No thread starts holding a lock by signature, and none starts with
    reasons. -/
theorem wurzel_of (hA : AkzeptiertSpec P S fs ws) (hZ : StartZulaessig P S fs ws sp init)
    (t : Faden) : D.haelt (init t).1 = [] ∧ D.gruende (init t).1 = 0 := by
  rcases hZ.wurzel t with h | h
  · exact hA.wurzeln _ h
  · exact ⟨h.1, h.2.1⟩

/-- **`Akzeptiert_ok` -- the checker's facts and an admitted start give every
    decidable premise of the flagships**, with the call graphs computed
    from the program (`kVon`). -/
theorem Akzeptiert_ok (hvoll : ∀ g : D.Fn, g ∈ fs) (hA : AkzeptiertSpec P S fs ws)
    (hZ : StartZulaessig P S fs ws sp init) :
    programmImFragmentG P fs = true ∧
    (∀ t, AbgK P fs (kVon P fs init t)) ∧
    (∀ t, kVon P fs init t (init t).1 = true) ∧
    (∀ f, FussS P S (lokK P (kVon P fs init)) f) ∧
    (∀ L c, c ∈ S.orte L → Bewacht c L) ∧
    StartGut P sp init ∧ (∀ L, S.inv L sp = true) ∧ StartExklusiv init ∧
    StufenM P ∧ (∀ t, D.haelt (init t).1 = []) ∧
    (∀ c, (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c →
      SchreibGetrenntK P (kVon P fs init) c) := by
  have hLeer : ∀ t, D.haelt (init t).1 = [] := fun t => (wurzel_of hA hZ t).1
  refine ⟨hA.frag, fun t => hA.abg _, fun t => reachB_wurzel P fs _, fun f => ?_, hA.sperrOrte,
    hZ.req, hZ.sperren, startExklusiv_ohne_haelt init hLeer, hA.stufen, hLeer,
    fun c hB hAt => schreibGetrenntK_of hZ hA.einzeln hB hAt (hA.renn c hB hAt)⟩
  refine fussS_mono (fun c _ hc => lokK_of (getrenntK_of hZ ?_)) (hA.fuss f)
  unfold lokW at hc
  exact @of_decide_eq_true _ (Classical.propDecidable _) hc

/-- **Race freedom for EVERY carrier (Spec's `RennfreiBis`) from the
    checker's facts and an admissible start.** Guarded carriers:
    `rennfrei_g_voll`; unguarded carriers that are not atomic -- publish
    payloads included (2026-09-15) -- write separation (`renn`) over the
    computed call graphs, `rennfrei_ungeschuetzt`. -/
theorem rennfreiBis_of (hvoll : ∀ g : D.Fn, g ∈ fs) (hA : AkzeptiertSpec P S fs ws)
    (hZ : StartZulaessig P S fs ws sp init) {O : Orakel D} (hO : GutO O) (passes : Nat)
    (M : RufMaschineG D) : RennfreiBis P O passes (RufStartG P sp init) M := by
  obtain ⟨-, hAbg, hW, -, -, -, -, hex, -, -, hsep⟩ := Akzeptiert_ok hvoll hA hZ
  intro ms ts n hl _ i j c hij hjn hfg hzi hzj hw hAt
  by_cases hB : ∃ L, Bewacht c L
  · obtain ⟨L, hL⟩ := hB
    exact ⟨L, hL, rennfrei_g_voll P O passes sp init hO hex ms ts n hl i j hij hjn hfg c L hL
      hzi hzj⟩
  · exact (rennfrei_ungeschuetzt hO hvoll sp init (kVon P fs init) hAbg hW ms ts n hl i j hij hjn
      hfg c (hsep c (fun L hL => hB ⟨L, hL⟩) hAt) hzi hzj hw).elim

end Start

/-! ## 6. `SperrInvOk`: the decided half and the user's half -/

theorem sperrInvOk_iff (S : SperrInv D) :
    SperrInvOk S ↔ (∀ L c, c ∈ S.orte L → Bewacht c L) ∧ SperrInvLokal S :=
  Iff.rfl

/-! ## 7. Finite start tables: `StartZulaessig` decided -/

/-- **A finite start table**: thread `i` below `aktiv.length` runs
    `aktiv[i]`, every later thread runs `ruhe` (G starts every thread of
    `Faden = Nat`). -/
structure StartTafel (D : Deklaration) where
  aktiv : List (Σ f : D.Fn, Env D (D.params f))
  ruhe : Σ f : D.Fn, Env D (D.params f)

/-- The start assignment of a table. -/
def StartTafel.init (st : StartTafel D) : Faden → Σ f : D.Fn, Env D (D.params f) :=
  fun t => st.aktiv.getD t st.ruhe

theorem StartTafel.init_mem (st : StartTafel D) (t : Faden) :
    st.init t = st.ruhe ∨ st.init t ∈ st.aktiv := by
  unfold StartTafel.init
  rw [List.getD_eq_getElem?_getD]
  cases h : st.aktiv[t]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_of_getElem? h)

theorem StartTafel.init_ab (st : StartTafel D) {t : Faden} (ht : st.aktiv.length ≤ t) :
    st.init t = st.ruhe := by
  unfold StartTafel.init
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none ht]
  rfl

section Tafel

variable [DecidableEq D.Fn]

/-- **`StartZulaessig` for a start table, as a Bool.** -/
def startB (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) (st : StartTafel D) (sp : Speicher D) : Bool :=
  ruheB P fs cs st.ruhe.1 &&
  (List.range st.aktiv.length).all (fun i =>
    (decide ((st.init i).1 ∈ ws) || ruheB P fs cs (st.init i).1) &&
    (List.range st.aktiv.length).all fun j =>
      decide (i = j) || !(decide ((st.init i).1 = (st.init j).1)) || ruheB P fs cs (st.init i).1) &&
  (st.ruhe :: st.aktiv).all (fun a =>
    wahr? (eval (sp.welt []) (P.requires a.1) (sp.welt []) a.2)) &&
  ls.all fun L => S.inv L sp

theorem startB_ok {P : Programm D} {S : SperrInv D} {fs : List D.Fn} {ls : List D.Lock}
    {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn} {st : StartTafel D} {sp : Speicher D}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    (h : startB P S fs ls cs ws st sp = true) : StartZulaessig P S fs ws sp st.init := by
  unfold startB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hR : ∀ w, ruheB P fs cs w = true → Ruhig P fs w := fun w hw => (ruheB_iff hvoll hcs).mp hw
  have hi : ∀ i, i < st.aktiv.length →
      ((st.init i).1 ∈ ws ∨ ruheB P fs cs (st.init i).1 = true) ∧
      ∀ j, j < st.aktiv.length → i ≠ j → (st.init i).1 = (st.init j).1 →
        ruheB P fs cs (st.init i).1 = true := by
    intro i hi
    have e := (List.all_eq_true.mp h2) i (List.mem_range.mpr hi)
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at e
    refine ⟨e.1, fun j hj hij he => ?_⟩
    have e2 := (List.all_eq_true.mp e.2) j (List.mem_range.mpr hj)
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
      at e2
    rcases e2 with (e2 | e2) | e2
    · exact absurd e2 hij
    · exact absurd he e2
    · exact e2
  refine ⟨fun t => ?_, fun t u htu he => ?_, fun t => ?_,
    fun L => (List.all_eq_true.mp h4) L (hls L)⟩
  · by_cases ht : t < st.aktiv.length
    · exact (hi t ht).1.imp id (hR _)
    · rw [st.init_ab (Nat.le_of_not_lt ht)]
      exact Or.inr (hR _ h1)
  · refine Or.inl (hR _ ?_)
    by_cases ht : t < st.aktiv.length
    · by_cases hu : u < st.aktiv.length
      · exact (hi t ht).2 u hu htu he
      · rw [he, st.init_ab (Nat.le_of_not_lt hu)]
        exact h1
    · rw [st.init_ab (Nat.le_of_not_lt ht)]
      exact h1
  · show wahr? (eval (sp.welt []) (P.requires (st.init t).1) (sp.welt []) (st.init t).2) = true
    rcases st.init_mem t with e | e
    · rw [e]
      exact (List.all_eq_true.mp h3) _ List.mem_cons_self
    · exact (List.all_eq_true.mp h3) _ (List.mem_cons_of_mem _ e)

end Tafel

#print axioms Gabbro.Grammatik.mehrfach_filter
#print axioms Gabbro.Grammatik.mehrfachB_iff
#print axioms Gabbro.Grammatik.nicht_mehrfach_of_nodup
#print axioms Gabbro.Grammatik.getrenntW_iff
#print axioms Gabbro.Grammatik.poolSicherWB_iff
#print axioms Gabbro.Grammatik.einzelnPoolB_iff
#print axioms Gabbro.Grammatik.schreibGetrenntW_iff
#print axioms Gabbro.Grammatik.rennB_iff
#print axioms Gabbro.Grammatik.antwortenB_iff
#print axioms Gabbro.Grammatik.maskenB_iff
#print axioms Gabbro.Grammatik.maskenB_ohne
#print axioms Gabbro.Grammatik.akzeptiert_iff
#print axioms Gabbro.Grammatik.akzeptiert_pruefer
#print axioms Gabbro.Grammatik.ruheB_iff
#print axioms Gabbro.Grammatik.getrenntK_of
#print axioms Gabbro.Grammatik.schreibGetrenntK_of
#print axioms Gabbro.Grammatik.Akzeptiert_ok
#print axioms Gabbro.Grammatik.rennfreiBis_of
#print axioms Gabbro.Grammatik.startB_ok

end Gabbro.Grammatik
