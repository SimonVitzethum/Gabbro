/-
  File:      Grammatik/Speichermodell/AtomarZeuge.lean
  Subject:   The checker side of racing atomics (Opus lane O25, 2026-09-26): the footprint
             component with the atomic exemption as a Bool (`fussWAB`), the checker Bool
             `AkzeptiertA` that uses it, its link to the memory theorem of `Atomar.lean`, and the
             witnesses. Standalone: `Zielsatz/Spec.lean` and `Akzeptiert` are unchanged.

  * `fussWAB_iff` -- the Bool decides `FussSA` (the footprint property with atomics exempt).
  * `akzeptiertA_of_akzeptiert` -- EMBEDDING: every program the goal's checker `Akzeptiert`
    accepts, `AkzeptiertA` accepts (old units keep their verdicts).
  * `schwach_ist_gA_akzeptiert` -- on a program `AkzeptiertA` accepts, with an admissible start:
    every step of W is a step of GA, and the memory it is presented is G's at every
    non-atomic carrier.
  * `w_sprache_akzeptiertA` -- the legs of `Ziel` that the LANGUAGE carries without the user's
    proof hold at every machine W reaches on such a program: the trace invariant
    (`speicherSicher`), lock exclusivity, no global deadlock, no wait cycle, the time bound.
    The contract legs are not here (they need the replay: OFFEN O25).
  * WITNESSES, on the noninterference fixture (`NIZeuge`: the globals `konfig`, `zaehler` are
    `atomic`, the tables `tabA`, `tabB` plain):
    - `n1_akzeptiertA` / `n1_nicht_sc_aber_ga` -- the FLAG: configuration 1 (`kern` publishes
      `konfig`, the tenants `hauptA`/`hauptB` read it with no lock) is refused by `Akzeptiert`
      and accepted by `AkzeptiertA`; on it W really takes the non-SC step of `w_nicht_sc`
      (`hauptA` reads the stale `konfig` after `kern`'s write) -- and that step is a GA step
      whose presented memory is G's at both plain tables. The leg `schwach` of `Ziel` (W takes
      only G's steps) is FALSE there (`schwach_nicht_trivial`): a goal over `AkzeptiertA`
      needs the leg in GA form (`messung/OPUS-O25-ATOMICS.md` §5).
    - `faltung_akzeptiertA` -- the PER-CORE FOLD (OFFEN O17, read half): `zaehlA` twice (a pool
      writing the atomic accumulator `zaehler`) and `zaehlB` (reads `zaehler`, the fold) --
      refused by `Akzeptiert` at the footprint component, accepted by `AkzeptiertA`.
    - `nutzlast_ohne_erwerb_abgelehnt` -- the REFUSAL: `hauptA` writes the PLAIN table `tabA`,
      `zaehlA` reads it with no lock (a payload read without any synchronisation) -- refused
      by `AkzeptiertA`, at its footprint component: the exemption is for atomics only.
-/
import Grammatik.Speichermodell.Atomar
import Grammatik.Speichermodell.Zeuge

namespace Gabbro.Grammatik

open Speichermodell Zielsatz

variable {D : Deklaration}

/-! ## 1. The Bool -/

theorem atomarB_iff {c : D.Tab ⊕ D.Glob} : atomarB c = true ↔ AtomarAusgenommen c := by
  cases c with
  | inl t =>
      constructor
      · intro h; cases h
      · rintro ⟨g, e, _⟩; cases e
  | inr g =>
      constructor
      · intro h; exact ⟨g, rfl, h⟩
      · rintro ⟨g', e, h⟩
        cases e
        exact h

section Bool

variable [DecidableEq D.Fn]

/-- **The footprint component with the atomic exemption**: `fussWB` with ONE more disjunct at
    the footprint carriers, `atomarB c`. Device carriers are unchanged. -/
def fussWAB (P : Programm D) (S : SperrInv D) (fs ws : List D.Fn) : Bool :=
  fs.all fun f =>
    (fussOrte P f).all (fun c =>
      sigB f c || getrenntW P fs ws c || ((waechterVon c).any fun L => istIn (S.orte L) c) ||
        atomarB c) &&
    ((P.rumpf f).regs.flatMap D.rtraeger).all (fun c => sigB f c || getrenntW P fs ws c)

/-- **The checker with racing atomics**: `Akzeptiert` with `fussWAB` in place of `fussWB`; every
    other component is the goal's. -/
def AkzeptiertA (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) : Bool :=
  programmImFragmentG P fs && abgAlleB P fs && fussWAB P S fs ws && stufenB P fs &&
    sperrOrteB S ls && wurzelnB ws && einzelnPoolB P fs cs ws && rennB P fs cs ws &&
    antwortenB P fs

variable {P : Programm D} {S : SperrInv D} {fs : List D.Fn} {ls : List D.Lock}
  {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn}

theorem fussWAB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) :
    fussWAB P S fs ws = true ↔ ∀ f, FussSA P S (lokW P fs ws) f := by
  rw [← getrenntW_eq_lokW hvoll]
  constructor
  · intro h f
    have h1 := (List.all_eq_true.mp h) f (hvoll f)
    simp only [Bool.and_eq_true] at h1
    refine ⟨fun c hc => ?_, fun c hc => (List.all_eq_true.mp h1.2) c hc⟩
    have h2 := (List.all_eq_true.mp h1.1) c hc
    simp only [Bool.or_eq_true] at h2
    rcases h2 with (h2 | h2) | h2
    · exact Or.inl (by simp only [Bool.or_eq_true]; exact h2)
    · obtain ⟨L, hL, hc'⟩ := List.any_eq_true.mp h2
      exact Or.inr (Or.inl ⟨L, waechterVon_mem.mp hL, istIn_iff.mp hc'⟩)
    · exact Or.inr (Or.inr (atomarB_iff.mp h2))
  · intro h
    refine List.all_eq_true.mpr fun f _ => ?_
    simp only [Bool.and_eq_true]
    refine ⟨List.all_eq_true.mpr fun c hc => ?_, List.all_eq_true.mpr fun c hc => (h f).2 c hc⟩
    simp only [Bool.or_eq_true]
    rcases (h f).1 c hc with h2 | ⟨L, hL, hc'⟩ | h2
    · simp only [Bool.or_eq_true] at h2
      exact Or.inl (Or.inl h2)
    · exact Or.inl (Or.inr (List.any_eq_true.mpr ⟨L, waechterVon_mem.mpr hL, istIn_iff.mpr hc'⟩))
    · exact Or.inr (atomarB_iff.mpr h2)

/-- The old footprint component implies the new one. -/
theorem fussWAB_of_fussWB (h : fussWB P S fs ws = true) : fussWAB P S fs ws = true := by
  refine List.all_eq_true.mpr fun f hf => ?_
  have h1 := (List.all_eq_true.mp h) f hf
  simp only [Bool.and_eq_true] at h1 ⊢
  refine ⟨List.all_eq_true.mpr fun c hc => ?_, h1.2⟩
  have h2 := (List.all_eq_true.mp h1.1) c hc
  simp only [Bool.or_eq_true] at h2 ⊢
  exact Or.inl h2

/-- **EMBEDDING: every program the goal's checker accepts, `AkzeptiertA` accepts.** -/
theorem akzeptiertA_of_akzeptiert (h : Akzeptiert P S fs ls cs ws = true) :
    AkzeptiertA P S fs ls cs ws = true := by
  unfold Akzeptiert at h
  unfold AkzeptiertA
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, fussWAB_of_fussWB h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩

omit [DecidableEq D.Fn] in
/-- `FussSA` is monotone in the local carriers. -/
theorem fussSA_mono {lok lok' : D.Tab ⊕ D.Glob → Bool} {f : D.Fn}
    (hl : ∀ c, c ∈ fussOrteG P f → lok c = true → lok' c = true)
    (h : FussSA P S lok f) : FussSA P S lok' f := by
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · rcases h.1 c hc with h1 | h1
    · refine Or.inl ?_
      simp only [Bool.or_eq_true] at h1 ⊢
      exact h1.imp id (hl c (fuss_teilG P f hc))
    · exact Or.inr h1
  · have h1 := h.2 c hc
    simp only [Bool.or_eq_true] at h1 ⊢
    exact h1.imp id (hl c (List.mem_append_right _ hc))

/-- **What `AkzeptiertA` and an admissible start give the memory theorem**: closed call graphs
    containing the starts, the footprint property with atomics exempt over the computed graphs,
    and an exclusive start. -/
theorem akzeptiertA_ok {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hAk : AkzeptiertA P S fs ls cs ws = true)
    (hZ : StartZulaessig P S fs ws sp init) :
    (∀ t, AbgK P fs (kVon P fs init t)) ∧ (∀ t, kVon P fs init t (init t).1 = true) ∧
      (∀ f, FussSA P S (lokK P (kVon P fs init)) f) ∧ StartExklusiv init := by
  unfold AkzeptiertA at hAk
  simp only [Bool.and_eq_true] at hAk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, h2⟩, h3⟩, _⟩, _⟩, h6⟩, _⟩, _⟩, _⟩ := hAk
  have hAbg := (abgAlleB_iff hvoll).mp h2
  have hF := (fussWAB_iff hvoll).mp h3
  have hW := wurzelnB_iff.mp h6
  have hLeer : ∀ t, D.haelt (init t).1 = [] := fun t => by
    rcases hZ.wurzel t with h | h
    · exact (hW _ h).1
    · exact h.1
  refine ⟨fun t => hAbg _, fun t => reachB_wurzel P fs _, fun f => ?_,
    startExklusiv_ohne_haelt init hLeer⟩
  refine fussSA_mono (fun c _ hc => lokK_of (getrenntK_of hZ ?_)) (hF f)
  unfold lokW at hc
  exact @of_decide_eq_true _ (Classical.propDecidable _) hc

/-- **THE MEMORY THEOREM FOR AN ACCEPTED PROGRAM WITH RACING ATOMICS.** On a program
    `AkzeptiertA` accepts, from an admissible start, for every order assignment: every step of
    W from a state W reaches is a step of GA, and the memory it is presented is G's at every
    non-atomic carrier. -/
theorem schwach_ist_gA_akzeptiert {sp : Speicher D}
    {init : Faden → Σ f : D.Fn, Env D (D.params f)} {O : Orakel D} {passes : Nat}
    {ord : D.Glob → Ordnung} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAk : AkzeptiertA P S fs ls cs ws = true) (hZ : StartZulaessig P S fs ws sp init)
    (hO : GutO O) {W W' : RufMaschineW D}
    (hr : RufErreichbarW P O passes ord (RufStartW (RufStartG P sp init)) W) {u : Faden}
    {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu) :
    RufSchrittGA P O passes W.g u W'.g ∧
      ∀ c, ¬ AtomarAusgenommen c → TraegerGleich σ W.g.speicher c := by
  obtain ⟨hAbg, hWu, hF, hex⟩ := akzeptiertA_ok hvoll hAk hZ
  exact schwach_ist_gA (S := S) hO hvoll hAbg hWu hF hex hr h

end Bool

/-! ## 2. The language-carried legs over W with racing atomics -/

section Sprache

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- The rank invariant of every thread on every GA run (it reads no memory). -/
theorem gaInv_rang (hO : GutO O) (hSt : StufenM P) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hND : ∀ t, (offen (startSpur (D := D) (init t).1)).Nodup) {M : RufMaschineG D}
    (hr : RufErreichbarGA P O passes (RufStartG P sp init) M) :
    ∀ t, RangInvG (init t).1 (M.faeden t) := by
  refine gaInv (I := fun M => ∀ t, RangInvG (init t).1 (M.faeden t))
    (fun M M' e h t => by rw [← e]; exact h t)
    (rangInvG_erreichbar (O := O) (passes := passes) hO hSt sp init hND .start) ?_ hr
  intro M M' u h hs t
  by_cases htu : t = u
  · subst htu; exact rangInvG_schritt hO hSt hs (h t)
  · rw [rufSchrittG_fremd hs t htu]; exact h t

/-- **No wait cycle** on every GA run (the argument of `kein_warteZyklusG`, from the rank
    invariant alone). -/
theorem kein_warteZyklusGA (hO : GutO O) (hSt : StufenM P) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hLeer : ∀ t, D.haelt (init t).1 = [])
    {M : RufMaschineG D} (hr : RufErreichbarGA P O passes (RufStartG P sp init) M) :
    KeinWarteZyklus M := by
  have hI := gaInv_rang hO hSt sp init (startSpur_nodup_leer init hLeer) hr
  intro n ts Ls hW he
  have hlt : ∀ i, i < n → D.rang (Ls i) < D.rang (Ls (i + 1)) := fun i hi =>
    (sperre_rang (hI (ts (i + 1))) (hW (i + 1) hi).1).2 (Ls i) (hW i (Nat.le_of_lt hi)).2
  have hle : ∀ i, i ≤ n → D.rang (Ls 0) ≤ D.rang (Ls i) := by
    intro i
    induction i with
    | zero => intro _; exact Int.le_refl _
    | succ i ih =>
        intro hi
        have h1 := hlt i hi
        have h2 := ih (Nat.le_of_succ_le hi)
        omega
  have h1 := (hW n (Nat.le_refl n)).2
  rw [he] at h1
  have hlast := (sperre_rang (hI (ts 0)) (hW 0 (Nat.zero_le n)).1).2 (Ls n) h1
  have := hle n (Nat.le_refl n)
  omega

/-- **No global deadlock** on every GA run (the argument of `keine_verklemmungG`). -/
theorem keine_verklemmungGA (hO : GutO O) (hSt : StufenM P) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hLeer : ∀ t, D.haelt (init t).1 = []) (ls : List D.Lock) (hls : ∀ L : D.Lock, L ∈ ls)
    {M : RufMaschineG D} (hr : RufErreichbarGA P O passes (RufStartG P sp init) M)
    (hW : ∀ t, ¬ FertigG M t → WartetG M t) : ∀ t, FertigG M t := by
  have hI := gaInv_rang hO hSt sp init (startSpur_nodup_leer init hLeer) hr
  intro t0
  refine Classical.byContradiction fun h0 => ?_
  let W := ls.filter fun L => @decide (∃ t, ¬ FertigG M t ∧ AnSperre M t L)
    (Classical.propDecidable _)
  have hWmem : ∀ L, L ∈ W ↔ ∃ t, ¬ FertigG M t ∧ AnSperre M t L := by
    intro L
    simp only [W, List.mem_filter, hls L, true_and]
    exact ⟨fun h => @of_decide_eq_true _ (Classical.propDecidable _) h,
      fun h => @decide_eq_true _ (Classical.propDecidable _) h⟩
  obtain ⟨L0, hL0⟩ := (hW t0 h0).1
  have hne : W ≠ [] := fun he => by
    have := (hWmem L0).mpr ⟨t0, h0, hL0⟩
    rw [he] at this
    exact List.not_mem_nil this
  obtain ⟨Lm, hLm, hmax⟩ := rang_max W hne
  obtain ⟨tm, htm, hAm⟩ := (hWmem Lm).mp hLm
  obtain ⟨u, hu, hLu⟩ := (hW tm htm).2 Lm hAm
  by_cases hFu : FertigG M u
  · rw [fertig_leer (hI u) (hLeer u) hFu] at hLu
    exact List.not_mem_nil hLu
  · obtain ⟨Lu, hAu⟩ := (hW u hFu).1
    have hlt := (sperre_rang (hI u) hAu).2 Lm hLu
    have hle := hmax Lu ((hWmem Lu).mpr ⟨u, hFu, hAu⟩)
    omega

variable [DecidableEq D.Fn] {S : SperrInv D} {fs : List D.Fn} {ls : List D.Lock}
  {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn}

/-- A run of W by index: the machines `Ws k`, the actors `ts k`. -/
def LaufW (P : Programm D) (O : Orakel D) (passes : Nat) (ord : D.Glob → Ordnung)
    (W0 : RufMaschineW D) (Ws : Nat → RufMaschineW D) (ts : Nat → Faden) (n : Nat) : Prop :=
  Ws 0 = W0 ∧ ∀ k, k < n → RufSchrittW P O passes ord (Ws k) (ts k) (Ws (k + 1))

omit [DecidableEq D.Fn] in
theorem laufW_erreichbar {ord : D.Glob → Ordnung} {W0 : RufMaschineW D}
    {Ws : Nat → RufMaschineW D} {ts : Nat → Faden} {n : Nat}
    (hl : LaufW P O passes ord W0 Ws ts n) : ∀ k, k ≤ n → RufErreichbarW P O passes ord W0 (Ws k)
  | 0, _ => by rw [hl.1]; exact .start
  | k + 1, hk => .schritt _ _ _ (laufW_erreichbar hl k (by omega)) (hl.2 k (by omega))

/-- **THE LANGUAGE-CARRIED LEGS OVER W, RACING ATOMICS INCLUDED.** On a program `AkzeptiertA`
    accepts, from an admissible start, for every order assignment, at every machine W reaches:
    * the trace invariant (`SpurInv`, the leg `speicherSicher` of `Ziel`) and lock exclusivity;
    * no global deadlock and no wait cycle (the legs `keineVerklemmung`, `keinZyklus`);
    * the time bound (`ZeitAb`, the leg `zeit`; it holds at every machine);
    * every step W takes from there is a step of GA whose presented memory is G's at every
      non-atomic carrier;
    and on every run of W (by index) RACE FREEDOM for every non-atomic carrier (the leg
    `rennfrei`, over W's runs): two accesses by different threads, one a write, are ordered
    through a guard lock. What is NOT here: the contract legs (`vertrag`, `sperrInv`,
    `invRueck`, `invGrund`, `startEnde`, `keinStartGrund`, `keinLogikHalt`, `fortschritt`),
    which come from the replay of the user's sequential proof -- OFFEN O25. -/
theorem w_sprache_akzeptiertA {sp : Speicher D}
    {init : Faden → Σ f : D.Fn, Env D (D.params f)} {ord : D.Glob → Ordnung}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls)
    (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    (hAk : AkzeptiertA P S fs ls cs ws = true) (hZ : StartZulaessig P S fs ws sp init)
    (hO : GutO O) :
    (∀ W : RufMaschineW D, RufErreichbarW P O passes ord (RufStartW (RufStartG P sp init)) W →
      SpurInv W.g ∧ Exklusiv W.g ∧
      ((∀ t, ¬ FertigG W.g t → WartetG W.g t) → ∀ t, FertigG W.g t) ∧
      KeinWarteZyklus W.g ∧ ZeitAb P O passes W.g ∧
      ∀ (W' : RufMaschineW D) (u : Faden), RufSchrittW P O passes ord W u W' →
        RufSchrittGA P O passes W.g u W'.g) ∧
    (∀ (Ws : Nat → RufMaschineW D) (ts : Nat → Faden) (n : Nat),
      LaufW P O passes ord (RufStartW (RufStartG P sp init)) Ws ts n →
      ∀ (i j : Nat) (c : D.Tab ⊕ D.Glob), i < j → j < n → ts i ≠ ts j →
        ZugriffG (Ws i).g (Ws (i + 1)).g (ts i) c → ZugriffG (Ws j).g (Ws (j + 1)).g (ts j) c →
        (SchreibG (Ws i).g (Ws (i + 1)).g (ts i) c ∨ SchreibG (Ws j).g (Ws (j + 1)).g (ts j) c) →
        ¬ AtomarAusgenommen c → ∃ L, Bewacht c L ∧ GeordnetG (fun k => (Ws k).g) ts L i j) := by
  obtain ⟨hAbg, hWu, hF, hex⟩ := akzeptiertA_ok hvoll hAk hZ
  have hAk' := hAk
  unfold AkzeptiertA at hAk'
  simp only [Bool.and_eq_true] at hAk'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, h4⟩, _⟩, h6⟩, h7⟩, h8⟩, _⟩ := hAk'
  have hSt := (stufenB_iff hvoll).mp h4
  have hW := wurzelnB_iff.mp h6
  have hPool := (einzelnPoolB_iff hvoll hcs).mp h7
  have hRenn := (rennB_iff hvoll hcs).mp h8
  have hLeer : ∀ t, D.haelt (init t).1 = [] := fun t => by
    rcases hZ.wurzel t with h | h
    · exact (hW _ h).1
    · exact h.1
  refine ⟨fun W hr => ?_, fun Ws ts n hl i j c hij hjn hfg hzi hzj hw hA => ?_⟩
  · have hGA := ga_aus_w hO hvoll hAbg hWu hF hex hr
    refine ⟨gaInv_spur hO sp init hGA, gaInv_exklusiv hO sp init hex hGA,
      fun hWt => keine_verklemmungGA hO hSt sp init hLeer ls hls hGA hWt,
      kein_warteZyklusGA hO hSt sp init hLeer hGA,
      fun f g n _ _ _ hadm hE _ run hA' =>
        frame_schritte_beschraenkt P O passes f g n hadm hE run hA',
      fun W' u hs => ?_⟩
    obtain ⟨σ, M'', wahl, neu, h⟩ := hs
    exact (schwach_ist_gA (S := S) hO hvoll hAbg hWu hF hex hr h).1
  · have hlGA : LaufGA P O passes (RufStartG P sp init) (fun k => (Ws k).g) ts n := by
      refine ⟨by show (Ws 0).g = _; rw [hl.1]; rfl, fun k hk => ?_⟩
      obtain ⟨σ, M'', wahl, neu, h⟩ := hl.2 k hk
      exact (schwach_ist_gA (S := S) hO hvoll hAbg hWu hF hex
        (laufW_erreichbar hl k (Nat.le_of_lt hk)) h).1
    exact rennfreiGA hO hvoll sp init hex (kVon P fs init) hAbg hWu
      (fun c hB hAt => schreibGetrenntK_of hZ hPool hB hAt (hRenn c hB hAt))
      (fun k => (Ws k).g) ts n hlGA i j c hij hjn hfg hzi hzj hw hA

end Sprache

/-! ## 3. Witnesses -/

namespace AtomarZeuge

open NIZeuge

/-- **The flag is refused by the goal's checker** (configuration 1: `kern` writes the atomic
    `konfig`, `hauptA`/`hauptB` read it, no lock)... -/
theorem n1_abgelehnt : Akzeptiert nP SchwachZeuge.nS nFs [] nCs [NFn.hauptA, NFn.hauptB, NFn.kern] = false :=
  SchwachZeuge.akzeptiert_n1_abgelehnt

/-- **... and accepted with the atomic exemption.** -/
theorem n1_akzeptiertA : AkzeptiertA nP SchwachZeuge.nS nFs [] nCs [NFn.hauptA, NFn.hauptB, NFn.kern] = true := by
  decide

/-- Every thread of `init1` runs `hauptA`, `hauptB`, `kern` or the idle `ruhe`. -/
theorem init1_fall (t : Faden) : (init1 t).1 = NFn.hauptA ∧ t = 0 ∨ (init1 t).1 = NFn.hauptB ∧ t = 1 ∨
    (init1 t).1 = NFn.kern ∧ t = 2 ∨ (init1 t).1 = NFn.ruhe := by
  by_cases h0 : t = 0
  · subst h0; exact Or.inl ⟨rfl, rfl⟩
  · by_cases h1 : t = 1
    · subst h1; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · by_cases h2 : t = 2
      · subst h2; exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · refine Or.inr (Or.inr (Or.inr ?_))
        unfold init1
        simp only [h0, h1, h2, if_false]
        rfl

/-- The idle routine is idle. -/
theorem ruhe_ruhig : Ruhig nP nFs NFn.ruhe :=
  (ruheB_iff nFs_voll nCs_voll).mp (by decide)

/-- **The start of configuration 1 is admissible** for its declared starts. -/
theorem n1_start (sp : Speicher nD) :
    StartZulaessig nP SchwachZeuge.nS nFs [NFn.hauptA, NFn.hauptB, NFn.kern] sp init1 where
  wurzel t := by
    rcases init1_fall t with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | h
    · exact Or.inl (by rw [h]; exact List.mem_cons_self)
    · exact Or.inl (by rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    · exact Or.inl (by rw [h]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · exact Or.inr (by rw [h]; exact ruhe_ruhig)
  einmal t u htu he := by
    refine Or.inl ?_
    rcases init1_fall t with ⟨h, ht⟩ | ⟨h, ht⟩ | ⟨h, ht⟩ | h
    · rcases init1_fall u with ⟨h', hu⟩ | ⟨h', _⟩ | ⟨h', _⟩ | h'
      · exact absurd (ht.trans hu.symm) htu
      · rw [h, h'] at he; cases he
      · rw [h, h'] at he; cases he
      · rw [h, h'] at he; cases he
    · rcases init1_fall u with ⟨h', _⟩ | ⟨h', hu⟩ | ⟨h', _⟩ | h'
      · rw [h, h'] at he; cases he
      · exact absurd (ht.trans hu.symm) htu
      · rw [h, h'] at he; cases he
      · rw [h, h'] at he; cases he
    · rcases init1_fall u with ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', hu⟩ | h'
      · rw [h, h'] at he; cases he
      · rw [h, h'] at he; cases he
      · exact absurd (ht.trans hu.symm) htu
      · rw [h, h'] at he; cases he
    · rw [h]; exact ruhe_ruhig
  req _ := rfl
  sperren L := nomatch L

/-- **THE FLAG, COVERED: on configuration 1 every W step is a GA step, and plain tables read
    the newest write** -- for every order assignment, every budget, every start memory. -/
theorem n1_ga (sp : Speicher nD) (ord : nD.Glob → Ordnung) (passes : Nat)
    {W W' : RufMaschineW nD}
    (hr : RufErreichbarW nP nO passes ord (RufStartW (RufStartG nP sp init1)) W) {u : Faden}
    {σ : Speicher nD} {M'' : RufMaschineG nD} {wahl : nD.Tab ⊕ nD.Glob → NachrichtW nD}
    {neu : nD.Tab ⊕ nD.Glob → Nat} (h : SchrittW nP nO passes ord W u W' σ M'' wahl neu) :
    RufSchrittGA nP nO passes W.g u W'.g ∧ ∀ t : NTab, σ.slots t = W.g.speicher.slots t := by
  obtain ⟨h1, h2⟩ := schwach_ist_gA_akzeptiert (ls := []) (cs := nCs) nFs_voll n1_akzeptiertA
    (n1_start sp) nO_gut hr h
  exact ⟨h1, fun t => h2 (.inl t) (fun ⟨_, e, _⟩ => by cases e)⟩

/-- **The language-carried legs on the flag program**, at every machine W reaches from
    configuration 1 (for every order assignment and budget). -/
theorem n1_sprache (sp : Speicher nD) (ord : nD.Glob → Ordnung) (passes : Nat)
    {W : RufMaschineW nD}
    (hr : RufErreichbarW nP nO passes ord (RufStartW (RufStartG nP sp init1)) W) :
    SpurInv W.g ∧ Exklusiv W.g ∧ KeinWarteZyklus W.g ∧ ZeitAb nP nO passes W.g := by
  obtain ⟨h1, h2, _, h4, h5, _⟩ := (w_sprache_akzeptiertA (ls := []) (cs := nCs) (ord := ord)
    (passes := passes) nFs_voll (fun L => nomatch L) nCs_voll n1_akzeptiertA (n1_start sp)
    nO_gut).1 W hr
  exact ⟨h1, h2, h4, h5⟩

/-- **NON-DEGENERATE: W's non-SC step really happens on this accepted program, and it is a GA
    step.** After `kern` wrote `konfig := 3`, W lets `hauptA` read the INITIAL `konfig` and
    store `0` into `tabA[0]`, where G on the same schedule stores `3` (`w_nicht_sc`): a stale
    atomic read. The theorem covers it -- the step is a GA step and the plain tables it was
    presented are G's. -/
theorem n1_nicht_sc_aber_ga (ord : nD.Glob → Ordnung) :
    ∃ W1 W2 : RufMaschineW nD,
      RufErreichbarW nP nO 0 ord (RufStartW (RufStartG nP sp0 init1)) W1 ∧
      RufSchrittW nP nO 0 ord W1 0 W2 ∧
      (W1.g.speicher.globs NGlob.konfig).n = 3 ∧ (W2.g.speicher.slots NTab.tabA 0 ()).n = 0 ∧
      ((r1M2 sp0).speicher.slots NTab.tabA 0 ()).n = 3 ∧
      RufSchrittGA nP nO 0 W1.g 0 W2.g := by
  obtain ⟨W1, W2, hW1, hs, _, hk, hA, hG⟩ := SchwachZeuge.w_nicht_sc ord
  obtain ⟨σ, M'', wahl, neu, h⟩ := hs
  exact ⟨W1, W2, hW1, ⟨σ, M'', wahl, neu, h⟩, hk, hA, hG, (n1_ga sp0 ord 0 hW1 h).1⟩

/-- On this accepted program the SC leg is false: `SchwachSC` fails at the machine G reaches
    after `kern`'s write (`schwach_nicht_trivial`). A goal over `AkzeptiertA` cannot keep the
    leg `schwach` as it is; its GA form is `n1_ga`. -/
theorem n1_schwachSC_falsch :
    AkzeptiertA nP SchwachZeuge.nS nFs [] nCs [NFn.hauptA, NFn.hauptB, NFn.kern] = true ∧
      ¬ SchwachSC nP nO 0 (RufStartG nP sp0 init1) (r1M1 sp0) :=
  ⟨n1_akzeptiertA, SchwachZeuge.schwach_nicht_trivial⟩

/-- **THE PER-CORE FOLD (OFFEN O17, read half).** `zaehlA` on two threads (a pool, each
    instance writing the atomic accumulator `zaehler`) and `zaehlB` reading it (the fold): the
    goal's checker refuses at the footprint component ... -/
theorem faltung_abgelehnt :
    Akzeptiert nP SchwachZeuge.nS nFs [] nCs [NFn.zaehlA, NFn.zaehlA, NFn.zaehlB] = false ∧
      fussWB nP SchwachZeuge.nS nFs [NFn.zaehlA, NFn.zaehlA, NFn.zaehlB] = false := by
  decide

/-- ... and `AkzeptiertA` accepts. -/
theorem faltung_akzeptiertA :
    AkzeptiertA nP SchwachZeuge.nS nFs [] nCs [NFn.zaehlA, NFn.zaehlA, NFn.zaehlB] = true := by
  decide

/-- Non-degenerate: the fold reads the atomic the pool writes. -/
theorem faltung_echt :
    TraegerSchreibt (D := nD) NFn.zaehlA (.inr NGlob.zaehler) = true ∧
      (.inr NGlob.zaehler : nD.Tab ⊕ nD.Glob) ∈ fussOrteG nP NFn.zaehlB ∧
      nD.atomar NGlob.zaehler = true :=
  ⟨rfl, istIn_iff.mp (by decide), rfl⟩

/-- **THE REFUSAL: a plain payload read with no synchronisation.** `hauptA` writes the PLAIN
    table `tabA`, `zaehlA` reads it, no lock: `AkzeptiertA` refuses, at its footprint
    component -- the exemption covers atomic carriers only, never a plain one. -/
theorem nutzlast_ohne_erwerb_abgelehnt :
    AkzeptiertA nP SchwachZeuge.nS nFs [] nCs [NFn.hauptA, NFn.zaehlA] = false ∧
      fussWAB nP SchwachZeuge.nS nFs [NFn.hauptA, NFn.zaehlA] = false := by
  decide

/-- Non-degenerate: the payload is plain, written by one start and read by the other. -/
theorem nutzlast_echt :
    TraegerSchreibt (D := nD) NFn.hauptA (.inl NTab.tabA) = true ∧
      (.inl NTab.tabA : nD.Tab ⊕ nD.Glob) ∈ fussOrteG nP NFn.zaehlA ∧
      ¬ AtomarAusgenommen (D := nD) (.inl NTab.tabA) := by
  refine ⟨rfl, istIn_iff.mp (by decide), fun ⟨_, e, _⟩ => by cases e⟩

end AtomarZeuge

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.fussWAB_iff
#print axioms Gabbro.Grammatik.akzeptiertA_of_akzeptiert
#print axioms Gabbro.Grammatik.schwach_ist_gA_akzeptiert
#print axioms Gabbro.Grammatik.w_sprache_akzeptiertA
#print axioms Gabbro.Grammatik.AtomarZeuge.n1_sprache
#print axioms Gabbro.Grammatik.AtomarZeuge.n1_akzeptiertA
#print axioms Gabbro.Grammatik.AtomarZeuge.n1_ga
#print axioms Gabbro.Grammatik.AtomarZeuge.n1_nicht_sc_aber_ga
#print axioms Gabbro.Grammatik.AtomarZeuge.n1_schwachSC_falsch
#print axioms Gabbro.Grammatik.AtomarZeuge.faltung_abgelehnt
#print axioms Gabbro.Grammatik.AtomarZeuge.faltung_akzeptiertA
#print axioms Gabbro.Grammatik.AtomarZeuge.nutzlast_ohne_erwerb_abgelehnt
