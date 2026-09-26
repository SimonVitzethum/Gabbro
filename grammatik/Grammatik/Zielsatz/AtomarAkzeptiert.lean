/-
  File:      Grammatik/Zielsatz/AtomarAkzeptiert.lean
  Subject:   THE CHECKER SIDE OF THE ATOMIC RELY, and the theorem from (a), (b), (c), (d) to the
             legs over machine W. Opus lane O25b, 2026-09-26. Standalone: `Spec.lean` is
             unchanged; this is the shape a Spec diff for OFFEN O25 would take.

  THE SHARED ATOMICS THE CHECKER ADMITS (`GeteiltV P ws c`): a shared atomic of the unit
  (`GeteiltA`: `atomic`, unguarded, not thread-local among the starts) that NO contract, requires,
  ensures or owed invariant mentions (`VertragsFrei`). A contract over such a carrier would be a
  claim about a value another thread may change at any moment; the rely cannot make it true,
  so the checker refuses it (`vertragsFreiB`, witness `vertrag_atomar_abgelehnt`).

  (a) `AkzeptiertSpecX` -- `AkzeptiertSpec` with ONE field changed: the footprint property
      `FussSX` admits a footprint carrier of `GeteiltV` beside the local and the guarded ones.
      Decided by `AkzeptiertX` (`akzeptiertSpecX_of`), which is `Akzeptiert` with the footprint
      component `fussWXB`.
  EMBEDDING: `akzeptiertSpecX_of_spec` / `akzeptiertX_of_akzeptiert` -- every unit the goal's
  checker accepts, the new one accepts.
  (b) `LogikPflichtA P S Q (GeteiltA P ws)` (Zielsatz/AtomarPflicht.lean): the user's bodies
      against every answer a shared atomic read may give; equivalent to `LogikPflicht` on every
      unit `AkzeptiertSpec` accepts (`logikPflichtA_iff_akzeptiert`).

  THE THEOREMS:
  * `ziel_atomar_spec` -- from (a) `AkzeptiertSpecX`, (b) `LogikPflichtA`, (c)
    `HardwareAnnahmen`, an admissible start: every machine W reaches (weak memory, racing
    atomics) satisfies `ZielAtomar` over `GeteiltV`: `ZielAtomarW` (Speichermodell/AtomarZiel.lean)
    and the four invariant legs of Opus agent D (Zielsatz/AtomarInvarianten.lean).
  * `rennfrei_atomar_spec` -- race freedom on every run of W, for every non-atomic carrier.
-/
import Grammatik.Speichermodell.AtomarZiel
import Grammatik.Zielsatz.AtomarInvarianten
import Grammatik.Zielsatz.AtomarPflicht
import Grammatik.Zielsatz.Akzeptiert

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik Speichermodell

variable {D : Deklaration}

section Spec

variable [DecidableEq D.Fn]

/-- **A shared atomic the checker admits**: shared (`GeteiltA`) and in no contract. -/
def GeteiltV (P : Programm D) (ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Prop :=
  GeteiltA P ws c ∧ VertragsFrei P c

/-- **(a) with the atomic rely**: `AkzeptiertSpec` with the footprint property `FussSX` over the
    admitted shared atomics `GeteiltV`. Every other field is `AkzeptiertSpec`'s. -/
structure AkzeptiertSpecX (P : Programm D) (S : SperrInv D) (fs ws : List D.Fn) : Prop where
  frag : programmImFragmentG P fs = true
  abg : ∀ w, AbgK P fs (reachB P fs w)
  fuss : ∀ f, FussSX P S (lokW P fs ws) (GeteiltV P ws) f
  stufen : StufenM P
  sperrOrte : ∀ L c, c ∈ S.orte L → Bewacht c L
  wurzeln : ∀ w ∈ ws, D.haelt w = [] ∧ D.gruende w = 0
  einzeln : EinzelnPool P fs ws
  renn : ∀ c, (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c → SchreibGetrennt P fs ws c
  antworten : ∀ f, ∀ x ∈ (P.rumpf f).ants, StelleOk D x

/-- **EMBEDDING: every unit the goal's checker specification accepts, the new one accepts.** -/
theorem akzeptiertSpecX_of_spec {P : Programm D} {S : SperrInv D} {fs ws : List D.Fn}
    (h : AkzeptiertSpec P S fs ws) : AkzeptiertSpecX P S fs ws :=
  ⟨h.frag, h.abg, fun f => fussSX_of_fussS (h.fuss f), h.stufen, h.sperrOrte, h.wurzeln,
    h.einzeln, h.renn, h.antworten⟩

variable {P : Programm D} {S : SperrInv D} {Q : AxEns D} {fs ws : List D.Fn}

omit [DecidableEq D.Fn] in
/-- The replay's fragment from the decided fragment and `FussSX` (the register half of the
    footprint is `FussS`'s). -/
theorem fragX_ok (hvoll : ∀ g : D.Fn, g ∈ fs) (h : programmImFragmentG P fs = true)
    {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} (hF : ∀ f, FussSX P S lok Tg f)
    (f : D.Fn) :
    (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true :=
  Endblock.gOk_mono (kandB_kandP P hvoll _) _ ((List.all_eq_true.mp h) f (hvoll f))
    (fun r hr => regP_of fun o ho => sicher_mem.mpr ⟨fuss_regG P f r hr o ho,
      (hF f).2 o (List.mem_flatMap.mpr ⟨r, hr, ho⟩)⟩)

/-- **An admitted shared atomic is stable nowhere**: it is not a signature-guarded carrier
    (unguarded), not thread-local (`lokW` is `Getrennt`, which is `GetrenntR` on closed graphs),
    and in no lock's carriers (`sperrOrte`). -/
theorem geteiltV_nicht_stabil (hvoll : ∀ g : D.Fn, g ∈ fs) (hA : AkzeptiertSpecX P S fs ws)
    {c : D.Tab ⊕ D.Glob} (hc : GeteiltV P ws c) (f : D.Fn) (Λ : List (Res D)) :
    c ∉ stabilS P S (lokW P fs ws) f Λ := by
  obtain ⟨⟨_, hB, hR⟩, _⟩ := hc
  intro hs
  rcases stabilS_mem.mp hs with h | ⟨L, _, hL⟩
  · have h2 := (sicher_mem.mp h).2
    simp only [Bool.or_eq_true] at h2
    rcases h2 with h2 | h2
    · obtain ⟨L, hL, _⟩ := List.any_eq_true.mp h2
      exact hB L (waechterVon_mem.mp hL)
    · unfold lokW at h2
      exact hR ((getrenntR_iff hvoll hA.abg c).mpr
        (@of_decide_eq_true _ (Classical.propDecidable _) h2))
  · exact hB L (hA.sperrOrte L c hL)

/-- **The legs with shared atomics at a machine W**: `ZielAtomarW` and the four invariant legs
    of Opus agent D -- `InvRuheG`, `InvSichtG` at W's G-part, and the lock-move legs over every
    GX step from it (so over every W step, by the leg `schwach`). -/
structure ZielAtomar (P : Programm D) (S : SperrInv D) (O : Orakel D) (passes : Nat)
    (ord : D.Glob → Ordnung) (Tg : D.Tab ⊕ D.Glob → Prop) (M0 : RufMaschineG D)
    (W : RufMaschineW D) : Prop extends ZielAtomarW P S O passes ord Tg M0 W where
  invRuhe : InvRuheG P M0 W.g
  invSicht : InvSichtG P M0 W.g
  sperrWechsel : SperrWechselGX P O passes Tg S W.g
  sperrSicht : SperrSichtGX P O passes Tg S W.g

/-- **THE LEGS WITH SHARED ATOMICS FROM THE PREMISE GROUPS.** (a) the checker specification with
    the admitted shared atomics, (b) the user's logic against every answer a shared atomic read
    may give, (c) the named hardware assumptions, an admissible start: every machine W reaches
    satisfies `ZielAtomar` over `GeteiltV`. -/
theorem ziel_atomar_spec (P : Programm D) (S : SperrInv D) (Q : AxEns D) {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) {ls : List D.Lock} (hls : ∀ L : D.Lock, L ∈ ls) (ws : List D.Fn)
    (hA : AkzeptiertSpecX P S fs ws) (hN : LogikPflichtA P S Q (GeteiltA P ws)) (O : Orakel D)
    (hH : HardwareAnnahmen O Q) (passes : Nat) (ord : D.Glob → Ordnung) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hZ : StartZulaessig P S fs ws sp init) :
    ∀ W : RufMaschineW D, RufErreichbarW P O passes ord (RufStartW (RufStartG P sp init)) W →
      ZielAtomar P S O passes ord (GeteiltV P ws) (RufStartG P sp init) W := by
  have hW : ∀ t, D.haelt (init t).1 = [] ∧ D.gruende (init t).1 = 0 := fun t => by
    rcases hZ.wurzel t with h | h
    · exact hA.wurzeln _ h
    · exact ⟨h.1, h.2.1⟩
  have hLeer : ∀ t, D.haelt (init t).1 = [] := fun t => (hW t).1
  have hS : SperrInvOk S := ⟨hA.sperrOrte, hN.2.1⟩
  have hT : ∀ c, GeteiltV P ws c → GeteiltA P ws c := fun c h => h.1
  have hTA : ∀ c, GeteiltV P ws c → AtomarAusgenommen c := fun c h => h.1.1
  have hTV : ∀ c, GeteiltV P ws c → VertragsFrei P c := fun c h => h.2
  have hTS : ∀ c, GeteiltV P ws c → ∀ f Λ, c ∉ stabilS P S (lokW P fs ws) f Λ :=
    fun c h f Λ => geteiltV_nicht_stabil hvoll hA h f Λ
  have hTO : ∀ c, GeteiltV P ws c → ∀ L, c ∉ S.orte L :=
    fun c h L hL => h.1.2.1 L (hA.sperrOrte L c hL)
  have hlokK : ∀ c, lokW P fs ws c = true → GetrenntK P (kVon P fs init) c := fun c hc =>
    getrenntK_of hZ (by
      unfold lokW at hc
      exact @of_decide_eq_true _ (Classical.propDecidable _) hc)
  have hK := fun f => koerperGutSA_mono hT ((hN.1 passes f).1)
  have hI := fun f => invGutSA_mono hT ((hN.1 passes f).2.1)
  have hIG := fun f => invGutGrundA_mono hT ((hN.1 passes f).2.2)
  have hex := startExklusiv_ohne_haelt init hLeer
  intro W hr
  have hZW := ziel_atomar_w P O passes ord Q S ls (kVon P fs init) (GeteiltV P ws) (lokW P fs ws)
    sp init hH.1 hH.2.1 hH.2.2 hN.2.2 hS hA.stufen hvoll hls (fun t => hA.abg _)
    (fun t => reachB_wurzel P fs _) hTA hTV hTS hTO (fragX_ok hvoll hA.frag hA.fuss) hA.fuss
    hlokK hK hI hIG hZ.req hZ.sperren hex (fun t => (hW t).2) hLeer hA.antworten W hr
  have hInv := invarianten_atomar P O passes Q S (kVon P fs init) (GeteiltV P ws) (lokW P fs ws)
    sp init hH.1 hH.2.1 hH.2.2 hN.2.2 hS hvoll (fun t => hA.abg _)
    (fun t => reachB_wurzel P fs _) hTA hTV hTS hTO (fragX_ok hvoll hA.frag hA.fuss) hA.fuss
    hlokK hK hI hIG hZ.req hZ.sperren hex (fun t => (hW t).2) W.g hZW.erreicht
  exact { hZW with
    invRuhe := hInv.1
    invSicht := hInv.2.1
    sperrWechsel := hInv.2.2.1
    sperrSicht := hInv.2.2.2 }

/-- **Race freedom with shared atomics, on every run of W**: two accesses by different threads
    to a NON-atomic carrier, one a write, are ordered through a guard lock. -/
theorem rennfrei_atomar_spec (P : Programm D) (S : SperrInv D) {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (ws : List D.Fn) (hA : AkzeptiertSpecX P S fs ws)
    (O : Orakel D) (hO : GutO O) (passes : Nat) (ord : D.Glob → Ordnung) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hZ : StartZulaessig P S fs ws sp init)
    (Ws : Nat → RufMaschineW D) (ts : Nat → Faden) (n : Nat)
    (hl : LaufW P O passes ord (RufStartW (RufStartG P sp init)) Ws ts n)
    (i j : Nat) (c : D.Tab ⊕ D.Glob) (hij : i < j) (hjn : j < n) (hfg : ts i ≠ ts j)
    (hzi : ZugriffG (Ws i).g (Ws (i + 1)).g (ts i) c)
    (hzj : ZugriffG (Ws j).g (Ws (j + 1)).g (ts j) c)
    (hw : SchreibG (Ws i).g (Ws (i + 1)).g (ts i) c ∨ SchreibG (Ws j).g (Ws (j + 1)).g (ts j) c)
    (hAt : ¬ AtomarAusgenommen c) : ∃ L, Bewacht c L ∧ GeordnetG (fun k => (Ws k).g) ts L i j := by
  have hLeer : ∀ t, D.haelt (init t).1 = [] := fun t => by
    rcases hZ.wurzel t with h | h
    · exact (hA.wurzeln _ h).1
    · exact h.1
  have hex := startExklusiv_ohne_haelt init hLeer
  have hlokK : ∀ c, lokW P fs ws c = true → GetrenntK P (kVon P fs init) c := fun c hc =>
    getrenntK_of hZ (by
      unfold lokW at hc
      exact @of_decide_eq_true _ (Classical.propDecidable _) hc)
  have hlGA : LaufGA P O passes (RufStartG P sp init) (fun k => (Ws k).g) ts n := by
    refine ⟨by show (Ws 0).g = _; rw [hl.1]; rfl, fun k hk => ?_⟩
    obtain ⟨σ, M'', wahl, neu, h⟩ := hl.2 k hk
    exact gx_ga (fun c h => h.1.1) (schwach_ist_gX (S := S) hO hvoll (fun t => hA.abg _)
      (fun t => reachB_wurzel P fs _) hA.fuss hlokK (fun c h => h.1.1) hex
      (laufW_erreichbar hl k (Nat.le_of_lt hk)) h).1
  exact rennfreiGA hO hvoll sp init hex (kVon P fs init) (fun t => hA.abg _)
    (fun t => reachB_wurzel P fs _)
    (fun c hB hAt => schreibGetrenntK_of hZ hA.einzeln hB hAt (hA.renn c hB hAt))
    (fun k => (Ws k).g) ts n hlGA i j c hij hjn hfg hzi hzj hw hAt

end Spec

/-! ## The Bool -/

section Bool

variable [DecidableEq D.Fn] {P : Programm D} {S : SperrInv D} {fs : List D.Fn}
  {ls : List D.Lock} {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn}

/-- **No contract mentions `c`**: no `requires`, no `ensures`, no owed invariant of a function
    of the member list. -/
def vertragsFreiB (P : Programm D) (fs : List D.Fn) (c : D.Tab ⊕ D.Glob) : Bool :=
  fs.all fun g => !(istIn (P.requires g).orte c) && !(istIn (P.ensures g).orte c) &&
    !(istIn (invOrteP P g) c)

omit [DecidableEq D.Fn] in
theorem vertragsFreiB_ok (hvoll : ∀ g : D.Fn, g ∈ fs) {c : D.Tab ⊕ D.Glob}
    (h : vertragsFreiB P fs c = true) : VertragsFrei P c := by
  intro g
  have h1 := (List.all_eq_true.mp h) g (hvoll g)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
  obtain ⟨⟨h1, h2⟩, h3⟩ := h1
  refine ⟨fun hc => ?_, fun hc => ?_, fun hc => ?_⟩
  · rw [istIn_iff.mpr hc] at h1; cases h1
  · rw [istIn_iff.mpr hc] at h2; cases h2
  · rw [istIn_iff.mpr hc] at h3; cases h3

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

/-- **The checker with the atomic rely**: `Akzeptiert` with `fussWXB` in place of `fussWB`. -/
def AkzeptiertX (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) : Bool :=
  programmImFragmentG P fs && abgAlleB P fs && fussWXB P S fs ws && stufenB P fs &&
    sperrOrteB S ls && wurzelnB ws && einzelnPoolB P fs cs ws && rennB P fs cs ws &&
    antwortenB P fs

theorem fussWXB_ok (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    (h : fussWXB P S fs ws = true) (f : D.Fn) : FussSX P S (lokW P fs ws) (GeteiltV P ws) f := by
  rw [← getrenntW_eq_lokW hvoll]
  have h1 := (List.all_eq_true.mp h) f (hvoll f)
  simp only [Bool.and_eq_true] at h1
  refine ⟨fun c hc => ?_, fun c hc => (List.all_eq_true.mp h1.2) c hc⟩
  have h2 := (List.all_eq_true.mp h1.1) c hc
  simp only [Bool.or_eq_true] at h2
  rcases h2 with ((h2 | h2) | h2) | h2
  · exact Or.inl (by simp [h2])
  · exact Or.inl (by simp [h2])
  · obtain ⟨L, hL, hc'⟩ := List.any_eq_true.mp h2
    exact Or.inr (Or.inl ⟨L, waechterVon_mem.mp hL, istIn_iff.mp hc'⟩)
  · cases hg : getrenntW P fs ws c
    · refine Or.inr (Or.inr ?_)
      simp only [geteiltVB, Bool.and_eq_true] at h2
      obtain ⟨⟨ha, hw⟩, hv⟩ := h2
      refine ⟨⟨atomarB_iff.mp ha, fun L hL => ?_, fun hR => ?_⟩, vertragsFreiB_ok hvoll hv⟩
      · have := waechterVon_mem.mpr hL
        rw [List.isEmpty_iff.mp hw] at this
        exact List.not_mem_nil this
      · have := (getrenntW_iff hvoll).mpr ((getrenntR_iff hvoll hAbg c).mp hR)
        rw [hg] at this
        cases this
    · exact Or.inl (by simp)

/-- **The Bool decides (a)**: `AkzeptiertX` gives `AkzeptiertSpecX`. -/
theorem akzeptiertSpecX_of (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls)
    (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) (h : AkzeptiertX P S fs ls cs ws = true) :
    AkzeptiertSpecX P S fs ws := by
  unfold AkzeptiertX at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  have hAbg := (abgAlleB_iff hvoll).mp h2
  exact ⟨h1, hAbg, fussWXB_ok hvoll hAbg h3, (stufenB_iff hvoll).mp h4,
    (sperrOrteB_iff hls).mp h5, wurzelnB_iff.mp h6, (einzelnPoolB_iff hvoll hcs).mp h7,
    (rennB_iff hvoll hcs).mp h8, (antwortenB_iff hvoll).mp h9⟩

/-- The old footprint component implies the new one. -/
theorem fussWXB_of_fussWB (h : fussWB P S fs ws = true) : fussWXB P S fs ws = true := by
  refine List.all_eq_true.mpr fun f hf => ?_
  have h1 := (List.all_eq_true.mp h) f hf
  simp only [Bool.and_eq_true] at h1 ⊢
  refine ⟨List.all_eq_true.mpr fun c hc => ?_, h1.2⟩
  have h2 := (List.all_eq_true.mp h1.1) c hc
  simp only [Bool.or_eq_true] at h2 ⊢
  exact Or.inl h2

/-- **EMBEDDING, as Bools: every unit the goal's checker accepts, `AkzeptiertX` accepts.** -/
theorem akzeptiertX_of_akzeptiert (h : Akzeptiert P S fs ls cs ws = true) :
    AkzeptiertX P S fs ls cs ws = true := by
  unfold Akzeptiert at h
  unfold AkzeptiertX
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, fussWXB_of_fussWB h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩

end Bool

#print axioms Gabbro.Grammatik.Zielsatz.akzeptiertSpecX_of_spec
#print axioms Gabbro.Grammatik.Zielsatz.ziel_atomar_spec
#print axioms Gabbro.Grammatik.Zielsatz.rennfrei_atomar_spec
#print axioms Gabbro.Grammatik.Zielsatz.akzeptiertSpecX_of
#print axioms Gabbro.Grammatik.Zielsatz.akzeptiertX_of_akzeptiert

end Gabbro.Grammatik.Zielsatz
