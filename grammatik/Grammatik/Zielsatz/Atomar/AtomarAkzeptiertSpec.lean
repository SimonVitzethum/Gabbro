/-
  File:      Grammatik/Zielsatz/AtomarAkzeptiert.lean
  Subject:   THE CHECKER SIDE OF THE ATOMIC RELY, and the theorem from (a), (b), (c), (d) to the
             legs over machine W. Opus lane O25b, 2026-09-26. Since lane O25c the
             definitions `GeteiltV`, `AkzeptiertSpecX`, `RennfreiBisGA` stand in `Spec.lean`.

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
module
public import Grammatik.Speichermodell.Atomar.AtomarZiel
public import Grammatik.Zielsatz.Atomar.AtomarInvarianten
public import Grammatik.Zielsatz.Atomar.AtomarMasken
public import Grammatik.Zielsatz.Atomar.AtomarPflicht
public import Grammatik.Zielsatz.Kern.Akzeptiert
public import Grammatik.Zielsatz.Kern.Akzeptiert.Bibliothek
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section


namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik Speichermodell

variable {D : Deklaration}

section Spec

variable [DecidableEq D.Fn]

/-- **EMBEDDING: every unit the goal's checker specification accepts, the new one accepts.**
    The checks ride along unchanged (the admission is over the same program). -/
theorem akzeptiertSpecX_of_spec {P : Programm D} {S : SperrInv D} {fs ws : List D.Fn}
    {A : List (Kernzelle.AccumulatorDecl D)} (h : AkzeptiertSpec P S fs ws A)
    (hI : ∀ f, Invarianten.Pruefer.InvariantDuties P S f)
    (hK : ∀ f, Vertraege.Pruefer.ContractDuties P S f) :
    AkzeptiertSpecX P S fs ws [] A :=
  ⟨h.frag, h.abg, fun f => fussSX_of_fussS (h.fuss f), h.stufen, h.sperrOrte, h.wurzeln,
    h.einzeln, h.renn, h.antworten, h.masken, h.schnittstellen, (fun _ h => nomatch h),
    (fun _ h => nomatch h), h.bibliothek, h.akku, h.pruef, h.reset, hI, hK⟩

/-- **The ownership judgment added to the checker's facts**: the facts of `AkzeptiertSpecX` that
    do not read the arenas hold for every arena list. -/
theorem AkzeptiertSpecX.mitBesitz {P : Programm D} {S : SperrInv D} {fs ws : List D.Fn}
    {B : List (ArenaOwnership.Body.ArenaIface D)} {A : List (Kernzelle.AccumulatorDecl D)}
    (h : AkzeptiertSpecX P S fs ws B A)
    (hb : ∀ a ∈ B', ArenaOwnership.Body.Checked P a.A a.I)
    (hw : ∀ a ∈ B', ArenaOwnership.Machine.ArenaPlain a.A) : AkzeptiertSpecX P S fs ws B' A :=
  { h with besitz := hb, worte := hw }

/-- **The accumulator admission added to the checker's facts**: the facts of `AkzeptiertSpecX`
    that do not read the accumulators hold for every accumulator list. -/
theorem AkzeptiertSpecX.mitAkku {P : Programm D} {S : SperrInv D} {fs ws : List D.Fn}
    {B : List (ArenaOwnership.Body.ArenaIface D)} {A A' : List (Kernzelle.AccumulatorDecl D)}
    (h : AkzeptiertSpecX P S fs ws B A)
    (ha : Kernzelle.AccumulatorAdmission P fs A') : AkzeptiertSpecX P S fs ws B A' :=
  { h with akku := ha }

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
theorem geteiltV_nicht_stabil (hvoll : ∀ g : D.Fn, g ∈ fs) {B : List (ArenaOwnership.Body.ArenaIface D)}
    {A : List (Kernzelle.AccumulatorDecl D)} (hA : AkzeptiertSpecX P S fs ws B A)
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

omit [DecidableEq D.Fn] in
/-- Every G run is a GA run: `RennfreiBisGA` contains `RennfreiBis`. -/
theorem rennfreiBis_of_GA {P : Programm D} {O : Orakel D} {passes : Nat} {M0 M : RufMaschineG D}
    (h : RennfreiBisGA P O passes M0 M) : RennfreiBis P O passes M0 M :=
  fun ms fs n hl hn => h ms fs n ⟨hl.1, fun k hk => schrittGA_of_g (hl.2 k hk)⟩ hn

/-- **The legs with shared atomics at a machine W**: `ZielAtomarW`, race freedom and the
    same-core interrupt leg on GA runs, and the four invariant legs
    of Opus agent D -- `InvRuheG`, `InvSichtG` at W's G-part, and the lock-move legs over every
    GX step from it (so over every W step, by the leg `schwach`). -/
structure ZielAtomar (P : Programm D) (S : SperrInv D) (O : Orakel D) (passes : Nat)
    (ord : D.Glob → Ordnung) (Tg : D.Tab ⊕ D.Glob → Prop) (M0 : RufMaschineG D)
    (W : RufMaschineW D) : Prop extends ZielAtomarW P S O passes ord Tg M0 W where
  invRuhe : InvRuheG P M0 W.g
  invSicht : InvSichtG P M0 W.g
  sperrWechsel : SperrWechselGX P O passes Tg S W.g
  sperrSicht : SperrSichtGX P O passes Tg S W.g
  -- race freedom and the same-core interrupt leg, on GA runs (which contain W's)
  rennfrei : RennfreiBisGA P O passes M0 W.g
  keinKernHalt : KernHaltGA P O passes M0 W.g

/-- **THE LEGS WITH SHARED ATOMICS FROM THE PREMISE GROUPS.** (a) the checker specification with
    the admitted shared atomics, (b) the user's logic against every answer a shared atomic read
    may give, (c) the named hardware assumptions, an admissible start: every machine W reaches
    satisfies `ZielAtomar` over `GeteiltV`. -/
theorem ziel_atomar_spec (P : Programm D) (S : SperrInv D) (Q : AxEns D) {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) {ls : List D.Lock} (hls : ∀ L : D.Lock, L ∈ ls) (ws : List D.Fn)
    {B : List (ArenaOwnership.Body.ArenaIface D)} {A : List (Kernzelle.AccumulatorDecl D)}
    (hA : AkzeptiertSpecX P S fs ws B A) (hN : LogikPflichtA P S Q (GeteiltA P ws)) (O : Orakel D)
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
  have hI := fun f => invGutSA_mono hT
    ((hA.invarianten f passes Q (GeteiltA P ws) (fun _ h => h.1)).1)
  have hIG := fun f => invGutGrundA_mono hT
    ((hA.invarianten f passes Q (GeteiltA P ws) (fun _ h => h.1)).2)
  have hex := startExklusiv_ohne_haelt init hLeer
  intro W hr
  have hZW := ziel_atomar_w P O passes ord Q S ls (kVon P fs init) (GeteiltV P ws) (lokW P fs ws)
    sp init hH.1 hH.2.1 (relyQ_of_O hH.2.2.1) hN.2.2 hS hA.stufen hvoll hls (fun t => hA.abg _)
    (fun t => reachB_wurzel P fs _) hTA hTV hTS hTO (fragX_ok hvoll hA.frag hA.fuss) hA.fuss
    hlokK hK hI hIG hZ.req hZ.sperren hex (fun t => (hW t).2) hLeer hA.antworten W hr
  have hInv := invarianten_atomar P O passes Q S (kVon P fs init) (GeteiltV P ws) (lokW P fs ws)
    sp init hH.1 hH.2.1 (relyQ_of_O hH.2.2.1) hN.2.2 hS hvoll (fun t => hA.abg _)
    (fun t => reachB_wurzel P fs _) hTA hTV hTS hTO (fragX_ok hvoll hA.frag hA.fuss) hA.fuss
    hlokK hK hI hIG hZ.req hZ.sperren hex (fun t => (hW t).2) W.g hZW.erreicht
  exact { hZW with
    invRuhe := hInv.1
    invSicht := hInv.2.1
    sperrWechsel := hInv.2.2.1
    sperrSicht := hInv.2.2.2
    rennfrei := fun ms fs' n hl _ i j c hij hjn hfg hzi hzj hw hAt =>
      rennfreiGA hH.1 hvoll sp init hex (kVon P fs init) (fun t => hA.abg _)
        (fun t => reachB_wurzel P fs _)
        (fun c hB hAt => schreibGetrenntK_of hZ hA.einzeln hB hAt (hA.renn c hB hAt))
        ms fs' n hl i j c hij hjn hfg hzi hzj hw hAt
    keinKernHalt := kernHaltGA_gilt P O passes _ _ }

/-- **Race freedom with shared atomics, on every run of W**: two accesses by different threads
    to a NON-atomic carrier, one a write, are ordered through a guard lock. -/
theorem rennfrei_atomar_spec (P : Programm D) (S : SperrInv D) {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (ws : List D.Fn) {B : List (ArenaOwnership.Body.ArenaIface D)}
    {A : List (Kernzelle.AccumulatorDecl D)} (hA : AkzeptiertSpecX P S fs ws B A)
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


end Gabbro.Grammatik.Zielsatz
