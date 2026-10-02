/-
  File:      Grammatik/X86/CarrierTraceBridge.lean
  Subject:   Growing TSO history to typed-carrier W transition (lane 650).

  Consumes the append-only `TSOTrace` projections (`traceHist`,
  `traceSicht`, `traceFrisch` over `SpurKnoten`, never the resetting
  `histVon` 0/1 snapshot), the admitted source representation
  (`SourceMemory`: `RepSlot`, `rep_schritt_bleibt`), the grouping
  discipline (`WordAccessGrouping`: `WortGruppe`, `DrainSpur`,
  `FremdFrei`, `wort_gruppe_liest_zurueck`) and the source access
  enumeration (`SourceAccessCompleteness`: `blattFragment_voll`).

  Produces: an explicit inherited history relation (`ErbtW`: W
  timestamps below the trace clock, source view covered by the target
  projection) with proved initial and step preservation, and at least
  one actual typed-carrier `SchrittW` transition for a no-read
  fragment write whose grouped TSO drain installs the same word the
  source step writes -- not only the `lies` consequent. Ordinary
  grouped drains stay observationally grouped under actual access
  exclusion (`WortGruppe` + `FremdFrei` at every visited state), never
  silently hardware-atomic. Full W/GX/LOCK/scheduling closure stays
  OPEN (see CUTS).
-/
import Grammatik.X86.TSOTrace
import Grammatik.X86.SourceMemory
import Grammatik.X86.WordAccessGrouping
import Grammatik.X86.SourceAccessCompleteness
import Grammatik.RufAdaequatG
import Grammatik.RennfreiVoll
import Grammatik.Speichermodell.MaschineW
import Grammatik.Speichermodell.Sicht

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- INHERITED HISTORY (`ErbtW`): the W machine `W` inherits its time
    discipline from the append-only trace node `n`. Every W message
    timestamp is strictly below the trace clock (`traceFrisch`), and
    the source thread view at carrier `e` is covered by the target
    projection (`traceSicht`) of the acting core `c` at the slot
    address `a`. A clock bound plus a view coverage -- never an
    assumed read and never a whole simulation. -/
def ErbtW (n : SpurKnoten) (W : RufMaschineW D) (u : Faden) (c : Nat)
    (e : D.Tab ⊕ D.Glob) (a : Adresse) : Prop :=
  (∀ d m, m ∈ W.hist d → m.ts < traceFrisch n) ∧
  W.sicht u e ≤ traceSicht n c a

/-! ## 1. Initial and step preservation of the inherited history -/

/-- INITIAL: a start W machine (`RufStartW`: one timestamp-0 message
    per carrier, empty views) inherits from any trace start node
    (`spurStart`: clock 1). Both conjuncts compute: `0 < 1` and
    `0 ≤ _`. Every premise is used: `s` names the trace state,
    `M0` the W machine. -/
theorem erbtW_start (s : TSOZustand) (M0 : RufMaschineG D) (u : Faden)
    (c : Nat) (e : D.Tab ⊕ D.Glob) (a : Adresse) :
    ErbtW (spurStart s) (RufStartW M0) u c e a := by
  refine ⟨?_, ?_⟩
  · intro d m hm
    simp only [RufStartW, traceFrisch, spurStart] at hm ⊢
    simp at hm
    subst hm
    exact Nat.zero_lt_one
  · simp only [RufStartW, traceSicht, spurStart]
    exact Nat.zero_le _

/-- STEP: one projected trace step preserves the inheritance. The
    clock never moves backwards (issues keep it, flushes advance by
    one), so every W timestamp stays below it; the writer view only
    ever joins the old clock at the flushed address (hence stays
    above the covered source view by the invariant), every other
    entry is untouched. Every premise is used: `hErbt` for both
    bounds, `hinv` for the joined view, `hs` for the step
    equations. -/
theorem erbtW_schritt (n n' : SpurKnoten) (W : RufMaschineW D) (u : Faden)
    (c : Nat) (e : D.Tab ⊕ D.Glob) (a : Adresse)
    (hErbt : ErbtW n W u c e a) (hinv : SpurInv n)
    (hs : SpurSchritt n n') : ErbtW n' W u c e a := by
  obtain ⟨hClock, hView⟩ := hErbt
  obtain ⟨_, hblick⟩ := hinv
  refine ⟨?_, ?_⟩
  · intro d m hm
    have hlt : m.ts < n.frisch := hClock d m hm
    simp only [traceFrisch]
    cases hs with
    | issue c' a' v' h' hh' hb' hf' =>
      rw [hf']
      exact hlt
    | flush c0' e0' rest' h' he' hh' hb' hf' =>
      rw [hf']
      omega
  · simp only [traceSicht]
    cases hs with
    | issue c' a' v' h' hh' hb' hf' =>
      rw [hb']
      exact hView
    | flush c0 e0 rest h he hh hb hf =>
      have hbca := congrFun hb c
      rw [hbca]
      by_cases hc : c = c0
      · subst hc
        rw [if_pos rfl]
        by_cases ha : a = e0.addr
        · subst ha
          rw [Speichermodell.Sicht.setze_selbst]
          have hle : traceSicht n c e0.addr ≤ n.frisch :=
            Nat.le_of_lt (hblick c e0.addr)
          exact Nat.le_trans hView hle
        · rw [Speichermodell.Sicht.setze_anders _ _ ha]
          exact hView
      · rw [if_neg hc]
        exact hView

/-- FINITE-TRACE TRANSPORT: over every reached trace node the
    inheritance holds: the invariant rides along (via
    `spurSchritt_inv`) and each step preserves the relation. The
    consumer of `spur_verlauf_waechst`'s clock discipline: timestamps
    are never reset, so a start inheritance reaches every grown
    history. Every premise is used: `hr` for the induction,
    `hinv0`/`hErbt0` at the start, both through the steps. -/
theorem erbtW_waechst (n0 n : SpurKnoten) (W : RufMaschineW D) (u : Faden)
    (c : Nat) (e : D.Tab ⊕ D.Glob) (a : Adresse)
    (hr : SpurErreichbar n0 n) (hinv0 : SpurInv n0)
    (hErbt0 : ErbtW n0 W u c e a) : ErbtW n W u c e a := by
  have hboth : ∀ {x}, SpurErreichbar n0 x → SpurInv x ∧ ErbtW x W u c e a := by
    intro x hx
    induction hx with
    | start => exact ⟨hinv0, hErbt0⟩
    | schritt _ hstep ih =>
      exact ⟨spurSchritt_inv _ _ hstep ih.1,
        erbtW_schritt _ _ _ _ _ _ _ ih.2 ih.1 hstep⟩
  exact (hboth hr).2

/-! ## 2. The trace of a no-read fragment step -/

/-- A no-read `assignSlot` step (`hOrte`: both footprints empty, as
    for literals) prepends exactly one event -- the write of `t` --
    to the thread trace. The value/index evaluations never enter the
    trace, so no `hk`/`hv` premises are needed. Every premise is
    used: `O`/`passes` through the executed statement, the worlds
    through the delta, `hOrte` killing the read events. -/
theorem assignSlot_spur {D : Deklaration} {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t)))
    (e : Expr D Γ Λ (D.typ t f))
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (σ : World D) (ρ : Env D Γ)
    (hOrte : i.orte ++ e.orte = [])
    (σ' : World D) (ρ' : Env D Γ)
    (hExec : execStmt O passes keinRuf (Stmt.assignSlot (l := l) t f i e hw hL) σ ρ =
      .ok σ' ρ') :
    σ'.spur = [Ereignis.zugriff t true Λ
      (σ.lese Λ (i.orte ++ e.orte)).haelt] ++ σ.spur := by
  have hU : execStmt O passes keinRuf (Stmt.assignSlot (l := l) t f i e hw hL) σ ρ =
      Ausgang.ok
        ((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
          (eval (σ.lese Λ (i.orte ++ e.orte)) i
            (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
          (eval (σ.lese Λ (i.orte ++ e.orte)) e
            (σ.lese Λ (i.orte ++ e.orte)) ρ)) ρ := by
    simp only [execStmt]
  rw [hU] at hExec
  cases hExec
  rw [hOrte]
  simp only [World.schreibSlot, World.merke, World.storeSlot, World.lese,
    List.map_nil, List.nil_append]

/-! ## 3. One actual typed-carrier SchrittW from a grouped drain -/

/-- **WRITE TRANSITION (`schrittW_aus_gruppen_drain`).** A no-read
    fragment write (`hOrte`) whose word the grouped TSO drain
    installs (`WortGruppe` + exclusion-checked `DrainSpur`) yields an
    actual typed-carrier `SchrittW` -- not only the `lies`
    consequent -- together with the cross-side value agreement (the
    drained word parses to the source value) and the representation
    (`RepSlot`) at the written slot.

    The TSO side contributes the installed value (via
    `wort_gruppe_liest_zurueck`, hence every grouping premise) and
    the fresh timestamp (`traceFrisch nN` with the inherited
    `ErbtW` bound, hence `nN`, `hErbt`, `hInvN`, `hnode`). The source
    side contributes the write step (via `rep_schritt_bleibt`, hence
    every representation premise) and the access enumeration (via
    `blattFragment_voll`: no reads from `hOrte`, slot ownership for
    the written carrier). The G machine head stands at the same
    `assignSlot` (`hs`, `hhead`, `hwelt`, `hΛ`); `W` rides on `M`
    (`hWg`). The new W message sits exactly where `SchrittW.histS`
    puts it; unwritten carriers keep history and views. Tearing and
    foreign buffered values are refused, never admitted (the drain
    needs the full eight-entry group plus `FremdFrei` at every
    visited state). Every premise is used. -/
theorem schrittW_aus_gruppen_drain {D : Deklaration} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)}
    (P : Programm D) (O : Orakel D) (passes : Nat)
    (ord : D.Glob → Speichermodell.Ordnung)
    (t : D.Tab) (f : D.Feld t)
    (lo hi : Int) (hT : D.typ t f = .int lo hi)
    (base len off : Nat)
    (hOk : repOk (D.typ t f) base len off = true)
    (i : Expr D Γ Λ (.index (D.count t)))
    (e : Expr D Γ Λ (D.typ t f))
    (M : RufMaschineG D) (u : Faden)
    (σ : World D) (ρ : Env D Γ)
    (hw : (vertragVon D (M.faeden u).kopf.f).schreibt t = true)
    (hL : darf D t Λ)
    (s : Stmt D (vertragVon D (M.faeden u).kopf.f) l Γ Λ Λ)
    (rest : Endblock D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)
    (hs : s = Stmt.assignSlot t f i e hw hL)
    (hhead : (M.faeden u).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.cons s rest)⟩)
    (σL : World D) (hLese : σL = σ.lese Λ (i.orte ++ e.orte))
    (k : Int) (v : Zahl lo hi)
    (hk : (eval σL i σL ρ).n = k)
    (hv : (cast (congrArg (Wert D) hT) (eval σL e σL ρ) :
      Wert D (.int lo hi)) = v)
    (hOrte : i.orte ++ e.orte = [])
    (a : Adresse) (m m' : Speicher)
    (σ' : World D) (ρ' : Env D Γ)
    (hExec : execStmt O passes keinRuf (Stmt.assignSlot (l := l) t f i e hw hL) σ ρ =
      .ok σ' ρ')
    (hTgt : write64 m a (zahlWort v) = some m')
    (hRd : lesbar8 m a = true)
    (hLo : 0 ≤ lo) (hHi : hi < 2 ^ 64)
    (hwelt : M.weltVon u = σ)
    (hΛ : HeldIn Λ (offen (M.faeden u).spur))
    (W : RufMaschineW D) (hWg : W.g = M)
    (co : Nat) (nN : SpurKnoten)
    (hErbt : ErbtW nN W u co (Sum.inl t) a)
    (hInvN : SpurInv nN)
    (sN : TSOZustand) (hnode : nN.tso = sN)
    (s2 : TSOZustand) (tlist : List TSOZustand)
    (hgrp : WortGruppe s2 co a (zahlWort v))
    (hles : lesbar8 s2.mem a = true)
    (hspur : DrainSpur co s2 sN tlist) (hend : sN ∈ tlist)
    (hleer : sN.puffer co = []) (hstoer : ∀ x ∈ tlist, FremdFrei x co a) :
    ∃ (W' : RufMaschineW D) (σm : Gabbro.Grammatik.Speicher D)
      (M'' : RufMaschineG D)
      (wahl : D.Tab ⊕ D.Glob → NachrichtW D) (neu : D.Tab ⊕ D.Glob → Nat),
      SchrittW P O passes ord W u W' σm M'' wahl neu ∧
      (∃ w, read64 nN.tso.mem a = some w ∧ wortZahl lo hi w = some v) ∧
      RepSlot t k f lo hi hT a m' σ' := by
  subst hWg
  have hMain := rep_schritt_bleibt O passes keinRuf t f lo hi hT base len off hOk
    i e hw hL σ ρ σL hLese k v hk hv a m m' σ' ρ' hExec hTgt hRd
  have hSpurEq : (W.g.faeden u).spur = σ.spur := congrArg World.spur hwelt
  have hMem : W.g.speicher = σ.speicher := congrArg World.speicher hwelt
  have hW : (mitSpeicher W.g σ.speicher).weltVon u = σ := by
    dsimp only [mitSpeicher, RufMaschineG.weltVon, Speicher.welt]
    rw [hSpurEq]
    rfl
  have hExec0 : execStmt O passes keinRuf (Stmt.assignSlot (l := l) t f i e hw hL)
      ((mitSpeicher W.g σ.speicher).weltVon u) ρ = .ok σ' ρ' := by
    rw [hW]
    exact hExec
  have hSpur : σ'.spur = [Ereignis.zugriff t true Λ
      (σ.lese Λ (i.orte ++ e.orte)).haelt] ++ σ.spur :=
    assignSlot_spur O passes t f i e hw hL σ ρ hOrte σ' ρ' hExec
  have hread : read64 sN.mem a = some (zahlWort v) :=
    wort_gruppe_liest_zurueck s2 sN tlist co a (zahlWort v) hgrp hles
      hspur hend hleer hstoer
  refine ⟨⟨⟨σ'.speicher,
      rufUpdateG (W.g.faeden) u ⟨((W.g.faeden u).stapel),
        ⟨((W.g.faeden u).kopf.f), ((W.g.faeden u).kopf.rho),
          ((W.g.faeden u).kopf.s0),
          ⟨l, Γ, Λ, ρ', .ende rest⟩⟩, σ'.spur, ((W.g.faeden u).log)⟩,
      (W.g.lauf) ++ rufEigenG u
        [Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt],
      (W.g.start)⟩,
    fun c => if c = Sum.inl t then
      Speichermodell.nachricht (ordVon ord c)
        (vorSicht ord W u σ.speicher
          ⟨σ'.speicher,
            rufUpdateG (W.g.faeden) u ⟨((W.g.faeden u).stapel),
              ⟨((W.g.faeden u).kopf.f), ((W.g.faeden u).kopf.rho),
                ((W.g.faeden u).kopf.s0),
                ⟨l, Γ, Λ, ρ', .ende rest⟩⟩, σ'.spur, ((W.g.faeden u).log)⟩,
            (W.g.lauf) ++ rufEigenG u
              [Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt],
            (W.g.start)⟩
          (fun _ => ⟨0, σ.speicher, Speichermodell.Sicht.null⟩))
        c (traceFrisch nN) σ'.speicher :: W.hist c else W.hist c,
    fun t' => if t' = u then (fun c => if c = Sum.inl t then traceFrisch nN
      else vorSicht ord W u σ.speicher
        ⟨σ'.speicher,
          rufUpdateG (W.g.faeden) u ⟨((W.g.faeden u).stapel),
            ⟨((W.g.faeden u).kopf.f), ((W.g.faeden u).kopf.rho),
              ((W.g.faeden u).kopf.s0),
              ⟨l, Γ, Λ, ρ', .ende rest⟩⟩, σ'.spur, ((W.g.faeden u).log)⟩,
          (W.g.lauf) ++ rufEigenG u
            [Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt],
          (W.g.start)⟩
        (fun _ => ⟨0, σ.speicher, Speichermodell.Sicht.null⟩) c)
      else W.sicht t',
    W.lsicht⟩,
    σ.speicher,
    ⟨σ'.speicher,
      rufUpdateG (W.g.faeden) u ⟨((W.g.faeden u).stapel),
        ⟨((W.g.faeden u).kopf.f), ((W.g.faeden u).kopf.rho),
          ((W.g.faeden u).kopf.s0),
          ⟨l, Γ, Λ, ρ', .ende rest⟩⟩, σ'.spur, ((W.g.faeden u).log)⟩,
      (W.g.lauf) ++ rufEigenG u
        [Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt],
      (W.g.start)⟩,
    (fun _ => ⟨0, σ.speicher, Speichermodell.Sicht.null⟩),
    (fun _ => traceFrisch nN),
    ?_, ?_, hMain.1⟩
  · -- The SchrittW fields from the G-side facts above.
    generalize hgen : (⟨σ'.speicher,
      rufUpdateG (W.g.faeden) u ⟨((W.g.faeden u).stapel),
        ⟨((W.g.faeden u).kopf.f), ((W.g.faeden u).kopf.rho),
          ((W.g.faeden u).kopf.s0),
          ⟨l, Γ, Λ, ρ', .ende rest⟩⟩, σ'.spur, ((W.g.faeden u).log)⟩,
      (W.g.lauf) ++ rufEigenG u
        [Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt],
      (W.g.start)⟩ : RufMaschineG D) = MT
    have hM : ((mitSpeicher W.g σ.speicher).faeden u).spur = σ.spur := hSpurEq
    have hMmem : (mitSpeicher W.g σ.speicher).speicher = σ.speicher := rfl
    have hM'sp : (MT.faeden u).spur = σ'.spur := by
      rw [← hgen]; simp only [rufUpdateG_self]
    have hMTsp : MT.speicher = σ'.speicher := by rw [← hgen]
    have hFrag := blattFragment_voll O passes keinRuf t f i e hw hL σ ρ σ' ρ'
      hExec (mitSpeicher W.g σ.speicher) MT u hM hM'sp hMmem hMTsp
    obtain ⟨hEq, hSchreib, hLi, _, hOwn⟩ := hFrag
    have hLesen : lesenVon (mitSpeicher W.g σ.speicher) MT u = [] := by
      simp [lesenVon, hEq, hOrte, fragmentListe]
    have hEreig : ereignisse (mitSpeicher W.g σ.speicher) MT u =
        [Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt] := by
      apply ereignisse_eq
      rw [hM'sp, hSpur, hM]
    have hGenommen : genommenVon (mitSpeicher W.g σ.speicher) MT u = [] := by
      simp [genommenVon, hEreig]
    have hGegeben : gegebenVon (mitSpeicher W.g σ.speicher) MT u = [] := by
      simp [gegebenVon, hEreig]
    have hVor : vorSicht ord W u σ.speicher MT
        (fun _ => ⟨0, σ.speicher, Speichermodell.Sicht.null⟩) = W.sicht u := by
      simp only [vorSicht, hGenommen, hLesen, locksicht, lesesicht,
        List.foldr_nil]
    have hleaf : s.istBlatt = true := by
      rw [hs]; exact BlattG.istBlatt (BlattG.assignSlot t f i e hw hL)
    have hstep : execStmt O passes keinRuf s
        ((mitSpeicher W.g σ.speicher).weltVon u) ρ = Ausgang.ok σ' ρ' := by
      rw [hs, hW]; exact hExec
    have hneu' : σ'.spur =
        [Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt] ++
        ((mitSpeicher W.g σ.speicher).faeden u).spur := by
      rw [hSpur, hM]
    have hkein : ∀ (L : D.Lock) (h : List D.Lock),
        Ereignis.nimmt L h ∉
          [Ereignis.zugriff t true Λ
            (σ.lese Λ (i.orte ++ e.orte)).haelt] := by
      intro L h hm; simp at hm
    have hblatt : RufSchrittG P O passes (mitSpeicher W.g σ.speicher) u MT := by
      rw [← hgen]
      exact RufSchrittG.blatt (mitSpeicher W.g σ.speicher) u l Γ Λ Λ s rest ρ
        hleaf hhead hΛ σ' ρ'
        [Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt]
        hstep hneu' hkein
    refine ⟨hblatt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      simp only [LiestG] at hc
      rw [hEq, hOrte] at hc
      simp [fragmentListe] at hc
    · intro c hc
      -- Vacuous: presented memory is G memory by construction
      -- (`σ.speicher` over `W.g`), so every carrier agrees.
      rw [hMem]
      exact traegerGleich_refl _ _
    · intro c hc
      have hcEq := hOwn c hc
      subst hcEq
      rw [hVor]
      obtain ⟨hClock, hView⟩ := hErbt
      refine ⟨?_, ?_⟩
      · show (W.sicht u) (Sum.inl t) < traceFrisch nN
        exact Nat.lt_of_le_of_lt hView (hInvN.2 co a)
      · intro m hm
        show m.ts ≠ traceFrisch nN
        have hlt := hClock _ _ hm
        omega
    · exact fun c _ => traegerGleich_refl _ _
    · intro c hc
      have hTG : TraegerGleich MT.speicher
          (mitSpeicher W.g σ.speicher).speicher c := by
        simp only [SchreibG, not_or] at hc
        exact Classical.byContradiction hc.2
      rw [hMem]
      exact hTG
    · rfl
    · rfl
    · rfl
    · intro c hc
      have hcEq := hOwn c hc
      subst hcEq
      show (if Sum.inl t = Sum.inl t then
        Speichermodell.nachricht (ordVon ord (Sum.inl t))
          (vorSicht ord W u σ.speicher MT
            (fun _ => ⟨0, σ.speicher, Speichermodell.Sicht.null⟩))
          (Sum.inl t) (traceFrisch nN) σ'.speicher ::
          W.hist (Sum.inl t) else W.hist (Sum.inl t)) = _
      rw [if_pos rfl, hMTsp]
    · intro c hc
      by_cases he : c = Sum.inl t
      · subst he
        exact absurd hSchreib hc
      · show (if c = Sum.inl t then
          Speichermodell.nachricht (ordVon ord c)
            (vorSicht ord W u σ.speicher MT
              (fun _ => ⟨0, σ.speicher, Speichermodell.Sicht.null⟩))
            c (traceFrisch nN) σ'.speicher :: W.hist c
          else W.hist c) = W.hist c
        exact if_neg he
    · intro c hc
      have hcEq := hOwn c hc
      subst hcEq
      simp
    · intro c hc
      by_cases he : c = Sum.inl t
      · subst he
        exact absurd hSchreib hc
      · simp [he]
    · intro t' ht
      show ((if t' = u then (fun c => if c = Sum.inl t then traceFrisch nN
        else vorSicht ord W u σ.speicher MT
          (fun _ => ⟨0, σ.speicher, Speichermodell.Sicht.null⟩) c)
        else W.sicht t')) = W.sicht t'
      exact if_neg ht
    · intro L
      rw [hGegeben]
      simp
    · intro g hg
      obtain ⟨l', Γ', Λ', Λ'', neuE, hw', hL', rest', k', ρ', hK⟩ := hg
      rw [hhead] at hK
      cases hK
  · exact ⟨zahlWort v, by rw [hnode]; exact hread,
      zahlWort_wortZahl v hLo hHi⟩

/-! ## 4. Joint witness drain at the slot address -/

/-- The word the source writes: 42 as one little-endian word. -/
def ctV : Wort := zahlWort witVal

/-- A distant foreign address, far outside the slot footprint. -/
def ctF : Adresse := BitVec.ofNat 64 8192

/-- The foreign byte value (differs from canonical zero). -/
def ctFv : Byte := BitVec.ofNat 8 7

/-- The foreign address lies outside the slot footprint. -/
theorem ctFfresh : ctF ∉ Fuss witA := by decide

/-- Exclusion from a fixed foreign entry: core 1 holds exactly one
    pending byte outside the footprint, every other foreign buffer is
    empty. Every premise is used: `h1` for core 1, `hO` elsewhere. -/
theorem ctFremdFF (s : TSOZustand) (h1 : s.puffer 1 = [⟨ctF, ctFv⟩])
    (hO : ∀ d : Nat, d ≠ 0 → d ≠ 1 → s.puffer d = []) :
    FremdFrei s 0 witA := by
  intro d hne e he
  by_cases h1d : d = 1
  · subst h1d
    rw [h1] at he
    simp only [List.mem_singleton] at he
    subst he
    show ctF ∉ Fuss witA
    exact ctFfresh
  · have h2 := hO d hne h1d
    rw [h2] at he
    simp at he

/-- Drain start: zeroed fully-permissive memory, core 0 carries the
    exact eight-entry group for the source word at the slot address,
    all other buffers empty. -/
def ctS2 : TSOZustand :=
  ⟨witM, fun d => if d = 0 then wortEintraege witA ctV else []⟩

/-- After own flush 1: byte 0 installed. -/
def ctS3 : TSOZustand :=
  ⟨{ witM with bytes := fun x =>
      if x = addrOff witA 0 then wortByte ctV 0 else witM.bytes x },
    pufferSetze ctS2.puffer 0 ((wortEintraege witA ctV).drop 1)⟩

/-- Foreign issue on core 1 outside the footprint (real foreign
    activity inside the drain). -/
def ctS4 : TSOZustand :=
  ⟨ctS3.mem,
    pufferSetze ctS3.puffer 1 (ctS3.puffer 1 ++ [⟨ctF, ctFv⟩])⟩

/-- After own flush 2: bytes 0–1 installed. -/
def ctS5 : TSOZustand :=
  ⟨{ ctS4.mem with bytes := fun x =>
      if x = addrOff witA 1 then wortByte ctV 1 else ctS4.mem.bytes x },
    pufferSetze ctS4.puffer 0 ((wortEintraege witA ctV).drop 2)⟩

/-- After own flush 3: bytes 0–2 installed. -/
def ctS6 : TSOZustand :=
  ⟨{ ctS5.mem with bytes := fun x =>
      if x = addrOff witA 2 then wortByte ctV 2 else ctS5.mem.bytes x },
    pufferSetze ctS5.puffer 0 ((wortEintraege witA ctV).drop 3)⟩

/-- After own flush 4: bytes 0–3 installed. -/
def ctS7 : TSOZustand :=
  ⟨{ ctS6.mem with bytes := fun x =>
      if x = addrOff witA 3 then wortByte ctV 3 else ctS6.mem.bytes x },
    pufferSetze ctS6.puffer 0 ((wortEintraege witA ctV).drop 4)⟩

/-- After own flush 5: bytes 0–4 installed. -/
def ctS8 : TSOZustand :=
  ⟨{ ctS7.mem with bytes := fun x =>
      if x = addrOff witA 4 then wortByte ctV 4 else ctS7.mem.bytes x },
    pufferSetze ctS7.puffer 0 ((wortEintraege witA ctV).drop 5)⟩

/-- After own flush 6: bytes 0–5 installed. -/
def ctS9 : TSOZustand :=
  ⟨{ ctS8.mem with bytes := fun x =>
      if x = addrOff witA 5 then wortByte ctV 5 else ctS8.mem.bytes x },
    pufferSetze ctS8.puffer 0 ((wortEintraege witA ctV).drop 6)⟩

/-- After own flush 7: bytes 0–6 installed. -/
def ctS10 : TSOZustand :=
  ⟨{ ctS9.mem with bytes := fun x =>
      if x = addrOff witA 6 then wortByte ctV 6 else ctS9.mem.bytes x },
    pufferSetze ctS9.puffer 0 ((wortEintraege witA ctV).drop 7)⟩

/-- After own flush 8: all bytes installed, own buffer empty;
    the foreign byte stays pending. -/
def ctS11 : TSOZustand :=
  ⟨{ ctS10.mem with bytes := fun x =>
      if x = addrOff witA 7 then wortByte ctV 7 else ctS10.mem.bytes x },
    pufferSetze ctS10.puffer 0 ((wortEintraege witA ctV).drop 8)⟩

/-- Each recorded drain step computes as claimed. -/
theorem ct_step1 : flushKern ctS2 0 = some ctS3 := by rfl

theorem ct_step2 : issueByte ctS3 1 ctF ctFv = some ctS4 := by rfl

theorem ct_step3 : flushKern ctS4 0 = some ctS5 := by rfl

theorem ct_step4 : flushKern ctS5 0 = some ctS6 := by rfl

theorem ct_step5 : flushKern ctS6 0 = some ctS7 := by rfl

theorem ct_step6 : flushKern ctS7 0 = some ctS8 := by rfl

theorem ct_step7 : flushKern ctS8 0 = some ctS9 := by rfl

theorem ct_step8 : flushKern ctS9 0 = some ctS10 := by rfl

theorem ct_step9 : flushKern ctS10 0 = some ctS11 := by rfl

/-- Foreign buffers start empty off core 0. -/
theorem ctS2leer : ∀ d : Nat, d ≠ 0 → ctS2.puffer d = [] := by
  intro d hne
  show (if d = 0 then wortEintraege witA ctV else []) = []
  rw [if_neg hne]

/-- Foreign-buffer emptiness survives the first own flush. -/
theorem ctS3leer : ∀ d : Nat, d ≠ 0 → ctS3.puffer d = [] :=
  fremd_leer_eigen_erhalten ctS2 ctS3 ct_step1 ctS2leer

/-- The foreign entry lands on core 1. -/
theorem ctBuf1_4 : ctS4.puffer 1 = [⟨ctF, ctFv⟩] := by rfl

/-- Off-core buffers stay empty except core 1 after the foreign issue. -/
theorem ctOff01_4 : ∀ d : Nat, d ≠ 0 → d ≠ 1 → ctS4.puffer d = [] := by
  intro d h0 h1
  show pufferSetze ctS3.puffer 1 (ctS3.puffer 1 ++ [⟨ctF, ctFv⟩]) d = []
  rw [pufferSetze_anders _ _ h1]
  show ctS3.puffer d = []
  show pufferSetze ctS2.puffer 0 ((wortEintraege witA ctV).drop 1) d = []
  rw [pufferSetze_anders _ _ h0]
  show ctS2.puffer d = []
  show (if d = 0 then wortEintraege witA ctV else []) = []
  rw [if_neg h0]

/-- The foreign entry rides every later own flush untouched. -/
theorem ctBuf1_5 : ctS5.puffer 1 = [⟨ctF, ctFv⟩] := by
  rw [eigen_fremd_gleich ctS4 ctS5 ct_step3 1 (by decide)]
  exact ctBuf1_4

theorem ctBuf1_6 : ctS6.puffer 1 = [⟨ctF, ctFv⟩] := by
  rw [eigen_fremd_gleich ctS5 ctS6 ct_step4 1 (by decide)]
  exact ctBuf1_5

theorem ctBuf1_7 : ctS7.puffer 1 = [⟨ctF, ctFv⟩] := by
  rw [eigen_fremd_gleich ctS6 ctS7 ct_step5 1 (by decide)]
  exact ctBuf1_6

theorem ctBuf1_8 : ctS8.puffer 1 = [⟨ctF, ctFv⟩] := by
  rw [eigen_fremd_gleich ctS7 ctS8 ct_step6 1 (by decide)]
  exact ctBuf1_7

theorem ctBuf1_9 : ctS9.puffer 1 = [⟨ctF, ctFv⟩] := by
  rw [eigen_fremd_gleich ctS8 ctS9 ct_step7 1 (by decide)]
  exact ctBuf1_8

theorem ctBuf1_10 : ctS10.puffer 1 = [⟨ctF, ctFv⟩] := by
  rw [eigen_fremd_gleich ctS9 ctS10 ct_step8 1 (by decide)]
  exact ctBuf1_9

theorem ctBuf1_11 : ctS11.puffer 1 = [⟨ctF, ctFv⟩] := by
  rw [eigen_fremd_gleich ctS10 ctS11 ct_step9 1 (by decide)]
  exact ctBuf1_10

/-- Off-core emptiness rides every later own flush untouched. -/
theorem ctOff01_5 : ∀ d : Nat, d ≠ 0 → d ≠ 1 → ctS5.puffer d = [] := by
  intro d h0 h1
  rw [eigen_fremd_gleich ctS4 ctS5 ct_step3 d h0]
  exact ctOff01_4 d h0 h1

theorem ctOff01_6 : ∀ d : Nat, d ≠ 0 → d ≠ 1 → ctS6.puffer d = [] := by
  intro d h0 h1
  rw [eigen_fremd_gleich ctS5 ctS6 ct_step4 d h0]
  exact ctOff01_5 d h0 h1

theorem ctOff01_7 : ∀ d : Nat, d ≠ 0 → d ≠ 1 → ctS7.puffer d = [] := by
  intro d h0 h1
  rw [eigen_fremd_gleich ctS6 ctS7 ct_step5 d h0]
  exact ctOff01_6 d h0 h1

theorem ctOff01_8 : ∀ d : Nat, d ≠ 0 → d ≠ 1 → ctS8.puffer d = [] := by
  intro d h0 h1
  rw [eigen_fremd_gleich ctS7 ctS8 ct_step6 d h0]
  exact ctOff01_7 d h0 h1

theorem ctOff01_9 : ∀ d : Nat, d ≠ 0 → d ≠ 1 → ctS9.puffer d = [] := by
  intro d h0 h1
  rw [eigen_fremd_gleich ctS8 ctS9 ct_step7 d h0]
  exact ctOff01_8 d h0 h1

theorem ctOff01_10 : ∀ d : Nat, d ≠ 0 → d ≠ 1 → ctS10.puffer d = [] := by
  intro d h0 h1
  rw [eigen_fremd_gleich ctS9 ctS10 ct_step8 d h0]
  exact ctOff01_9 d h0 h1

theorem ctOff01_11 : ∀ d : Nat, d ≠ 0 → d ≠ 1 → ctS11.puffer d = [] := by
  intro d h0 h1
  rw [eigen_fremd_gleich ctS10 ctS11 ct_step9 d h0]
  exact ctOff01_10 d h0 h1

/-- Every visited state is foreign-free at the slot footprint. -/
theorem ct_ff2 : FremdFrei ctS2 0 witA :=
  fremdFrei_aus_leer ctS2 0 witA ctS2leer

theorem ct_ff3 : FremdFrei ctS3 0 witA :=
  fremdFrei_aus_leer ctS3 0 witA ctS3leer

theorem ct_ff4 : FremdFrei ctS4 0 witA :=
  ctFremdFF ctS4 ctBuf1_4 ctOff01_4

theorem ct_ff5 : FremdFrei ctS5 0 witA :=
  ctFremdFF ctS5 ctBuf1_5 ctOff01_5

theorem ct_ff6 : FremdFrei ctS6 0 witA :=
  ctFremdFF ctS6 ctBuf1_6 ctOff01_6

theorem ct_ff7 : FremdFrei ctS7 0 witA :=
  ctFremdFF ctS7 ctBuf1_7 ctOff01_7

theorem ct_ff8 : FremdFrei ctS8 0 witA :=
  ctFremdFF ctS8 ctBuf1_8 ctOff01_8

theorem ct_ff9 : FremdFrei ctS9 0 witA :=
  ctFremdFF ctS9 ctBuf1_9 ctOff01_9

theorem ct_ff10 : FremdFrei ctS10 0 witA :=
  ctFremdFF ctS10 ctBuf1_10 ctOff01_10

theorem ct_ff11 : FremdFrei ctS11 0 witA :=
  ctFremdFF ctS11 ctBuf1_11 ctOff01_11

/-- The witness start carries the exact group. -/
theorem ct_hgrp : WortGruppe ctS2 0 witA ctV := by
  refine ⟨rfl, ?_⟩
  exact fremdFrei_aus_leer ctS2 0 witA ctS2leer

/-- The witness start reads the grouped footprint. -/
theorem ct_hles : lesbar8 ctS2.mem witA = true := by rfl

/-- Each recorded step is a drain step (eight own flushes around one
    foreign issue). -/
theorem ct_e1 : DrainSchritt 0 ctS2 ctS3 := .eigen ct_step1

theorem ct_e2 : DrainSchritt 0 ctS3 ctS4 :=
  .fremdAusgabe 1 ⟨ctF, ctFv⟩ (by decide) ct_step2

theorem ct_e3 : DrainSchritt 0 ctS4 ctS5 := .eigen ct_step3

theorem ct_e4 : DrainSchritt 0 ctS5 ctS6 := .eigen ct_step4

theorem ct_e5 : DrainSchritt 0 ctS6 ctS7 := .eigen ct_step5

theorem ct_e6 : DrainSchritt 0 ctS7 ctS8 := .eigen ct_step6

theorem ct_e7 : DrainSchritt 0 ctS8 ctS9 := .eigen ct_step7

theorem ct_e8 : DrainSchritt 0 ctS9 ctS10 := .eigen ct_step8

theorem ct_e9 : DrainSchritt 0 ctS10 ctS11 := .eigen ct_step9

/-- The full drain trace with its visited states. -/
theorem ct_spur : DrainSpur 0 ctS2 ctS11
    [ctS2, ctS3, ctS4, ctS5, ctS6, ctS7, ctS8, ctS9, ctS10, ctS11] :=
  .schritt _ _ _ _ ct_e1 (.schritt _ _ _ _ ct_e2 (.schritt _ _ _ _ ct_e3
    (.schritt _ _ _ _ ct_e4 (.schritt _ _ _ _ ct_e5 (.schritt _ _ _ _ ct_e6
      (.schritt _ _ _ _ ct_e7 (.schritt _ _ _ _ ct_e8 (.schritt _ _ _ _ ct_e9
        (.leer ctS11)))))))))

/-- The drain end is visited. -/
theorem ct_hend :
    ctS11 ∈ [ctS2, ctS3, ctS4, ctS5, ctS6, ctS7, ctS8, ctS9, ctS10,
      ctS11] := by
  simp

/-- The drain ends with an empty own buffer. -/
theorem ct_hempty : ctS11.puffer 0 = [] := by rfl

/-- Every visited state is foreign-free at the slot footprint. -/
theorem ct_hstoer :
    ∀ x ∈ [ctS2, ctS3, ctS4, ctS5, ctS6, ctS7, ctS8, ctS9, ctS10, ctS11],
      FremdFrei x 0 witA := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ct_ff2
  · exact ct_ff3
  · exact ct_ff4
  · exact ct_ff5
  · exact ct_ff6
  · exact ct_ff7
  · exact ct_ff8
  · exact ct_ff9
  · exact ct_ff10
  · exact ct_ff11

/-- The grouped word reads back whole at the drain end. -/
theorem ct_hread : read64 ctS11.mem witA = some ctV :=
  wort_gruppe_liest_zurueck ctS2 ctS11 _ 0 witA ctV ct_hgrp ct_hles
    ct_spur ct_hend ct_hempty ct_hstoer

/-- Stale-view divergence at the foreign address: core 0 still reads
    canonical zero while core 1 forwards its pending seven. -/
theorem ct_stale0 : loadByte ctS4 0 ctF = some (BitVec.ofNat 8 0) := by
  decide

theorem ct_stale1 : loadByte ctS4 1 ctF = some ctFv := by
  decide

/-- First trace node: start over the drain start (clock 1). -/
def ctNA : SpurKnoten := spurStart ctS2

/-- Second trace node: one flush later (clock 2), carrying the
    flushed byte as a timestamp-1 release message. -/
def ctNB : SpurKnoten :=
  { tso := ctS3
    hist := fun x => if x = addrOff witA 0 then ctNA.hist x ++
      [Speichermodell.nachricht Speichermodell.Ordnung.freigabe
        (ctNA.blick 0) (addrOff witA 0) ctNA.frisch (wortByte ctV 0)]
      else ctNA.hist x
    blick := fun d => if d = 0 then
      (ctNA.blick 0).setze (addrOff witA 0) ctNA.frisch else ctNA.blick d
    frisch := 2 }

/-- The first flush as a projected trace step. -/
theorem ct_stufe1 : SpurSchritt ctNA ctNB :=
  SpurSchritt.flush ctNA ctNB 0 ⟨addrOff witA 0, wortByte ctV 0⟩
    ((wortEintraege witA ctV).drop 1) ct_step1 rfl rfl rfl rfl

/-- The one-flush trace is reached. -/
theorem ct_erreichbar : SpurErreichbar ctNA ctNB :=
  SpurErreichbar.schritt SpurErreichbar.start ct_stufe1

/-- Two distinct timestamps on the reached trace. -/
theorem ct_uhren : ctNA.frisch ≠ ctNB.frisch := by decide

/-- Witness program over `witD` (never consulted by the blatt step). -/
def ctProg : Programm witD where
  invariante := fun i => nomatch i
  requires := fun _ => Expr.wahr
  ensures := fun _ => Expr.wahr
  rumpf := fun _ => .ret .keine (List.Perm.refl _)

/-- The frame contract writes the table. -/
theorem ctHw : (vertragVon witD ()).schreibt () = true := rfl

/-- Witness statement at `l = true` with frame-contract permission. -/
def ctS : Stmt witD (vertragVon witD ()) true [] [] [] :=
  Stmt.assignSlot () () witI witE ctHw witHL

def ctRest : Endblock witD (vertragVon witD ()) true [] [] :=
  Endblock.leave rfl

def ctRahmen : RufRahmenG witD :=
  ⟨(), Env.nil, witSigma,
    ⟨true, [], [], Env.nil,
      GRest.ende (Endblock.cons ctS ctRest)⟩⟩

def ctFaden : RufFadenG witD :=
  ⟨[], ctRahmen, [], []⟩

def ctM : RufMaschineG witD :=
  ⟨witSigma.speicher, fun _ => ctFaden, [], witSigma⟩

/-- Head, world and lock facts compute. -/
theorem ct_hhead : (ctM.faeden 0).kopf.rest =
    ⟨true, [], [], Env.nil,
      GRest.ende (Endblock.cons ctS ctRest)⟩ := rfl

theorem ct_hwelt : ctM.weltVon 0 = witSigma := rfl

theorem ct_hΛ : HeldIn ([] : List (Res witD)) (offen ([] : List (Ereignis witD))) := by
  simp [HeldIn]

/-- The start W machine sits on the G machine. -/
theorem ct_hWg : (RufStartW ctM).g = ctM := rfl

/-! ## 5. Joint witness: source write plus growing TSO drain -/

/-- **JOINT WITNESS for `schrittW_aus_gruppen_drain`.** Every premise
    holds jointly on concrete values: the witness declaration with one
    table that the witness function writes, a reached one-step run that
    changes the source slot `0 → 42` and the mapped target bytes, the
    growing eight-flush drain at the slot address with a real foreign
    issue inside it, and the inherited history over the drain end — and
    so do the `SchrittW` transition, the value agreement and the
    representation. On top: two distinct trace timestamps on a reached
    step, the pending foreign byte outside the footprint, and the
    stale-view divergence (core 0 canonically reads zero where core 1
    forwards seven — the unflushed store is refused a global value).
    Non-degenerate: a written table, a memory-changing source step and
    a memory-changing target drain. -/
theorem schrittW_aus_gruppen_drain_zeuge :
    ∃ (σ' : World witD) (ρ' : Env witD []),
      execStmt witO 0 keinRuf
        (Stmt.assignSlot (l := true) () () witI witE ctHw witHL)
        witSigma Env.nil = .ok σ' ρ' ∧
      write64 witM witA (zahlWort witVal) = some witM' ∧
      (witSigma.slots () 0 ()).n = 0 ∧ (σ'.slots () 0 ()).n = 42 ∧
      witM.bytes witA ≠ witM'.bytes witA ∧
      ErbtW (spurStart ctS11) (RufStartW ctM) 0 0 (Sum.inl ()) witA ∧
      SpurInv (spurStart ctS11) ∧
      SpurErreichbar ctNA ctNB ∧ ctNA.frisch ≠ ctNB.frisch ∧
      ctS4.puffer 1 = [⟨ctF, ctFv⟩] ∧ ctF ∉ Fuss witA ∧
      loadByte ctS4 0 ctF = some (BitVec.ofNat 8 0) ∧
      loadByte ctS4 1 ctF = some ctFv ∧
      (∃ (W' : RufMaschineW witD) (σm : Gabbro.Grammatik.Speicher witD)
        (M'' : RufMaschineG witD)
        (wahl : witD.Tab ⊕ witD.Glob → NachrichtW witD)
        (neu : witD.Tab ⊕ witD.Glob → Nat),
        SchrittW ctProg witO 0 (fun g => nomatch g) (RufStartW ctM) 0 W'
          σm M'' wahl neu ∧
        (∃ w, read64 (spurStart ctS11).tso.mem witA = some w ∧
          wortZahl 0 100 w = some witVal) ∧
        RepSlot () 0 () 0 100 witHT witA witM' σ') := by
  have hOk : repOk (witD.typ () ()) 4096 16 0 = true := by decide
  have hk : (eval witSL witI witSL Env.nil).n = 0 := rfl
  have hv : (cast (congrArg (Wert witD) witHT)
      (eval witSL witE witSL Env.nil) : Wert witD (.int 0 100)) =
      witVal := rfl
  have hRd : lesbar8 witM witA = true := by decide
  have hLese : witSL = witSigma.lese [] (witI.orte ++ witE.orte) := rfl
  have hBefore : (witSigma.slots () 0 ()).n = 0 := rfl
  have hExecFull : ∃ σ' ρ', execStmt witO 0 keinRuf
      (Stmt.assignSlot (l := true) () () witI witE ctHw witHL)
      witSigma Env.nil = .ok σ' ρ' := by
    simp only [execStmt]
    exact ⟨_, _, rfl⟩
  obtain ⟨σ', ρ', hExec⟩ := hExecFull
  have hTgt : write64 witM witA (zahlWort witVal) = some witM' := by
    simp only [write64, witM']
    rw [if_pos (by decide : schreibbar8 witM witA = true)]
  have hAfter : (σ'.slots () 0 ()).n = 42 := by
    cases hExec
    rfl
  have hByte : writeBytes witM witA (zahlWort witVal) witA =
      wortByte (zahlWort witVal) 0 := by
    have h := writeBytesN_hit witM witA (zahlWort witVal) 8 0
      (by decide) (by decide)
    rw [addrOff_null] at h
    unfold writeBytes
    exact h
  have hBytes : witM.bytes witA ≠ witM'.bytes witA := by
    show BitVec.ofNat 8 0 ≠ writeBytes witM witA (zahlWort witVal) witA
    rw [hByte]
    decide
  have hErbt := erbtW_start ctS11 ctM 0 0 (Sum.inl ()) witA
  have hInv := spurStart_inv ctS11
  have hMain := schrittW_aus_gruppen_drain ctProg witO 0 (fun g => nomatch g)
    () () 0 100 witHT 4096 16 0 hOk witI witE ctM 0 witSigma Env.nil
    ctHw witHL ctS ctRest rfl ct_hhead witSL rfl 0 witVal hk hv rfl
    witA witM witM' σ' ρ' hExec hTgt hRd (by decide) (by decide)
    ct_hwelt ct_hΛ (RufStartW ctM) ct_hWg 0 (spurStart ctS11) hErbt hInv
    ctS11 rfl ctS2
    [ctS2, ctS3, ctS4, ctS5, ctS6, ctS7, ctS8, ctS9, ctS10, ctS11]
    ct_hgrp ct_hles ct_spur ct_hend ct_hempty ct_hstoer
  obtain ⟨W', σm, M'', wahl, neu, hSW, hVal, hRep⟩ := hMain
  exact ⟨σ', ρ', hExec, hTgt, hBefore, hAfter, hBytes, hErbt, hInv,
    ct_erreichbar, ct_uhren, ctBuf1_4, ctFfresh, ct_stale0, ct_stale1,
    W', σm, M'', wahl, neu, hSW, hVal, hRep⟩

/- CUTS:
     - Proved here: `ErbtW` with initial (`erbtW_start`), step
       (`erbtW_schritt`) and finite-trace (`erbtW_waechst`) preservation;
       the no-read fragment trace (`assignSlot_spur`); one actual
       typed-carrier `SchrittW` for a no-read fragment write whose
       grouped TSO drain installs the source-written word
       (`schrittW_aus_gruppen_drain`), with a joint non-degenerate
       witness (`schrittW_aus_gruppen_drain_zeuge`): written table,
       memory-changing source step (`0 → 42`) and target drain, two
       distinct trace timestamps on a reached flush step, a pending
       foreign byte outside the footprint, and the stale-view
       divergence (core 0 reads canonical zero where core 1 forwards
       seven — no global value for the unflushed store).
     - NOT proved here, left OPEN: fragment reads (literals only via
       `hOrte`; read carriers need the lowering certificate's value
       link, cf. `wLesbar_aus_weiterleitung`); LOCK/RMW steps (the
       `rmw` field is discharged by refuting the exchange head);
       per-access run induction from x86 traces to W runs; the GX
       refinement consuming these facts; scheduling, fairness,
       progress, timing; interrupts, devices, MMIO, DMA.
     - Byte-tearing at the grouped footprint is unobservable for
       single-significant-byte values (here: 42): every mid-drain
       canonical word is already `0` or the full word. Multi-byte
       tearing stays with the byte layer (`hist_zerreissen`,
       `riss_gemischt_verweigert`); grouped drains are observationally
       grouped only under the checked exclusion, never by hardware
       atomicity.
     - `HavocA`/`GeteiltV` need no use here: the fragment touches no
       shared atomic (plain table carrier); the atomic rely leg stays
       with the consumers that bridge shared atomics.
-/

#print axioms ErbtW
#print axioms erbtW_start
#print axioms erbtW_schritt
#print axioms erbtW_waechst
#print axioms assignSlot_spur
#print axioms ctV
#print axioms ctF
#print axioms ctFv
#print axioms ctFfresh
#print axioms ctFremdFF
#print axioms schrittW_aus_gruppen_drain
#print axioms schrittW_aus_gruppen_drain_zeuge

end Gabbro.Grammatik.X86
