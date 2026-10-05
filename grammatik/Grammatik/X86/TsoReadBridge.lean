/-
  File:      Grammatik/X86/TsoReadBridge.lean
  Subject:   TSO to W bridge: fragment READS (lane 1143).

  Closes the OPEN read leg of `CarrierTraceBridge.lean` (which proves one
  no-read fragment write step into W): a typed-carrier read whose value
  comes from forwarding or canonical memory yields a `SchrittW` read step.
  Consumes the accepted `TSOTrace`/`SourceMemory`/`WordAccessGrouping`
  vocabulary, the source access enumeration (`blattFragment_voll`), the
  group-load value links (`BridgeRead`: `ladeWort8`, `wLesbar_aus_gruppe`,
  `wLesbar_aus_weiterleitung`) and the coherent machine observations
  (`HardwareExecution`: `HwSchritt.lade`, `hwSchritt_wf`). The stale-view
  case is stated honestly: no global value for an unflushed store.
-/
import Grammatik.X86.TSOTrace
import Grammatik.X86.SourceMemory
import Grammatik.X86.WordAccessGrouping
import Grammatik.X86.SourceAccessCompleteness
import Grammatik.X86.BridgeRead
import Grammatik.X86.CarrierTraceBridge
import Grammatik.X86.HardwareExecution
import Grammatik.RufAdaequatG
import Grammatik.RennfreiVoll
import Grammatik.Speichermodell.MaschineW
import Grammatik.Speichermodell.Sicht

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-! ## 1. Machine read observations: preservation and canonical value. -/

/-- Machine read observations preserve well-formedness: the read case of
    the accepted `hwSchritt_wf`, named for the bridge consumer. -/
theorem hwLade_erhaelt_wf (m : HwMaschine) (c : Nat) (a : Adresse) (v : Byte)
    (h : loadByte (tsoAnsicht m) c a = some v) (hwf : HwWf m) : HwWf m :=
  hwSchritt_wf m m _ (.lade c a v h) hwf

/-- A machine read observation at a committed address returns the canonical
    byte: the accepted `load_ohne_eintrag` lifted through the shared-memory
    projections (`tsoAnsicht_speicher`, `tsoAnsicht_puffer`). Every premise
    is used: `h` for the observed value, `hmiss`/`hrd` for the no-forward
    equations. -/
theorem hwLade_trifft_speicher (m : HwMaschine) (c : Nat) (x : Adresse)
    (v : Byte)
    (h : loadByte (tsoAnsicht m) c x = some v)
    (hmiss : neuestens (m.puffer c) x = none)
    (hrd : m.mem.lesbar x = true) :
    v = m.mem.bytes x := by
  have h1 : neuestens ((tsoAnsicht m).puffer c) x = none := by
    rw [tsoAnsicht_puffer]
    exact hmiss
  have h2 : (tsoAnsicht m).mem.lesbar x = true := by
    rw [tsoAnsicht_speicher]
    exact hrd
  have h3 := load_ohne_eintrag (tsoAnsicht m) c x h1 h2
  rw [h] at h3
  simp only [Option.some.injEq] at h3
  exact h3

/-- A table read contributes at most its own timestamp to any carrier view:
    tables are `entspannt` (`ordVon`), so the contribution is the singleton
    view at the read carrier. Used to keep the write timestamp fresh above
    the read-joined view in the fragment assembly (§2). -/
theorem beitrag_tabelle_le {D : Deklaration} (ord : D.Glob → Speichermodell.Ordnung)
    (t : D.Tab) (m : NachrichtW D) (c : D.Tab ⊕ D.Glob) :
    Speichermodell.beitrag (ordVon ord (.inl t)) (.inl t) m c ≤ m.ts := by
  have h : ordVon ord (.inl t) = .entspannt := rfl
  rw [h]
  simp only [Speichermodell.beitrag, Speichermodell.Sicht.eins]
  by_cases hc : c = Sum.inl t
  · rw [if_pos hc]
    exact Nat.le_refl _
  · rw [if_neg hc]
    exact Nat.zero_le _

/-! ## 2. The trace of a one-read fragment step. -/

/-- A one-read `assignSlot` step (`hOrte`: the footprint is exactly the
    read of `t2`) prepends exactly two events -- the write of `t` and the
    read of `t2` -- to the thread trace. The read analogue of the accepted
    `assignSlot_spur` (which covers literals via `hOrte = []`); the value
    and index evaluations never enter the trace, so no `hk`/`hv` premises
    are needed. Every premise is used: `O`/`passes` through the executed
    statement, the worlds through the delta, `hOrte` fixing the read
    events, `hLese` naming the read world. -/
theorem lesespur_assignSlot {D : Deklaration} {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t)))
    (e : Expr D Γ Λ (D.typ t f))
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (σ : World D) (ρ : Env D Γ)
    (σL : World D) (hLese : σL = σ.lese Λ (i.orte ++ e.orte))
    (t2 : D.Tab)
    (hOrte : i.orte ++ e.orte = [.inl t2])
    (σ' : World D) (ρ' : Env D Γ)
    (hExec : execStmt O passes keinRuf (Stmt.assignSlot (l := l) t f i e hw hL) σ ρ =
      .ok σ' ρ') :
    σ'.spur = [Ereignis.zugriff t true Λ σL.haelt,
      Ereignis.zugriff t2 false Λ σ.haelt] ++ σ.spur := by
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
  rw [hLese, hOrte]
  rfl

/-! ## 3. Committed fragment read: one actual typed-carrier SchrittW. -/

/-- **READ TRANSITION, COMMITTED (`schrittW_aus_lesefragment_gruppe`).** A
    fragment write of `t` whose footprint reads exactly one carrier
    (`hOrte`: the value/index expressions read `t2`, e.g. a copy) and whose
    grouped TSO drain installs the written word yields an actual
    typed-carrier `SchrittW` whose G step READS `t2` -- not only the `lies`
    consequent. The read value comes from canonical memory: no pending
    own-buffer entry on the read footprint (`hMiss`) with full read
    permission (`hRdR`), so the group load is the canonical word
    (`ladeWort8_ohne_weiterleitung` inside `wLesbar_aus_gruppe`), which
    parses to the source slot value. The `lies` field at the read carrier
    is DERIVED from the accepted representation, never assumed; at every
    other carrier the enumeration (`blattFragment_voll` against `hOrte`)
    leaves no read. The write timestamp stays fresh above the read-joined
    view: the read message timestamp sits below the trace clock (inherited
    `ErbtW` bound over `hMemR`) and the table-read contribution adds at
    most that timestamp (`beitrag_tabelle_le`). Every premise is used. -/
theorem schrittW_aus_lesefragment_gruppe {D : Deklaration} {l : Bool}
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
    (t2 : D.Tab) (f2 : D.Feld t2)
    (lo2 hi2 : Int) (hT2 : D.typ t2 f2 = .int lo2 hi2)
    (k2 : Int)
    (hOrte : i.orte ++ e.orte = [.inl t2])
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
    (hleer : sN.puffer co = []) (hstoer : ∀ x ∈ tlist, FremdFrei x co a)
    (rdA : Adresse) (vr : Zahl lo2 hi2)
    (hRepRead : RepSlot t2 k2 f2 lo2 hi2 hT2 rdA s2.mem σ)
    (hMiss : ∀ j : Nat, j < 8 → neuestens (s2.puffer co) (addrOff rdA j) = none)
    (hRdR : lesbar8 s2.mem rdA = true)
    (hLo2 : 0 ≤ lo2) (hHi2 : hi2 < 2 ^ 64)
    (w2 : Wort) (hWort : ladeWort8 s2 co rdA = some w2)
    (hv2 : (cast (congrArg (Wert D) hT2) (σ.slots t2 k2 f2)) = vr)
    (ts : Nat)
    (hMemR : (⟨ts, σ.speicher, Speichermodell.Sicht.null⟩ : NachrichtW D) ∈
      W.hist (.inl t2))
    (hProjR : W.sicht u (.inl t2) ≤ sichtVon s2 co rdA)
    (hTsR : sichtVon s2 co rdA ≤ ts)
    (hTraegerR : TraegerGleich σ.speicher σ.speicher (.inl t2)) :
    ∃ (W' : RufMaschineW D) (σm : Gabbro.Grammatik.Speicher D)
      (M'' : RufMaschineG D)
      (wahl : D.Tab ⊕ D.Glob → NachrichtW D) (neu : D.Tab ⊕ D.Glob → Nat),
      SchrittW P O passes ord W u W' σm M'' wahl neu ∧
      (∃ w, read64 nN.tso.mem a = some w ∧ wortZahl lo hi w = some v) ∧
      RepSlot t k f lo hi hT a m' σ' ∧
      wortZahl lo2 hi2 w2 = some vr := by
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
  have hSpur : σ'.spur = [Ereignis.zugriff t true Λ σL.haelt,
      Ereignis.zugriff t2 false Λ σ.haelt] ++ σ.spur :=
    lesespur_assignSlot O passes t f i e hw hL σ ρ σL hLese t2 hOrte σ' ρ' hExec
  have hread : read64 sN.mem a = some (zahlWort v) :=
    wort_gruppe_liest_zurueck s2 sN tlist co a (zahlWort v) hgrp hles
      hspur hend hleer hstoer
  refine ⟨⟨⟨σ'.speicher,
      rufUpdateG (W.g.faeden) u ⟨((W.g.faeden u).stapel),
        ⟨((W.g.faeden u).kopf.f), ((W.g.faeden u).kopf.rho),
          ((W.g.faeden u).kopf.s0),
          ⟨l, Γ, Λ, ρ', .ende rest⟩⟩, σ'.spur, ((W.g.faeden u).log)⟩,
      (W.g.lauf) ++ rufEigenG u
        [Ereignis.zugriff t true Λ σL.haelt,
          Ereignis.zugriff t2 false Λ σ.haelt],
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
              [Ereignis.zugriff t true Λ σL.haelt,
                Ereignis.zugriff t2 false Λ σ.haelt],
            (W.g.start)⟩
          (fun _ => (⟨ts, σ.speicher, Speichermodell.Sicht.null⟩ :
            NachrichtW D)))
        c (traceFrisch nN) σ'.speicher :: W.hist c else W.hist c,
    fun t' => if t' = u then (fun c => if c = Sum.inl t then traceFrisch nN
      else vorSicht ord W u σ.speicher
        ⟨σ'.speicher,
          rufUpdateG (W.g.faeden) u ⟨((W.g.faeden u).stapel),
            ⟨((W.g.faeden u).kopf.f), ((W.g.faeden u).kopf.rho),
              ((W.g.faeden u).kopf.s0),
              ⟨l, Γ, Λ, ρ', .ende rest⟩⟩, σ'.spur, ((W.g.faeden u).log)⟩,
          (W.g.lauf) ++ rufEigenG u
            [Ereignis.zugriff t true Λ σL.haelt,
              Ereignis.zugriff t2 false Λ σ.haelt],
          (W.g.start)⟩
        (fun _ => (⟨ts, σ.speicher, Speichermodell.Sicht.null⟩ :
          NachrichtW D)) c)
      else W.sicht t',
    W.lsicht⟩,
    σ.speicher,
    ⟨σ'.speicher,
      rufUpdateG (W.g.faeden) u ⟨((W.g.faeden u).stapel),
        ⟨((W.g.faeden u).kopf.f), ((W.g.faeden u).kopf.rho),
          ((W.g.faeden u).kopf.s0),
          ⟨l, Γ, Λ, ρ', .ende rest⟩⟩, σ'.spur, ((W.g.faeden u).log)⟩,
      (W.g.lauf) ++ rufEigenG u
        [Ereignis.zugriff t true Λ σL.haelt,
          Ereignis.zugriff t2 false Λ σ.haelt],
      (W.g.start)⟩,
    (fun _ => (⟨ts, σ.speicher, Speichermodell.Sicht.null⟩ : NachrichtW D)),
    (fun _ => traceFrisch nN),
    ?_, ?_, hMain.1, ?_⟩
  · -- The SchrittW fields from the G-side facts above.
    generalize hgen : (⟨σ'.speicher,
      rufUpdateG (W.g.faeden) u ⟨((W.g.faeden u).stapel),
        ⟨((W.g.faeden u).kopf.f), ((W.g.faeden u).kopf.rho),
          ((W.g.faeden u).kopf.s0),
          ⟨l, Γ, Λ, ρ', .ende rest⟩⟩, σ'.spur, ((W.g.faeden u).log)⟩,
      (W.g.lauf) ++ rufEigenG u
        [Ereignis.zugriff t true Λ σL.haelt,
          Ereignis.zugriff t2 false Λ σ.haelt],
      (W.g.start)⟩ : RufMaschineG D) = MT
    have hM : ((mitSpeicher W.g σ.speicher).faeden u).spur = σ.spur := hSpurEq
    have hMmem : (mitSpeicher W.g σ.speicher).speicher = σ.speicher := rfl
    have hM'sp : (MT.faeden u).spur = σ'.spur := by
      rw [← hgen]; simp only [rufUpdateG_self]
    have hMTsp : MT.speicher = σ'.speicher := by rw [← hgen]
    have hFrag := blattFragment_voll O passes keinRuf t f i e hw hL σ ρ σ' ρ'
      hExec (mitSpeicher W.g σ.speicher) MT u hM hM'sp hMmem hMTsp
    obtain ⟨hEq, hSchreib, hLi, _, hOwn⟩ := hFrag
    have hEq' : zugriffe (mitSpeicher W.g σ.speicher) MT u =
        fragmentListe t [.inl t2] := by
      rw [← hOrte]
      exact hEq
    have hLi' : ∀ c, LiestG (mitSpeicher W.g σ.speicher) MT u c →
        c ∈ ([.inl t2] : List (D.Tab ⊕ D.Glob)) := by
      intro c hc
      have hmem := hLi c hc
      rw [hOrte] at hmem
      exact hmem
    have hLiR : LiestG (mitSpeicher W.g σ.speicher) MT u (.inl t2) := by
      unfold LiestG
      rw [hEq']
      simp [fragmentListe]
    have hValLies := wLesbar_aus_gruppe (σ := σ.speicher) (σw := σ) (M'' := MT)
      vr hRepRead hMiss hRdR hLo2 hHi2 w2 hWort hv2 hMemR hProjR hTsR hTraegerR
    have hEreig : ereignisse (mitSpeicher W.g σ.speicher) MT u =
        [Ereignis.zugriff t true Λ σL.haelt,
          Ereignis.zugriff t2 false Λ σ.haelt] :=
      ereignisse_eq (hM'sp.trans (by rw [hSpur, hM]))
    have hLesen : lesenVon (mitSpeicher W.g σ.speicher) MT u = [.inl t2] := by
      simp [lesenVon, hEq, hOrte, fragmentListe]
    have hGenommen : genommenVon (mitSpeicher W.g σ.speicher) MT u = [] := by
      simp [genommenVon, hEreig]
    have hGegeben : gegebenVon (mitSpeicher W.g σ.speicher) MT u = [] := by
      simp [gegebenVon, hEreig]
    have hVorAt : vorSicht ord W u σ.speicher MT
        (fun _ => (⟨ts, σ.speicher, Speichermodell.Sicht.null⟩ : NachrichtW D))
        (.inl t) =
        max (W.sicht u (.inl t))
          (Speichermodell.beitrag (ordVon ord (.inl t2)) (.inl t2)
            (⟨ts, σ.speicher, Speichermodell.Sicht.null⟩ : NachrichtW D)
            (.inl t)) := by
      simp [vorSicht, hGenommen, hLesen, locksicht, lesesicht,
        Speichermodell.Sicht.verein]
    have hleaf : s.istBlatt = true := by
      rw [hs]; exact BlattG.istBlatt (BlattG.assignSlot t f i e hw hL)
    have hstep : execStmt O passes keinRuf s
        ((mitSpeicher W.g σ.speicher).weltVon u) ρ = Ausgang.ok σ' ρ' := by
      rw [hs, hW]
      exact hExec
    have hneu' : σ'.spur =
        [Ereignis.zugriff t true Λ σL.haelt,
          Ereignis.zugriff t2 false Λ σ.haelt] ++
        ((mitSpeicher W.g σ.speicher).faeden u).spur := by
      rw [hSpur, hM]
    have hkein : ∀ (L : D.Lock) (h : List D.Lock),
        Ereignis.nimmt L h ∉
          [Ereignis.zugriff t true Λ σL.haelt,
            Ereignis.zugriff t2 false Λ σ.haelt] := by
      intro L h hm; simp at hm
    have hblatt : RufSchrittG P O passes (mitSpeicher W.g σ.speicher) u MT := by
      rw [← hgen]
      exact RufSchrittG.blatt (mitSpeicher W.g σ.speicher) u l Γ Λ Λ s rest ρ
        hleaf hhead hΛ σ' ρ'
        [Ereignis.zugriff t true Λ σL.haelt,
          Ereignis.zugriff t2 false Λ σ.haelt]
        hstep hneu' hkein
    refine ⟨hblatt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      have hcmem := hLi' c hc
      simp only [List.mem_singleton] at hcmem
      subst hcmem
      exact hValLies.2 hLiR
    · intro c hc
      -- Vacuous: presented memory is G memory by construction
      -- (`σ.speicher` over `W.g`), so every carrier agrees.
      rw [hMem]
      exact traegerGleich_refl _ _
    · intro c hc
      have hcEq := hOwn c hc
      subst hcEq
      obtain ⟨hClock, hView⟩ := hErbt
      have hWahlTs : ts < traceFrisch nN := hClock _ _ hMemR
      have hle1 : W.sicht u (Sum.inl t) < traceFrisch nN :=
        Nat.lt_of_le_of_lt hView (hInvN.2 co a)
      have hle2 : Speichermodell.beitrag (ordVon ord (.inl t2)) (.inl t2)
          (⟨ts, σ.speicher, Speichermodell.Sicht.null⟩ : NachrichtW D)
          (Sum.inl t) < traceFrisch nN :=
        Nat.lt_of_le_of_lt (beitrag_tabelle_le ord t2 _ _) hWahlTs
      refine ⟨?_, ?_⟩
      · rw [hVorAt]
        exact Nat.max_lt.mpr ⟨hle1, hle2⟩
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
            (fun _ => (⟨ts, σ.speicher, Speichermodell.Sicht.null⟩ :
              NachrichtW D)))
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
              (fun _ => (⟨ts, σ.speicher, Speichermodell.Sicht.null⟩ :
                NachrichtW D)))
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
          (fun _ => (⟨ts, σ.speicher, Speichermodell.Sicht.null⟩ :
            NachrichtW D)) c)
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
  · exact gruppenwert_rep vr hRepRead hMiss hRdR hLo2 hHi2 w2 hWort hv2

/-! ## 4. Forwarded fragment read: one actual typed-carrier SchrittW. -/

/-- **READ TRANSITION, FORWARDED (`schrittW_aus_lesefragment_weiterleitung`).**
    The same one-read fragment shape as §3, but the read value comes from
    own-buffer forwarding: every footprint byte loads (`hL`) while pending
    own-buffer entries exist (`hPend`). Each byte is exhibited as the
    youngest buffer entry (no silent forward, inside
    `wLesbar_aus_weiterleitung`); the VALUE identity across sides (`hWert`:
    the assembled word parses to the source slot value) is an explicit
    premise -- it is the lowering certificate's job (write side), never
    derived from the buffer here. The read carrier differs from the
    written one (`hNe`), so the relaxed table-read contributes nothing to
    the written carrier's view and the write timestamp stays fresh at the
    trace clock. Every premise is used. -/
theorem schrittW_aus_lesefragment_weiterleitung {D : Deklaration} {l : Bool}
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
    (t2 : D.Tab) (f2 : D.Feld t2)
    (lo2 hi2 : Int) (hT2 : D.typ t2 f2 = .int lo2 hi2)
    (k2 : Int)
    (hOrte : i.orte ++ e.orte = [.inl t2])
    (hNe : (.inl t2 : D.Tab ⊕ D.Glob) ≠ .inl t)
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
    (hleer : sN.puffer co = []) (hstoer : ∀ x ∈ tlist, FremdFrei x co a)
    (rdA : Adresse) (vr : Zahl lo2 hi2)
    (f8 : Fin 8 → Byte)
    (hL8 : ∀ j : Fin 8, loadByte s2 co (addrOff rdA j.val) = some (f8 j))
    (hPend : ∀ j : Fin 8, ∃ w : Byte,
      neuestens (s2.puffer co) (addrOff rdA j.val) = some w)
    (hWert : wortZahl lo2 hi2 (bytesWort f8) =
      some (cast (congrArg (Wert D) hT2) (σ.speicher.slots t2 k2 f2)))
    (hv2 : (cast (congrArg (Wert D) hT2) (σ.speicher.slots t2 k2 f2)) = vr)
    (ts : Nat)
    (hMemR : (⟨ts, σ.speicher, Speichermodell.Sicht.null⟩ : NachrichtW D) ∈
      W.hist (.inl t2))
    (hProjR : W.sicht u (.inl t2) ≤ sichtVon s2 co rdA)
    (hTsR : sichtVon s2 co rdA ≤ ts)
    (hTraegerR : TraegerGleich σ.speicher σ.speicher (.inl t2)) :
    ∃ (W' : RufMaschineW D) (σm : Gabbro.Grammatik.Speicher D)
      (M'' : RufMaschineG D)
      (wahl : D.Tab ⊕ D.Glob → NachrichtW D) (neu : D.Tab ⊕ D.Glob → Nat),
      SchrittW P O passes ord W u W' σm M'' wahl neu ∧
      (∃ w, read64 nN.tso.mem a = some w ∧ wortZahl lo hi w = some v) ∧
      RepSlot t k f lo hi hT a m' σ' ∧
      wortZahl lo2 hi2 (bytesWort f8) = some vr := by
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
  have hSpur : σ'.spur = [Ereignis.zugriff t true Λ σL.haelt,
      Ereignis.zugriff t2 false Λ σ.haelt] ++ σ.spur :=
    lesespur_assignSlot O passes t f i e hw hL σ ρ σL hLese t2 hOrte σ' ρ' hExec
  have hread : read64 sN.mem a = some (zahlWort v) :=
    wort_gruppe_liest_zurueck s2 sN tlist co a (zahlWort v) hgrp hles
      hspur hend hleer hstoer
  refine ⟨⟨⟨σ'.speicher,
      rufUpdateG (W.g.faeden) u ⟨((W.g.faeden u).stapel),
        ⟨((W.g.faeden u).kopf.f), ((W.g.faeden u).kopf.rho),
          ((W.g.faeden u).kopf.s0),
          ⟨l, Γ, Λ, ρ', .ende rest⟩⟩, σ'.spur, ((W.g.faeden u).log)⟩,
      (W.g.lauf) ++ rufEigenG u
        [Ereignis.zugriff t true Λ σL.haelt,
          Ereignis.zugriff t2 false Λ σ.haelt],
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
              [Ereignis.zugriff t true Λ σL.haelt,
                Ereignis.zugriff t2 false Λ σ.haelt],
            (W.g.start)⟩
          (fun _ => (⟨ts, σ.speicher, Speichermodell.Sicht.null⟩ :
            NachrichtW D)))
        c (traceFrisch nN) σ'.speicher :: W.hist c else W.hist c,
    fun t' => if t' = u then (fun c => if c = Sum.inl t then traceFrisch nN
      else vorSicht ord W u σ.speicher
        ⟨σ'.speicher,
          rufUpdateG (W.g.faeden) u ⟨((W.g.faeden u).stapel),
            ⟨((W.g.faeden u).kopf.f), ((W.g.faeden u).kopf.rho),
              ((W.g.faeden u).kopf.s0),
              ⟨l, Γ, Λ, ρ', .ende rest⟩⟩, σ'.spur, ((W.g.faeden u).log)⟩,
          (W.g.lauf) ++ rufEigenG u
            [Ereignis.zugriff t true Λ σL.haelt,
              Ereignis.zugriff t2 false Λ σ.haelt],
          (W.g.start)⟩
        (fun _ => (⟨ts, σ.speicher, Speichermodell.Sicht.null⟩ :
          NachrichtW D)) c)
      else W.sicht t',
    W.lsicht⟩,
    σ.speicher,
    ⟨σ'.speicher,
      rufUpdateG (W.g.faeden) u ⟨((W.g.faeden u).stapel),
        ⟨((W.g.faeden u).kopf.f), ((W.g.faeden u).kopf.rho),
          ((W.g.faeden u).kopf.s0),
          ⟨l, Γ, Λ, ρ', .ende rest⟩⟩, σ'.spur, ((W.g.faeden u).log)⟩,
      (W.g.lauf) ++ rufEigenG u
        [Ereignis.zugriff t true Λ σL.haelt,
          Ereignis.zugriff t2 false Λ σ.haelt],
      (W.g.start)⟩,
    (fun _ => (⟨ts, σ.speicher, Speichermodell.Sicht.null⟩ : NachrichtW D)),
    (fun _ => traceFrisch nN),
    ?_, ?_, hMain.1, ?_⟩
  · -- The SchrittW fields from the G-side facts above.
    generalize hgen : (⟨σ'.speicher,
      rufUpdateG (W.g.faeden) u ⟨((W.g.faeden u).stapel),
        ⟨((W.g.faeden u).kopf.f), ((W.g.faeden u).kopf.rho),
          ((W.g.faeden u).kopf.s0),
          ⟨l, Γ, Λ, ρ', .ende rest⟩⟩, σ'.spur, ((W.g.faeden u).log)⟩,
      (W.g.lauf) ++ rufEigenG u
        [Ereignis.zugriff t true Λ σL.haelt,
          Ereignis.zugriff t2 false Λ σ.haelt],
      (W.g.start)⟩ : RufMaschineG D) = MT
    have hM : ((mitSpeicher W.g σ.speicher).faeden u).spur = σ.spur := hSpurEq
    have hMmem : (mitSpeicher W.g σ.speicher).speicher = σ.speicher := rfl
    have hM'sp : (MT.faeden u).spur = σ'.spur := by
      rw [← hgen]; simp only [rufUpdateG_self]
    have hMTsp : MT.speicher = σ'.speicher := by rw [← hgen]
    have hFrag := blattFragment_voll O passes keinRuf t f i e hw hL σ ρ σ' ρ'
      hExec (mitSpeicher W.g σ.speicher) MT u hM hM'sp hMmem hMTsp
    obtain ⟨hEq, hSchreib, hLi, _, hOwn⟩ := hFrag
    have hEq' : zugriffe (mitSpeicher W.g σ.speicher) MT u =
        fragmentListe t [.inl t2] := by
      rw [← hOrte]
      exact hEq
    have hLi' : ∀ c, LiestG (mitSpeicher W.g σ.speicher) MT u c →
        c ∈ ([.inl t2] : List (D.Tab ⊕ D.Glob)) := by
      intro c hc
      have hmem := hLi c hc
      rw [hOrte] at hmem
      exact hmem
    have hLiR : LiestG (mitSpeicher W.g σ.speicher) MT u (.inl t2) := by
      unfold LiestG
      rw [hEq']
      simp [fragmentListe]
    have hValFw := wLesbar_aus_weiterleitung (σ := σ.speicher) (σw := σ)
      (M'' := MT) (hT := hT2)
      vr f8 hL8 hPend hWert hv2 hMemR hProjR hTsR hTraegerR
    have hEreig : ereignisse (mitSpeicher W.g σ.speicher) MT u =
        [Ereignis.zugriff t true Λ σL.haelt,
          Ereignis.zugriff t2 false Λ σ.haelt] :=
      ereignisse_eq (hM'sp.trans (by rw [hSpur, hM]))
    have hLesen : lesenVon (mitSpeicher W.g σ.speicher) MT u = [.inl t2] := by
      simp [lesenVon, hEq, hOrte, fragmentListe]
    have hGenommen : genommenVon (mitSpeicher W.g σ.speicher) MT u = [] := by
      simp [genommenVon, hEreig]
    have hGegeben : gegebenVon (mitSpeicher W.g σ.speicher) MT u = [] := by
      simp [gegebenVon, hEreig]
    have hVorAt : vorSicht ord W u σ.speicher MT
        (fun _ => (⟨ts, σ.speicher, Speichermodell.Sicht.null⟩ : NachrichtW D))
        (.inl t) =
        max (W.sicht u (.inl t))
          (Speichermodell.beitrag (ordVon ord (.inl t2)) (.inl t2)
            (⟨ts, σ.speicher, Speichermodell.Sicht.null⟩ : NachrichtW D)
            (.inl t)) := by
      simp [vorSicht, hGenommen, hLesen, locksicht, lesesicht,
        Speichermodell.Sicht.verein]
    have hBeitrag0 : Speichermodell.beitrag (ordVon ord (.inl t2)) (.inl t2)
        (⟨ts, σ.speicher, Speichermodell.Sicht.null⟩ : NachrichtW D)
        (.inl t) = 0 := by
      have hO : ordVon ord (.inl t2) = .entspannt := rfl
      rw [hO]
      simp only [Speichermodell.beitrag, Speichermodell.Sicht.eins]
      rw [if_neg (fun heq => hNe heq.symm)]
    have hleaf : s.istBlatt = true := by
      rw [hs]; exact BlattG.istBlatt (BlattG.assignSlot t f i e hw hL)
    have hstep : execStmt O passes keinRuf s
        ((mitSpeicher W.g σ.speicher).weltVon u) ρ = Ausgang.ok σ' ρ' := by
      rw [hs, hW]
      exact hExec
    have hneu' : σ'.spur =
        [Ereignis.zugriff t true Λ σL.haelt,
          Ereignis.zugriff t2 false Λ σ.haelt] ++
        ((mitSpeicher W.g σ.speicher).faeden u).spur := by
      rw [hSpur, hM]
    have hkein : ∀ (L : D.Lock) (h : List D.Lock),
        Ereignis.nimmt L h ∉
          [Ereignis.zugriff t true Λ σL.haelt,
            Ereignis.zugriff t2 false Λ σ.haelt] := by
      intro L h hm; simp at hm
    have hblatt : RufSchrittG P O passes (mitSpeicher W.g σ.speicher) u MT := by
      rw [← hgen]
      exact RufSchrittG.blatt (mitSpeicher W.g σ.speicher) u l Γ Λ Λ s rest ρ
        hleaf hhead hΛ σ' ρ'
        [Ereignis.zugriff t true Λ σL.haelt,
          Ereignis.zugriff t2 false Λ σ.haelt]
        hstep hneu' hkein
    refine ⟨hblatt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      have hcmem := hLi' c hc
      simp only [List.mem_singleton] at hcmem
      subst hcmem
      exact hValFw.2.2.2 hLiR
    · intro c hc
      -- Vacuous: presented memory is G memory by construction
      -- (`σ.speicher` over `W.g`), so every carrier agrees.
      rw [hMem]
      exact traegerGleich_refl _ _
    · intro c hc
      have hcEq := hOwn c hc
      subst hcEq
      obtain ⟨hClock, hView⟩ := hErbt
      have hle1 : W.sicht u (Sum.inl t) < traceFrisch nN :=
        Nat.lt_of_le_of_lt hView (hInvN.2 co a)
      have hle0 : Speichermodell.beitrag (ordVon ord (.inl t2)) (.inl t2)
          (⟨ts, σ.speicher, Speichermodell.Sicht.null⟩ : NachrichtW D)
          (Sum.inl t) < traceFrisch nN := by
        rw [hBeitrag0]
        have hlt := hInvN.2 co a
        omega
      refine ⟨?_, ?_⟩
      · rw [hVorAt]
        exact Nat.max_lt.mpr ⟨hle1, hle0⟩
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
            (fun _ => (⟨ts, σ.speicher, Speichermodell.Sicht.null⟩ :
              NachrichtW D)))
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
              (fun _ => (⟨ts, σ.speicher, Speichermodell.Sicht.null⟩ :
                NachrichtW D)))
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
          (fun _ => (⟨ts, σ.speicher, Speichermodell.Sicht.null⟩ :
            NachrichtW D)) c)
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
  · exact hWert.trans (congrArg Option.some hv2)

/-! ## 5. Stale views are allowed; no global value for unflushed stores. -/

/-- **STALE DIVERGENCE (proved):** in `sbNach2` core 0 loads `0` at `sbY`
    while core 1 holds the unflushed `1` there -- the two cores observe
    different values at one address. An unflushed store has no global
    value; a validator that needs one global value per address refuses
    this state. -/
theorem stale_kein_globaler_wert :
    ∃ (s : TSOZustand) (a : Adresse),
      loadByte s 0 a ≠ loadByte s 1 a := by
  refine ⟨sbNach2, sbY, ?_⟩
  have h0 : loadByte sbNach2 0 sbY = some 0 := sb_beide_laden_null.1
  have h1 : loadByte sbNach2 1 sbY = some sbEins := by decide
  rw [h0, h1]
  decide

/-- **GROUP DIVERGENCE (proved):** at `hS3` (two issued bytes, only the
    first flushed) the forwarding core and the foreign core assemble
    different words at one base address. No single source message covers
    both observations: the committed path (§3) and the uniformly-linked
    forwarded path (§4) never fire on a torn footprint. -/
theorem gruppe_kein_globaler_wert :
    ladeWort8 hS3 1 sbX ≠ ladeWort8 hS3 0 sbX := by
  have h := gruppe_reisst_fremd
  rw [h.1, h.2.1]
  decide

/-! ## 6. Joint witness: two tables, one copy, growing drain. -/

/- CUTS:
    - Proved here (§§1-5): read-case preservation (`hwLade_erhaelt_wf`),
      the committed machine-read value (`hwLade_trifft_speicher`), the
      table-read contribution bound (`beitrag_tabelle_le`), the trace of a
      one-read fragment (`lesespur_assignSlot`), the committed
      read-fragment `SchrittW` (`schrittW_aus_lesefragment_gruppe`) and the
      forwarded read-fragment `SchrittW`
      (`schrittW_aus_lesefragment_weiterleitung`), the stale-view
      refusals (`stale_kein_globaler_wert`, `gruppe_kein_globaler_wert`).
    - OPEN: the joint witness (two-table declaration, drain chain,
      `_zeuge` for both transitions and the trace lemma).
-/

#print axioms hwLade_erhaelt_wf
#print axioms hwLade_trifft_speicher
#print axioms beitrag_tabelle_le
#print axioms lesespur_assignSlot
#print axioms schrittW_aus_lesefragment_gruppe
#print axioms schrittW_aus_lesefragment_weiterleitung
#print axioms stale_kein_globaler_wert
#print axioms gruppe_kein_globaler_wert

end Gabbro.Grammatik.X86
