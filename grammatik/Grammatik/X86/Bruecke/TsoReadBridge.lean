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
import Grammatik.X86.TSO.Kern.TSOTrace
import Grammatik.X86.Quelle.SourceMemory
import Grammatik.X86.TSO.Kern.WordAccessGrouping
import Grammatik.X86.Quelle.SourceAccessCompleteness
import Grammatik.X86.Bruecke.BridgeRead
import Grammatik.X86.Bruecke.CarrierTraceBridge
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.Logik.Ruf.RufAdaequatG
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll
import Grammatik.Speichermodell.Maschine.MaschineW
import Grammatik.Speichermodell.Maschine.Sicht

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
    trace clock. The read observations live at their own TSO state `sR`
    (loads and projection), the grouped drain at `s2`: they share only
    the source fragment (which reads one and writes the other), never a
    buffer -- the temporal read-before-issue ordering stays with the
    lowering consumer that owns the executed program. Every premise is
    used. -/
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
    (sR : TSOZustand)
    (f8 : Fin 8 → Byte)
    (hL8 : ∀ j : Fin 8, loadByte sR co (addrOff rdA j.val) = some (f8 j))
    (hPend : ∀ j : Fin 8, ∃ w : Byte,
      neuestens (sR.puffer co) (addrOff rdA j.val) = some w)
    (hWert : wortZahl lo2 hi2 (bytesWort f8) =
      some (cast (congrArg (Wert D) hT2) (σ.speicher.slots t2 k2 f2)))
    (hv2 : (cast (congrArg (Wert D) hT2) (σ.speicher.slots t2 k2 f2)) = vr)
    (ts : Nat)
    (hMemR : (⟨ts, σ.speicher, Speichermodell.Sicht.null⟩ : NachrichtW D) ∈
      W.hist (.inl t2))
    (hProjR : W.sicht u (.inl t2) ≤ sichtVon sR co rdA)
    (hTsR : sichtVon sR co rdA ≤ ts)
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

/-- Witness signature: parameterless, no answer, writes every table. -/
def rdSig : Signatur Bool Empty Empty Empty :=
  { params := [], erg := none, gruende := 0, haelt := [],
    schreibt := fun _ => true, gschreibt := fun g => (nomatch g),
    konsumiert := [], produziert := [], boden := none }

/-- Witness declaration: two tables (`false` written, `true` read) with one
    `.int 0 100` field each, one parameterless function whose contract
    writes both, nothing else. -/
def rdD : Deklaration where
  Tab := Bool
  count := fun _ => 1
  Feld := fun _ => Unit
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => true
  tabNr := fun _ => some false
  Glob := Empty
  gtyp := fun g => nomatch g
  nutzlast := fun g => nomatch g
  atomar := fun g => nomatch g
  geteilt := fun _ => false
  ggeteilt := fun g => nomatch g
  Lock := Empty
  rang := fun L => nomatch L
  maskiert := fun L => nomatch L
  Marke := Empty
  stufen := fun m => nomatch m
  braucht := fun _ => []
  gbraucht := fun g => nomatch g
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => rdSig
  eigner_nie_erzeugt := fun n t m s _ => nomatch m
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Empty
  aparams := fun a => nomatch a
  aerg := fun a => nomatch a
  aschreibt := fun a => nomatch a
  agschreibt := fun a => nomatch a
  Reg := Empty
  rtyp := fun r => nomatch r
  rklasse := fun r => nomatch r
  spiegel := fun r => nomatch r
  rzusage := fun r => nomatch r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun n i _ => nomatch i
  ggeteilt_bewacht := fun g => nomatch g

/-- The witness contract: writes every table. -/
def rdV : Vertrag rdD :=
  { schreibt := fun _ => true
    gschreibt := fun g => nomatch g
    erg := none
    gruende := 0
    haelt := []
    produziert := []
    boden := none }

/-- The witness oracle: no axioms, registers or globals to answer. -/
def rdO : Orakel rdD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun g => nomatch g

/-- The witness index: row 0 (of the read table). -/
def rdI : Expr rdD [] [] (.index (rdD.count true)) := Expr.lit 0

/-- The witness read permission: the read table needs no guards. -/
theorem rdHLread : darf rdD true [] :=
  fun _ h => False.elim (List.not_mem_nil h)

/-- The witness value: the read slot of the read table (one read event). -/
def rdE : Expr rdD [] [] (rdD.typ false ()) := Expr.slot true () rdI rdHLread

/-- The witness write permission: the written table needs no guards. -/
theorem rdHLW : darf rdD false [] :=
  fun _ h => False.elim (List.not_mem_nil h)

/-- The frame contract writes the written table. -/
theorem rdHwW : (vertragVon rdD ()).schreibt false = true := rfl

/-- The witness world: the written slot holds 9, the read slot holds 0,
    no trace yet. The copy stores 0 over 9: both sides change. -/
def rdSigma : World rdD where
  slots := fun t _ f => by
    cases t with
    | false => cases f; exact ⟨9, by decide, by decide⟩
    | true => cases f; exact ⟨0, by decide, by decide⟩
  globs := fun g => nomatch g
  spur := []

/-- The witness read world: the trace entry of the one read. -/
def rdSL : World rdD := rdSigma.lese [] (rdI.orte ++ rdE.orte)

/-- The witness footprint of the one read: layout base 4096, offset 8
    (disjoint from the write footprint at offset 0). -/
def rdA2 : Adresse := slotAddr 4096 8

/-- The witness read value: 0. -/
def rdZero : Zahl 0 100 := ⟨0, by decide, by decide⟩

/-- The witness overwritten value: 9. -/
def rdNine : Zahl 0 100 := ⟨9, by decide, by decide⟩

/-- The witness target memory: the write word is 9, everything else zero;
    full R/W, never executable. -/
def rdM9bytes (x : Adresse) : Byte :=
  if x = addrOff witA 0 then wortByte (zahlWort rdNine) 0
  else if x = addrOff witA 1 then wortByte (zahlWort rdNine) 1
  else if x = addrOff witA 2 then wortByte (zahlWort rdNine) 2
  else if x = addrOff witA 3 then wortByte (zahlWort rdNine) 3
  else if x = addrOff witA 4 then wortByte (zahlWort rdNine) 4
  else if x = addrOff witA 5 then wortByte (zahlWort rdNine) 5
  else if x = addrOff witA 6 then wortByte (zahlWort rdNine) 6
  else if x = addrOff witA 7 then wortByte (zahlWort rdNine) 7
  else BitVec.ofNat 8 0

/-- The witness target memory: 9 at the write footprint, zero elsewhere. -/
def rdM9 : Speicher :=
  { bytes := rdM9bytes, lesbar := fun _ => true,
    schreibbar := fun _ => true, ausfuehrbar := fun _ => false }

/-- The witness target memory after the zero-word write. -/
def rdM9' : Speicher :=
  { rdM9 with bytes := writeBytes rdM9 witA (zahlWort rdZero) }

/-- The footprint reads the read table: the index and value footprints are
    exactly the one read. -/
theorem rdOrte : rdI.orte ++ rdE.orte = [.inl true] := rfl

/-- The witness field types. -/
theorem rdHTW : rdD.typ false () = .int 0 100 := rfl

/-- The witness read field type. -/
theorem rdHTR : rdD.typ true () = .int 0 100 := rfl

/-! ## 7. Witness drain: the zero word over the nine word. -/

/-- The word the drain installs: zero (overwriting the witness nine). -/
def rdV0 : Wort := zahlWort rdZero

/-- Drain start: nine-word memory, core 0 carries the exact eight-entry
    group for the zero word at the slot address, all other buffers
    empty. -/
def rdS2 : TSOZustand :=
  ⟨rdM9, fun d => if d = 0 then wortEintraege witA rdV0 else []⟩

/-- After own flush 1: byte 0 installed. -/
def rdS3 : TSOZustand :=
  ⟨{ rdM9 with bytes := fun x =>
      if x = addrOff witA 0 then wortByte rdV0 0 else rdS2.mem.bytes x },
    pufferSetze rdS2.puffer 0 ((wortEintraege witA rdV0).drop 1)⟩

/-- Foreign issue on core 1 outside the footprint (real foreign
    activity inside the drain). -/
def rdS4 : TSOZustand :=
  ⟨rdS3.mem,
    pufferSetze rdS3.puffer 1 (rdS3.puffer 1 ++ [⟨ctF, ctFv⟩])⟩

/-- After own flush 2: bytes 0–1 installed. -/
def rdS5 : TSOZustand :=
  ⟨{ rdS4.mem with bytes := fun x =>
      if x = addrOff witA 1 then wortByte rdV0 1 else rdS4.mem.bytes x },
    pufferSetze rdS4.puffer 0 ((wortEintraege witA rdV0).drop 2)⟩

/-- After own flush 3: bytes 0–2 installed. -/
def rdS6 : TSOZustand :=
  ⟨{ rdS5.mem with bytes := fun x =>
      if x = addrOff witA 2 then wortByte rdV0 2 else rdS5.mem.bytes x },
    pufferSetze rdS5.puffer 0 ((wortEintraege witA rdV0).drop 3)⟩

/-- After own flush 4: bytes 0–3 installed. -/
def rdS7 : TSOZustand :=
  ⟨{ rdS6.mem with bytes := fun x =>
      if x = addrOff witA 3 then wortByte rdV0 3 else rdS6.mem.bytes x },
    pufferSetze rdS6.puffer 0 ((wortEintraege witA rdV0).drop 4)⟩

/-- After own flush 5: bytes 0–4 installed. -/
def rdS8 : TSOZustand :=
  ⟨{ rdS7.mem with bytes := fun x =>
      if x = addrOff witA 4 then wortByte rdV0 4 else rdS7.mem.bytes x },
    pufferSetze rdS7.puffer 0 ((wortEintraege witA rdV0).drop 5)⟩

/-- After own flush 6: bytes 0–5 installed. -/
def rdS9 : TSOZustand :=
  ⟨{ rdS8.mem with bytes := fun x =>
      if x = addrOff witA 5 then wortByte rdV0 5 else rdS8.mem.bytes x },
    pufferSetze rdS8.puffer 0 ((wortEintraege witA rdV0).drop 6)⟩

/-- After own flush 7: bytes 0–6 installed. -/
def rdS10 : TSOZustand :=
  ⟨{ rdS9.mem with bytes := fun x =>
      if x = addrOff witA 6 then wortByte rdV0 6 else rdS9.mem.bytes x },
    pufferSetze rdS9.puffer 0 ((wortEintraege witA rdV0).drop 7)⟩

/-- After own flush 8: all bytes installed, own buffer empty;
    the foreign byte stays pending. -/
def rdS11 : TSOZustand :=
  ⟨{ rdS10.mem with bytes := fun x =>
      if x = addrOff witA 7 then wortByte rdV0 7 else rdS10.mem.bytes x },
    pufferSetze rdS10.puffer 0 ((wortEintraege witA rdV0).drop 8)⟩

/-- Each recorded drain step computes as claimed. -/
theorem rd_step1 : flushKern rdS2 0 = some rdS3 := by rfl

theorem rd_step2 : issueByte rdS3 1 ctF ctFv = some rdS4 := by rfl

theorem rd_step3 : flushKern rdS4 0 = some rdS5 := by rfl

theorem rd_step4 : flushKern rdS5 0 = some rdS6 := by rfl

theorem rd_step5 : flushKern rdS6 0 = some rdS7 := by rfl

theorem rd_step6 : flushKern rdS7 0 = some rdS8 := by rfl

theorem rd_step7 : flushKern rdS8 0 = some rdS9 := by rfl

theorem rd_step8 : flushKern rdS9 0 = some rdS10 := by rfl

theorem rd_step9 : flushKern rdS10 0 = some rdS11 := by rfl

/-- Foreign buffers start empty off core 0. -/
theorem rdS2leer : ∀ d : Nat, d ≠ 0 → rdS2.puffer d = [] := by
  intro d hne
  show (if d = 0 then wortEintraege witA rdV0 else []) = []
  rw [if_neg hne]

/-- Foreign-buffer emptiness survives the first own flush. -/
theorem rdS3leer : ∀ d : Nat, d ≠ 0 → rdS3.puffer d = [] :=
  fremd_leer_eigen_erhalten rdS2 rdS3 rd_step1 rdS2leer

/-- The foreign entry lands on core 1. -/
theorem rdBuf1_4 : rdS4.puffer 1 = [⟨ctF, ctFv⟩] := by rfl

/-- Off-core buffers stay empty except core 1 after the foreign issue. -/
theorem rdOff01_4 : ∀ d : Nat, d ≠ 0 → d ≠ 1 → rdS4.puffer d = [] := by
  intro d h0 h1
  show pufferSetze rdS3.puffer 1 (rdS3.puffer 1 ++ [⟨ctF, ctFv⟩]) d = []
  rw [pufferSetze_anders _ _ h1]
  show rdS3.puffer d = []
  show pufferSetze rdS2.puffer 0 ((wortEintraege witA rdV0).drop 1) d = []
  rw [pufferSetze_anders _ _ h0]
  show rdS2.puffer d = []
  show (if d = 0 then wortEintraege witA rdV0 else []) = []
  rw [if_neg h0]

/-- The foreign entry rides every later own flush untouched. -/
theorem rdBuf1_5 : rdS5.puffer 1 = [⟨ctF, ctFv⟩] := by
  rw [eigen_fremd_gleich rdS4 rdS5 rd_step3 1 (by decide)]
  exact rdBuf1_4

theorem rdBuf1_6 : rdS6.puffer 1 = [⟨ctF, ctFv⟩] := by
  rw [eigen_fremd_gleich rdS5 rdS6 rd_step4 1 (by decide)]
  exact rdBuf1_5

theorem rdBuf1_7 : rdS7.puffer 1 = [⟨ctF, ctFv⟩] := by
  rw [eigen_fremd_gleich rdS6 rdS7 rd_step5 1 (by decide)]
  exact rdBuf1_6

theorem rdBuf1_8 : rdS8.puffer 1 = [⟨ctF, ctFv⟩] := by
  rw [eigen_fremd_gleich rdS7 rdS8 rd_step6 1 (by decide)]
  exact rdBuf1_7

theorem rdBuf1_9 : rdS9.puffer 1 = [⟨ctF, ctFv⟩] := by
  rw [eigen_fremd_gleich rdS8 rdS9 rd_step7 1 (by decide)]
  exact rdBuf1_8

theorem rdBuf1_10 : rdS10.puffer 1 = [⟨ctF, ctFv⟩] := by
  rw [eigen_fremd_gleich rdS9 rdS10 rd_step8 1 (by decide)]
  exact rdBuf1_9

theorem rdBuf1_11 : rdS11.puffer 1 = [⟨ctF, ctFv⟩] := by
  rw [eigen_fremd_gleich rdS10 rdS11 rd_step9 1 (by decide)]
  exact rdBuf1_10

/-- Off-core emptiness rides every later own flush untouched. -/
theorem rdOff01_5 : ∀ d : Nat, d ≠ 0 → d ≠ 1 → rdS5.puffer d = [] := by
  intro d h0 h1
  rw [eigen_fremd_gleich rdS4 rdS5 rd_step3 d h0]
  exact rdOff01_4 d h0 h1

theorem rdOff01_6 : ∀ d : Nat, d ≠ 0 → d ≠ 1 → rdS6.puffer d = [] := by
  intro d h0 h1
  rw [eigen_fremd_gleich rdS5 rdS6 rd_step4 d h0]
  exact rdOff01_5 d h0 h1

theorem rdOff01_7 : ∀ d : Nat, d ≠ 0 → d ≠ 1 → rdS7.puffer d = [] := by
  intro d h0 h1
  rw [eigen_fremd_gleich rdS6 rdS7 rd_step5 d h0]
  exact rdOff01_6 d h0 h1

theorem rdOff01_8 : ∀ d : Nat, d ≠ 0 → d ≠ 1 → rdS8.puffer d = [] := by
  intro d h0 h1
  rw [eigen_fremd_gleich rdS7 rdS8 rd_step6 d h0]
  exact rdOff01_7 d h0 h1

theorem rdOff01_9 : ∀ d : Nat, d ≠ 0 → d ≠ 1 → rdS9.puffer d = [] := by
  intro d h0 h1
  rw [eigen_fremd_gleich rdS8 rdS9 rd_step7 d h0]
  exact rdOff01_8 d h0 h1

theorem rdOff01_10 : ∀ d : Nat, d ≠ 0 → d ≠ 1 → rdS10.puffer d = [] := by
  intro d h0 h1
  rw [eigen_fremd_gleich rdS9 rdS10 rd_step8 d h0]
  exact rdOff01_9 d h0 h1

theorem rdOff01_11 : ∀ d : Nat, d ≠ 0 → d ≠ 1 → rdS11.puffer d = [] := by
  intro d h0 h1
  rw [eigen_fremd_gleich rdS10 rdS11 rd_step9 d h0]
  exact rdOff01_10 d h0 h1

/-- Exclusion from the fixed foreign entry: core 1 holds exactly one
    pending byte outside the footprint, every other foreign buffer is
    empty. -/
theorem rdFremdFF (s : TSOZustand) (h1 : s.puffer 1 = [⟨ctF, ctFv⟩])
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

/-- Every visited state is foreign-free at the slot footprint. -/
theorem rd_ff2 : FremdFrei rdS2 0 witA :=
  fremdFrei_aus_leer rdS2 0 witA rdS2leer

theorem rd_ff3 : FremdFrei rdS3 0 witA :=
  fremdFrei_aus_leer rdS3 0 witA rdS3leer

theorem rd_ff4 : FremdFrei rdS4 0 witA :=
  rdFremdFF rdS4 rdBuf1_4 rdOff01_4

theorem rd_ff5 : FremdFrei rdS5 0 witA :=
  rdFremdFF rdS5 rdBuf1_5 rdOff01_5

theorem rd_ff6 : FremdFrei rdS6 0 witA :=
  rdFremdFF rdS6 rdBuf1_6 rdOff01_6

theorem rd_ff7 : FremdFrei rdS7 0 witA :=
  rdFremdFF rdS7 rdBuf1_7 rdOff01_7

theorem rd_ff8 : FremdFrei rdS8 0 witA :=
  rdFremdFF rdS8 rdBuf1_8 rdOff01_8

theorem rd_ff9 : FremdFrei rdS9 0 witA :=
  rdFremdFF rdS9 rdBuf1_9 rdOff01_9

theorem rd_ff10 : FremdFrei rdS10 0 witA :=
  rdFremdFF rdS10 rdBuf1_10 rdOff01_10

theorem rd_ff11 : FremdFrei rdS11 0 witA :=
  rdFremdFF rdS11 rdBuf1_11 rdOff01_11

/-- The witness start carries the exact group. -/
theorem rd_hgrp : WortGruppe rdS2 0 witA rdV0 := by
  refine ⟨rfl, ?_⟩
  exact fremdFrei_aus_leer rdS2 0 witA rdS2leer

/-- The witness start reads the grouped footprint. -/
theorem rd_hles : lesbar8 rdS2.mem witA = true := by rfl

/-- Each recorded step is a drain step (eight own flushes around one
    foreign issue). -/
theorem rd_e1 : DrainSchritt 0 rdS2 rdS3 := .eigen rd_step1

theorem rd_e2 : DrainSchritt 0 rdS3 rdS4 :=
  .fremdAusgabe 1 ⟨ctF, ctFv⟩ (by decide) rd_step2

theorem rd_e3 : DrainSchritt 0 rdS4 rdS5 := .eigen rd_step3

theorem rd_e4 : DrainSchritt 0 rdS5 rdS6 := .eigen rd_step4

theorem rd_e5 : DrainSchritt 0 rdS6 rdS7 := .eigen rd_step5

theorem rd_e6 : DrainSchritt 0 rdS7 rdS8 := .eigen rd_step6

theorem rd_e7 : DrainSchritt 0 rdS8 rdS9 := .eigen rd_step7

theorem rd_e8 : DrainSchritt 0 rdS9 rdS10 := .eigen rd_step8

theorem rd_e9 : DrainSchritt 0 rdS10 rdS11 := .eigen rd_step9

/-- The full drain trace with its visited states. -/
theorem rd_spur : DrainSpur 0 rdS2 rdS11
    [rdS2, rdS3, rdS4, rdS5, rdS6, rdS7, rdS8, rdS9, rdS10, rdS11] :=
  .schritt _ _ _ _ rd_e1 (.schritt _ _ _ _ rd_e2 (.schritt _ _ _ _ rd_e3
    (.schritt _ _ _ _ rd_e4 (.schritt _ _ _ _ rd_e5 (.schritt _ _ _ _ rd_e6
      (.schritt _ _ _ _ rd_e7 (.schritt _ _ _ _ rd_e8 (.schritt _ _ _ _ rd_e9
        (.leer rdS11)))))))))

/-- The drain end is visited. -/
theorem rd_hend :
    rdS11 ∈ [rdS2, rdS3, rdS4, rdS5, rdS6, rdS7, rdS8, rdS9, rdS10,
      rdS11] := by
  simp

/-- The drain ends with an empty own buffer. -/
theorem rd_hempty : rdS11.puffer 0 = [] := by rfl

/-- Every visited state is foreign-free at the slot footprint. -/
theorem rd_hstoer :
    ∀ x ∈ [rdS2, rdS3, rdS4, rdS5, rdS6, rdS7, rdS8, rdS9, rdS10, rdS11],
      FremdFrei x 0 witA := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact rd_ff2
  · exact rd_ff3
  · exact rd_ff4
  · exact rd_ff5
  · exact rd_ff6
  · exact rd_ff7
  · exact rd_ff8
  · exact rd_ff9
  · exact rd_ff10
  · exact rd_ff11

/-- The grouped word reads back whole at the drain end. -/
theorem rd_hread : read64 rdS11.mem witA = some rdV0 :=
  wort_gruppe_liest_zurueck rdS2 rdS11 _ 0 witA rdV0 rd_hgrp rd_hles
    rd_spur rd_hend rd_hempty rd_hstoer

/-- Stale-view divergence at the foreign address: core 0 still reads
    canonical zero while core 1 forwards its pending seven. -/
theorem rd_stale0 : loadByte rdS4 0 ctF = some (BitVec.ofNat 8 0) := by
  decide

theorem rd_stale1 : loadByte rdS4 1 ctF = some ctFv := by
  decide

/-- The zero word lands where the nine stood: the target write. -/
theorem rd_hTgt : write64 rdM9 witA (zahlWort rdZero) = some rdM9' := by
  simp only [write64, rdM9']
  rw [if_pos (by decide : schreibbar8 rdM9 witA = true)]

/-- The drain observably changes the canonical byte at the slot. -/
theorem rd_hBytes : rdM9.bytes witA ≠ rdM9'.bytes witA := by
  have hByte : writeBytes rdM9 witA (zahlWort rdZero) witA =
      wortByte (zahlWort rdZero) 0 := by
    have h := writeBytesN_hit rdM9 witA (zahlWort rdZero) 8 0
      (by decide) (by decide)
    rw [addrOff_null] at h
    unfold writeBytes
    exact h
  show rdM9bytes witA ≠ writeBytes rdM9 witA (zahlWort rdZero) witA
  rw [hByte]
  decide

/-! ## 8. Witness machine and source-step facts. -/

/-- Witness program over `rdD` (never consulted by the blatt step). -/
def rdProg : Programm rdD where
  invariante := fun i => nomatch i
  requires := fun _ => Expr.wahr
  ensures := fun _ => Expr.wahr
  rumpf := fun _ => .ret .keine (List.Perm.refl _)

/-- Witness statement: copy the read slot into the write slot. -/
def rdS : Stmt rdD (vertragVon rdD ()) true [] [] [] :=
  Stmt.assignSlot false () rdI rdE rdHwW rdHLW

def rdRest : Endblock rdD (vertragVon rdD ()) true [] [] :=
  Endblock.leave rfl

def rdRahmen : RufRahmenG rdD :=
  ⟨(), Env.nil, rdSigma,
    ⟨true, [], [], Env.nil,
      GRest.ende (Endblock.cons rdS rdRest)⟩⟩

def rdFaden : RufFadenG rdD :=
  ⟨[], rdRahmen, [], []⟩

def rdMachine : RufMaschineG rdD :=
  ⟨rdSigma.speicher, fun _ => rdFaden, [], rdSigma⟩

/-- Head, world and lock facts compute. -/
theorem rd_hhead : (rdMachine.faeden 0).kopf.rest =
    ⟨true, [], [], Env.nil,
      GRest.ende (Endblock.cons rdS rdRest)⟩ := rfl

theorem rd_hwelt : rdMachine.weltVon 0 = rdSigma := rfl

theorem rd_hΛ : HeldIn ([] : List (Res rdD)) (offen (rdMachine.faeden 0).spur) := by
  simp [HeldIn]

/-- The start W machine sits on the G machine. -/
theorem rd_hWg : (RufStartW rdMachine).g = rdMachine := rfl

/-- The copy fragment is admitted with full permissions. -/
theorem rd_hOk : repOk (rdD.typ false ()) 4096 16 0 = true := by decide

/-- The index evaluates to row 0. -/
theorem rd_hk : (eval rdSL rdI rdSL Env.nil).n = 0 := rfl

/-- The value expression reads the read slot: 0. -/
theorem rd_hv : (cast (congrArg (Wert rdD) rdHTW)
    (eval rdSL rdE rdSL Env.nil) : Wert rdD (.int 0 100)) =
    rdZero := rfl

/-- The source step runs: one reached step (no calls). -/
theorem rd_hExecFull : ∃ σ' ρ', execStmt rdO 0 keinRuf
    (Stmt.assignSlot (l := true) false () rdI rdE rdHwW rdHLW)
    rdSigma Env.nil = .ok σ' ρ' := by
  simp only [execStmt]
  exact ⟨_, _, rfl⟩

/-- The write slot holds 9 before the step. -/
theorem rd_hBefore : (rdSigma.slots false 0 ()).n = 9 := rfl

/-- The write-side footprint is fully readable. -/
theorem rd_hRd : lesbar8 rdM9 witA = true := by decide

/-- The read world is the named one. -/
theorem rd_hLese : rdSL = rdSigma.lese [] (rdI.orte ++ rdE.orte) := rfl

/-- The frame contract writes the written table. -/
theorem rd_hWr : rdD.schreibt () false = true := rfl

/-! ## 9. Witness read-side facts and the committed joint witness. -/

/-- The read footprint is untouched by the write drain's buffer. -/
theorem rd_hMiss : ∀ j : Nat, j < 8 →
    neuestens (rdS2.puffer 0) (addrOff rdA2 j) = none := by
  decide

/-- The read footprint is fully readable. -/
theorem rd_hRdR : lesbar8 rdS2.mem rdA2 = true := by decide

/-- The read slot is represented at the read footprint: it holds 0. -/
theorem rd_hRepRead :
    RepSlot true 0 () 0 100 rdHTR rdA2 rdS2.mem rdSigma := by
  unfold RepSlot
  decide

/-- The canonical word at the read footprint is the zero word. -/
theorem rd_hR64 : read64 rdS2.mem rdA2 = some (zahlWort rdZero) :=
  rd_hRepRead

/-- The committed group load at the read footprint is the zero word. -/
theorem rd_hWort : ladeWort8 rdS2 0 rdA2 = some (zahlWort rdZero) :=
  (ladeWort8_ohne_weiterleitung rdS2 0 rdA2 rd_hMiss rd_hRdR).trans rd_hR64

/-- The source read slot holds the witness zero. -/
theorem rd_hv2 : (cast (congrArg (Wert rdD) rdHTR)
    (rdSigma.slots true 0 ())) = rdZero := rfl

/-- The start W history carries the timestamp-0 read message. -/
theorem rd_hMemR : (⟨0, rdSigma.speicher, Speichermodell.Sicht.null⟩ :
    NachrichtW rdD) ∈ (RufStartW rdMachine).hist (.inl true) :=
  List.mem_singleton_self _

/-- The start view is covered by the read projection. -/
theorem rd_hProjR : (RufStartW rdMachine).sicht 0 (.inl true) ≤
    sichtVon rdS2 0 rdA2 :=
  Nat.zero_le _

/-- The read projection sits below timestamp 0: no pending entry at the
    read base address. -/
theorem rd_hTsR : sichtVon rdS2 0 rdA2 ≤ 0 := by decide

/-- The presented memory agrees with itself at the read carrier. -/
theorem rd_hTraegerR :
    TraegerGleich rdSigma.speicher rdSigma.speicher (.inl true) :=
  traegerGleich_refl _ _

/-- The inherited history over the drain end. -/
theorem rd_hErbt :
    ErbtW (spurStart rdS11) (RufStartW rdMachine) 0 0 (Sum.inl false) witA :=
  erbtW_start _ _ _ _ _ _

/-- The drain-end start node satisfies the trace invariant. -/
theorem rd_hInv : SpurInv (spurStart rdS11) := spurStart_inv _

/-- The drain-end node stands over the drain-end state. -/
theorem rd_hnode : (spurStart rdS11).tso = rdS11 := rfl

/-! ## 10. Forwarded-witness state and reading W. -/

/-- Forwarded-read TSO state: the nine-word memory, core 0 carries eight
    pending zero bytes at the read footprint, all other buffers empty.
    Every footprint byte forwards its (zero) value to core 0 only. -/
def rdSF : TSOZustand :=
  ⟨rdM9, fun d => if d = 0 then wortEintraege rdA2 (zahlWort rdZero) else []⟩

/-- The forwarded bytes: all zero. -/
def rdF8 : Fin 8 → Byte := fun _ => BitVec.ofNat 8 0

/-- Every footprint byte loads its forwarded zero. -/
theorem rd_hL8 : ∀ j : Fin 8,
    loadByte rdSF 0 (addrOff rdA2 j.val) = some (rdF8 j) := by
  decide

/-- Every footprint byte has a pending own-buffer entry. -/
theorem rd_hPend : ∀ j : Fin 8, ∃ w : Byte,
    neuestens (rdSF.puffer 0) (addrOff rdA2 j.val) = some w := by
  decide

/-- The assembled forwarded word parses to the source read value. -/
theorem rd_hWertFw : wortZahl 0 100 (bytesWort rdF8) =
    some (cast (congrArg (Wert rdD) rdHTR)
      (rdSigma.speicher.slots true 0 ())) := by
  have hB : bytesWort rdF8 = zahlWort rdZero := by decide
  rw [hB, zahlWort_wortZahl rdZero (by decide) (by decide)]
  rfl

/-- The message memory holds the witness zero at the read slot. -/
theorem rd_hv2Fw : (cast (congrArg (Wert rdD) rdHTR)
    (rdSigma.speicher.slots true 0 ())) = rdZero := rfl

/-- Read and written carriers differ. -/
theorem rd_hNe : (.inl true : rdD.Tab ⊕ rdD.Glob) ≠ .inl false := by
  decide

/-- The reading W: the G machine with a timestamp-0 message everywhere
    and one timestamp-1 message at the read carrier (value: the witness
    memory), view 1 at the read carrier, 0 elsewhere. This is the W shape
    a lowering certificate must supply for a forwarded read: the value
    link is explicit, never derived from the buffer here. -/
def rdW1 : RufMaschineW rdD :=
  ⟨rdMachine,
    fun c => if c = .inl true then
      [⟨0, rdSigma.speicher, Speichermodell.Sicht.null⟩,
        ⟨1, rdSigma.speicher, Speichermodell.Sicht.null⟩]
      else [⟨0, rdSigma.speicher, Speichermodell.Sicht.null⟩],
    fun _ c => if c = .inl true then 1 else 0,
    fun _ => Speichermodell.Sicht.null⟩

/-- The timestamp-1 read message is in the reading history. -/
theorem rd_hMemRFw : (⟨1, rdSigma.speicher, Speichermodell.Sicht.null⟩ :
    NachrichtW rdD) ∈ rdW1.hist (.inl true) := by
  simp [rdW1]

/-- The reading view is covered by the forwarding projection. -/
theorem rd_hProjRFw : rdW1.sicht 0 (.inl true) ≤ sichtVon rdSF 0 rdA2 := by
  decide

/-- The forwarding projection sits below timestamp 1. -/
theorem rd_hTsRFw : sichtVon rdSF 0 rdA2 ≤ 1 := by decide

/-! ## 11. Clock-2 projection of the drain end. -/

/-- Start node over the last drain state (clock 1). -/
def rdNA10 : SpurKnoten := spurStart rdS10

/-- Second node: one flush later (clock 2), carrying the flushed byte as
    a timestamp-1 release message. A real projected step, not a stub:
    the history and views follow the accepted `SpurSchritt.flush`
    equations. Only the last drain flush is traced; the earlier seven
    stay with the `DrainSpur` witness. -/
def rdNB11 : SpurKnoten :=
  { tso := rdS11
    hist := fun x => if x = addrOff witA 7 then rdNA10.hist x ++
      [Speichermodell.nachricht Speichermodell.Ordnung.freigabe
        (rdNA10.blick 0) (addrOff witA 7) rdNA10.frisch (wortByte rdV0 7)]
      else rdNA10.hist x
    blick := fun d => if d = 0 then
      (rdNA10.blick 0).setze (addrOff witA 7) rdNA10.frisch else rdNA10.blick d
    frisch := 2 }

/-- The last flush as a projected trace step. -/
theorem rd_stufe : SpurSchritt rdNA10 rdNB11 :=
  SpurSchritt.flush rdNA10 rdNB11 0 ⟨addrOff witA 7, wortByte rdV0 7⟩
    [] rd_step9 rfl rfl rfl rfl

/-- The clock-2 node satisfies the trace invariant. -/
theorem rd_hInvB : SpurInv rdNB11 :=
  spurSchritt_inv _ _ rd_stufe (spurStart_inv _)

/-- The inherited history over the clock-2 node: every reading timestamp
    (0 or 1) sits below clock 2, and the write carrier's view (0) is
    covered. -/
theorem rd_hErbtFw :
    ErbtW rdNB11 rdW1 0 0 (Sum.inl false) witA := by
  refine ⟨?_, ?_⟩
  · intro d m hm
    show m.ts < 2
    have hmem : m ∈ (if d = (Sum.inl true : rdD.Tab ⊕ rdD.Glob) then
        [⟨0, rdSigma.speicher, Speichermodell.Sicht.null⟩,
          ⟨1, rdSigma.speicher, Speichermodell.Sicht.null⟩]
        else [⟨0, rdSigma.speicher, Speichermodell.Sicht.null⟩] :
        List (NachrichtW rdD)) := hm
    by_cases hd : d = (Sum.inl true : rdD.Tab ⊕ rdD.Glob)
    · rw [if_pos hd] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl <;> decide
    · rw [if_neg hd] at hmem
      simp only [List.mem_singleton] at hmem
      subst hmem
      decide
  · exact Nat.zero_le _

/-- The clock-2 node stands over the drain-end state. -/
theorem rd_hnodeFw : rdNB11.tso = rdS11 := rfl

/-! ## 12. Joint witnesses: forwarded transition and trace lemma. -/

/-- **JOINT WITNESS for `schrittW_aus_lesefragment_weiterleitung`.**
    Every premise holds jointly on concrete values: the same two-table
    copy run (`0` over `9`, memory-changing on both sides) and the same
    growing drain as §9, but the read value comes from eight pending
    own-buffer zero bytes assembled by core 0, linked to the source read
    value by the explicit value certificate, over the reading W with its
    timestamp-1 message and the clock-2 projected drain end. The
    stale-view divergence rides along unchanged: no global value for the
    unflushed foreign store. Non-degenerate: a written table, a
    memory-changing source step and a memory-changing target drain. -/
theorem schrittW_aus_lesefragment_weiterleitung_zeuge :
    ∃ (σ' : World rdD) (ρ' : Env rdD []),
      execStmt rdO 0 rdR
        (Stmt.assignSlot (l := true) false () rdI rdE rdHwW rdHLW)
        rdSigma Env.nil = .ok σ' ρ' ∧
      (rdSigma.slots false 0 ()).n = 9 ∧ (σ'.slots false 0 ()).n = 0 ∧
      rdM9.bytes witA ≠ rdM9'.bytes witA ∧
      rdD.schreibt () false = true ∧
      (.inl true : rdD.Tab ⊕ rdD.Glob) ≠ .inl false ∧
      ErbtW rdNB11 rdW1 0 0 (Sum.inl false) witA ∧
      SpurInv rdNB11 ∧
      rdS4.puffer 1 = [⟨ctF, ctFv⟩] ∧ ctF ∉ Fuss witA ∧
      loadByte rdS4 0 ctF = some (BitVec.ofNat 8 0) ∧
      loadByte rdS4 1 ctF = some ctFv ∧
      (∃ (W' : RufMaschineW rdD) (σm : Gabbro.Grammatik.Speicher rdD)
        (M'' : RufMaschineG rdD)
        (wahl : rdD.Tab ⊕ rdD.Glob → NachrichtW rdD)
        (neu : rdD.Tab ⊕ rdD.Glob → Nat),
        SchrittW rdProg rdO 0 (fun g => nomatch g) rdW1 0 W'
          σm M'' wahl neu ∧
        (∃ w, read64 rdNB11.tso.mem witA = some w ∧
          wortZahl 0 100 w = some rdZero) ∧
        RepSlot false 0 () 0 100 rdHTW witA rdM9' σ' ∧
        wortZahl 0 100 (bytesWort rdF8) = some rdZero) := by
  obtain ⟨σ', ρ', hExec⟩ := rd_hExecFull
  have hAfter : (σ'.slots false 0 ()).n = 0 := by
    cases hExec
    rfl
  have hMain := schrittW_aus_lesefragment_weiterleitung rdProg rdO 0
    (fun g => nomatch g) false () 0 100 rdHTW 4096 16 0 rd_hOk rdI rdE
    rdMachine 0 rdSigma Env.nil rdHwW rdHLW rdS rdRest rfl rd_hhead rdSL
    rd_hLese 0 rdZero rd_hk rd_hv true () 0 100 rdHTR 0 rdOrte rd_hNe witA rdM9
    rdM9' σ' ρ' hExec rd_hTgt rd_hRd (by decide) (by decide) rd_hwelt rd_hΛ
    rdW1 rfl 0 rdNB11 rd_hErbtFw rd_hInvB rdS11
    rd_hnodeFw rdS2 [rdS2, rdS3, rdS4, rdS5, rdS6, rdS7, rdS8, rdS9, rdS10, rdS11]
    rd_hgrp rd_hles rd_spur rd_hend rd_hempty rd_hstoer
    rdA2 rdZero rdSF rdF8 rd_hL8 rd_hPend rd_hWertFw rd_hv2Fw 1
    rd_hMemRFw rd_hProjRFw rd_hTsRFw rd_hTraegerR
  obtain ⟨W', σm, M'', wahl, neu, hSW, hValW, hRepW, hReadV⟩ := hMain
  exact ⟨σ', ρ', hExec, rd_hBefore, hAfter, rd_hBytes, rd_hWr, rd_hNe,
    rd_hErbtFw, rd_hInvB, rdBuf1_4, ctFfresh, rd_stale0, rd_stale1,
    W', σm, M'', wahl, neu, hSW, hValW, hRepW, hReadV⟩

/-- **JOINT WITNESS for `lesespur_assignSlot`.** Every premise holds
    jointly on the two-table copy run -- one table the witness function
    writes, a reached step changing the source slot `9 → 0` and the
    mapped target bytes -- and so does the two-event trace shape, with
    the writer fact and the memory change beside it. -/
theorem lesespur_assignSlot_zeuge :
    ∃ (σ' : World rdD) (ρ' : Env rdD []),
      execStmt rdO 0 rdR
        (Stmt.assignSlot (l := true) false () rdI rdE rdHwW rdHLW)
        rdSigma Env.nil = .ok σ' ρ' ∧
      σ'.spur = [Ereignis.zugriff false true [] rdSL.haelt,
        Ereignis.zugriff true false [] rdSigma.haelt] ++ rdSigma.spur ∧
      rdI.orte ++ rdE.orte = [.inl true] ∧
      rdD.schreibt () false = true ∧
      (rdSigma.slots false 0 ()).n = 9 ∧ (σ'.slots false 0 ()).n = 0 ∧
      rdM9.bytes witA ≠ rdM9'.bytes witA := by
  obtain ⟨σ', ρ', hExec⟩ := rd_hExecFull
  have hAfter : (σ'.slots false 0 ()).n = 0 := by
    cases hExec
    rfl
  have hSpur := lesespur_assignSlot rdO 0 false () rdI rdE rdHwW rdHLW rdSigma
    Env.nil rdSL rd_hLese true rdOrte σ' ρ' hExec
  exact ⟨σ', ρ', hExec, hSpur, rdOrte, rd_hWr, rd_hBefore, hAfter, rd_hBytes⟩

/-- **JOINT WITNESS for `schrittW_aus_lesefragment_gruppe`.** Every
    premise holds jointly on concrete values: the two-table declaration
    with a table the witness function writes, a reached one-step run that
    copies 0 over 9 (memory-changing on both sides: source slot `9 → 0`,
    target bytes nine-word to zero-word), the growing eight-flush drain
    at the slot address with a real foreign issue inside it, the committed
    group read of the read slot at its actual value 0, and the inherited
    history over the drain end -- and so do the `SchrittW` transition, the
    write-side value agreement and representation, and the read-side value
    agreement. On top: two distinct trace timestamps on a reached step,
    the pending foreign byte outside the footprint, and the stale-view
    divergence (core 0 canonically reads zero where core 1 forwards
    seven -- the unflushed store is refused a global value).
    Non-degenerate: a written table, a memory-changing source step and a
    memory-changing target drain. -/
theorem schrittW_aus_lesefragment_gruppe_zeuge :
    ∃ (σ' : World rdD) (ρ' : Env rdD []),
      execStmt rdO 0 rdR
        (Stmt.assignSlot (l := true) false () rdI rdE rdHwW rdHLW)
        rdSigma Env.nil = .ok σ' ρ' ∧
      (rdSigma.slots false 0 ()).n = 9 ∧ (σ'.slots false 0 ()).n = 0 ∧
      rdM9.bytes witA ≠ rdM9'.bytes witA ∧
      rdD.schreibt () false = true ∧
      ErbtW (spurStart rdS11) (RufStartW rdMachine) 0 0 (Sum.inl false) witA ∧
      SpurInv (spurStart rdS11) ∧
      rdS4.puffer 1 = [⟨ctF, ctFv⟩] ∧ ctF ∉ Fuss witA ∧
      loadByte rdS4 0 ctF = some (BitVec.ofNat 8 0) ∧
      loadByte rdS4 1 ctF = some ctFv ∧
      (∃ (W' : RufMaschineW rdD) (σm : Gabbro.Grammatik.Speicher rdD)
        (M'' : RufMaschineG rdD)
        (wahl : rdD.Tab ⊕ rdD.Glob → NachrichtW rdD)
        (neu : rdD.Tab ⊕ rdD.Glob → Nat),
        SchrittW rdProg rdO 0 (fun g => nomatch g) (RufStartW rdMachine) 0 W'
          σm M'' wahl neu ∧
        (∃ w, read64 (spurStart rdS11).tso.mem witA = some w ∧
          wortZahl 0 100 w = some rdZero) ∧
        RepSlot false 0 () 0 100 rdHTW witA rdM9' σ' ∧
        wortZahl 0 100 (zahlWort rdZero) = some rdZero) := by
  obtain ⟨σ', ρ', hExec⟩ := rd_hExecFull
  have hAfter : (σ'.slots false 0 ()).n = 0 := by
    cases hExec
    rfl
  have hMain := schrittW_aus_lesefragment_gruppe rdProg rdO 0
    (fun g => nomatch g) false () 0 100 rdHTW 4096 16 0 rd_hOk rdI rdE
    rdMachine 0 rdSigma Env.nil rdHwW rdHLW rdS rdRest rfl rd_hhead rdSL
    rd_hLese 0 rdZero rd_hk rd_hv true () 0 100 rdHTR 0 rdOrte witA rdM9
    rdM9' σ' ρ' hExec rd_hTgt rd_hRd (by decide) (by decide) rd_hwelt rd_hΛ
    (RufStartW rdMachine) rd_hWg 0 (spurStart rdS11) rd_hErbt rd_hInv rdS11
    rd_hnode rdS2 [rdS2, rdS3, rdS4, rdS5, rdS6, rdS7, rdS8, rdS9, rdS10, rdS11]
    rd_hgrp rd_hles rd_spur rd_hend rd_hempty rd_hstoer rdA2 rdZero rd_hRepRead
    rd_hMiss rd_hRdR (by decide) (by decide) (zahlWort rdZero) rd_hWort rd_hv2 0
    rd_hMemR rd_hProjR rd_hTsR rd_hTraegerR
  obtain ⟨W', σm, M'', wahl, neu, hSW, hValW, hRepW, hReadV⟩ := hMain
  exact ⟨σ', ρ', hExec, rd_hBefore, hAfter, rd_hBytes, rd_hWr, rd_hErbt,
    rd_hInv, rdBuf1_4, ctFfresh, rd_stale0, rd_stale1,
    W', σm, M'', wahl, neu, hSW, hValW, hRepW, hReadV⟩

/- CUTS:
    - Proved here: read-case preservation (`hwLade_erhaelt_wf`), the
      committed machine-read value (`hwLade_trifft_speicher`), the
      table-read contribution bound (`beitrag_tabelle_le`), the trace of a
      one-read fragment (`lesespur_assignSlot`), the committed
      read-fragment `SchrittW` (`schrittW_aus_lesefragment_gruppe`), the
      forwarded read-fragment `SchrittW`
      (`schrittW_aus_lesefragment_weiterleitung`, read and drain at
      separate TSO states sharing only the source fragment), the
      stale-view refusals (`stale_kein_globaler_wert`,
      `gruppe_kein_globaler_wert`), and the joint non-degenerate
      witnesses (`schrittW_aus_lesefragment_gruppe_zeuge`,
      `schrittW_aus_lesefragment_weiterleitung_zeuge`,
      `lesespur_assignSlot_zeuge` over the two-table copy run `9 → 0`
      with a growing drain, a real foreign issue and the stale-view
      divergence beside it).
    - NOT proved here, and not claimed:
      - No hardware correspondence beyond self-consistency; no silicon,
        timing, fairness or progress claim.
      - The forwarded witness uses a clock-2 node carrying only the last
        drain flush as a real projected step; the earlier seven flushes
        ride the `DrainSpur` witness, and the full 9-step projected trace
        stays OPEN.
      - The forwarded value link (`hWert`) and the reading W shape
        (timestamp-1 message, view 1) are explicit premises supplied by
        the lowering certificate, never derived here; mixed
        committed/forwarded footprints have no value simulation (tearing
        refusal of §5).
      - No per-access run induction from x86 traces to W runs, no GX
        refinement, no validator soundness (`valX86_sound`); the
        source-to-final-bytes closing theorem stays OPEN.
      - No new executor, no second IR, no source/checker/contract change;
        `TSOZustand`, `RepSlot`, `witA`, `ctF`/`ctFv` and the `witD`
        vocabulary are reused unchanged.
-/

#print axioms hwLade_erhaelt_wf
#print axioms hwLade_trifft_speicher
#print axioms beitrag_tabelle_le
#print axioms lesespur_assignSlot
#print axioms schrittW_aus_lesefragment_gruppe
#print axioms schrittW_aus_lesefragment_weiterleitung
#print axioms stale_kein_globaler_wert
#print axioms gruppe_kein_globaler_wert
#print axioms schrittW_aus_lesefragment_gruppe_zeuge
#print axioms schrittW_aus_lesefragment_weiterleitung_zeuge
#print axioms lesespur_assignSlot_zeuge

end Gabbro.Grammatik.X86
