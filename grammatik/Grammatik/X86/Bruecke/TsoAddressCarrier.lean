/-
  File:      Grammatik/X86/TsoAddressCarrier.lean
  Subject:   x86 address to source carrier mapping for the TSO-to-W bridges.

  Lane 1245 (follow-up of lane 1213, `TsoRmwLink.lean`): the links in
  `CarrierTraceBridge.lean`, `TsoReadBridge.lean` and `TsoRunInduction.lean`
  hold over the GENERIC history shape because no accepted x86-address to
  carrier mapping existed. This module defines that mapping from the
  pipeline's placement layout (`PipelineImage.lean`: `Platz`, `layoutVon`,
  `TabLayout`) to the source carriers (`t`, `k`, `f`) used by the W
  history: the relation `kartiert` (address `a` is the placed address of
  slot `(t, k, f)`), proved injective on admitted placements
  (`kartiert_injektiv`: one address names one slot) with disjoint 8-byte
  footprints for distinct carriers (`kartiert_sep`: same slot or
  `Disjunkt`), and specialises the no-read write bridge
  (`schrittW_aus_gruppen_drain`) to placed addresses, discharging its
  `repOk` premise from the decided placement admission (`platzOkB`).

  Reused, never redefined: `Platz`/`layoutVon`/`sepB`/`sepB_sound`/
  `layoutVon_loc`/`trifft_inv`/`platzOkB` (PipelineImage), `LayoutSep`/
  `repOk_int`/`natAdresse_ohneUmbruch` (Pipeline), `Disjunkt`/
  `disjunkt_von_intervallen` (Speicher), `natAdresse`
  (Regionen), `rep_schritt_bleibt`/`RepSlot`/`zahlWort`/`wortZahl`
  (SourceMemory), `schrittW_aus_gruppen_drain` with its witness vocabulary
  (`witD`, `ctProg`, `ctS*`, ...) (CarrierTraceBridge).

  SCOPE (honest): the mapping covers placed integer slots only (the
  `repOk` fragment); globals, bools, sums, floats and function pointers
  have no address form here. The full per-access target-to-W/GX simulation
  stays OPEN (see CUTS).
-/
import Grammatik.X86.Pipeline.Kern.PipelineImage
import Grammatik.X86.Bruecke.CarrierTraceBridge

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

variable {D : Deklaration}

/-- THE MAPPING: byte address `a` is the placed address of source slot
    `(t, k, f)` under placements `ps` (the pipeline's `layoutVon`). -/
def kartiert (ps : List (PipelineImage.Platz D)) (a : Nat)
    (t : D.Tab) (k : Int) (f : D.Feld t) : Prop :=
  (PipelineImage.layoutVon ps).loc t k f = some a

/-! ## 1. Separation and injectivity on admitted placements -/

/-- **DISJOINT FOOTPRINTS (`kartiert_sep`).** Two placed slots are the
    same slot or have disjoint 8-byte footprints: the decided `sepB`
    gives `LayoutSep` (`sepB_sound`), and the Nat interval disjointness
    becomes `Disjunkt` under the no-wrap bounds (from placement
    admission, see `zugelassen_schranke`). Every premise is used: `hsep`
    for the layout separation, `h1`/`h2` for the two placed slots,
    `w1`/`w2` for the no-wrap side conditions. -/
theorem kartiert_sep (ps : List (PipelineImage.Platz D))
    (hsep : PipelineImage.sepB ps = true)
    (t1 : D.Tab) (k1 : Int) (f1 : D.Feld t1) (a1 : Nat)
    (t2 : D.Tab) (k2 : Int) (f2 : D.Feld t2) (a2 : Nat)
    (h1 : kartiert ps a1 t1 k1 f1)
    (h2 : kartiert ps a2 t2 k2 f2)
    (w1 : a1 + 8 ≤ 2 ^ 64) (w2 : a2 + 8 ≤ 2 ^ 64) :
    (t1 = t2 ∧ k1 = k2 ∧ HEq f1 f2) ∨
      Disjunkt (natAdresse a1) (natAdresse a2) := by
  have hL := PipelineImage.sepB_sound ps hsep
  rcases hL t1 k1 f1 a1 t2 k2 f2 a2 h1 h2 with hEq | hDis
  · exact Or.inl hEq
  · exact Or.inr (by
      apply disjunkt_von_intervallen _ _
        (Pipeline.natAdresse_ohneUmbruch a1 w1)
        (Pipeline.natAdresse_ohneUmbruch a2 w2)
      rw [PipelineImage.natAdresse_toNat_lt a1 (by omega),
        PipelineImage.natAdresse_toNat_lt a2 (by omega)]
      exact hDis)

/-- **INJECTIVITY (`kartiert_injektiv`).** One placed address names one
    source slot: two slots placed at the same address are the same slot.
    The disjoint-footprint alternative of `kartiert_sep` is impossible
    (a footprint always meets itself). Every premise is used: `hsep`
    through the separation, `h1`/`h2` for the two placements, `w` for
    both no-wrap bounds. -/
theorem kartiert_injektiv (ps : List (PipelineImage.Platz D))
    (hsep : PipelineImage.sepB ps = true)
    (t1 : D.Tab) (k1 : Int) (f1 : D.Feld t1)
    (t2 : D.Tab) (k2 : Int) (f2 : D.Feld t2) (a : Nat)
    (h1 : kartiert ps a t1 k1 f1)
    (h2 : kartiert ps a t2 k2 f2)
    (w : a + 8 ≤ 2 ^ 64) :
    t1 = t2 ∧ k1 = k2 ∧ HEq f1 f2 := by
  rcases kartiert_sep ps hsep t1 k1 f1 a t2 k2 f2 a h1 h2 w w with
    hEq | hDis
  · exact hEq
  · exact False.elim (hDis 0 0 (by decide) (by decide) rfl)

/-! ## 2. Admission: placed slots are admitted, bounded slots -/

/-- **ADMISSION FROM THE CHECK (`platzOk_rep`).** A member placement
    that names slot `(t, k, f)` discharges the representation admission
    (`repOk`) for that slot at its placed address, plus the read/write
    permissions the bridges consume. Proved from the decided
    `platzOkB` over the member (`List.all_eq_true`) with the key
    rewritten through `trifft_inv`. Every premise is used: `h` for the
    decided check, `hp` for the membership, `htr` for the key rewrite
    (all three key components via `subst`). -/
theorem platzOk_rep {D : Deklaration} (m : Speicher)
    (ps : List (PipelineImage.Platz D))
    (h : PipelineImage.platzOkB m ps = true)
    (p : PipelineImage.Platz D) (hp : p ∈ ps)
    (t : D.Tab) (k : Int) (f : D.Feld t)
    (htr : p.trifft t k f = true) :
    repOk (D.typ t f) p.a 8 0 = true ∧
      lesbar8 m (natAdresse p.a) = true ∧
      schreibbar8 m (natAdresse p.a) = true := by
  obtain ⟨pt, pk, pf, pa⟩ := p
  have h1 := List.all_eq_true.mp h ⟨pt, pk, pf, pa⟩ hp
  simp only [Bool.and_eq_true] at h1
  obtain ⟨⟨hre, hles⟩, hschr⟩ := h1
  obtain ⟨ht, hk, hf⟩ := PipelineImage.trifft_inv ⟨pt, pk, pf, pa⟩ t k f htr
  simp only at ht hk hf ⊢
  subst ht hk
  simp only [cast_eq] at hf
  subst hf
  exact ⟨hre, hles, hschr⟩

/-- **ADMITTED PLACEMENTS DO NOT WRAP (`zugelassen_schranke`).** A slot
    the placement layout maps to `a` satisfies `a + 8 ≤ 2 ^ 64`: the
    placed address comes from a member placement (`layoutVon_loc`),
    whose decided admission carries the bound (`repOk_int` over
    `platzOk_rep`). Feeds the no-wrap premises of `kartiert_sep` from
    the checks instead of an assumed bound. Every premise is used. -/
theorem zugelassen_schranke {D : Deklaration} (m : Speicher)
    (ps : List (PipelineImage.Platz D))
    (h : PipelineImage.platzOkB m ps = true)
    (t : D.Tab) (k : Int) (f : D.Feld t) (a : Nat)
    (hloc : (PipelineImage.layoutVon ps).loc t k f = some a) :
    a + 8 ≤ 2 ^ 64 := by
  obtain ⟨p, hmem, htr, rfl⟩ := PipelineImage.layoutVon_loc ps t k f a hloc
  obtain ⟨lo, hi, -, -, -, hbound⟩ :=
    Pipeline.repOk_int (D.typ t f) p.a
      (platzOk_rep m ps h p hmem t k f htr).1
  exact hbound

/-- **FIRST HIT IS THE MAPPING (`kartiert_von_erst`).** If `p` is the
    first placement naming `(t, k, f)`, the layout maps the slot to
    `p.a` -- and `p` indeed names the slot (from the `find?` equation,
    never assumed). Both conjuncts are derived from `hfirst`. -/
theorem kartiert_von_erst {D : Deklaration}
    (ps : List (PipelineImage.Platz D))
    (t : D.Tab) (k : Int) (f : D.Feld t)
    (p : PipelineImage.Platz D)
    (hfirst : ps.find? (fun q => q.trifft t k f) = some p) :
    kartiert ps p.a t k f ∧ p.trifft t k f = true := by
  refine ⟨?_, List.find?_some (p := fun q : PipelineImage.Platz D => q.trifft t k f) hfirst⟩
  unfold kartiert PipelineImage.layoutVon
  simp only [hfirst, Option.map_some]

/-! ## 3. Planted refusals: what is NOT admitted -/

/-- **EMPTY PLACEMENT MAPS NOTHING:** over no placements no slot has an
    address. An unplaced slot never enters a bridge. -/
theorem leer_ohne_kartierung {D : Deklaration}
    (t : D.Tab) (k : Int) (f : D.Feld t) (a : Nat) :
    ¬ kartiert ([] : List (PipelineImage.Platz D)) a t k f := by
  unfold kartiert PipelineImage.layoutVon
  simp only [List.find?_nil, Option.map_none]
  exact Ne.symm (Option.some_ne_none a)

/-- **OVERLAP REFUSAL:** two placements 4096 and 4100 (four bytes
    apart, eight-byte footprints) are refused by the decided `sepB` --
    on the witness declaration with two distinct rows. Admitted
    placements never overlap; overlapping candidates never reach the
    injectivity theorems. -/
theorem platz_ueberlapp_verweigert :
    PipelineImage.sepB ([⟨(), 0, (), 4096⟩, ⟨(), 1, (), 4100⟩] :
      List (PipelineImage.Platz witD)) = false := by
  decide

/-! ## 4. Witness placement: one placed table that a function writes -/

/-- Witness placement: row 0 of the witness table at byte address
    4096 (the witness target address `witA`). -/
def psWit : List (PipelineImage.Platz witD) :=
  [⟨(), 0, (), 4096⟩]

/-- The witness placement is admitted by the decided separation. -/
theorem psWit_sep : PipelineImage.sepB psWit = true := by
  decide

/-- The witness placement is admitted by the decided placement check
    over the witness memory. -/
theorem psWit_platz : PipelineImage.platzOkB witM psWit = true := by
  decide

/-- The witness member names the witness slot. -/
theorem psWit_trifft :
    (⟨(), 0, (), 4096⟩ : PipelineImage.Platz witD).trifft () 0 () = true := by
  decide

/-- The witness member is the placement list's member. -/
theorem psWit_mem :
    (⟨(), 0, (), 4096⟩ : PipelineImage.Platz witD) ∈ psWit := by
  simp [psWit]

/-- The witness layout maps the written slot to 4096. -/
theorem psWit_loc :
    (PipelineImage.layoutVon psWit).loc () 0 () = some 4096 := by
  decide

/-- The witness target address is the placed address: `witA` is
    definitionally `natAdresse 4096`. -/
theorem witA_ist_platziert : witA = natAdresse 4096 := rfl

/-! ## 5. Bridge specialisation: the write bridge at placed addresses -/

/-- **WRITE BRIDGE AT A PLACED ADDRESS
    (`schrittW_aus_gruppen_drain_platziert`).** The accepted no-read
    write bridge (`schrittW_aus_gruppen_drain`: a fragment write whose
    grouped TSO drain installs the source-written word yields an actual
    typed-carrier `SchrittW`) specialised to the placement mapping: the
    target address is the placed address `natAdresse p.a` of a member
    placement naming the written slot, and the bridge's `repOk`
    premise is DISCHARGED from the decided placement admission
    (`platzOk_rep` over `hplatz`/`hp`/`htr`) instead of assumed. Every
    premise is used: the placement premises through the discharged
    admission, every bridge premise through the applied theorem. -/
theorem schrittW_aus_gruppen_drain_platziert {D : Deklaration} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)}
    (ps : List (PipelineImage.Platz D)) (m0 : Speicher)
    (hplatz : PipelineImage.platzOkB m0 ps = true)
    (p : PipelineImage.Platz D) (hp : p ∈ ps)
    (P : Programm D) (O : Orakel D) (passes : Nat)
    (ord : D.Glob → Speichermodell.Ordnung)
    (t : D.Tab) (f : D.Feld t)
    (lo hi : Int) (hT : D.typ t f = .int lo hi)
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
    (htr : p.trifft t k f = true)
    (hOrte : i.orte ++ e.orte = [])
    (m m' : Speicher)
    (σ' : World D) (ρ' : Env D Γ)
    (hExec : execStmt O passes keinRuf (Stmt.assignSlot (l := l) t f i e hw hL) σ ρ =
      .ok σ' ρ')
    (hTgt : write64 m (natAdresse p.a) (zahlWort v) = some m')
    (hRd : lesbar8 m (natAdresse p.a) = true)
    (hLo : 0 ≤ lo) (hHi : hi < 2 ^ 64)
    (hwelt : M.weltVon u = σ)
    (hΛ : HeldIn Λ (offen (M.faeden u).spur))
    (W : RufMaschineW D) (hWg : W.g = M)
    (co : Nat) (nN : SpurKnoten)
    (hErbt : ErbtW nN W u co (Sum.inl t) (natAdresse p.a))
    (hInvN : SpurInv nN)
    (sN : TSOZustand) (hnode : nN.tso = sN)
    (s2 : TSOZustand) (tlist : List TSOZustand)
    (hgrp : WortGruppe s2 co (natAdresse p.a) (zahlWort v))
    (hles : lesbar8 s2.mem (natAdresse p.a) = true)
    (hspur : DrainSpur co s2 sN tlist) (hend : sN ∈ tlist)
    (hleer : sN.puffer co = []) (hstoer : ∀ x ∈ tlist, FremdFrei x co (natAdresse p.a)) :
    ∃ (W' : RufMaschineW D) (σm : Gabbro.Grammatik.Speicher D)
      (M'' : RufMaschineG D)
      (wahl : D.Tab ⊕ D.Glob → NachrichtW D) (neu : D.Tab ⊕ D.Glob → Nat),
      SchrittW P O passes ord W u W' σm M'' wahl neu ∧
      (∃ w, read64 nN.tso.mem (natAdresse p.a) = some w ∧ wortZahl lo hi w = some v) ∧
      RepSlot t k f lo hi hT (natAdresse p.a) m' σ' := by
  obtain ⟨hok, -, -⟩ := platzOk_rep m0 ps hplatz p hp t k f htr
  exact schrittW_aus_gruppen_drain P O passes ord t f lo hi hT p.a 8 0 hok
    i e M u σ ρ hw hL s rest hs hhead σL hLese k v hk hv hOrte
    (natAdresse p.a) m m' σ' ρ' hExec hTgt hRd hLo hHi hwelt hΛ W hWg
    co nN hErbt hInvN sN hnode s2 tlist hgrp hles hspur hend hleer hstoer

/-! ## 6. Joint witness: placed write plus growing TSO drain -/

/-- **JOINT WITNESS for `schrittW_aus_gruppen_drain_platziert`.** Every
    premise holds jointly on concrete values: the witness declaration
    `witD` with one table that the witness function writes (`ctHw`), a
    reached one-step run that changes the source slot `0 → 42` and the
    mapped target bytes at the placed address 4096, the admitted
    witness placement (`sepB`/`platzOkB` decided, layout maps the slot
    to 4096), the growing eight-flush drain installing the written
    word, the inherited history over the drain end -- and so do the
    `SchrittW` transition, the value agreement and the representation
    at the placed address. Non-degenerate: a written table, a
    memory-changing source step and target drain. -/
theorem schrittW_aus_gruppen_drain_platziert_zeuge :
    ∃ (σ' : World witD) (ρ' : Env witD []),
      execStmt witO 0 keinRuf
        (Stmt.assignSlot (l := true) () () witI witE ctHw witHL)
        witSigma Env.nil = .ok σ' ρ' ∧
      (witSigma.slots () 0 ()).n = 0 ∧ (σ'.slots () 0 ()).n = 42 ∧
      (vertragVon witD ()).schreibt () = true ∧
      witM.bytes (natAdresse 4096) ≠ witM'.bytes (natAdresse 4096) ∧
      PipelineImage.sepB psWit = true ∧
      PipelineImage.platzOkB witM psWit = true ∧
      kartiert psWit 4096 () 0 () ∧
      (∃ (W' : RufMaschineW witD) (σm : Gabbro.Grammatik.Speicher witD)
        (M'' : RufMaschineG witD)
        (wahl : witD.Tab ⊕ witD.Glob → NachrichtW witD)
        (neu : witD.Tab ⊕ witD.Glob → Nat),
        SchrittW ctProg witO 0 (fun g => nomatch g) (RufStartW ctM) 0 W'
          σm M'' wahl neu ∧
        (∃ w, read64 (spurStart ctS11).tso.mem (natAdresse 4096) = some w ∧
          wortZahl 0 100 w = some witVal) ∧
        RepSlot () 0 () 0 100 witHT (natAdresse 4096) witM' σ') := by
  have hExecFull : ∃ σ' ρ', execStmt witO 0 keinRuf
      (Stmt.assignSlot (l := true) () () witI witE ctHw witHL)
      witSigma Env.nil = .ok σ' ρ' := by
    simp only [execStmt]
    exact ⟨_, _, rfl⟩
  obtain ⟨σ', ρ', hExec⟩ := hExecFull
  have hBefore : (witSigma.slots () 0 ()).n = 0 := rfl
  have hAfter : (σ'.slots () 0 ()).n = 42 := by
    cases hExec
    rfl
  have hk : (eval witSL witI witSL Env.nil).n = 0 := rfl
  have hv : (cast (congrArg (Wert witD) witHT)
      (eval witSL witE witSL Env.nil) : Wert witD (.int 0 100)) =
      witVal := rfl
  have hTgt : write64 witM (natAdresse 4096) (zahlWort witVal) =
      some witM' := by
    simp only [write64, witM']
    rw [if_pos (by decide : schreibbar8 witM (natAdresse 4096) = true)]
    rw [witA_ist_platziert]
  have hRd : lesbar8 witM (natAdresse 4096) = true := by decide
  have hByte : writeBytes witM (natAdresse 4096) (zahlWort witVal)
      (natAdresse 4096) = wortByte (zahlWort witVal) 0 := by
    have h := writeBytesN_hit witM (natAdresse 4096) (zahlWort witVal) 8 0
      (by decide) (by decide)
    rw [addrOff_null] at h
    unfold writeBytes
    exact h
  have hBytes : witM.bytes (natAdresse 4096) ≠
      witM'.bytes (natAdresse 4096) := by
    show BitVec.ofNat 8 0 ≠
      writeBytes witM (natAdresse 4096) (zahlWort witVal) (natAdresse 4096)
    rw [hByte]
    decide
  have hMain := schrittW_aus_gruppen_drain_platziert
    psWit witM psWit_platz (⟨(), 0, (), 4096⟩ : PipelineImage.Platz witD)
    psWit_mem ctProg witO 0 (fun g => nomatch g) () () 0 100 witHT
    witI witE ctM 0 witSigma Env.nil ctHw witHL ctS ctRest rfl ct_hhead
    witSL rfl 0 witVal hk hv psWit_trifft rfl witM witM' σ' ρ' hExec hTgt
    hRd (by decide) (by decide) ct_hwelt ct_hΛ (RufStartW ctM) ct_hWg 0
    (spurStart ctS11) (erbtW_start ctS11 ctM 0 0 (Sum.inl ()) (natAdresse 4096))
    (spurStart_inv ctS11) ctS11 rfl ctS2
    [ctS2, ctS3, ctS4, ctS5, ctS6, ctS7, ctS8, ctS9, ctS10, ctS11]
    ct_hgrp ct_hles ct_spur ct_hend ct_hempty ct_hstoer
  obtain ⟨W', σm, M'', wahl, neu, hSW, hVal, hRep⟩ := hMain
  exact ⟨σ', ρ', hExec, hBefore, hAfter, ctHw, hBytes, psWit_sep,
    psWit_platz, psWit_loc, W', σm, M'', wahl, neu, hSW, hVal, hRep⟩

/- CUTS:
     Proved here: the x86-address to source-carrier mapping over the
     pipeline placement layout -- the relation `kartiert` (address `a`
     is the placed address of slot `(t, k, f)`); separation
     (`kartiert_sep`: same slot or disjoint 8-byte `Disjunkt`
     footprints, from the decided `sepB` via `sepB_sound` plus the
     no-wrap bounds); injectivity on admitted placements
     (`kartiert_injektiv`: one address names one slot); admission from
     the decided check (`platzOk_rep`: `repOk` plus read/write
     permissions for a member placement naming the slot);
     the no-wrap bound from admission (`zugelassen_schranke`);
     the first-hit mapping (`kartiert_von_erst`); the write-bridge
     specialisation (`schrittW_aus_gruppen_drain_platziert`: the
     accepted no-read `SchrittW` bridge at `natAdresse p.a` with its
     `repOk` premise discharged from `platzOkB`); planted refusals
     beside the run (`leer_ohne_kartierung`,
     `platz_ueberlapp_verweigert`); the joint non-degenerate witness
     (`schrittW_aus_gruppen_drain_platziert_zeuge`:
     one table the witness function writes, source slot `0 -> 42`
     with observably changed target bytes at placed address 4096,
     decided admission and layout facts, `SchrittW` with value
     agreement and representation).
     Silicon provenance: none new -- this lane adds no hardware claim;
     all byte facts reuse the accepted `Speicher`/`SourceMemory`/
     `PipelineImage` definitions.
     NOT proved here, and not claimed:
     - No per-access target-to-W/GX simulation: the mapping specialises
       ONE write bridge (`schrittW_aus_gruppen_drain`, no-read
       fragments); the committed-read bridge
       (`schrittW_aus_lesefragment_gruppe`), the forwarded-read bridge
       (`schrittW_aus_lesefragment_weiterleitung`) and run induction
       (`brueckenLauf_erreichbar`) are NOT specialised to placed
       addresses here -- each needs its own `repOk`-from-`platzOkB`
       discharge plus its read-side premises. FINDING for the consumer
       lanes (see report).
     - No LOCK/RMW leg: the `rmw` field stays discharged by refuting
       the exchange head at `assignSlot` (inherited); `TsoRmwLink`'s
       timestamp/value link is over generic history addresses, still
       not over placed carriers.
     - No globals: the mapping covers table slots `(t, k, f)` only;
       `D.Glob` carriers (and bools, sums, floats, function pointers)
       have no address form here (`repOk` refuses them).
     - No hardware correspondence beyond self-consistency; no source,
       checker, contract, budget, duty or goal change: nothing here
       speaks about `Vertrag` beyond the reused bridge premises.
-/

#print axioms kartiert
#print axioms kartiert_sep
#print axioms kartiert_injektiv
#print axioms platzOk_rep
#print axioms zugelassen_schranke
#print axioms kartiert_von_erst
#print axioms leer_ohne_kartierung
#print axioms platz_ueberlapp_verweigert
#print axioms psWit
#print axioms psWit_sep
#print axioms psWit_platz
#print axioms psWit_trifft
#print axioms psWit_mem
#print axioms psWit_loc
#print axioms witA_ist_platziert
#print axioms schrittW_aus_gruppen_drain_platziert
#print axioms schrittW_aus_gruppen_drain_platziert_zeuge

end Gabbro.Grammatik.X86
