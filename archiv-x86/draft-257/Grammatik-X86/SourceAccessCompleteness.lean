/-
  File:      Grammatik/X86/SourceAccessCompleteness.lean
  Subject:   Source access completeness for the admitted lowering fragment (lane 630).

  G5 of CONCURRENCY-CLOSURE-PLAN.md: the source access enumeration of one
  admitted table-write step (`Stmt.assignSlot` on an `.int` slot with
  `repOk = true`, executed through the actual `execStmt`), proved complete
  against the actual G access predicates (`LiestG`/`SchreibG`/`ZugriffG`
  over `zugriffe`), and matched to the realised target footprint
  (`Zugriffe.zugriff` of an actual successful `schritt`). Unsupported rules
  (`regelOk`: only `assignSlot`) and profiles (`repOk`, globals) are
  refused by decision. Full source-to-final-bytes remains OPEN.
-/
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.RennfreiG
import Grammatik.RennfreiVoll
import Grammatik.ZielOrt
import Grammatik.RufMaschineG
import Grammatik.X86.SourceMemory
import Grammatik.X86.Zugriffe
import Grammatik.X86.AccessExecution
import Grammatik.X86.LockedOps
import Grammatik.X86.TableLayout
import Grammatik.X86.BridgeRead

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The source access enumeration of one admitted table-write step: the
    write of `t` (newest first, as the trace prepends it) plus one read
    per carrier of the actual read footprint `orte`. Computed from actual
    source data (`t`, `i.orte ++ e.orte`), never a parallel machine. -/
def fragmentListe {D : Deklaration} (t : D.Tab)
    (orte : List (D.Tab ⊕ D.Glob)) : List ((D.Tab ⊕ D.Glob) × Bool) :=
  (.inl t, true) :: orte.map (·, false)

/-- The enumeration really lists the write. -/
theorem fragmentListe_schreibt {D : Deklaration} (t : D.Tab)
    (orte : List (D.Tab ⊕ D.Glob)) :
    ((.inl t, true) : (D.Tab ⊕ D.Glob) × Bool) ∈ fragmentListe t orte := by
  unfold fragmentListe
  exact List.mem_cons_self

/-! ## 1. Syntax-free helpers: read-event mapping, delta take, inversion. -/

/-- Filtering the recorded read events of `World.lese` by `zugriffVon`
    yields exactly one unread-flagged entry per carrier of `os`. Every
    premise is used: `Λ`/`h` name the event payloads, `os` is inducted. -/
theorem filterMap_leseEv {D : Deklaration} (Λ : List (Res D))
    (h : List D.Lock) (os : List (D.Tab ⊕ D.Glob)) :
    ((os.map fun o => match o with
      | .inl t => Ereignis.zugriff t false Λ h
      | .inr g => Ereignis.gzugriff g false Λ h)).filterMap zugriffVon =
    os.map (·, false) := by
  induction os with
  | nil => rfl
  | cons o _ ih =>
    cases o with
    | inl t =>
      simp only [List.map_cons, List.filterMap_cons, zugriffVon, ih]
    | inr g =>
      simp only [List.map_cons, List.filterMap_cons, zugriffVon, ih]

/-- Taking the trace delta back off a prepended trace recovers the new
    events. Used for both the source-world delta and the G thread delta. -/
theorem take_neuAppend {α : Type} (neu s : List α) :
    ((neu ++ s).take ((neu ++ s).length - s.length)) = neu := by
  rw [List.length_append, Nat.add_sub_cancel]
  exact List.take_left

/-- Inversion of the enumeration: every listed entry is either the write
    of `t` or a read of a carrier of `os`. Every premise is used: `hm`
    is the membership inverted here. -/
theorem fragmentListe_invert {D : Deklaration} (t : D.Tab)
    (os : List (D.Tab ⊕ D.Glob)) (c : D.Tab ⊕ D.Glob) (w : Bool)
    (hm : (c, w) ∈ fragmentListe t os) :
    (w = true ∧ c = .inl t) ∨ (w = false ∧ c ∈ os) := by
  unfold fragmentListe at hm
  simp only [List.mem_cons, List.mem_map, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨o, ho, rfl, h⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨h.symm, ho⟩

/-- A recorded write is an access: `SchreibG` implies `ZugriffG` through
    the recorded-write disjunct (the changed-memory disjunct is shared). -/
theorem schreibG_zugriff {D : Deklaration} {M M' : RufMaschineG D}
    {f : Faden} {c : D.Tab ⊕ D.Glob} (h : SchreibG M M' f c) :
    ZugriffG M M' f c := by
  unfold SchreibG ZugriffG at *
  rcases h with h | h
  · exact Or.inl ⟨true, h⟩
  · exact Or.inr h

/-! ## 2. Source delta: the actual execStmt step records exactly the enumeration. -/

/-- An actual `Stmt.assignSlot` step through the real `execStmt` records
    exactly the enumeration: the write event of `t` plus one read event
    per carrier of `i.orte ++ e.orte`. The value/index evaluations never
    enter the trace, so no `hk`/`hv` premises are needed. Every premise is
    used: `O`/`passes`/`R`/`hw`/`hL` through the executed statement in
    `hExec`, the worlds through the delta. -/
theorem fragmentDelta_voll {D : Deklaration} {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t)))
    (e : Expr D Γ Λ (D.typ t f))
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (σ : World D) (ρ : Env D Γ)
    (σ' : World D) (ρ' : Env D Γ)
    (hExec : execStmt O passes R (Stmt.assignSlot (l := l) t f i e hw hL) σ ρ =
      .ok σ' ρ') :
    ((σ'.spur.take (σ'.spur.length - σ.spur.length)).filterMap zugriffVon) =
      fragmentListe t (i.orte ++ e.orte) := by
  have hU : execStmt O passes R (Stmt.assignSlot (l := l) t f i e hw hL) σ ρ =
      Ausgang.ok
        ((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
          (eval (σ.lese Λ (i.orte ++ e.orte)) i
            (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
          (eval (σ.lese Λ (i.orte ++ e.orte)) e
            (σ.lese Λ (i.orte ++ e.orte)) ρ)) ρ := by
    simp only [execStmt]
  rw [hU] at hExec
  cases hExec
  generalize hRdef : ((i.orte ++ e.orte).map (fun o => match o with
    | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
    | .inr g => Ereignis.gzugriff g false Λ σ.haelt) : List (Ereignis D)) = R
  have hspur : ((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
        (eval (σ.lese Λ (i.orte ++ e.orte)) i
          (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
        (eval (σ.lese Λ (i.orte ++ e.orte)) e
          (σ.lese Λ (i.orte ++ e.orte)) ρ)).spur =
      [Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt] ++ R ++
        σ.spur := by
    rw [← hRdef]
    rfl
  have hflt : List.filterMap zugriffVon R =
      (i.orte ++ e.orte).map (·, false) := by
    rw [← hRdef]
    exact filterMap_leseEv _ _ _
  have hspurL : ((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
        (eval (σ.lese Λ (i.orte ++ e.orte)) i
          (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
        (eval (σ.lese Λ (i.orte ++ e.orte)) e
          (σ.lese Λ (i.orte ++ e.orte)) ρ)).spur =
      (([Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt] ++ R) ++
        σ.spur) :=
    hspur.trans (List.append_assoc
      [Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt]
      R σ.spur).symm
  rw [hspurL, take_neuAppend]
  simp only [fragmentListe, List.filterMap_cons, zugriffVon, hflt,
    List.cons_append, List.nil_append]

/-- JOINT WITNESS for `fragmentDelta_voll`: every premise holds jointly
    on the witness declaration — one table that the witness function
    writes, a reached one-step run changing the source slot `0 → 42` and
    the mapped target bytes — and so does the conclusion. -/
theorem fragmentDelta_voll_zeuge :
    ∃ (σ' : World witD) (ρ' : Env witD []) (m' : Speicher),
      execStmt witO 0 witR
        (Stmt.assignSlot (l := false) () () witI witE witHw witHL)
        witSigma Env.nil = .ok σ' ρ' ∧
      ((σ'.spur.take (σ'.spur.length - witSigma.spur.length)).filterMap
        zugriffVon) =
        fragmentListe () (witI.orte ++ witE.orte) ∧
      ((.inl (), true) : (witD.Tab ⊕ witD.Glob) × Bool) ∈
        fragmentListe () (witI.orte ++ witE.orte) ∧
      witD.schreibt () () = true ∧
      (witSigma.slots () 0 ()).n = 0 ∧
      (σ'.slots () 0 ()).n = 42 ∧
      witM.bytes witA ≠ m'.bytes witA := by
  obtain ⟨σ', ρ', m', hOk, hWr, hk, hv, hExec, hTgt, hRd, hRep, hRt,
    hBefore, hAfter, hBytes⟩ := rep_schritt_bleibt_zeuge
  exact ⟨σ', ρ', m', hExec,
    fragmentDelta_voll witO 0 witR () () witI witE witHw witHL
      witSigma Env.nil σ' ρ' hExec,
    fragmentListe_schreibt (D := witD) () (witI.orte ++ witE.orte),
    hWr, hBefore, hAfter, hBytes⟩

#print axioms fragmentDelta_voll
#print axioms fragmentDelta_voll_zeuge

/-! ## 3. G completeness: every carrier access of the fragment step is listed. -/

/-- G-level completeness for the admitted fragment: for a fragment-shaped
    source step (actual `Stmt.assignSlot` through `execStmt`) whose worlds
    line up with the G thread endpoints and memories, the G access list
    IS the enumeration; the write is recorded; every read is a footprint
    carrier; every access is the written table or a footprint carrier; and
    only the written table is ever written (slot ownership). The
    changed-memory disjunct of `ZugriffG`/`SchreibG` is discharged for
    every other carrier by the actual disjoint-slot frame: one slot write
    leaves every other carrier alone (`schreibSlot_fremd_tab`, globs by
    construction). Every premise is used: the source premises through the
    executed step and the frame, the machine premises through the access
    list and the memory links. -/
theorem blattFragment_voll {D : Deklaration} {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t)))
    (e : Expr D Γ Λ (D.typ t f))
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (σ : World D) (ρ : Env D Γ)
    (σ' : World D) (ρ' : Env D Γ)
    (hExec : execStmt O passes R (Stmt.assignSlot (l := l) t f i e hw hL) σ ρ =
      .ok σ' ρ')
    (M M' : RufMaschineG D) (u : Faden)
    (hM : (M.faeden u).spur = σ.spur)
    (hM' : (M'.faeden u).spur = σ'.spur)
    (hSpeicher : M.speicher = σ.speicher)
    (hSpeicher' : M'.speicher = σ'.speicher) :
    zugriffe M M' u = fragmentListe t (i.orte ++ e.orte) ∧
      SchreibG M M' u (.inl t) ∧
      (∀ c, LiestG M M' u c → c ∈ i.orte ++ e.orte) ∧
      (∀ c, ZugriffG M M' u c → c = .inl t ∨ c ∈ i.orte ++ e.orte) ∧
      (∀ c, SchreibG M M' u c → c = .inl t) := by
  have hEq : zugriffe M M' u = fragmentListe t (i.orte ++ e.orte) := by
    unfold zugriffe
    rw [hM, hM']
    exact fragmentDelta_voll O passes R t f i e hw hL σ ρ σ' ρ' hExec
  have hTGstab : ∀ c : D.Tab ⊕ D.Glob, c ≠ .inl t →
      TraegerGleich M'.speicher M.speicher c := by
    intro c hne
    rw [hSpeicher, hSpeicher']
    have hU : execStmt O passes R (Stmt.assignSlot (l := l) t f i e hw hL) σ ρ =
        Ausgang.ok
          ((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
            (eval (σ.lese Λ (i.orte ++ e.orte)) i
              (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
            (eval (σ.lese Λ (i.orte ++ e.orte)) e
              (σ.lese Λ (i.orte ++ e.orte)) ρ)) ρ := by
      simp only [execStmt]
    rw [hU] at hExec
    cases hExec
    cases c with
    | inl t2 =>
      have ht : t2 ≠ t := fun h => hne (congrArg Sum.inl h)
      show ((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ _ f _).speicher.slots
        t2 = σ.speicher.slots t2
      funext k2 f2
      show ((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ _ f _).slots t2 k2
        f2 = σ.slots t2 k2 f2
      exact schreibSlot_fremd_tab _ t Λ _ f _ t2 k2 f2 ht
    | inr g =>
      show ((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ _ f _).speicher.globs
        g = σ.speicher.globs g
      rfl
  have hSchreib : SchreibG M M' u (.inl t) := by
    unfold SchreibG
    rw [hEq]
    exact Or.inl (fragmentListe_schreibt t _)
  have hLiest : ∀ c, LiestG M M' u c → c ∈ i.orte ++ e.orte := by
    intro c hc
    unfold LiestG at hc
    rw [hEq] at hc
    have hinv := fragmentListe_invert t (i.orte ++ e.orte) c false hc
    rcases hinv with ⟨hcon, -⟩ | ⟨-, ho⟩
    · exact absurd hcon (by decide)
    · exact ho
  have hZugriff : ∀ c, ZugriffG M M' u c → c = .inl t ∨ c ∈ i.orte ++ e.orte := by
    intro c hc
    unfold ZugriffG at hc
    rcases hc with ⟨w, hw⟩ | hTG
    · rw [hEq] at hw
      have hinv := fragmentListe_invert t (i.orte ++ e.orte) c w hw
      rcases hinv with ⟨rfl, hct⟩ | ⟨rfl, ho⟩
      · exact Or.inl hct
      · exact Or.inr ho
    · by_cases hct : c = .inl t
      · exact Or.inl hct
      · exact absurd (hTGstab c hct) hTG
  refine ⟨hEq, hSchreib, hLiest, hZugriff, ?_⟩
  intro c hc
  unfold SchreibG at hc
  rcases hc with hw | hTG
  · rw [hEq] at hw
    have hinv := fragmentListe_invert t (i.orte ++ e.orte) c true hw
    rcases hinv with ⟨-, hct⟩ | ⟨hcon, -⟩
    · exact hct
    · exact absurd hcon (by decide)
  · by_cases hct : c = .inl t
    · exact hct
    · exact absurd (hTGstab c hct) hTG

#print axioms blattFragment_voll

/-- JOINT WITNESS for `blattFragment_voll`: all machine and source
    premises hold jointly on the witness declaration and the reached
    two-state G frame over it — one table that the witness function
    writes, a reached step changing the source slot `0 → 42` — and so do
    the enumeration, the recorded write and the table-writer fact. -/
theorem blattFragment_voll_zeuge :
    ∃ (M M' : RufMaschineG witD) (u : Faden) (σ' : World witD)
      (ρ' : Env witD []),
      (M.faeden u).spur = witSigma.spur ∧
      (M'.faeden u).spur = σ'.spur ∧
      M.speicher = witSigma.speicher ∧
      M'.speicher = σ'.speicher ∧
      execStmt witO 0 witR
        (Stmt.assignSlot (l := false) () () witI witE witHw witHL)
        witSigma Env.nil = .ok σ' ρ' ∧
      zugriffe M M' u = fragmentListe () (witI.orte ++ witE.orte) ∧
      SchreibG M M' u (.inl ()) ∧
      witD.schreibt () () = true ∧
      (witSigma.slots () 0 ()).n = 0 ∧
      (σ'.slots () 0 ()).n = 42 := by
  have hExecFull : ∃ σ' ρ', execStmt witO 0 witR
      (Stmt.assignSlot (l := false) () () witI witE witHw witHL)
      witSigma Env.nil = .ok σ' ρ' := by
    simp only [execStmt]
    exact ⟨_, _, rfl⟩
  obtain ⟨σ', ρ', hExec⟩ := hExecFull
  have hM : (brueckenG.faeden 0).spur = witSigma.spur := rfl
  have hS : (brueckenG : RufMaschineG witD).speicher = witSigma.speicher := rfl
  have hMain := blattFragment_voll witO 0 witR () () witI witE witHw witHL
    witSigma Env.nil σ' ρ' hExec brueckenG
    ⟨σ'.speicher, fun _ => ⟨[], brueckenRahmen, σ'.spur, []⟩,
      brueckenG.lauf, brueckenG.start⟩
    0 hM rfl hS rfl
  have hBefore : (witSigma.slots () 0 ()).n = 0 := rfl
  have hAfter : (σ'.slots () 0 ()).n = 42 := by
    cases hExec
    rfl
  exact ⟨brueckenG,
    ⟨σ'.speicher, fun _ => ⟨[], brueckenRahmen, σ'.spur, []⟩,
      brueckenG.lauf, brueckenG.start⟩,
    0, σ', ρ', hM, rfl, hS, rfl, hExec, hMain.1,
    hMain.2.1, rfl, hBefore, hAfter⟩

#print axioms blattFragment_voll_zeuge

/-! ## 4. Target match: the admitted slot is one realised 8-byte footprint. -/

/-- The admitted source write lands on exactly one realised target
    footprint: for a guarded source step (admitted profile, evaluated
    index/value, matching target word write) together with a realised
    `store64` step whose effective address and source register match the
    slot address and value, the extracted write footprint is the 8-byte
    `Fuss` of the slot, eight bytes long, carrying the source value, which
    parses back. This consumes (not restates) `rep_schritt_bleibt` for
    the source/target value link and `realisiert_store64_fuss` for the
    realised footprint; the new connection is `hAddr`/`hReg`/`hSlot`.
    Every premise is used. -/
theorem fragmentStore_passt {D : Deklaration} {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (t : D.Tab) (f : D.Feld t)
    (lo hi : Int) (hT : D.typ t f = .int lo hi)
    (base len off : Nat)
    (hOk : repOk (D.typ t f) base len off = true)
    (i : Expr D Γ Λ (.index (D.count t)))
    (e : Expr D Γ Λ (D.typ t f))
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (σ : World D) (ρ : Env D Γ)
    (σL : World D) (hLese : σL = σ.lese Λ (i.orte ++ e.orte))
    (k : Int) (v : Zahl lo hi)
    (hk : (eval σL i σL ρ).n = k)
    (hv : (cast (congrArg (Wert D) hT) (eval σL e σL ρ) :
      Wert D (.int lo hi)) = v)
    (a : Adresse) (m m' : Speicher)
    (σ' : World D) (ρ' : Env D Γ)
    (hExec : execStmt O passes R (Stmt.assignSlot (l := l) t f i e hw hL) σ ρ =
      .ok σ' ρ')
    (hTgt : write64 m a (zahlWort v) = some m')
    (hRd : lesbar8 m a = true)
    (dd : Decodiert) (s s' : Zustand)
    (baseR src : Register) (disp : BitVec 32)
    (hok : laengeOk dd.laenge = true)
    (hbef : dd.befehl = .store64 baseR src disp)
    (hstep : schritt dd s = some s')
    (hAddr : effAddr s baseR disp = slotAddr base off)
    (hSlot : a = slotAddr base off)
    (hReg : s.register src = zahlWort v) :
    (zugriff dd s).schreiben = Fuss (slotAddr base off) ∧
      (zugriff dd s).schreiben.length = 8 ∧
      (zugriff dd s).speicherWert = some (zahlWort v) ∧
      (∃ w, read64 m' (slotAddr base off) = some w ∧
        wortZahl lo hi w = some v) := by
  have hMain2 := (rep_schritt_bleibt O passes R t f lo hi hT base len off hOk
    i e hw hL σ ρ σL hLese k v hk hv a m m' σ' ρ' hExec hTgt hRd).2
  have hFuss := realisiert_store64_fuss dd s s' baseR src disp hok hbef hstep
  have hAcht := zugriff_store64_acht s baseR src disp dd hbef
  rw [hAddr] at hFuss
  rw [hSlot] at hMain2
  exact ⟨hFuss.2.1, hAcht, hFuss.2.2.trans (congrArg Option.some hReg),
    hMain2⟩

#print axioms fragmentStore_passt

/-- Witness decoded store: `store [rsp], rax` at the fragment slot address. -/
def fragStore : Decodiert :=
  { befehl := Befehl.store64 Register.rsp Register.rax (BitVec.ofNat 32 0),
    laenge := 4 }

/-- Witness pre-state: `rsp` at the slot base, `rax` holding the source value. -/
def fragStoreVor : Zustand :=
  { register :=
      regSet (regSet zeugeReg Register.rsp (BitVec.ofNat 64 4096))
        Register.rax (zahlWort witVal),
    flags := zeugeFlags, rip := BitVec.ofNat 64 4096,
    speicher := zeugeSpeicher }

/-- JOINT WITNESS for `fragmentStore_passt`: every source and target
    premise holds jointly — the witness table written `0 → 42`, the
    matching word write, and a reached realised `store64` step at the
    slot address carrying the source value — and so do the footprint,
    width, value and read-back conclusions with changed bytes on both
    sides. -/
theorem fragmentStore_passt_zeuge :
    ∃ (σ' : World witD) (ρ' : Env witD []) (m' : Speicher)
      (dd : Decodiert) (s sT : Zustand),
      repOk (witD.typ () ()) 4096 16 0 = true ∧
      execStmt witO 0 witR
        (Stmt.assignSlot (l := false) () () witI witE witHw witHL)
        witSigma Env.nil = .ok σ' ρ' ∧
      write64 witM witA (zahlWort witVal) = some m' ∧
      lesbar8 witM witA = true ∧
      schritt dd s = some sT ∧
      dd.befehl = .store64 Register.rsp Register.rax (BitVec.ofNat 32 0) ∧
      laengeOk dd.laenge = true ∧
      effAddr s Register.rsp (BitVec.ofNat 32 0) = slotAddr 4096 0 ∧
      s.register Register.rax = zahlWort witVal ∧
      (zugriff dd s).schreiben = Fuss (slotAddr 4096 0) ∧
      (zugriff dd s).schreiben.length = 8 ∧
      (zugriff dd s).speicherWert = some (zahlWort witVal) ∧
      (∃ w, read64 m' (slotAddr 4096 0) = some w ∧
        wortZahl 0 100 w = some witVal) ∧
      (witSigma.slots () 0 ()).n = 0 ∧
      (σ'.slots () 0 ()).n = 42 ∧
      witM.bytes witA ≠ m'.bytes witA ∧
      s.speicher.bytes witA ≠ sT.speicher.bytes witA := by
  obtain ⟨σ', ρ', m', hOk, hWr, hk, hv, hExec, hTgt, hRd, hRep, hRt,
    hBefore, hAfter, hBytes⟩ := rep_schritt_bleibt_zeuge
  have hbef : fragStore.befehl =
      .store64 Register.rsp Register.rax (BitVec.ofNat 32 0) := rfl
  have hok : laengeOk fragStore.laenge = true := rfl
  have hAddr : effAddr fragStoreVor Register.rsp (BitVec.ofNat 32 0) =
      slotAddr 4096 0 := by
    decide
  have hSlot : witA = slotAddr 4096 0 := rfl
  have hReg : fragStoreVor.register Register.rax = zahlWort witVal := rfl
  have hLese : witSL = witSigma.lese [] (witI.orte ++ witE.orte) := rfl
  have hdec : ((schritt fragStore fragStoreVor).map
      (fun s' => s'.speicher.bytes witA) =
      some (BitVec.ofNat 8 42)) := by
    decide
  obtain ⟨sT, hstep, hval⟩ := Option.map_eq_some_iff.mp hdec
  have hMain := fragmentStore_passt witO 0 witR () () 0 100 witHT
    4096 16 0 hOk witI witE witHw witHL witSigma Env.nil witSL hLese
    0 witVal hk hv witA witM m' σ' ρ' hExec hTgt hRd fragStore
    fragStoreVor sT Register.rsp Register.rax (BitVec.ofNat 32 0) hok hbef
    hstep hAddr hSlot hReg
  have hTa : sT.speicher.bytes witA = BitVec.ofNat 8 42 := hval
  have hTo : fragStoreVor.speicher.bytes witA = BitVec.ofNat 8 0 := rfl
  exact ⟨σ', ρ', m', fragStore, fragStoreVor, sT, hOk, hExec, hTgt, hRd,
    hstep, hbef, hok, hAddr, hReg, hMain.1, hMain.2.1, hMain.2.2.1,
    hMain.2.2.2, hBefore, hAfter, hBytes, by rw [hTo, hTa]; decide⟩

#print axioms fragmentStore_passt_zeuge

/-- A realised `load64` at a represented slot loads exactly the source
    slot value: the loaded word parses back via `wortZahl`, the
    destination holds it, and memory is unchanged (reads change no
    byte). Consumes `realisiert_load64_gefunden` for the realised read
    and `RepSlot` plus the roundtrip for the value link; the new
    connection is `hAddr`. Every premise is used. -/
theorem fragmentLoad_passt {D : Deklaration}
    {t : D.Tab} {k : Int} {f : D.Feld t} {lo hi : Int}
    {hT : D.typ t f = .int lo hi}
    (v : Zahl lo hi)
    {a : Adresse} {s s' : Zustand}
    {σw : World D}
    (hRep : RepSlot t k f lo hi hT a s.speicher σw)
    (hLo : 0 ≤ lo) (hHi : hi < 2 ^ 64)
    (hv : (cast (congrArg (Wert D) hT) (σw.slots t k f)) = v)
    (dd : Decodiert) (dst baseR : Register) (disp : BitVec 32)
    (hok : laengeOk dd.laenge = true)
    (hbef : dd.befehl = .load64 dst baseR disp)
    (hstep : schritt dd s = some s')
    (hAddr : effAddr s baseR disp = a) :
    ∃ w, read64 s.speicher a = some w ∧ wortZahl lo hi w = some v ∧
      s'.register dst = w ∧ s'.speicher = s.speicher := by
  have hRd := realisiert_load64_gefunden dd s s' dst baseR disp hok hbef hstep
  obtain ⟨v', hread, hreg, hmem⟩ := hRd
  rw [hAddr] at hread
  unfold RepSlot at hRep
  rw [hread] at hRep
  simp only [Option.some.injEq] at hRep
  rw [hv] at hRep
  refine ⟨v', hread, ?_, hreg, hmem⟩
  rw [hRep]
  exact zahlWort_wortZahl v hLo hHi

#print axioms fragmentLoad_passt

/-- Witness decoded load: `rbx := [rax]` at the fragment slot address. -/
def fragLoad : Decodiert :=
  { befehl := Befehl.load64 Register.rbx Register.rax (BitVec.ofNat 32 0),
    laenge := 4 }

/-- Witness pre-state: `rax` at the slot base, `rbx` holding a sentinel. -/
def fragLoadVor : Zustand :=
  { register :=
      regSet (regSet zeugeReg Register.rax (BitVec.ofNat 64 4096))
        Register.rbx (BitVec.ofNat 64 7),
    flags := zeugeFlags, rip := BitVec.ofNat 64 4096,
    speicher := zeugeSpeicher }

/-- JOINT WITNESS for `fragmentLoad_passt`: a represented slot holding
    zero, a reached realised `load64` step at its address loading the
    zero word into the destination (observably changing the register
    from its sentinel), with memory unchanged — on a declaration with a
    table its function writes. -/
theorem fragmentLoad_passt_zeuge :
    ∃ (s s' : Zustand),
      RepSlot () (0 : Int) () 0 100 witHT witA s.speicher witSigma ∧
      schritt fragLoad s = some s' ∧
      fragLoad.befehl =
        .load64 Register.rbx Register.rax (BitVec.ofNat 32 0) ∧
      laengeOk fragLoad.laenge = true ∧
      effAddr s Register.rax (BitVec.ofNat 32 0) = witA ∧
      (∃ w, read64 s.speicher witA = some w ∧
        wortZahl 0 100 w = some (⟨0, by decide, by decide⟩ : Zahl 0 100) ∧
        s'.register Register.rbx = w ∧ s'.speicher = s.speicher) ∧
      witD.schreibt () () = true ∧
      s.register Register.rbx ≠ s'.register Register.rbx := by
  have hRep : RepSlot () (0 : Int) () 0 100 witHT witA fragLoadVor.speicher
      witSigma := by
    unfold RepSlot
    decide
  have hbef : fragLoad.befehl =
      .load64 Register.rbx Register.rax (BitVec.ofNat 32 0) := rfl
  have hok : laengeOk fragLoad.laenge = true := rfl
  have hAddr : effAddr fragLoadVor Register.rax (BitVec.ofNat 32 0) =
      witA := by
    decide
  have hv : (cast (congrArg (Wert witD) witHT)
      (witSigma.slots () (0 : Int) ())) =
      (⟨0, by decide, by decide⟩ : Zahl 0 100) := rfl
  have hdec : ((schritt fragLoad fragLoadVor).map
      (fun s' => s'.register Register.rbx) =
      some (BitVec.ofNat 64 0)) := by
    decide
  obtain ⟨sT, hstep, hval⟩ := Option.map_eq_some_iff.mp hdec
  have hMain := fragmentLoad_passt (⟨0, by decide, by decide⟩ : Zahl 0 100)
    hRep (by decide : (0 : Int) ≤ 0) (by decide) hv fragLoad
    Register.rbx Register.rax (BitVec.ofNat 32 0) hok hbef hstep hAddr
  have hval' : sT.register Register.rbx = BitVec.ofNat 64 0 := hval
  have hchg : fragLoadVor.register Register.rbx ≠
      sT.register Register.rbx := by
    rw [show fragLoadVor.register Register.rbx = BitVec.ofNat 64 7 from
      rfl, hval']
    decide
  exact ⟨fragLoadVor, sT, hRep, hstep, hbef, hok, hAddr, hMain, rfl, hchg⟩

#print axioms fragmentLoad_passt_zeuge

/-! ## 5. Refusals: unsupported rules and profiles are rejected. -/

/-- Rule admission: only `Stmt.assignSlot` belongs to the fragment.
    Every other statement form is refused by decision (`false`). -/
def regelOk {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Bool
  | .assignSlot .. => true
  | _ => false

/-- The admitted rule shape: `s` is an `assignSlot`. Stated as a
    classifier family rather than an equation, so every case stays
    well-typed across the statement indices; consumers recover the
    components by inversion. -/
inductive IstAssignSlot {D : Deklaration} {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)} : ∀ {Λ' : List (Res D)},
    Stmt D V l Γ Λ Λ' → Prop where
  | mk {t : D.Tab} {f : D.Feld t}
    {i : Expr D Γ Λ (.index (D.count t))}
    {e : Expr D Γ Λ (D.typ t f)}
    {hw : V.schreibt t = true} {hL : darf D t Λ} :
    IstAssignSlot (Stmt.assignSlot t f i e hw hL)

/-- Every admitted rule is an `assignSlot`: all unsupported source rules
    (pointer/global/byte writes, calls, locks, loops, gates, returns and
    the rest) are rejected — proved by casing on the actual statement,
    never by enumerating names. -/
theorem regelOk_nur {D : Deklaration} {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    (h : regelOk s = true) : IstAssignSlot s := by
  cases s with
  | assignSlot t f i e hw hL => exact .mk
  | _ => simp [regelOk] at h

/-- Witness that the only admitted rule is inhabited on a declaration
    with a table its function writes. -/
theorem regelOk_nur_zeuge :
    ∃ (s : Stmt witD witV false [] [] []) (_ : regelOk s = true),
      IstAssignSlot s ∧
      witV.schreibt () = true := by
  exact ⟨Stmt.assignSlot () () witI witE witHw witHL, rfl,
    .mk, rfl⟩

/-- Profile refusals: every non-`.int` type has no word representation.
    (`bool`, over-wide and out-of-region refusals are pinned in
    `SourceMemory`; globals are refused by `fragmentProfilOk` below.) -/
theorem repOk_opt_verweigert : repOk (.opt 5) 4096 16 0 = false := by decide
theorem repOk_summe_verweigert : repOk (.sum []) 4096 16 0 = false := by decide
theorem repOk_grund_verweigert : repOk (.grund 2) 4096 16 0 = false := by decide
theorem repOk_nie_verweigert : repOk .never 4096 16 0 = false := by decide
theorem repOk_float_verweigert : repOk (.fl (0, 1) (0, 1)) 4096 16 0 = false := by decide
theorem repOk_fnzeiger_verweigert : repOk (.fnptr 0) 4096 16 0 = false := by decide
theorem repOk_zeiger_verweigert : repOk (.ptr 0 true) 4096 16 0 = false := by decide

/-- Carrier admission: a table carrier is admitted exactly by `repOk`;
    a global carrier is refused (globals have no `RepSlot`). -/
def fragmentProfilOk {D : Deklaration} (c : D.Tab ⊕ D.Glob) (ty : Ty)
    (base len off : Nat) : Bool :=
  match c with
  | .inl _ => repOk ty base len off
  | .inr _ => false

/-- Global carriers are refused on every profile. -/
theorem fragmentProfil_global_verweigert {D : Deklaration} (g : D.Glob)
    (ty : Ty) (base len off : Nat) :
    fragmentProfilOk (D := D) (.inr g) ty base len off = false := by
  rfl

/-- The witness profile is admitted. -/
theorem fragmentProfil_wit_ok :
    fragmentProfilOk (D := witD) (.inl ()) (.int 0 100) 4096 16 0 = true := by
  decide

/-! ## 6. Byte grouping, width, alignment and slot ownership. -/

/-- No wrap: an admitted slot address covers eight consecutive bytes.
    Derived from the checked `repOk` region bounds, never assumed. -/
theorem fragmentOhneUmbruch {lo hi : Int} {base len off : Nat}
    (h : repOk (.int lo hi) base len off = true) :
    OhneUmbruch (slotAddr base off) := by
  obtain ⟨-, -, -, hWrap⟩ := repOk_klingt h
  unfold OhneUmbruch slotAddr natAdresse
  rw [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : base + off < 2 ^ 64)]
  omega

/-- Checked alignment admission for one fragment word: the slot address
    carries 8-alignment. The lowering admits only words passing this
    guard alongside `repOk`; the refused case is proved below. -/
def fragmentZielOk (base off : Nat) : Bool :=
  ausgerichtet8 (slotAddr base off)

/-- The witness slot address is aligned. -/
theorem fragmentZiel_ok_zeuge : fragmentZielOk 4096 0 = true := by decide

/-- A misaligned slot address is refused. -/
theorem fragmentZiel_schief_verweigert : fragmentZielOk 4096 1 = false := by decide

/-- Slot ownership witness: two admitted disjoint slots own disjoint
    8-byte footprints (source side: `rep_fremd_tab`; target side here). -/
theorem fragmentFussEigentum_zeuge :
    Disjunkt (slotAddr 4096 0) (slotAddr 4104 0) :=
  disjunkt_von_layout { tab := 0, basis := 4096, len := 8, ausr := 8 }
    { tab := 1, basis := 4104, len := 8, ausr := 8 } 0 0
    (by decide) (by decide) (by decide) (by decide) (by decide)

#print axioms regelOk_nur
#print axioms regelOk_nur_zeuge
#print axioms repOk_opt_verweigert
#print axioms repOk_summe_verweigert
#print axioms repOk_grund_verweigert
#print axioms repOk_nie_verweigert
#print axioms repOk_float_verweigert
#print axioms repOk_fnzeiger_verweigert
#print axioms repOk_zeiger_verweigert
#print axioms fragmentProfil_global_verweigert
#print axioms fragmentProfil_wit_ok
#print axioms fragmentOhneUmbruch
#print axioms fragmentZiel_ok_zeuge
#print axioms fragmentZiel_schief_verweigert
#print axioms fragmentFussEigentum_zeuge

/- CUTS:
    - Fragment only: one `Stmt.assignSlot` step on one `.int lo hi` slot
      (`0 <= lo`, `hi < 2 ^ 64` checked by `repOk`) stored as one
      little-endian 8-byte word, with 8-aligned slot address
      (`fragmentZielOk`) and no 64-bit wrap (`fragmentOhneUmbruch`).
      Every other rule is refused (`regelOk_nur`); every non-`.int`
      profile and every global carrier is refused (`repOk_*_verweigert`,
      `fragmentProfil_global_verweigert`).
    - Single-slot steps only: multi-slot statements (`schreibBytes`),
      calls, lock open/close, loops, gates, registers, payloads and
      reason channels are outside (refused by `regelOk`, not covered).
    - No validator soundness: `repOk`/`fragmentProfilOk`/`fragmentZielOk`
      are decided admission predicates; `valX86_sound` and the
      source-to-final-bytes closing theorem stay OPEN.
    - No concurrency claim beyond the per-step access list: footprints
      are sequential byte footprints; per-access TSO refinement stays
      with the TSO bridge (`BrueckenProfil`/`WortGuard` are the handoff
      vocabulary, reused unchanged, never redefined here).
    - No hardware claim: refusal is validator admission, never an
      invented hardware fault. Only named silicon/device/time behaviour
      is hardware; loader/binding logic stays user logic with contracts.
    - No OS/loader assumption: layout bases are taken as checked numbers
      against decided Bools; the loaded-image mapping contract is OPEN.
    - No int->ptr conversion enters the language: slot addresses are
      target-side `natAdresse` computations over accepted layout bases,
      never source values cast to pointers.
    - Consumer interface (OPEN until cited): the lowering/validator
      consumes `fragmentListe`/`fragmentDelta_voll` (source enumeration),
      `blattFragment_voll` (G completeness), `fragmentStore_passt` /
      `fragmentLoad_passt` (realised footprint match) and admits only
      findings with `regelOk`/`fragmentProfilOk`/`fragmentZielOk` true.
-/

#print axioms fragmentListe_schreibt
#print axioms filterMap_leseEv
#print axioms take_neuAppend
#print axioms fragmentListe_invert
#print axioms schreibG_zugriff
#print axioms fragmentDelta_voll
#print axioms fragmentDelta_voll_zeuge
#print axioms blattFragment_voll
#print axioms blattFragment_voll_zeuge
#print axioms fragmentStore_passt
#print axioms fragmentStore_passt_zeuge
#print axioms fragmentLoad_passt
#print axioms fragmentLoad_passt_zeuge

end Gabbro.Grammatik.X86
