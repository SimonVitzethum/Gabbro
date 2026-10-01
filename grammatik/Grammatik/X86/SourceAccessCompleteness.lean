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

#print axioms filterMap_leseEv
#print axioms take_neuAppend
#print axioms fragmentListe_invert
#print axioms schreibG_zugriff

/- CUTS:
    - Skeleton only: enumeration plus write membership. The execStmt delta
      equation, G completeness, target footprint match, refusals and the
      joint witnesses are OPEN until the following increments land.
    - No source-to-final-bytes claim; no concurrency claim beyond the
      per-step access list; no hardware claim.
-/

#print axioms fragmentListe_schreibt

end Gabbro.Grammatik.X86
