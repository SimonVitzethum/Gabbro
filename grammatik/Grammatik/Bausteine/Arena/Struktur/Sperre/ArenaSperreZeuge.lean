/-
  File:      Grammatik/ArenaSperreZeuge.lean
  Subject:   WITNESS AND PLANTED DEFECTS FOR THE SECTION THEOREM (PLAN-DYNAMISCH.md section 8a.2): a locked section over
             the shared four-slot arena of `ArenaSperreWelt.lean`, RUN, and a section that stores a link outside what the
             recognizer allows, whose release check FIRES.

  Accepted (witness): `locks () { let i = alloc A (7) else return; lnk[i] = head; head = i; }` -- take slot `1` off the free
  list and link it in at the head of the list -- over ANY environment move of the acquire (`HavocOk`): the section ends
  `.ok`, the arena invariant holds, the head is the slot `1`, the release check passed. The recognizer derives the body
  (`erk_nimmPushL`), the lock family is well formed (`sperr_ok_zeuge`), and `U0` is a member of the class (`havoc_U0`), so
  no hypothesis of `abschnitt_erk` is vacuous.

  Rejected (planted defects):
    * `locks () { lnk[2] = 2; }` -- a link stored without the head and the move it belongs to, here a self link on the
      head -- is run: the body returns `.ok` in a world where the arena invariant FAILS (`stray_bricht`) and the release
      check of the lock invariant turns the section into `logik schleife` (`abschnitt_defekt_schleife`); the section
      theorem is not applicable: the soundness theorem, applied to a derivation, would give the invariant (`stray_abgelehnt`:
      no derivation exists).
    * the same stray world is no environment move: no member of `HavocOk` hands it to an acquirer (`stray_kein_havoc`).
-/
import Grammatik.Bausteine.Arena.Struktur.Sperre.ArenaSperreWelt

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

namespace SperreZeuge

open InvDynZeuge

/-- The contract of the witness bodies: they run with `()` held and end holding it (a locked arena operation). -/
def FVL : Vertrag FDL where
  schreibt := fun _ => true
  gschreibt := fun _ => true
  erg := none
  gruende := 0
  haelt := [()]
  produziert := []

/-- Held locks inside the section. -/
abbrev HL : List (Res FDL) := [Res.held ()]

theorem fdarfL : darf FDL () HL := by
  intro w hw
  simp only [FDL, List.mem_singleton] at hw
  subst hw
  simp [HL, Res.von]

theorem fgdarfL (g : FDL.Glob) : gdarf FDL g HL := by
  intro w hw
  simp only [FDL, List.mem_singleton] at hw
  subst hw
  simp [HL, Res.von]

/-- The payload `7`, at the payload field's declared type. -/
def siebenL : Expr FDL [] HL (FDL.typ FAL.tab FAL.feld) :=
  Expr.umTyp (show Ty.int 0 255 = FDL.typ FAL.tab FAL.feld from by decide)
    (Expr.widen (by decide) (by decide) (Expr.lit 7))

abbrev GL1 : Ctx := [Ty.index (FDL.count FAL.tab)]

/-- The section body: take a slot off the free list and link it in at the head of the list. -/
def nimmPushL (voll : Endblock FDL FVL false [] HL) : Block FDL FVL false [] HL HL :=
  Block.freiNimm FAL siebenL rfl fdarfL rfl (fgdarfL _) voll
    (Block.linkPush LLL LGL (.here : Var GL1 _) rfl fdarfL rfl (fgdarfL _) .nil)

/-- The `else` branch: it returns, and stores nothing. -/
def vollL : Endblock FDL FVL false [] HL := Endblock.ret ErgExpr.empty (List.Perm.refl _)

theorem rein_vollL : Rein vollL := Rein.ret _ _

/-- **The recognizer accepts the body** -- from a state that knows nothing. -/
theorem erk_nimmPushL :
    Erk KLL Abs.leer (nimmPushL vollL) (((Abs.leer.ext .frei).set 0 .liste).tail) :=
  Erk.nimm siebenL rfl fdarfL rfl (fgdarfL _) vollL _ rein_vollL
    (Erk.push ⟨LLL, LGL⟩ rfl (.here : Var GL1 _) rfl fdarfL rfl (fgdarfL _) .nil (by simp [Abs.ext, Var.pos])
      (Erk.nil _))

/-- The section itself. -/
def abschnittL : Stmt FDL FVL false [] [] [] :=
  Stmt.locks () (fun M hM => by simp at hM) (nimmPushL vollL)

/-- An environment move of the acquire that hands over the scenario world (and keeps the trace). -/
def U0 : Umwelt FDL := fun _ σ => ⟨w0L.slots, w0L.globs, σ.spur⟩

theorem ok_U0 (σ : World FDL) : KLL.Ok (U0 () σ) :=
  Dekl.ok_gleich_wort (K := KLL) (σ := w0L) (σ' := U0 () σ) rfl (fun _ _ => rfl) ok_w0L

/-- **`U0` is in the class of environment moves** the section theorem quantifies over: the hypothesis `HavocOk` of
    `abschnitt_erk` is satisfiable. -/
theorem havoc_U0 : HavocOk (KLL.sperr ()) U0 := by
  intro L σ
  cases L
  refine ⟨rfl, fun c hc => absurd (by rw [Dekl.sperr_orte_self]; exact alle_orte c) hc, ?_⟩
  exact (Dekl.sperr_inv_iff' (U0 () σ)).mpr (ok_U0 σ)

/-- **The section, run:** over the environment move `U0` -- and the starting world is whatever trace the thread had --
    the section ends `.ok` in a world where the arena invariant holds, the head of the list is slot `1` (taken off the
    free list), and the release check passed. Neither the list nor the free list is empty before, so the section does
    something. -/
theorem abschnitt_zeuge (O : Orakel FDL) (passes : Nat)
    (R : ∀ f : FDL.Fn, World FDL → Env FDL (FDL.params f) → RufAusgang f) (σ : World FDL) :
    ∃ σ' : World FDL,
      execStmtH (KLL.sperr ()) O U0 passes R abschnittL σ .nil = .ok (σ'.gibt ()) .nil ∧
      KLL.Ok σ' ∧ LGL.st σ' = 1 := by
  have hS0 : KLL.Ok ((U0 () σ).nimmt ()) := abschnitt_start KLL () havoc_U0 σ
  have hpost := erk_erhaeltH (KLL.sperr ()) O U0 passes R KLL erk_nimmPushL ((U0 () σ).nimmt ()) .nil hS0
    (StrukturPasst.leer KLL _ _)
  obtain ⟨σ1, k, he1, hkn, -⟩ := nimmAlloc_ausfuehren O passes R FAL siebenL rfl fdarfL rfl (fgdarfL _) vollL
    (Block.linkPush LLL LGL (.here : Var GL1 _) rfl fdarfL rfl (fgdarfL _) .nil) ((U0 () σ).nimmt ()) .nil
    (by show FAL.kopfSt w0L < 4; rw [kopf_w0L]; decide)
    hS0.1
  obtain ⟨σ2, he2, -, hg2, -⟩ := linkPush_ausfuehren O passes R LLL LGL (V := FVL) (l := false) (Γ := GL1) (Λ := HL)
    (Λ' := HL) .here rfl fdarfL rfl (fgdarfL _) .nil σ1 (.cons k .nil)
  have hrun : execBlock (V := FVL) O passes R (nimmPushL vollL) ((U0 () σ).nimmt ()) .nil = .ok σ2 .nil := by
    unfold nimmPushL
    rw [he1]
    simp only [Ausgang.schrumpf]
    rw [he2]
    rfl
  rw [erk_execBlockH (KLL.sperr ()) O U0 passes R KLL erk_nimmPushL, hrun] at hpost
  have hrunH := erk_execBlockH (KLL.sperr ()) O U0 passes R KLL erk_nimmPushL ((U0 () σ).nimmt ()) .nil
  rw [hrun] at hrunH
  have hok : (KLL.sperr ()).inv () σ2.speicher = true := (Dekl.sperr_inv_iff' σ2).mpr hpost.1
  refine ⟨σ2, ?_, hpost.1, ?_⟩
  · show freiH (KLL.sperr ()) () (execBlockH (KLL.sperr ()) O U0 passes R (nimmPushL vollL)
      ((U0 () σ).nimmt ()) .nil) = _
    rw [hrunH]
    simp only [freiH, hok, if_true]
  · rw [hg2]
    show k.n = 1
    rw [hkn]
    rfl

/-! ## The planted defects -/

/-- A link store is read back at the slot it went to. -/
theorem wert_schreib {A : FreiForm FDL} (L : LinkFeld A) (σ : World FDL) (Λ : List (Res FDL)) (k : Int)
    (v : Wert FDL (FDL.typ A.tab L.f)) : L.wert (σ.schreibSlot A.tab Λ k L.f v) k = (Wert.umTyp L.hf v).n := by
  simp only [LinkFeld.wert, World.slots_schreibSlot_selbst]

/-- The index `2` and the value `2` of the stray store. -/
def idx2L : Expr FDL [] HL (Ty.index (FDL.count FAL.tab)) :=
  Expr.umTyp (show Ty.int 0 3 = Ty.index (FDL.count FAL.tab) from by decide)
    (Expr.widen (by decide) (by decide) (Expr.lit 2))

def val2L : Expr FDL [] HL (FDL.typ FAL.tab LLL.f) :=
  Expr.umTyp (show Ty.int 0 4 = FDL.typ FAL.tab LLL.f from by decide)
    (Expr.widen (by decide) (by decide) (Expr.lit 2))

theorem idx2L_n (σ : World FDL) (ρ : Env FDL []) : (eval σ idx2L σ ρ).n = 2 := rfl

theorem val2L_n (σ : World FDL) (ρ : Env FDL []) : (Wert.umTyp LLL.hf (eval σ val2L σ ρ)).n = 2 := rfl

/-- The section body of the defect: a link stored on its own -- `lnk[2] = 2`, the head linked to itself. -/
def schlechtL : Block FDL FVL false [] HL HL :=
  Block.cons (Stmt.assignSlot FAL.tab LLL.f idx2L val2L rfl fdarfL) .nil

theorem schlecht_ohneLocks : schlechtL.ohneLocks = true := rfl

/-- The section of the defect. -/
def schlechtAbschnitt : Stmt FDL FVL false [] [] [] :=
  Stmt.locks () (fun M hM => by simp at hM) schlechtL

/-- **The stray store, run:** from any world the body returns `.ok`, with the link of slot `2` now `2`, and the head
    word as it was. -/
theorem schlecht_lauf (O : Orakel FDL) (passes : Nat)
    (R : ∀ f : FDL.Fn, World FDL → Env FDL (FDL.params f) → RufAusgang f) (σ0 : World FDL) :
    ∃ σ1 : World FDL, execBlock (V := FVL) O passes R schlechtL σ0 .nil = .ok σ1 .nil ∧
      LLL.wert σ1 2 = 2 ∧ LGL.st σ1 = LGL.st σ0 := by
  refine ⟨_, rfl, ?_, rfl⟩
  have h := wert_schreib LLL (σ0.lese HL (idx2L.orte ++ val2L.orte)) HL
    (eval (σ0.lese HL (idx2L.orte ++ val2L.orte)) idx2L (σ0.lese HL (idx2L.orte ++ val2L.orte)) .nil).n
    (eval (σ0.lese HL (idx2L.orte ++ val2L.orte)) val2L (σ0.lese HL (idx2L.orte ++ val2L.orte)) .nil)
  rw [val2L_n, idx2L_n] at h
  exact h

/-- An oracle for the shared witness declaration (no axioms, no registers). -/
def oL : Orakel FDL where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun _ _ => false

/-- A callee for the shared witness declaration (the bodies call nothing). -/
def rL : ∀ f : FDL.Fn, World FDL → Env FDL (FDL.params f) → RufAusgang f := fun _ _ _ => .logik .vorzustand

/-- **A list whose head links to itself has no chain**: the arena invariant fails. -/
theorem stray_bricht {σ : World FDL} (h2 : LLL.wert σ 2 = 2) (hg : LGL.st σ = 2) : ¬ KLL.Ok σ := by
  intro hok
  have hl : ListOk FAL LLL LGL σ := (Dekl.LOk_some (K := KLL) (d := ⟨LLL, LGL⟩) rfl σ).mp hok.2.1
  obtain ⟨L, hk, -, -⟩ := hl
  rw [hg] at hk
  exact push_doppelt_bricht (c := 4) (nx' := LLL.wert σ) (i := 2) (by decide) (by decide) h2 ⟨L, hk⟩

/-- **THE PLANTED DEFECT, in the section:** a section that stores a link on its own (`lnk[2] = 2`, no move that goes with
    it) is run from the scenario world: the body returns `.ok` -- and the release check of the lock invariant FIRES, the
    section ends in `logik schleife`. The invariant is not silently broken: the model refuses the release. -/
theorem abschnitt_defekt_schleife (O : Orakel FDL) (passes : Nat)
    (R : ∀ f : FDL.Fn, World FDL → Env FDL (FDL.params f) → RufAusgang f) (σ : World FDL) :
    execStmtH (KLL.sperr ()) O U0 passes R schlechtAbschnitt σ .nil = .logik .schleife := by
  obtain ⟨σ1, hrun, h2, hg⟩ := schlecht_lauf O passes R ((U0 () σ).nimmt ())
  have hbad : ¬ (KLL.sperr ()).inv () σ1.speicher = true := fun h =>
    stray_bricht h2 (by rw [hg]; exact lg_w0L) ((Dekl.sperr_inv_iff' σ1).mp h)
  show freiH (KLL.sperr ()) () (execBlockH (KLL.sperr ()) O U0 passes R schlechtL ((U0 () σ).nimmt ()) .nil) = _
  rw [Block.execH_ohne (KLL.sperr ()) O U0 passes R schlechtL schlecht_ohneLocks, hrun]
  simp [freiH, hbad]

/-- **The defect has no derivation:** the recognizer is sound (`erk_erhaelt`), and this body breaks the invariant in a
    real run from a world where it holds, so no `Erk` derivation of it exists; `abschnitt_erk` does not apply. -/
theorem stray_abgelehnt (a' : Abs) : ¬ Erk KLL Abs.leer schlechtL a' := by
  intro h
  have hpost := erk_erhaelt oL 0 rL KLL h w0L .nil ok_w0L (StrukturPasst.leer KLL _ _)
  obtain ⟨σ1, hrun, h2, hg⟩ := schlecht_lauf oL 0 rL w0L
  rw [hrun] at hpost
  exact stray_bricht h2 (by rw [hg]; exact lg_w0L) hpost.1

/-- **The stray world is no environment move:** no member of the class `HavocOk` hands a world where the stray link was
    stored to an acquirer -- the lock invariant of the acquire excludes it. This is why an unlocked link store is a
    refusal of the statement (`sperrSicht`: every carrier access is under `L`) and not a state the next section meets. -/
theorem stray_kein_havoc {U : Umwelt FDL} (hU : HavocOk (KLL.sperr ()) U) (σ : World FDL) :
    ¬ (LLL.wert (U () σ) 2 = 2 ∧ LGL.st (U () σ) = 2) := fun h =>
  stray_bricht h.1 h.2 ((Dekl.sperr_inv_iff' (U () σ)).mp (hU () σ).2.2)

end SperreZeuge

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.SperreZeuge.abschnitt_zeuge
#print axioms Gabbro.Grammatik.SperreZeuge.abschnitt_defekt_schleife
#print axioms Gabbro.Grammatik.SperreZeuge.stray_abgelehnt
#print axioms Gabbro.Grammatik.SperreZeuge.havoc_U0
