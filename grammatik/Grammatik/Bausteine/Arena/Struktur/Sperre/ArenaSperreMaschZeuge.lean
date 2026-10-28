/-
  File:      Grammatik/ArenaSperreMaschZeuge.lean
  Subject:   WITNESS FOR THE MACHINE BRIDGE `erkE_maschine` (PLAN-DYNAMIC.md section 8a.3, premise 2): the writer
             `if true { let i = alloc A (7) else return; lnk[i] = head; head = i; }; return` of the shared arena of
             `ArenaSperreWelt.lean` is run by the SMALL STEPS of a thread of the call machine (a thread that holds the lock
             `()` -- its trace says `nimmt ()` -- over the scenario memory `w0L`). Both premises are instantiated: the
             body is covered (`EndR`) and recognized (`ErkE`). The conclusion is non-degenerate: the machine pops the
             frame, its shared memory meets the arena invariant, and the head of the list is slot `1`.
-/
import Grammatik.Bausteine.Arena.Struktur.Sperre.ArenaSperreZeuge
import Grammatik.Bausteine.Arena.Struktur.Sperre.ArenaSperreAbdeckung

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

namespace SperreZeuge

open InvDynZeuge

/-- The writer: a function body (an end block). -/
def schreiberL : Endblock FDL FVL false [] HL :=
  Endblock.cons (Stmt.ite Expr.tru (nimmPushL vollL) Block.nil) (Endblock.ret ErgExpr.empty (List.Perm.refl _))

/-- **The recognizer accepts the writer** -- from a state that knows nothing. -/
theorem erkE_schreiberL : ErkE KLL Abs.leer schreiberL :=
  ErkE.ite (K := KLL) (V := FVL) (l := false) (Γ := []) (Λ := HL) (Λ1 := HL) (a := Abs.leer)
    (a1 := ((Abs.leer.ext .frei).set 0 .liste).tail) (a2 := Abs.leer) (a3 := Abs.leer) Expr.tru (nimmPushL vollL)
    Block.nil (Endblock.ret ErgExpr.empty (List.Perm.refl _)) erk_nimmPushL (Erk.nil _)
    (fun _ => Or.inr rfl) (fun _ => Or.inl rfl) (ErkE.ret _ _)

/-- The program: every function is the writer (the declaration has one). -/
def PL : Programm FDL where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ => schreiberL

/-- The frame below the writer (any frame will do: it is only resumed). -/
def untenL : RufRahmenG FDL :=
  ⟨(), Env.nil, w0L, ⟨false, [], HL, Env.nil, .ende schreiberL⟩⟩

/-- The trace of a thread that holds the lock. -/
def spurL : List (Ereignis FDL) := [Ereignis.nimmt () []]

/-- A machine whose threads all run the writer's frame, holding `()`, over the scenario memory. -/
def ML : RufMaschineG FDL :=
  ⟨w0L.speicher, fun _ => ⟨[untenL], ⟨(), Env.nil, w0L, ⟨false, [], HL, Env.nil, .ende schreiberL⟩⟩, spurL, []⟩, [],
    w0L⟩

theorem ml_welt : (ML.weltVon 0).slots = w0L.slots ∧ (ML.weltVon 0).globs = w0L.globs := ⟨rfl, rfl⟩

theorem schreiberL_schleifenfrei : schreiberL.schleifenfrei = true := rfl

/-- The writer is covered by the machine's fragment, at every depth -- derived from the certificate (`erkE_endR`), no second
    derivation is written. -/
theorem schreiberL_R (A : FDL.Lock → Prop) (n : Nat) : EndR A (Tief PL A n) schreiberL :=
  erkE_endR erkE_schreiberL rfl schreiberL_schleifenfrei

theorem held_spurL : HeldGenau HL (offen spurL) := by
  intro L
  cases L
  simp only [HL, List.mem_cons, List.not_mem_nil, or_false, spurL, offen]

theorem frei_ML (A : FDL.Lock → Prop) (hA : ∀ L, ¬ A L) : ∀ L, A L → RufFreiG ML 0 L := fun L h => absurd h (hA L)

/-- The sequential run of the writer, with ANY handler, from any world that holds the scenario memory (the trace may be
    anything): it returns, and the head of the list is slot `1`. -/
theorem schreiber_exec (O : Orakel FDL) (passes : Nat)
    (R : ∀ f : FDL.Fn, World FDL → Env FDL (FDL.params f) → RufAusgang f) (σ0 : World FDL)
    (hs : σ0.slots = w0L.slots) (hg : σ0.globs = w0L.globs) :
    ∃ (σ' : World FDL) (v : ErgVal FDL (vertragVon FDL ()).erg),
      execEnd (V := FVL) O passes R schreiberL σ0 .nil = .zurueck σ' v ∧ LGL.st σ' = 1 := by
  have hok0 : KLL.Ok σ0 := Dekl.ok_gleich_wort (K := KLL) (σ := w0L) (σ' := σ0) (by rw [hs]) (fun _ _ => by rw [hg]) ok_w0L
  have hkopf : FAL.kopfSt σ0 = 1 := by
    show (Wert.umTyp FAL.hkopf (σ0.globs FAL.kopf)).n = 1
    rw [hg]; exact kopf_w0L
  obtain ⟨σ1, k, he1, hkn, -⟩ := nimmAlloc_ausfuehren O passes R FAL siebenL rfl fdarfL rfl (fgdarfL _) vollL
    (Block.linkPush LLL LGL (.here : Var GL1 _) rfl fdarfL rfl (fgdarfL _) .nil) σ0 .nil
    (by rw [hkopf]; decide) hok0.1
  obtain ⟨σ2, he2, -, hg2, -⟩ := linkPush_ausfuehren O passes R LLL LGL (V := FVL) (l := false) (Γ := GL1) (Λ := HL)
    (Λ' := HL) .here rfl fdarfL rfl (fgdarfL _) .nil σ1 (.cons k .nil)
  have hrun : execBlock (V := FVL) O passes R (nimmPushL vollL) σ0 .nil = .ok σ2 .nil := by
    unfold nimmPushL
    rw [he1]
    simp only [Ausgang.schrumpf]
    rw [he2]
    rfl
  refine ⟨σ2.lese HL [], (), ?_, ?_⟩
  · have hl : σ0.lese HL (Expr.tru : Expr FDL [] HL Ty.bool).orte = σ0 := by
      simp only [World.lese, World.merke, Expr.orte, List.map_nil, List.nil_append]
    simp only [schreiberL, execEnd, execStmt, eval, wahr?]
    rw [hl]
    simp only [if_true, hrun]
    rfl
  · show LGL.st σ2 = 1
    rw [hg2]
    show k.n = 1
    rw [hkn, hkopf]

/-- **THE WITNESS.** The writer, covered and recognized, run by the machine's steps from a thread that holds the lock over
    the scenario memory: the frame is popped with the return value, the shared memory meets the arena invariant, and
    the head of the list is slot `1`. -/
theorem erkE_maschine_zeuge :
    ∃ (M' : RufMaschineG FDL) (σ' : World FDL), RufLaufG PL oL 0 0 ML M' ∧ M'.speicher = σ'.speicher ∧
      KLL.Ok (M'.speicher.welt []) ∧ LGL.st σ' = 1 := by
  obtain ⟨σ', v, hex, hlg⟩ := schreiber_exec oL 0 (rufRumpf PL oL 0 1) (ML.weltVon 0) rfl rfl
  obtain ⟨M', ext, hl, -, hsp, -, hok⟩ := erkE_maschine_erk (Alk := fun _ => False) (K := KLL) PL oL 0 1 ML 0 () Env.nil w0L untenL [] spurL []
    (Γ := []) (Λ := HL) Env.nil schreiberL erkE_schreiberL schreiberL_schleifenfrei rfl rfl held_spurL
    (frei_ML _ (fun _ h => h)) (by show KLL.Ok (ML.speicher.welt spurL); exact (Dekl.ok_spur w0L spurL).mpr ok_w0L) σ' v hex
  exact ⟨M', σ', hl, hsp, hok, hlg⟩

/-! ## The call form of the section theorem, on the same program -/

theorem hpL : RufPasst FDL FVL (FDL.signatur ()) HL where
  hw := fun _ _ => rfl
  hg := fun _ _ => rfl
  hk := ⟨[], List.Perm.nil, List.nil_sublist _⟩
  hx := fun L hL hn => absurd (by
    have : L = () := by
      cases L
      rfl
    subst this
    simp only [FDL, Fin.isValue, Deklaration.signatur, List.mem_cons, List.not_mem_nil, or_false]) hn
  hh := fun L hL => by
    have : L = () := by
      cases L
      rfl
    subst this
    simp only [HL, List.mem_cons, List.not_mem_nil, or_false]

/-- The section body of the call form: `f();` -- the writer is a function, called with the lock held. -/
def rufeL : Block FDL FVL false [] HL HL :=
  Block.cons (Stmt.call () Args.nil hpL rfl) Block.nil

/-- The call section: `locks () { f(); }`. -/
def abschnittRufe : Stmt FDL FVL false [] [] [] :=
  Stmt.locks () (fun M hM => by simp only [List.not_mem_nil] at hM) rufeL

theorem rufe_L : Rufe (fun _ => True) rufeL := Rufe.cons () Args.nil hpL rfl Block.nil trivial Rufe.nil

/-- **The premise of the call form is satisfiable:** `rufAt` of the program, whose every function is the writer, answers
    in an arena-consistent world (`rufAt_erk`). -/
theorem rErhaelt_PL (n : Nat) : RErhaelt KLL (fun _ => True) (rufAt PL oL 0 n) :=
  rufAt_erk KLL PL oL 0 (fun _ => True) (fun _ _ => erkE_schreiberL) n

/-- **The call section, by the section theorem:** over any environment move of the acquire, every exit of `locks () { f(); }`
    meets the arena invariant. -/
theorem abschnitt_rufe_zeuge (n : Nat) (σ : World FDL) :
    StrukturPost KLL Abs.leer (execStmtH (KLL.sperr ()) oL U0 0 (rufAt PL oL 0 n) abschnittRufe σ .nil) :=
  abschnitt_rufe KLL () oL U0 0 (rufAt PL oL 0 n) (rErhaelt_PL n) (fun M hM => by simp only [List.not_mem_nil] at hM) rufe_L havoc_U0 σ .nil

/-- **`rufAt` of the writer, run** from a world that holds the scenario memory: at depth `n + 1` the call answers a value,
    the arena invariant holds in the answer's world, and the head of the list is slot `1`. -/
theorem rufAt_PL_lauf (n : Nat) (σ1 : World FDL) (hs : σ1.slots = w0L.slots) (hg : σ1.globs = w0L.globs) :
    ∃ (σ3 : World FDL) (v : ErgVal FDL (FDL.erg ())), rufAt PL oL 0 (n + 1) () σ1 .nil = .ok σ3 v ∧
      KLL.Ok σ3 ∧ LGL.st σ3 = 1 := by
  have hW : σ1.lese (Signatur.anfang FDL (FDL.signatur ())) (PL.requires ()).orte = σ1.lese HL [] := rfl
  obtain ⟨σ2, v, hex, hlg⟩ := schreiber_exec oL 0 (rufAt PL oL 0 n) (σ1.lese HL []) hs hg
  have hpost := erkE_koerper oL 0 (rufAt PL oL 0 n) KLL erkE_schreiberL (σ1.lese HL []) .nil
    (Dekl.ok_gleich_wort (K := KLL) (σ := w0L) (σ' := σ1.lese HL []) (by rw [show (σ1.lese HL []).slots = σ1.slots from rfl, hs])
      (fun _ _ => by rw [show (σ1.lese HL []).globs = σ1.globs from rfl, hg]) ok_w0L) Abs.leer
  rw [hex] at hpost
  refine ⟨(σ2.lese (Vertrag.ende FDL (vertragVon FDL ())) (PL.ensures ()).orte), v, ?_, ?_, ?_⟩
  · simp only [rufAt]
    rw [hW]
    simp only [PL, wahr?, eval, Expr.orte]
    erw [hex]
    simp only [Bool.true_eq_false, ↓reduceIte, List.filter_nil, List.foldl_nil, List.find?_nil]
  · exact (Dekl.Ok.lese KLL _ _ hpost)
  · exact hlg

/-- **The call section, run:** with `rufAt` at depth `n + 1` the call returns, the section ends `.ok`, the arena invariant
    holds and the head of the list is slot `1`. -/
theorem abschnitt_rufe_lauf (n : Nat) (σ : World FDL) :
    ∃ σ' : World FDL, execStmtH (KLL.sperr ()) oL U0 0 (rufAt PL oL 0 (n + 1)) abschnittRufe σ .nil =
      .ok (σ'.gibt ()) .nil ∧ KLL.Ok σ' ∧ LGL.st σ' = 1 := by
  obtain ⟨σ3, v, hr, hok, hlg⟩ := rufAt_PL_lauf n (((U0 () σ).nimmt ()).lese HL []) rfl rfl
  have hrun : execBlock (V := FVL) oL 0 (rufAt PL oL 0 (n + 1)) rufeL ((U0 () σ).nimmt ()) .nil = .ok σ3 .nil := by
    simp only [rufeL, execBlock, execStmt]
    erw [hr]
  have hinv : (KLL.sperr ()).inv () σ3.speicher = true := (Dekl.sperr_inv_iff' σ3).mpr hok
  refine ⟨σ3, ?_, hok, hlg⟩
  show freiH (KLL.sperr ()) () (execBlockH (KLL.sperr ()) oL U0 0 (rufAt PL oL 0 (n + 1)) rufeL
    ((U0 () σ).nimmt ()) .nil) = _
  rw [Block.execH_ohne (KLL.sperr ()) oL U0 0 (rufAt PL oL 0 (n + 1)) rufeL (rufe_ohneLocks rufe_L), hrun]
  simp only [freiH, hinv, if_true]

end SperreZeuge

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.SperreZeuge.erkE_maschine_zeuge
#print axioms Gabbro.Grammatik.SperreZeuge.abschnitt_rufe_zeuge
#print axioms Gabbro.Grammatik.SperreZeuge.abschnitt_rufe_lauf
