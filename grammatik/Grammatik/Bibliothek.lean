/-
  File:      Grammatik/Bibliothek.lean
  Subject:   LIBRARY CALLS (lane E2, PLAN-ERWEITUNG.md section 6) -- a
             run-time library function is an `Ax` whose parameter list is
             the ordinary parameters with the payload type appended.
             No new statement constructor: the call IS an `axiomCall`.
-/
import Grammatik.RufMaschineF

namespace Gabbro.Grammatik

/-- A run-time library function (PLAN-ERWEITUNG.md section 6, lane E2):
    ordinary parameters, a payload type (a table or tree type on the
    checker side; one more parameter here), an optional result, and
    declared effects. -/
structure BibliotheksFunktion (D : Deklaration) where
  params : List Ty
  nutzlast : Ty
  erg : Option Ty
  schreibt : D.Tab → Bool
  gschreibt : D.Glob → Bool

/-- The axiom serving a library function: its parameter list is the
    ordinary parameters with the payload appended, its result is the
    declared one, and its declared effects agree with the library
    function's. -/
def DientBibliothek (D : Deklaration) (L : BibliotheksFunktion D)
    (a : D.Ax) : Prop :=
  D.aparams a = L.params ++ [L.nutzlast] ∧ D.aerg a = L.erg ∧
  (∀ t, D.aschreibt a t = L.schreibt t) ∧
  ∀ g, D.agschreibt a g = L.gschreibt g

/-! ## 1. Argument lists split at the payload -/

/-- Appending the payload argument to the ordinary arguments gives
    arguments for the axiom's full parameter list. Both append equations
    hold by computation (`rfl`); the `have` names them so the cast reads. -/
def args_snoc (D : Deklaration) {Γ : Ctx} {Λ : List (Res D)}
    {ps : List Ty} {p : Ty} :
    Args D Γ Λ ps → Expr D Γ Λ p → Args D Γ Λ (ps ++ [p])
  | .nil, last =>
    have h : ([] : List Ty) ++ [p] = [p] := rfl
    h ▸ Args.cons last .nil
  | .cons e rest, last =>
    have h : ∀ (τ : Ty) (qs : List Ty) (q : Ty),
        (τ :: qs) ++ [q] = τ :: (qs ++ [q]) := fun _ _ _ => rfl
    h _ _ _ ▸ Args.cons e (args_snoc D rest last)

/-- Splitting arguments for the full list into the ordinary arguments
    and the payload argument. Induction on the ordinary parameters; at
    each step the append equation is named (`rfl`) and the impossible
    `nil` case is closed by the tactic from index unification. -/
theorem args_unsnoc (D : Deklaration) {Γ : Ctx} {Λ : List (Res D)}
    (ps : List Ty) (p : Ty) (args : Args D Γ Λ (ps ++ [p])) :
    ∃ (rest : Args D Γ Λ ps) (last : Expr D Γ Λ p), True := by
  revert args
  induction ps with
  | nil =>
    intro args
    have h : ([] : List Ty) ++ [p] = [p] := rfl
    rw [h] at args
    cases args
    case cons last rest => exact ⟨rest, last, trivial⟩
  | cons t ps ih =>
    intro args
    have h : (t :: ps) ++ [p] = t :: (ps ++ [p]) := rfl
    rw [h] at args
    cases args
    case cons e rest =>
      obtain ⟨r, l, _⟩ := ih rest
      exact ⟨Args.cons e r, l, trivial⟩

/-! ## 2. The call obligations are the `axiomCall` obligations -/

/-- A library call is an `Ax` whose parameter list includes the payload
    (PLAN-ERWEITUNG.md section 6, lane E2): the typing obligation (the
    full argument list) together with the effect obligations (callee
    effects inside the caller's contract, accesses guarded) -- checked
    as ordinary arguments plus the payload argument against the declared
    library function -- are exactly the `Stmt.axiomCall` premises for
    the serving axiom. Both directions use the whole bridge `hDient`:
    `hap` transports the argument list, `herg` the result, `hschw` and
    `hgschw` the four effect premises. -/
theorem bibliotheksruf_ist_ax (D : Deklaration) (V : Vertrag D)
    {Γ : Ctx} {Λ : List (Res D)}
    (L : BibliotheksFunktion D) (a : D.Ax)
    (hDient : DientBibliothek D L a) :
    (∃ (args : Args D Γ Λ (D.aparams a)),
      D.aerg a = none ∧
      (∀ t, D.aschreibt a t = true → V.schreibt t = true) ∧
      (∀ g, D.agschreibt a g = true → V.gschreibt g = true) ∧
      (∀ t, D.aschreibt a t = true → darf D t Λ) ∧
      (∀ g, D.agschreibt a g = true → gdarf D g Λ)) ↔
    (∃ (args : Args D Γ Λ L.params) (last : Expr D Γ Λ L.nutzlast),
      L.erg = none ∧
      (∀ t, L.schreibt t = true → V.schreibt t = true) ∧
      (∀ g, L.gschreibt g = true → V.gschreibt g = true) ∧
      (∀ t, L.schreibt t = true → darf D t Λ) ∧
      (∀ g, L.gschreibt g = true → gdarf D g Λ)) := by
  obtain ⟨hap, herg, hschw, hgschw⟩ := hDient
  constructor
  · rintro ⟨args, hno, hw, hg, hd, hgd⟩
    rw [hap] at args
    obtain ⟨rest, last, _⟩ := args_unsnoc D L.params L.nutzlast args
    refine ⟨rest, last, herg ▸ hno, ?_, ?_, ?_, ?_⟩
    · intro t ht
      apply hw t
      rw [hschw t]
      exact ht
    · intro g hg'
      apply hg g
      rw [hgschw g]
      exact hg'
    · intro t ht
      apply hd t
      rw [hschw t]
      exact ht
    · intro g hg'
      apply hgd g
      rw [hgschw g]
      exact hg'
  · rintro ⟨rest, last, hno, hw, hg, hd, hgd⟩
    refine ⟨hap.symm ▸ args_snoc D rest last, ?_, ?_, ?_, ?_, ?_⟩
    · rw [herg]
      exact hno
    · intro t ht
      rw [hschw t] at ht
      exact hw t ht
    · intro g hg'
      rw [hgschw g] at hg'
      exact hg g hg'
    · intro t ht
      rw [hschw t] at ht
      exact hd t ht
    · intro g hg'
      rw [hgschw g] at hg'
      exact hgd g hg'

/-! ## 3. Witness fixture: `refD`'s konto shape with one axiom

    `refD` has `Ax := Empty`, so no axiom-shaped theorem admits a `refD`
    witness. `bibD` copies the reference shape (one two-slot `konto`
    table of `.int 0 100`, one guarding lock, one writer taking `.int
    0 10` and storing the cap `100`) and adds the one axiom the library
    call needs: ordinary parameter `.int 0 10` with payload `.int 0 100`
    appended. The F-machine run below (lock, writing leaf) is the same
    two steps as `refReachBF`'s first half. -/

/-- Signature of the writer: one `.int 0 10` parameter, no result, holds
    the lock, may write the table. -/
def bibSigW : Signatur Unit Empty Unit Empty where
  params := [.int 0 10]
  erg := none
  gruende := 0
  haelt := [()]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- The witness declaration: `refD`'s table, lock and writer, plus one
    axiom whose parameters are the ordinary parameter with the payload
    (`.int 0 100`) appended. -/
def bibD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => true
  ggeteilt := fun e => nomatch e
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => [.inl ()]
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => bibSigW
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Unit
  aparams := fun _ => [.int 0 10, .int 0 100]
  aerg := fun _ => none
  aschreibt := fun _ _ => true
  agschreibt := fun _ g => nomatch g
  Reg := Empty
  rtyp := fun r => nomatch r
  rklasse := fun r => nomatch r
  spiegel := fun r => nomatch r
  rzusage := fun r => nomatch r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t _ => by decide
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

/-- The writer function. -/
def bibW : bibD.Fn := ()

/-- The writer takes one `.int 0 10` parameter. -/
theorem bibW_params : bibD.params bibW = [.int 0 10] := rfl

/-- The writer returns nothing. -/
theorem bibW_erg : bibD.erg bibW = none := rfl

/-- The writer writes the table. -/
theorem bibW_schreibt : (vertragVon bibD bibW).schreibt () = true := rfl

/-- The axiom takes the ordinary parameter with the payload appended. -/
theorem bibAx_params : bibD.aparams () = [.int 0 10, .int 0 100] := rfl

/-- The axiom returns nothing. -/
theorem bibAx_erg : bibD.aerg () = none := rfl

/-! ## 4. Call arguments, the library record, and the program -/

/-- The table access is allowed holding the lock. -/
theorem bibDarf : darf bibD () [Res.held (D := bibD) ()] := by
  intro w h
  simp only [bibD] at h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  have hh : w ∈ bibD.braucht () := h
  rw [e] at hh ⊢
  exact List.mem_singleton.mpr rfl

/-- Index `0` into the two-slot table, in the writer context. -/
def bibIdx : Expr bibD [.int 0 10] [Res.held (D := bibD) ()]
    (.index (bibD.count ())) :=
  .weiter (by decide) (by decide) (.lit 0)

/-- The cap value `100` in range. -/
def bibHundert : Expr bibD [.int 0 10] [Res.held (D := bibD) ()] (.int 0 100) :=
  .weiter (by decide) (by decide) (.lit 100)

/-- The writer holds the lock: start equals end. -/
theorem bibW_start : Signatur.anfang bibD (bibD.signatur bibW) =
    [Res.held (D := bibD) ()] := rfl

/-- Same access right at the writer end holdings. -/
theorem bibDarfW : darf bibD () (vertragVon bibD bibW).ende := by
  have e : (vertragVon bibD bibW).ende = [Res.held (D := bibD) ()] := rfl
  rw [e]
  exact bibDarf

/-- The writer statement: `konto[0] := 100`. -/
def bibWriteSt : Stmt bibD (vertragVon bibD bibW) false [.int 0 10]
    (vertragVon bibD bibW).ende (vertragVon bibD bibW).ende :=
  .assignSlot () () bibIdx bibHundert (by cases () <;> rfl) bibDarfW

/-- The writer statement at the lock holdings. -/
def bibWriteStAt : Stmt bibD (vertragVon bibD bibW) false [.int 0 10]
    [Res.held (D := bibD) ()] [Res.held (D := bibD) ()] :=
  (by rfl : (vertragVon bibD bibW).ende = [Res.held (D := bibD) ()]) ▸
    bibWriteSt

/-- The writer body: write the cap, return. -/
def bibRumpfW :
    Endblock bibD (vertragVon bibD bibW) false [.int 0 10]
      [Res.held (D := bibD) ()] :=
  .cons bibWriteStAt (.ret .keine (by rfl))

/-- The writer requires `true`. -/
def bibReqW : Expr bibD (bibD.params bibW)
    (Signatur.anfang bibD (bibD.signatur bibW)) .bool :=
  .wahr

/-- The writer ensures the slot did not decrease (`old ≤ new`). -/
def bibEnsW : Expr bibD (ErgCtx (bibD.params bibW) (bibD.erg bibW))
    (vertragVon bibD bibW).ende .bool :=
  .le (.altSlot () () bibIdx bibDarfW)
    (.slot () () bibIdx bibDarfW)

/-- The program: one writer with its contract and write-return body. -/
def bibP : Programm bibD where
  invariante := fun i => nomatch i
  requires := fun _ => bibReqW
  ensures := fun _ => bibEnsW
  rumpf := fun _ => bibW_start ▸ bibRumpfW

/-- The witness oracle: the axiom answers the payload value `0` and moves
    no memory; no registers, nothing visible. The run below never fires
    the axiom, so the answer is never read. -/
def bibO : Orakel bibD where
  wirkt := fun _ σ _ => (σ, 0)
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

/-- The start memory: every slot reads `0`. -/
def bibSp0 : Speicher bibD :=
  ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- The declared library function: one ordinary `.int 0 10` parameter,
    payload `.int 0 100`, no result, writes the table. -/
def bibLib : BibliotheksFunktion bibD where
  params := [.int 0 10]
  nutzlast := .int 0 100
  erg := none
  schreibt := fun _ => true
  gschreibt := fun g => nomatch g

/-- The bridge holds: the axiom serves the library function. Every
    conjunct is computation (`rfl` after casing the one table). -/
theorem bibDient : DientBibliothek bibD bibLib () := by
  refine ⟨rfl, rfl, fun t => by cases t <;> rfl, fun g => nomatch g⟩

/-- The ordinary call argument: the parameter itself. -/
def bibArgs : Args bibD [.int 0 10] [Res.held (D := bibD) ()] [.int 0 10] :=
  .cons (.var .hier) .nil

/-- The payload argument: the cap `100`. -/
def bibLast : Expr bibD [.int 0 10] [Res.held (D := bibD) ()] (.int 0 100) :=
  .weiter (by decide) (by decide) (.lit 100)

/-! ## 5. The witness run: lock, then the writing leaf -/

/-- The call argument of the run: 7 in `.int 0 10`. -/
def bibRho7 : Env bibD (bibD.params bibW) :=
  bibW_params.symm ▸ (.cons ⟨7, by decide, by decide⟩ .nil :
    Env bibD [.int 0 10])

/-- Thread start: every thread runs the writer on 7. -/
def bibInit : Faden → Σ f : bibD.Fn, Env bibD (bibD.params f) :=
  fun _ => ⟨bibW, bibRho7⟩

/-- The start machine for the witness run. -/
def bibM0F : RufMaschineF bibD := RufStartF bibP bibSp0 bibInit

/-- The lock is free at the start: every trace is empty. -/
theorem bibFrei0F : RufFreiF bibM0F 0 (()) := by
  intro g hne hmem
  have e : (bibM0F.faeden g).spur = [] := rfl
  have hnil : offen (bibM0F.faeden g).spur = [] := by rw [e]; rfl
  have h2 : (()) ∈ ([] : List bibD.Lock) := hnil ▸ hmem
  exact (List.mem_nil_iff _).mp h2 |>.elim

/-- Thread 0 holds nothing yet. -/
theorem bibSelf0F : (() : bibD.Lock) ∉ offen (bibM0F.faeden 0).spur := by
  intro hmem
  have e : (bibM0F.faeden 0).spur = [] := rfl
  have hnil : offen (bibM0F.faeden 0).spur = [] := by rw [e]; rfl
  have h2 : (()) ∈ ([] : List bibD.Lock) := hnil ▸ hmem
  exact (List.mem_nil_iff _).mp h2 |>.elim

/-- Thread 0 holds nothing, so the rank side is vacuous. -/
theorem bibRang0F (K : bibD.Lock) (hK : K ∈ offen (bibM0F.faeden 0).spur) :
    bibD.rang K < bibD.rang (()) := by
  have e : (bibM0F.faeden 0).spur = [] := rfl
  have hnil : offen ([] : List (Ereignis bibD)) = [] := rfl
  rw [e, hnil, List.mem_nil_iff] at hK
  exact absurd hK (by decide)

/-- Step A: thread 0 takes the lock. -/
def bibM1F : RufMaschineF bibD :=
  ⟨bibM0F.speicher,
   rufUpdateF bibM0F.faeden 0
     ⟨(bibM0F.faeden 0).stapel, (bibM0F.faeden 0).kopf,
      Ereignis.nimmt () (offen (bibM0F.faeden 0).spur) :: (bibM0F.faeden 0).spur,
      (bibM0F.faeden 0).log⟩,
   bibM0F.lauf ++ rufEigenF 0 [Ereignis.nimmt () (offen (bibM0F.faeden 0).spur)],
   bibM0F.start⟩

theorem bibSchrittAF :
    RufSchrittF bibP bibO 0 bibM0F 0 bibM1F := by
  unfold bibM1F
  exact RufSchrittF.nimmt bibM0F 0 () bibSelf0F (fun K hK => bibRang0F K hK)
    bibFrei0F

theorem bibReachAF : RufErreichbarF bibP bibO 0 bibM0F bibM1F :=
  RufErreichbarF.schritt _ _ 0 RufErreichbarF.start bibSchrittAF

/-- Thread 0 holds the lock exactly after step A. -/
theorem bibM1Fhaelt :
    HeldGenau [Res.held (D := bibD) ()]
      (offen (bibM1F.faeden 0).spur) := by
  intro L
  have eL : L = () := by cases L <;> rfl
  have eH : offen (bibM1F.faeden 0).spur = [()] := rfl
  rw [eH, eL]
  constructor
  · intro hL
    have heq : Res.held (D := bibD) L = Res.held (D := bibD) () :=
      (List.mem_singleton.mp hL)
    cases heq
    exact List.mem_singleton.mpr rfl
  · intro hL
    have heq : L = () :=
      (List.mem_singleton.mp (eH ▸ hL))
    cases heq
    exact List.mem_singleton.mpr rfl

/-- The evaluated index: `0`. -/
def bibK0 : Int := 0

/-- The evaluated cap: `100` in range. -/
def bibV100 : Wert bibD (.int 0 100) := ⟨100, by decide, by decide⟩

/-- Step B: thread 0 fires the writing leaf `konto[0] := 100` under the
    stored `bibRho7`; the outcome stores the same environment. -/
def bibM2F : RufMaschineF bibD :=
  ⟨(((bibM1F.weltVon 0).lese [Res.held (D := bibD) ()]
      (bibIdx.orte ++ bibHundert.orte)).schreibSlot () [Res.held (D := bibD) ()]
      bibK0 () bibV100).speicher,
   rufUpdateF bibM1F.faeden 0
     ⟨(bibM1F.faeden 0).stapel,
      ⟨(bibM1F.faeden 0).kopf.f, (bibM1F.faeden 0).kopf.rho,
       (bibM1F.faeden 0).kopf.s0,
       ⟨false, [.int 0 10], [Res.held (D := bibD) ()], bibRho7,
        .ret (.keine (D := bibD) (Γ := [.int 0 10])
          (Λ := [Res.held (D := bibD) ()])) (by rfl)⟩⟩,
      (((bibM1F.weltVon 0).lese [Res.held (D := bibD) ()]
        (bibIdx.orte ++ bibHundert.orte)).schreibSlot () [Res.held (D := bibD) ()]
        bibK0 () bibV100).spur,
      (bibM1F.faeden 0).log⟩,
   bibM1F.lauf ++ rufEigenF 0
     [Ereignis.zugriff () true [Res.held (D := bibD) ()]
       (bibM1F.weltVon 0).haelt],
   bibM1F.start⟩

theorem bibSchrittBF : RufSchrittF bibP bibO 0 bibM1F 0 bibM2F := by
  have hhead : (bibM1F.faeden 0).kopf.rest =
      ⟨false, [.int 0 10], [Res.held (D := bibD) ()], bibRho7,
        .cons bibWriteStAt
          (.ret (.keine (D := bibD) (Γ := [.int 0 10])
            (Λ := [Res.held (D := bibD) ()])) (by rfl))⟩ := rfl
  have hstep : (execStmt bibO 0 keinRuf bibWriteStAt
      (bibM1F.weltVon 0) bibRho7) =
      Ausgang.ok (D := bibD) (V := vertragVon bibD bibW)
        (((bibM1F.weltVon 0).lese [Res.held (D := bibD) ()]
          (bibIdx.orte ++ bibHundert.orte)).schreibSlot ()
          [Res.held (D := bibD) ()] bibK0 () bibV100) bibRho7 := rfl
  have hneu : (((bibM1F.weltVon 0).lese [Res.held (D := bibD) ()]
      (bibIdx.orte ++ bibHundert.orte)).schreibSlot () [Res.held (D := bibD) ()]
      bibK0 () bibV100).spur =
      [Ereignis.zugriff () true [Res.held (D := bibD) ()]
        (bibM1F.weltVon 0).haelt] ++ (bibM1F.faeden 0).spur := rfl
  have hkn : ∀ (L : bibD.Lock) (h : List bibD.Lock),
      Ereignis.nimmt L h ∉ [Ereignis.zugriff () true
        [Res.held (D := bibD) ()] (bibM1F.weltVon 0).haelt] := by
    intro L h hm
    simp at hm
  exact RufSchrittF.blatt bibM1F 0 false [.int 0 10]
    [Res.held (D := bibD) ()] [Res.held (D := bibD) ()]
    bibWriteStAt _ bibRho7 rfl hhead bibM1Fhaelt _ _ _ hstep hneu hkn

theorem bibReachBF : RufErreichbarF bibP bibO 0 bibM0F bibM2F :=
  RufErreichbarF.schritt _ _ 0 bibReachAF bibSchrittBF

/-- `bibM0F` IS the start machine. -/
theorem bibM0F_start : bibM0F = RufStartF bibP bibSp0 bibInit := rfl

/-- The witness run: lock, then the writing leaf -- reached from the
    start state. -/
theorem bib_erreicht :
    RufErreichbarF bibP bibO 0 (RufStartF bibP bibSp0 bibInit) bibM2F := by
  rw [← bibM0F_start]
  exact bibReachBF

/-- The final memory carries the written cap at `konto[0]`. -/
theorem bibM2_slot : bibM2F.speicher.slots () 0 () = bibV100 := by
  have hhit := storeSlot_hit (D := bibD)
    ((bibM1F.weltVon 0).lese [Res.held (D := bibD) ()]
      (bibIdx.orte ++ bibHundert.orte)) () bibK0 () bibV100
  have k0 : bibK0 = (0 : Int) := rfl
  have hmem : bibM2F.speicher.slots () 0 () =
      ((((bibM1F.weltVon 0).lese [Res.held (D := bibD) ()]
        (bibIdx.orte ++ bibHundert.orte)).storeSlot ()
        bibK0 () bibV100).slots () 0 ()) := rfl
  rw [k0] at hhit
  rw [hmem, k0]
  exact hhit

/-- Memory really moved: `konto[0]` reads `100`, the start reads `0`. -/
theorem bib_schreibt : bibM2F.speicher.slots () 0 () ≠
    bibSp0.slots () 0 () := by
  have h100 := bibM2_slot
  have h0 : bibSp0.slots () 0 () =
      (⟨0, by decide, by decide⟩ : Wert bibD (bibD.typ () ())) := rfl
  rw [h100, h0]
  intro hcon
  have hn : (bibV100.n) = ((⟨0, by decide, by decide⟩ :
      Wert bibD (bibD.typ () ())).n) := congrArg Zahl.n hcon
  simp [bibV100] at hn

/-! ## 6. Witness: the bridge holds jointly on a non-degenerate program -/

/-- ZEUGE: all premises of `bibliotheksruf_ist_ax` hold JOINTLY -- the
    concrete declaration `bibD`, the writer's contract `V` (which writes
    `konto`), the bridge `bibDient`, the ordinary argument with the
    payload argument -- and the program is NON-DEGENERATE: the writer
    writes table `()` (`bibW_schreibt`) and the reached run `bib_erreicht`
    moves memory (slot `0 -> 100`, `bib_schreibt`). Every conjunct is
    used: the bridge feeds the equivalence, the writer fact and the run
    feed non-degeneracy. -/
theorem bibliotheksruf_ist_ax_zeuge :
    ∃ (V : Vertrag bibD),
      DientBibliothek bibD bibLib () ∧
      V.schreibt () = true ∧
      Nonempty (Args bibD [.int 0 10] [Res.held (D := bibD) ()]
        bibLib.params ×
        Expr bibD [.int 0 10] [Res.held (D := bibD) ()] bibLib.nutzlast) ∧
      ∃ (M : RufMaschineF bibD),
        RufErreichbarF bibP bibO 0 (RufStartF bibP bibSp0 bibInit) M ∧
        M.speicher.slots () 0 () ≠ bibSp0.slots () 0 () :=
  ⟨vertragVon bibD bibW, bibDient, bibW_schreibt, ⟨bibArgs, bibLast⟩,
    bibM2F, bib_erreicht, bib_schreibt⟩

/-!
CUTS:
- The equivalence covers the STATEMENT-position call (`axiomCall`,
  `D.aerg a = none` on the left, `L.erg = none` on the right). The
  binding-position call (`Stmt.bindAxiom`, `D.aerg a = some`) needs the
  same split with the result carried -- not stated here.
- `bibD` is not `refD`: `refD` has `Ax := Empty`, so no axiom-shaped
  theorem admits a `refD` witness. `bibD` copies the reference shape
  (two-slot `konto` of `.int 0 100`, one guarding lock, writer storing
  the cap `100`) and adds the one axiom; the run mirrors the first two
  steps of `refReachBF`.
- No contract discharge: neither machine gates on contracts, and no
  theorem connects the axiom answer to `ReqAmEintritt`/`EnsAmRueck`.
-/

#print axioms Gabbro.Grammatik.bibliotheksruf_ist_ax
#print axioms Gabbro.Grammatik.bibliotheksruf_ist_ax_zeuge
#print axioms Gabbro.Grammatik.bibDient
#print axioms Gabbro.Grammatik.bib_erreicht
#print axioms Gabbro.Grammatik.bib_schreibt

end Gabbro.Grammatik
