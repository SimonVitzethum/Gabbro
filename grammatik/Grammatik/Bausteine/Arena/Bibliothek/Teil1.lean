module
public import Grammatik.Bausteine.Arena.Bibliothek.Teil1Basis
import all Grammatik.Bausteine.Arena.Bibliothek.Teil1Basis

public import Grammatik.Logik.Ruf.Maschine.RufMaschineF

@[expose] public section



namespace Gabbro.Grammatik
/-- The writer function. -/
def bibW : bibD.Fn := ()

/-- The writer takes one `.int 0 10` parameter. -/
theorem bibW_params : bibD.params bibW = [.int 0 10] := by rfl

/-- The writer returns nothing. -/
theorem bibW_erg : bibD.erg bibW = none := by rfl

/-- The writer writes the table. -/
theorem bibW_schreibt : (vertragVon bibD bibW).schreibt () = true := by rfl

/-- The axiom takes the ordinary parameter with the payload appended. -/
theorem bibAx_params : bibD.aparams () = [.int 0 10, .int 0 100] := by rfl

/-- The axiom returns nothing. -/
theorem bibAx_erg : bibD.aerg () = none := by rfl

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
  .widen (by decide) (by decide) (.lit 0)

/-- The cap value `100` in range. -/
def bibHundert : Expr bibD [.int 0 10] [Res.held (D := bibD) ()] (.int 0 100) :=
  .widen (by decide) (by decide) (.lit 100)

/-- The writer holds the lock: start equals end. -/
theorem bibW_start : Signatur.anfang bibD (bibD.signatur bibW) =
    [Res.held (D := bibD) ()] := by rfl

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
  .cons bibWriteStAt (.ret .empty (by rfl))

/-- The writer requires `true`. -/
def bibReqW : Expr bibD (bibD.params bibW)
    (Signatur.anfang bibD (bibD.signatur bibW)) .bool :=
  .tru

/-- The writer ensures the slot did not decrease (`old ≤ new`). -/
def bibEnsW : Expr bibD (ErgCtx (bibD.params bibW) (bibD.erg bibW))
    (vertragVon bibD bibW).ende .bool :=
  .le (.oldS () () bibIdx bibDarfW)
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
  wirktL := fun _ σ _ => ({ σ with spur := [] }, 0)
  regLiesL := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbarL := fun g => nomatch g

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
  .cons (.var .here) .nil

/-- The payload argument: the cap `100`. -/
def bibLast : Expr bibD [.int 0 10] [Res.held (D := bibD) ()] (.int 0 100) :=
  .widen (by decide) (by decide) (.lit 100)

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
        .ret (.empty (D := bibD) (Γ := [.int 0 10])
          (Λ := [Res.held (D := bibD) ()])) (by rfl)⟩⟩,
      (((bibM1F.weltVon 0).lese [Res.held (D := bibD) ()]
        (bibIdx.orte ++ bibHundert.orte)).schreibSlot () [Res.held (D := bibD) ()]
        bibK0 () bibV100).spur,
      (bibM1F.faeden 0).log⟩,
   bibM1F.lauf ++ rufEigenF 0
     [Ereignis.zugriff () true [Res.held (D := bibD) ()]
       (bibM1F.weltVon 0).haelt],
   bibM1F.start⟩

end Gabbro.Grammatik
