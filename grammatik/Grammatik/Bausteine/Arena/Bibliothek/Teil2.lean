module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineF
public import Grammatik.Bausteine.Arena.Bibliothek.Teil1

@[expose] public section

namespace Gabbro.Grammatik

theorem bibSchrittBF : RufSchrittF bibP bibO 0 bibM1F 0 bibM2F := by
  have hhead : (bibM1F.faeden 0).kopf.rest =
      ⟨false, [.int 0 10], [Res.held (D := bibD) ()], bibRho7,
        .cons bibWriteStAt
          (.ret (.empty (D := bibD) (Γ := [.int 0 10])
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
    simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at hm
  exact RufSchrittF.blatt bibM1F 0 false [.int 0 10]
    [Res.held (D := bibD) ()] [Res.held (D := bibD) ()]
    bibWriteStAt _ bibRho7 rfl hhead bibM1Fhaelt _ _ _ hstep hneu hkn

theorem bibReachBF : RufErreichbarF bibP bibO 0 bibM0F bibM2F :=
  RufErreichbarF.schritt _ _ 0 bibReachAF bibSchrittBF

/-- `bibM0F` IS the start machine. -/
theorem bibM0F_start : bibM0F = RufStartF bibP bibSp0 bibInit := by rfl

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
  simp only [bibV100, Int.reduceEq] at hn

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
