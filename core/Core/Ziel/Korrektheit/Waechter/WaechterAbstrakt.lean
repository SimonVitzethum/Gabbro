/-
  File:      core/Core/Ziel/Korrektheit/Waechter/WaechterAbstrakt.lean
  Subject:   ABSTRACTION from the computable guard analysis to `WaechterHalten`.

  If the static check accepts the code (`waechterPruefeCode`), every generated guard
  holds on every ideal run of the unit, no reachable cut contains an internal
  deadlock or a closed waiting set, and every lock held under a declared hold bound
  stays checker-eligible: `waechterAbstrakt`.

  The run invariants carry the whole-code bounds to all frames and the prefix
  bounds to frames certified to advance. A guard demand read at a satisfying frame
  meets the pinned guard row by `pruefeBedarf_gilt`. Deadlock freedom is vacuous:
  the elaborated system never blocks
  (`blockiert` is constantly false). The holder conjunct is vacuous: locks stay
  free, so its premise never holds.

  `WaechterFragmentVollstaendigAussage` asks for completeness on the named fragment.
  `waechterCode_keinEntscheider` records the entrance-scope obstruction.
-/
module

public import Core.Ziel.Korrektheit.Waechter.WaechterRahmen
public import Core.Ziel.Korrektheit.Waechter.WaechterBedarf
public import Core.Ziel.Korrektheit.Waechter.WaechterVorwaerts
public import Core.Maschine.Start
public import Core.Annahme.Waechter
public import Core.Ast.Semantik.Elaborierung
public import Core.Ast.Semantik.Runtime.Mehrkontext.System
public import Core.Ziel.Korrektheit.Beweise.BegleitZusammensetzung
public import Core.Ziel.Korrektheit.NichtAkzeptierteEinheit

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse

open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Ast
open Gabbro.Core.Maschine
open Gabbro.Core.Aussenfrage
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Classical

/-- A guard demand read at a satisfying frame meets the pinned guard row. -/
theorem pruefeBedarf_gilt (code : List Befehl) (b : Befehl) (frame : Gabbro.Core.Ast.Semantik.Rahmen)
    (h : RahmenErfuellt code frame)
    (hp : pruefeBedarf code b = true) (op : PartielleOperation) (args : Operanden op)
    (hg : b.guard frame = some ⟨op, args⟩) :
    waechterBedarf op args := by
  cases b with
  | teilen links => exact teilenBedarf_gilt code links frame h hp op args hg
  | liesArray basis element count =>
      exact liesArrayBedarf_gilt code basis element count frame h hp op args hg
  | textIndex basis capacity =>
      exact textIndexBedarf_gilt code basis capacity frame h hp op args hg
  | substring basis capacity =>
      exact substringBedarf_gilt code basis capacity frame h hp op args hg
  | literal _ _ => exact guard_none_absurd hg rfl
  | binaer _ _ => exact guard_none_absurd hg rfl
  | binden _ _ => exact guard_none_absurd hg rfl
  | wahrheitswert _ _ => exact guard_none_absurd hg rfl
  | lesen _ _ => exact guard_none_absurd hg rfl
  | negativ _ _ => exact guard_none_absurd hg rfl
  | negieren _ => exact guard_none_absurd hg rfl
  | verneinen _ => exact guard_none_absurd hg rfl
  | vergleichen _ _ => exact guard_none_absurd hg rfl
  | springeWenn _ _ _ => exact guard_none_absurd hg rfl
  | zuweisen _ _ _ => exact guard_none_absurd hg rfl
  | zurueck _ _ => exact guard_none_absurd hg rfl
  | springe _ => exact guard_none_absurd hg rfl
  | blockEnde _ => exact guard_none_absurd hg rfl
  | bindeWert _ _ _ => exact guard_none_absurd hg rfl
  | definiere _ _ _ _ _ _ _ _ => exact guard_none_absurd hg rfl
  | rufe _ _ _ => exact guard_none_absurd hg rfl
  | rueckVoid => exact guard_none_absurd hg rfl
  | pruefeMass _ => exact guard_none_absurd hg rfl
  | setzePasszahl _ _ => exact guard_none_absurd hg rfl
  | whileTest _ _ _ => exact guard_none_absurd hg rfl
  | forAnfang _ _ _ _ _ _ => exact guard_none_absurd hg rfl
  | forTest _ _ => exact guard_none_absurd hg rfl
  | forNaechster _ _ => exact guard_none_absurd hg rfl
  | zurueckSprung _ => exact guard_none_absurd hg rfl
  | starte _ => exact guard_none_absurd hg rfl
  | ende => exact guard_none_absurd hg rfl
  | baueArray _ _ _ => exact guard_none_absurd hg rfl
  | baueTupel _ _ => exact guard_none_absurd hg rfl
  | liesTupelfeld _ _ _ => exact guard_none_absurd hg rfl
  | bindeTupel _ _ _ => exact guard_none_absurd hg rfl
  | definiereRecord _ _ _ => exact guard_none_absurd hg rfl
  | baueRecord _ _ _ _ _ => exact guard_none_absurd hg rfl
  | liesRecordFeld _ _ _ _ _ => exact guard_none_absurd hg rfl
  | setzeRecordFeld _ _ _ _ _ _ => exact guard_none_absurd hg rfl
  | definiereVariante _ _ _ => exact guard_none_absurd hg rfl
  | baueVariante _ _ _ _ _ => exact guard_none_absurd hg rfl
  | waehleVariante _ _ _ _ _ => exact guard_none_absurd hg rfl
  | textLiteral _ _ => exact guard_none_absurd hg rfl
  | textConcat _ _ _ => exact guard_none_absurd hg rfl
  | textLength _ _ => exact guard_none_absurd hg rfl
  | definiereTraeger _ _ _ _ => exact guard_none_absurd hg rfl
  | optionIstBesetzt _ _ => exact guard_none_absurd hg rfl
  | definiereEffektgruppe _ => exact guard_none_absurd hg rfl
  | waehleUmgebung _ _ _ => exact guard_none_absurd hg rfl
  | bindeRegion _ _ => exact guard_none_absurd hg rfl
  | zugriff _ => exact guard_none_absurd hg rfl
  | faden _ => exact guard_none_absurd hg rfl
  | aussen _ => exact guard_none_absurd hg rfl
  | maskiere _ _ => exact guard_none_absurd hg rfl
  | prioritaet _ => exact guard_none_absurd hg rfl
  | sendeUnterbrechung _ _ => exact guard_none_absurd hg rfl
  | leiteLeitung _ _ _ => exact guard_none_absurd hg rfl

/-- The abstraction lemma: acceptance of the static analysis gives `WaechterHalten`
    over all ideal runs of the unit. The guard conjunct uses the appropriate frame
    invariant and `pruefeBedarf_gilt`. Deadlock freedom is vacuous because the
    elaborated system never blocks; the holder conjunct is vacuous because locks
    stay free. -/
theorem waechterAbstrakt (p : Fragment) (platform : Katalog.Plattform)
    (h : waechterPruefeCode p.code = true) : WaechterHalten (p.einheit platform) := by
  simp only [waechterPruefeCode, Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨hfre, guards⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro ρ hρ t op args hbed
    have hguard : (p.einheit platform).quelltabellen.guard (ρ.zeit.zustand t.val)
        op args := hbed
    obtain ⟨c, b, head, hdemand⟩ := hguard
    rcases guards with whole | forward
    · have hfr := (invariantAlle p platform hfre ρ hρ t.val).1 c
      have checked := List.all_eq_true.mp whole b (kopf_mem head)
      exact pruefeBedarf_gilt p.code b _ hfr checked op args hdemand
    · simp only [pruefeVorwaerts, Bool.and_eq_true] at forward
      let r := (ρ.zeit.zustand t.val).lokal c
      have lookup : p.code[r.pc]? = some b := Gabbro.Core.Ast.Semantik.kopf_code head
      have checked := List.all_eq_true.mp forward.2 (b, r.pc)
        (List.mk_mem_zipIdx_iff_getElem?.mpr lookup)
      change ((bedarfStellen b).isEmpty || pruefeBedarf (p.code.take r.pc) b) = true at checked
      have needs : (bedarfStellen b).isEmpty = false := by
        cases b <;> first | rfl | cases hdemand
      simp only [needs, Bool.false_or] at checked
      have frame := vorwaertsRahmen_lauf p platform forward.1 hfre ρ hρ t.val c
      exact pruefeBedarf_gilt (p.code.take r.pc) b r
        (frame.2 r.pc (kopf_aktiv head) (Nat.le_refl _)) checked op args hdemand
  · intro ρ hρ t
    intro hC
    obtain ⟨C, ⟨c, hcC⟩, hclosed⟩ := hC
    obtain ⟨b, hblock, _⟩ := hclosed c hcC
    exact False.elim hblock
  · intro ρ hρ t l holder hbes
    have hfree := (invariantAlle p platform hfre ρ hρ t.val).2 l
    rw [hfree] at hbes
    cases hbes

/-- The pinned completeness statement for the named fragment. Its premise refers
    to guards at reachable heads of a particular unit, which can depend on the
    unit's entrance scope even when the code is fixed. -/
def WaechterFragmentVollstaendigAussage : Prop :=
  ∀ (p : Fragment) (platform : Katalog.Plattform),
    waechterFragmentCode p.code = true → WaechterHalten (p.einheit platform) →
      waechterPruefeCode p.code = true

/-- The fragment statement is about a nonempty set of fragments: the empty unit
    lies on the fragment, its guards hold, and the analysis accepts it. -/
theorem WaechterFragmentVollstaendigAussage.erfuellbar :
    ∃ (p : Fragment) (platform : Katalog.Plattform),
      waechterFragmentCode p.code = true ∧ WaechterHalten (p.einheit platform) ∧
        waechterPruefeCode p.code = true := by
  refine ⟨fragment Ast.Category.unit trivialUnit, Katalog.Plattform.x86_64, ?_, ?_, ?_⟩
  · show waechterFragmentCode (fragment Ast.Category.unit trivialUnit).code = true
    have hcode : (fragment Ast.Category.unit trivialUnit).code =
        [Befehl.starte mainName, Befehl.ende] := rfl
    rw [hcode]
    rfl
  · exact (trivialUnit_akzeptiert Katalog.Plattform.x86_64).2.2
  · show waechterPruefeCode (fragment Ast.Category.unit trivialUnit).code = true
    have hcode : (fragment Ast.Category.unit trivialUnit).code =
        [Befehl.starte mainName, Befehl.ende] := rfl
    rw [hcode]
    rfl

/-- The fragment statement is load-bearing: the witness unit lies on the fragment
    while the analysis refuses it, so completeness does not hold vacuously. -/
theorem WaechterFragmentVollstaendigAussage.nichtTrivial :
    ∃ (p : Fragment) (platform : Katalog.Plattform),
      waechterFragmentCode p.code = true ∧ waechterPruefeCode p.code = false := by
  refine ⟨fragment Ast.Category.unit textIndexUnit, Katalog.Plattform.x86_64, ?_, ?_⟩
  · show waechterFragmentCode textIndexCode = true
    rw [textIndexUnit_code]
    rfl
  · show waechterPruefeCode textIndexCode = false
    rw [textIndexUnit_code]
    rfl

end Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse
