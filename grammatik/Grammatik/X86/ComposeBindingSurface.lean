/-
  Composition closing: binding-surface closing (lane 851).

  Producer/consumer interface closed here: the caller-side gate admission
  (`GateStub.torOkB` with the mov-establishment, the `0F 05`-suffix stub
  shape and the `-4095`-fence errno decode) produces an admitted caller
  stub, the checked entry predicate (`EntryState.eintrittOk`) produces an
  admitted entry state, and the source contract side (`ContractSites`)
  consumes both: a program-supplied binding body discharges its
  implementation obligation (`InlinePflicht` with `RufEnsCheck`) at the
  ACTUAL argument/result worlds. This file only composes already-accepted
  definitions and theorems; it re-proves no gate, entry, contract, decoder
  or memory fact and defines no second interpreter or executor. An OS gate
  number alone proves nothing.
-/
import Grammatik.X86.GateStub
import Grammatik.X86.EntryState
import Grammatik.X86.ContractSites

namespace Gabbro.Grammatik.X86

/-- CLOSING INTERFACE (producer/consumer): the binding surface admits a
    caller gate together with its stub bytes and an entry state: every
    decided caller check holds, no refusal shape fires (C186/C187/M140),
    the stub establishes the register map and ends in the trap, and the
    entry predicate holds. Generic over arbitrary admitted inputs. -/
def bindungsFlaecheOkB (t : TorDekl) (moves : List Befehl) (stub : List Byte)
    (wartetZeiger : List Nat) (werte : List (Nat × StubenWert))
    (p : Profil) (bild : Bild) (bias : Nat) (art : EintrittArt)
    (z : EintrittZustand) : Bool :=
  torOkB t && !c186VerweigertB t && !c187VerweigertB t &&
    !m140VerweigertB wartetZeiger werte &&
    bindungErstelltB t moves && stubEndsTrapB stub &&
    eintrittOk p bild bias art z

/-- BINDING-SURFACE CLOSING, generic over arbitrary admitted inputs: an
    admitted caller stub plus an admitted entry state plus one successful
    source call at actual values close the surface -- the composed
    admission holds AND the program-supplied body discharges its
    implementation obligation (`InlinePflicht`) with the return contract
    at the actual result (`RufEnsCheck`). Composes
    `inlinePflicht_aus_rufAt`, `rufAt_ok_gibt_ens` and the seven decided
    admission legs; no gate, entry, contract or memory fact is re-proved
    here. -/
theorem ComposeBindingSurface_verbindung
    {D : Deklaration} (P : Programm D) (O : Orakel D) (passes fuel : Nat)
    (caller g : D.Fn) (Λ : List (Res D))
    (hp : RufPasst D (vertragVon D caller) (D.signatur g) Λ)
    (hr : D.gruende g = 0)
    (σ : World D) (ρ : Env D (D.params g))
    (sread : World D)
    (hread : sread = σ.lese (Signatur.anfang D (D.signatur g))
      (P.requires g).orte)
    (hreq : wahr? (eval sread (P.requires g) sread ρ) = true)
    (σ1 : World D) (v : ErgVal D (D.erg g))
    (hbody : execEnd (V := vertragVon D g) O passes (rufAt P O passes fuel)
      (P.rumpf g) sread ρ = EndAusgang.zurueck σ1 v)
    (sret : World D)
    (hret : sret = σ1.lese (vertragVon D g).ende (P.ensures g).orte)
    (sinv : World D)
    (hsinv : sinv = (D.invs.filter (schuldet g)).foldl
      (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte) sret)
    (hinv : D.invs.find? (fun i => schuldet g i &&
      !wahr? (eval sinv (P.invariante i) sinv .nil)) = none)
    (h : rufAt P O passes (fuel + 1) g σ ρ =
      RufAusgang.ok (D := D) (f := g) sinv v)
    (t : TorDekl) (moves : List Befehl) (stub : List Byte)
    (wartetZeiger : List Nat) (werte : List (Nat × StubenWert))
    (p : Profil) (bild : Bild) (bias : Nat) (art : EintrittArt)
    (z : EintrittZustand)
    (hTor : torOkB t = true)
    (h186 : c186VerweigertB t = false)
    (h187 : c187VerweigertB t = false)
    (hM140 : m140VerweigertB wartetZeiger werte = false)
    (hMoves : bindungErstelltB t moves = true)
    (hStub : stubEndsTrapB stub = true)
    (hEntry : eintrittOk p bild bias art z = true) :
    bindungsFlaecheOkB t moves stub wartetZeiger werte p bild bias art z
      = true ∧
    Nonempty (InlinePflicht P caller g Λ) ∧
    RufEnsCheck P g sread sret ρ v := by
  have hens := rufAt_ok_gibt_ens P O passes fuel g σ ρ sread hread hreq
    σ1 v hbody sret hret sinv hsinv hinv sinv h
  have hpfl : Nonempty (InlinePflicht P caller g Λ) :=
    ⟨inlinePflicht_aus_rufAt P O passes fuel caller g Λ hp hr σ ρ sread
      hread hreq σ1 v hbody sret hret sinv hsinv hinv h⟩
  refine ⟨?_, hpfl, hens.1⟩
  simp [bindungsFlaecheOkB, hTor, h186, h187, hM140, hMoves, hStub, hEntry]

/-- OS NAMES PROVE NOTHING: the refused gate carries the witness gate
    number, yet the composed surface refuses it in every stub/entry
    context. A gate name, an `assume` item or any named premise alone
    discharges no implementation obligation. Uses the accepted
    duplicate-register refusal. -/
theorem osName_beweist_nichts (moves : List Befehl) (stub : List Byte)
    (wartetZeiger : List Nat) (werte : List (Nat × StubenWert))
    (p : Profil) (bild : Bild) (bias : Nat) (art : EintrittArt)
    (z : EintrittZustand) :
    torDoppelt.nummer = schreibTor.nummer ∧
    bindungsFlaecheOkB torDoppelt moves stub wartetZeiger werte p bild bias
      art z = false := by
  have hTor : torOkB torDoppelt = false := by
    simp [torOkB, torDoppelt_verweigert]
  refine ⟨rfl, ?_⟩
  simp [bindungsFlaecheOkB, hTor]

/-- PLANTED REFUSAL (C186 leg): a region answer without its `or R` channel
    refuses the composed surface in every stub/entry context. -/
theorem bindung_verweigert_c186 (moves : List Befehl) (stub : List Byte)
    (wartetZeiger : List Nat) (werte : List (Nat × StubenWert))
    (p : Profil) (bild : Bild) (bias : Nat) (art : EintrittArt)
    (z : EintrittZustand) :
    bindungsFlaecheOkB torRegionOhneOr moves stub wartetZeiger werte p bild
      bias art z = false := by
  simp [bindungsFlaecheOkB, torRegionOhneOr_verweigert]

/-- PLANTED REFUSAL (C187 leg): a stack gate with fewer than two free
    trampoline registers refuses the composed surface in every
    stub/entry context. -/
theorem bindung_verweigert_c187 (moves : List Befehl) (stub : List Byte)
    (wartetZeiger : List Nat) (werte : List (Nat × StubenWert))
    (p : Profil) (bild : Bild) (bias : Nat) (art : EintrittArt)
    (z : EintrittZustand) :
    bindungsFlaecheOkB torStapelOhneTrampolin moves stub wartetZeiger werte
      p bild bias art z = false := by
  simp [bindungsFlaecheOkB, torStapelOhneTrampolin_verweigert]

/-- PLANTED REFUSAL (M140 leg): a bare number where a pointer is expected
    refuses the composed surface in every stub/entry context. -/
theorem bindung_verweigert_m140 (moves : List Befehl) (stub : List Byte)
    (p : Profil) (bild : Bild) (bias : Nat) (art : EintrittArt)
    (z : EintrittZustand) :
    bindungsFlaecheOkB schreibTor moves stub [1]
      [(0, .zahl 5), (1, .zahl 7)] p bild bias art z = false := by
  unfold bindungsFlaecheOkB
  rw [m140_geschmiedet]
  simp

/-- PLANTED REFUSAL (entry leg): a call-boundary stack that is not
    16-aligned refuses the composed surface whatever the admitted gate. -/
theorem bindung_verweigert_eintritt (moves : List Befehl) (stub : List Byte)
    (wartetZeiger : List Nat) (werte : List (Nat × StubenWert)) :
    bindungsFlaecheOkB schreibTor moves stub wartetZeiger werte .p48
      zeugenBild 0 .hostedMain zeugenEintrittSchief = false := by
  simp [bindungsFlaecheOkB, zeugenStapelSchief_verweigert]

/-- ADMISSION IS NOT A CONTRACT: the witness stub and entry are admitted
    while the entry contract at the start world is refused. No admitted
    gate, stub shape or entry state smuggles the user-logic obligation:
    the implementation proof at actual values is still owed. -/
theorem zulassungOhneVertrag :
    bindungsFlaecheOkB schreibTor zeugenMoves zeugenStub [] [(0, .zahl 5)]
      .p48 zeugenBild 0 .hostedMain zeugenEintrittHosted = true ∧
    ¬ ReqAmEintritt eP ePruefe (eSp.welt []) .nil := by
  refine ⟨?_, pruefe_requires_falsch_am_start⟩
  have h187 : c187VerweigertB schreibTor = false := by decide
  have hm140 : m140VerweigertB [] [(0, .zahl 5)] = false := m140_zahl_erlaubt
  unfold bindungsFlaecheOkB
  rw [schreibTor_ok, schreibTor_kein_c186, h187, hm140, zeugenMoves_ok,
    zeugenStub_trap, zeugenEintrittHosted_ok]
  simp

/-- JOINT WITNESS: every premise of `ComposeBindingSurface_verbindung`
    holds jointly on the non-degenerate table-writing fixture -- the real
    `setze` call runs clean with its entry contract at the actual
    arguments, the witness stub and entry are admitted, the implementation
    obligation is discharged with the `0 -> 5` memory change on a reached
    machine run, a real X86 byte write reads back with an observable
    change, and EBADF decodes to reason 0. -/
theorem ComposeBindingSurface_verbindung_zeuge :
    ∃ (sread σ1 sret sinv σ' : World eD) (v : ErgVal eD (eD.erg eSetze)),
      sread = ((((eSp.welt []).lese [] []).lese
        (Signatur.anfang eD (eD.signatur eSetze))
        (eP.requires eSetze).orte)) ∧
      wahr? (eval sread (eP.requires eSetze) sread .nil) = true ∧
      execEnd (V := vertragVon eD eSetze) eO 0 (rufAt eP eO 0 0)
        (eP.rumpf eSetze) sread .nil = EndAusgang.zurueck σ1 v ∧
      sret = σ1.lese (vertragVon eD eSetze).ende (eP.ensures eSetze).orte ∧
      sinv = (eD.invs.filter (schuldet eSetze)).foldl
        (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte) sret ∧
      (eD.invs.find? (fun i => schuldet eSetze i &&
        !wahr? (eval sinv (eP.invariante i) sinv .nil))) = none ∧
      rufAt eP eO 0 1 eSetze ((eSp.welt []).lese [] []) .nil =
        RufAusgang.ok σ' v ∧
      bindungsFlaecheOkB schreibTor zeugenMoves zeugenStub [] [(0, .zahl 5)]
        .p48 zeugenBild 0 .hostedMain zeugenEintrittHosted = true ∧
      Nonempty (InlinePflicht eP eHaupt eSetze []) ∧
      RufEnsCheck eP eSetze sread sret .nil v ∧
      (eD.signatur eSetze).schreibt () = true ∧
      ((((eSp.welt []).lese [] []).slots () 0 ()).n = 0 ∧
        (sret.slots () 0 ()).n = 5) ∧
      (∃ M : RufMaschineG eD,
        RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M ∧
        (eSp.slots () 0 ()).n = 0) ∧
      (∃ (m m' : Speicher) (a : Adresse) (w : Wort),
        w ≠ 0 ∧ write64 m a w = some m' ∧ read64 m' a = some w ∧
          m.bytes a ≠ m'.bytes a) ∧
      torKlassifiziere schreibTor.errors 0 8192 (-9) = .grund 0 := by
  obtain ⟨sread, σ1, sret, sinv, σ', v, hread0, hreq0, hbody, hret0, hsinv0,
    hinv0, hok, _hens1, hschr, hmem, _hpfl⟩ := rufAt_ok_gibt_ens_zeuge
  obtain ⟨M, hr, hsl0, _hrest⟩ := vertragStandort_lauf_zeuge
  have h187 : c187VerweigertB schreibTor = false := by decide
  have heq : σ' = sinv :=
    (rufAt_ok_gibt_ens eP eO 0 0 eSetze ((eSp.welt []).lese [] []) .nil
      sread hread0 hreq0 σ1 v hbody sret hret0 sinv hsinv0 hinv0 σ' hok).2
  have hok' : rufAt eP eO 0 (0 + 1) eSetze ((eSp.welt []).lese [] []) .nil =
      RufAusgang.ok sinv v := by
    rw [← heq]
    exact hok
  have hconn := ComposeBindingSurface_verbindung eP eO 0 0 eHaupt eSetze []
    eHpSetze rfl ((eSp.welt []).lese [] []) .nil sread hread0 hreq0 σ1 v
    hbody sret hret0 sinv hsinv0 hinv0 hok' schreibTor zeugenMoves zeugenStub
    [] [(0, .zahl 5)] .p48 zeugenBild 0 .hostedMain zeugenEintrittHosted
    schreibTor_ok schreibTor_kein_c186 h187 m140_zahl_erlaubt zeugenMoves_ok
    zeugenStub_trap zeugenEintrittHosted_ok
  obtain ⟨hadm, hpfl2, hens2⟩ := hconn
  exact ⟨sread, σ1, sret, sinv, σ', v, hread0, hreq0, hbody, hret0, hsinv0,
    hinv0, hok, hadm, hpfl2, hens2, hschr, hmem, ⟨M, hr, hsl0⟩,
    torStub_zeuge.2.2.2.2, torStub_zeuge.2.2.2.1⟩

/- CUTS:
   Proved here: the binding-surface closing (`ComposeBindingSurface_verbindung`):
   an admitted caller stub plus an admitted entry state plus one successful
   source call at actual values close the surface -- the composed admission
   holds AND the program-supplied body discharges its implementation
   obligation (`InlinePflicht`) with the return contract at the actual
   result (`RufEnsCheck`); the joint witness below (non-degenerate
   table-writing fixture, reached machine run, `0 -> 5` source memory
   change, X86 byte memory change, errno decode); the planted refusals
   (OS gate number alone, C186/C187/M140/entry legs, admission without
   contract).
   NOT proved here, and not claimed:
   - No source-to-byte correspondence: that a checked source `syscall`
     declaration lowers to these stub bytes is OPEN (IR/lowering closure
     waits on lane 287; see `ContractSites` CUTS).
   - No TSO/W/GX bridge, no budget/cost transfer (`budget_simulation`
     stays OPEN; see `CostSummary` CUTS), no hardware correspondence, no
     kernel behaviour (user logic, never an assumption).
   - No decoder coverage beyond the accepted pins: patched-site
     re-decoding and wider-family canonical closing belong to the
     validator/decoder owners (see `ValidatorSkeleton`/`ExtendedExecution`
     CUTS).
-/

#print axioms bindungsFlaecheOkB
#print axioms ComposeBindingSurface_verbindung
#print axioms ComposeBindingSurface_verbindung_zeuge
#print axioms osName_beweist_nichts
#print axioms bindung_verweigert_c186
#print axioms bindung_verweigert_c187
#print axioms bindung_verweigert_m140
#print axioms bindung_verweigert_eintritt
#print axioms zulassungOhneVertrag

end Gabbro.Grammatik.X86
