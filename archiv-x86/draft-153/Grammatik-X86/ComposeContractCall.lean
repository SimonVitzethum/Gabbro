/-
  File:      Grammatik/X86/ComposeContractCall.lean
  Subject:   COMPOSITION CLOSING: contract-at-call closing (lane 831).

  Producer/consumer interface closed here (nothing re-proved, no new
  interpreter or executor):
  - Producer (source, lane 546 `ContractSites`): a clean direct call
    yields `requires` at the actual arguments (`callSite_vorOk`),
    `ensures` at the actual result (`rufAt_ok_gibt_ens`) and the
    discharged `InlinePflicht` (`inlinePflicht_aus_rufAt`).
  - Ghost (log, lane 310 `AufrufOpt` vocabulary): the call's return
    ghost event `RufEreignisF.rueck` with actual values is visible in
    the reached thread log. Identical contracts without that event
    refuse (`ComposeContractCall_ohne_geist_verweigert`, planted
    `ComposeContractCall_geistlos_verweigert_zeuge`).
  - Consumer (caller, lanes 346/349 `GateStub`/`ValidatorSkeleton`):
    admitted gate declaration (`torOkB`), established stub moves
    (`bindungErstelltB`), trap suffix (`stubEndsTrapB`) and the
    pointer-operand mirror (`valZeigerOk`).
-/
import Grammatik.X86.ContractSites
import Grammatik.X86.GateStub
import Grammatik.X86.ValidatorSkeleton

namespace Gabbro.Grammatik.X86

variable {D : Deklaration}

/-- Composed call-site closing for one direct call of `g` from `caller`:
    contracts at their place with actual values, the discharged inline
    obligation, the call's return ghost event in the reached thread log,
    the admitted caller-side gate stub, and the reached run itself. -/
def rufSchluss (P : Programm D) (O : Orakel D) (passes : Nat)
    (caller g : D.Fn) (Λ : List (Res D))
    (ρ : Env D (D.params g)) (sread sret : World D) (v : ErgVal D (D.erg g))
    (log : List (RufEreignisF D)) (M : RufMaschineG D)
    (sp : Gabbro.Grammatik.Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (t : TorDekl) (moves : List Befehl) (stub : List Byte)
    (wartetZeiger : List Nat) (werte : List (Nat × StubenWert)) : Prop :=
  ReqAmEintritt P g sread ρ ∧
  RufEnsCheck P g sread sret ρ v ∧
  Nonempty (InlinePflicht P caller g Λ) ∧
  (∃ rhoR vR wR bR, RufEreignisF.rueck g rhoR vR wR bR ∈ log) ∧
  (torOkB t = true ∧ bindungErstelltB t moves = true ∧
    stubEndsTrapB stub = true ∧ valZeigerOk wartetZeiger werte = true) ∧
  (RufErreichbarG P O passes (RufStartG P sp init) M ∧ (M.faeden 0).log = log)

/-! ## 1. The closing step.

    From one clean direct call: the entry half is derived through the
    `execStmt` call arm (`callSite_vorOk`), the return half and the
    inline discharge through the shared `rufAt` unfolding
    (`rufAt_ok_gibt_ens`, `inlinePflicht_aus_rufAt`); the ghost half is
    the call's return event in the reached log, the consumer half the
    admitted gate stub. Nothing here re-proves a producer lemma. -/

/-- CLOSING: one successful direct call yields the full composed
    contract-at-call closing -- requires at the actual arguments,
    ensures at the actual result, the discharged inline obligation,
    the return ghost event in the reached log, and the admitted
    caller-side gate. Every premise is used below. -/
theorem ComposeContractCall_verbindung (P : Programm D) (O : Orakel D)
    (passes : Nat) (caller g : D.Fn) (Λa : List (Res D))
    {l : Bool} {Γ : Ctx} {args : Args D Γ Λa (D.params g)}
    (hp : RufPasst D (vertragVon D caller) (D.signatur g) Λa)
    (hr : D.gruende g = 0)
    {σ : World D} {ρ₀ : Env D Γ} {σ' : World D} {ρ₀' : Env D Γ}
    (fe fr : Nat)
    (hexec : execStmt (V := vertragVon D caller) O passes (rufAt P O passes fe)
      (Stmt.call (V := vertragVon D caller) (l := l) g args hp hr) σ ρ₀ =
      .ok σ' ρ₀')
    (sread : World D)
    (hread : sread = (σ.lese Λa args.orte).lese
      (Signatur.anfang D (D.signatur g)) (P.requires g).orte)
    (hreq : wahr? (eval sread (P.requires g) sread
      (evalArgs (σ.lese Λa args.orte) args (σ.lese Λa args.orte) ρ₀)) = true)
    (σ₁ : World D) (v : ErgVal D (D.erg g))
    (hbody : execEnd (V := vertragVon D g) O passes (rufAt P O passes fr)
      (P.rumpf g) sread
      (evalArgs (σ.lese Λa args.orte) args (σ.lese Λa args.orte) ρ₀) =
      EndAusgang.zurueck σ₁ v)
    (sret : World D)
    (hret : sret = σ₁.lese (vertragVon D g).ende (P.ensures g).orte)
    (sinv : World D)
    (hsinv : sinv = (D.invs.filter (schuldet g)).foldl
      (fun σ'' i => σ''.lese (invSicht D i) (P.invariante i).orte) sret)
    (hinv : D.invs.find? (fun i => schuldet g i &&
      !wahr? (eval sinv (P.invariante i) sinv .nil)) = none)
    (h : rufAt P O passes (fr + 1) g (σ.lese Λa args.orte)
      (evalArgs (σ.lese Λa args.orte) args (σ.lese Λa args.orte) ρ₀) =
      RufAusgang.ok (D := D) (f := g) sinv v)
    (log : List (RufEreignisF D))
    (hgeist : ∃ rhoR vR wR bR, RufEreignisF.rueck g rhoR vR wR bR ∈ log)
    (t : TorDekl) (moves : List Befehl) (stub : List Byte)
    (wartetZeiger : List Nat) (werte : List (Nat × StubenWert))
    (htor : torOkB t = true)
    (hmoves : bindungErstelltB t moves = true)
    (hstub : stubEndsTrapB stub = true)
    (hzeiger : valZeigerOk wartetZeiger werte = true)
    (M : RufMaschineG D)
    (sp : Gabbro.Grammatik.Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hreach : RufErreichbarG P O passes (RufStartG P sp init) M)
    (hlog : (M.faeden 0).log = log) :
    rufSchluss P O passes caller g Λa
      (evalArgs (σ.lese Λa args.orte) args (σ.lese Λa args.orte) ρ₀)
      sread sret v log M sp init t moves stub wartetZeiger werte := by
  have hentry := callSite_vorOk P O passes fe hexec
  rw [← hread] at hentry
  have hens := (rufAt_ok_gibt_ens P O passes fr g (σ.lese Λa args.orte)
    (evalArgs (σ.lese Λa args.orte) args (σ.lese Λa args.orte) ρ₀)
    sread hread hreq σ₁ v hbody sret hret sinv hsinv hinv sinv h).1
  have hpfl : Nonempty (InlinePflicht P caller g Λa) :=
    ⟨inlinePflicht_aus_rufAt P O passes fr caller g Λa hp hr
      (σ.lese Λa args.orte)
      (evalArgs (σ.lese Λa args.orte) args (σ.lese Λa args.orte) ρ₀)
      sread hread hreq σ₁ v hbody sret hret sinv hsinv hinv h⟩
  exact ⟨hentry, hens, hpfl, hgeist,
    ⟨htor, hmoves, hstub, hzeiger⟩, ⟨hreach, hlog⟩⟩

/-! ## 2. Refusal: identical contracts without ghost events.

    The closing carries the call's return ghost event. Where the
    reached log holds no such event, the alleged closing is refused --
    even with the very same contracts and the very same admitted gate.
    Both premises are used: the ghost conjunct of the alleged closing
    against the absence fact. -/

/-- REFUSAL: a closing alleged over a log with no return ghost event
    for `g` is impossible. -/
theorem ComposeContractCall_ohne_geist_verweigert (P : Programm D)
    (O : Orakel D) (passes : Nat) (caller g : D.Fn) (Λ : List (Res D))
    (ρ : Env D (D.params g)) (sread sret : World D) (v : ErgVal D (D.erg g))
    (log : List (RufEreignisF D)) (M : RufMaschineG D)
    (sp : Gabbro.Grammatik.Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (t : TorDekl) (moves : List Befehl) (stub : List Byte)
    (wartetZeiger : List Nat) (werte : List (Nat × StubenWert))
    (hfehlt : ∀ rhoR vR wR bR,
      RufEreignisF.rueck g rhoR vR wR bR ∉ log)
    (hschluss : rufSchluss P O passes caller g Λ ρ sread sret v log M sp
      init t moves stub wartetZeiger werte) :
    False := by
  obtain ⟨_, _, _, hgeist, _, _⟩ := hschluss
  obtain ⟨rhoR, vR, wR, bR, hmem⟩ := hgeist
  exact hfehlt rhoR vR wR bR hmem

/-! ## 3. Joint witness: every premise jointly on a table-writing run.

    All `rfl` reductions below are the exact reductions the producer
    witnesses already perform: the entry equation is `callSite_vorOk_zeuge`'s
    (`fe = 1`), the body/`rufAt` pair is `rufAt_ok_gibt_ens_zeuge`'s
    (`fr = 0`); the ghost event, the `0 -> 5` memory change, the entry
    contract and the order leg come from `vertragStandort_lauf_zeuge` on
    one reached run; the gate facts are decided; the target memory change
    is `write_read_zeuge`. -/

/-- JOINT WITNESS (`ComposeContractCall_verbindung_zeuge`): every premise
    of `ComposeContractCall_verbindung` holds jointly on the real `setze`
    call -- clean execution, requires at the actual arguments, ensures at
    the actual result, the return ghost event in the reached log, the
    admitted gate, the reached run -- hence the composed closing, on a
    non-degenerate table-writing program with a memory-changing run
    (`0` at the start, `5` at the entry world) and a target-side
    write/read change. -/
theorem ComposeContractCall_verbindung_zeuge :
    ∃ (args : Args eD [] [] (eD.params eSetze))
      (σ σ' : World eD) (ρ₀ ρ₀' : Env eD [])
      (sread σ₁ sret sinv : World eD) (v : ErgVal eD (eD.erg eSetze))
      (log : List (RufEreignisF eD)) (M : RufMaschineG eD),
      execStmt (V := vertragVon eD eHaupt) eO 0 (rufAt eP eO 0 1)
        (Stmt.call (V := vertragVon eD eHaupt) (l := false) eSetze args
          eHpSetze rfl) σ ρ₀ = .ok σ' ρ₀' ∧
      sread = (σ.lese [] args.orte).lese
        (Signatur.anfang eD (eD.signatur eSetze))
        (eP.requires eSetze).orte ∧
      wahr? (eval sread (eP.requires eSetze) sread
        (evalArgs (σ.lese [] args.orte) args (σ.lese [] args.orte) ρ₀)) =
        true ∧
      execEnd (V := vertragVon eD eSetze) eO 0 (rufAt eP eO 0 0)
        (eP.rumpf eSetze) sread
        (evalArgs (σ.lese [] args.orte) args (σ.lese [] args.orte) ρ₀) =
        EndAusgang.zurueck σ₁ v ∧
      sret = σ₁.lese (vertragVon eD eSetze).ende (eP.ensures eSetze).orte ∧
      sinv = (eD.invs.filter (schuldet eSetze)).foldl
        (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte) sret ∧
      (eD.invs.find? (fun i => schuldet eSetze i &&
        !wahr? (eval sinv (eP.invariante i) sinv .nil))) = none ∧
      rufAt eP eO 0 1 eSetze (σ.lese [] args.orte)
        (evalArgs (σ.lese [] args.orte) args (σ.lese [] args.orte) ρ₀) =
        RufAusgang.ok sinv v ∧
      (∃ rhoR vR wR bR,
        RufEreignisF.rueck eSetze rhoR vR wR bR ∈ log) ∧
      torOkB schreibTor = true ∧
      bindungErstelltB schreibTor zeugenMoves = true ∧
      stubEndsTrapB zeugenStub = true ∧
      valZeigerOk [1] [(0, .zahl 5), (1, .zeiger 0x2000 8)] = true ∧
      RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M ∧
      (M.faeden 0).log = log ∧
      rufSchluss eP eO 0 eHaupt eSetze []
        (evalArgs (σ.lese [] args.orte) args (σ.lese [] args.orte) ρ₀)
        sread sret v log M eSp eInit schreibTor zeugenMoves zeugenStub
        [1] [(0, .zahl 5), (1, .zeiger 0x2000 8)] ∧
      (eSp.slots () 0 ()).n = 0 ∧
      (eD.signatur eSetze).schreibt () = true ∧
      (∃ w0 rho0, (w0.slots () 0 ()).n = 5 ∧
        ReqAmEintritt eP ePruefe w0 rho0) ∧
      (∃ (m m' : Speicher) (a : Adresse) (v : Wort),
        v ≠ 0 ∧ write64 m a v = some m' ∧ read64 m' a = some v ∧
          m.bytes a ≠ m'.bytes a) := by
  have hexec : ∃ σ' ρ₀', execStmt (V := vertragVon eD eHaupt) eO 0
      (rufAt eP eO 0 1)
      (Stmt.call (V := vertragVon eD eHaupt) (l := false) eSetze
        (.nil : Args eD [] [] (eD.params eSetze)) eHpSetze rfl)
      ((eSp.welt []).lese [] []) .nil = .ok σ' ρ₀' := ⟨_, _, rfl⟩
  obtain ⟨σ', ρ₀', hexec⟩ := hexec
  have hreq0 : wahr? (eval
      ((((eSp.welt []).lese [] []).lese []
        ((.nil : Args eD [] [] (eD.params eSetze)).orte)).lese
        (Signatur.anfang eD (eD.signatur eSetze)) (eP.requires eSetze).orte)
      (eP.requires eSetze)
      ((((eSp.welt []).lese [] []).lese []
        ((.nil : Args eD [] [] (eD.params eSetze)).orte)).lese
        (Signatur.anfang eD (eD.signatur eSetze)) (eP.requires eSetze).orte)
      (evalArgs (((eSp.welt []).lese [] []).lese []
        ((.nil : Args eD [] [] (eD.params eSetze)).orte))
        (.nil : Args eD [] [] (eD.params eSetze))
        (((eSp.welt []).lese [] []).lese []
          ((.nil : Args eD [] [] (eD.params eSetze)).orte)) .nil)) =
      true := by rfl
  have hok : ∃ σ₁ v, execEnd (V := vertragVon eD eSetze) eO 0
        (rufAt eP eO 0 0) (eP.rumpf eSetze)
        ((((eSp.welt []).lese [] []).lese []
          ((.nil : Args eD [] [] (eD.params eSetze)).orte)).lese
          (Signatur.anfang eD (eD.signatur eSetze)) (eP.requires eSetze).orte)
        (evalArgs (((eSp.welt []).lese [] []).lese []
          ((.nil : Args eD [] [] (eD.params eSetze)).orte))
          (.nil : Args eD [] [] (eD.params eSetze))
          (((eSp.welt []).lese [] []).lese []
            ((.nil : Args eD [] [] (eD.params eSetze)).orte)) .nil) =
        EndAusgang.zurueck σ₁ v ∧
      rufAt eP eO 0 1 eSetze
        (((eSp.welt []).lese [] []).lese []
          ((.nil : Args eD [] [] (eD.params eSetze)).orte))
        (evalArgs (((eSp.welt []).lese [] []).lese []
          ((.nil : Args eD [] [] (eD.params eSetze)).orte))
          (.nil : Args eD [] [] (eD.params eSetze))
          (((eSp.welt []).lese [] []).lese []
            ((.nil : Args eD [] [] (eD.params eSetze)).orte)) .nil) =
        RufAusgang.ok
          ((eD.invs.filter (schuldet eSetze)).foldl
            (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
            (σ₁.lese (vertragVon eD eSetze).ende (eP.ensures eSetze).orte))
          v := by
    refine ⟨_, _, rfl, rfl⟩
  obtain ⟨σ₁, v, hbody, h⟩ := hok
  have hret0 : σ₁.lese (vertragVon eD eSetze).ende
      (eP.ensures eSetze).orte =
      σ₁.lese (vertragVon eD eSetze).ende (eP.ensures eSetze).orte := rfl
  have hsinv0 : (eD.invs.filter (schuldet eSetze)).foldl
      (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
        (σ₁.lese (vertragVon eD eSetze).ende (eP.ensures eSetze).orte) =
      (eD.invs.filter (schuldet eSetze)).foldl
        (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
        (σ₁.lese (vertragVon eD eSetze).ende
          (eP.ensures eSetze).orte) := rfl
  have hinv0 : (eD.invs.find? (fun i => schuldet eSetze i &&
      !wahr? (eval ((eD.invs.filter (schuldet eSetze)).foldl
        (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
        (σ₁.lese (vertragVon eD eSetze).ende (eP.ensures eSetze).orte))
        (eP.invariante i)
        ((eD.invs.filter (schuldet eSetze)).foldl
          (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
          (σ₁.lese (vertragVon eD eSetze).ende
            (eP.ensures eSetze).orte)) .nil))) = none := by rfl
  obtain ⟨M, hr, hsl0, hschr, rhoP, wP, bP, vP, rhoS, vS, aS, bS, rest,
    hlog, hsl5, hreqP, hfol⟩ := vertragStandort_lauf_zeuge
  have hgeistW : ∃ rhoR vR wR bR,
      RufEreignisF.rueck eSetze rhoR vR wR bR ∈ (M.faeden 0).log :=
    ⟨rhoS, vS, aS, bS, by
      rw [hlog]
      exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hzeigerW : valZeigerOk [1]
      [(0, StubenWert.zahl 5), (1, StubenWert.zeiger 0x2000 8)] = true := by
    decide
  have hschluss := ComposeContractCall_verbindung eP eO 0 eHaupt eSetze []
    eHpSetze rfl 1 0 hexec _ rfl hreq0 _ _ hbody _ hret0 _ hsinv0 hinv0 h _
    hgeistW schreibTor zeugenMoves zeugenStub [1]
    [(0, StubenWert.zahl 5), (1, StubenWert.zeiger 0x2000 8)]
    schreibTor_ok zeugenMoves_ok zeugenStub_trap hzeigerW _ eSp eInit hr rfl
  exact ⟨(.nil : Args eD [] [] (eD.params eSetze)), _, σ', .nil, ρ₀', _, _, _,
    _, _, _, _, hexec, rfl, hreq0, hbody, hret0,
    hsinv0, hinv0, h, hgeistW, schreibTor_ok, zeugenMoves_ok, zeugenStub_trap,
    hzeigerW, hr, rfl, hschluss, hsl0, hschr, ⟨wP, rhoP, hsl5, hreqP⟩,
    write_read_zeuge⟩

/-! ## 4. Planted refusal: the same contracts, no ghost event.

    On the start log -- which holds no return ghost event for `setze` --
    the very same requires/ensures (proved from the very same reductions
    as §3) and the very same admitted gate do NOT close: the closing is
    refused for the missing ghost event alone, while the run is reached. -/

/-- PLANTED REFUSAL (`ComposeContractCall_geistlos_verweigert_zeuge`):
    identical contracts and gate, reached run, ghost-less log --
    no closing. -/
theorem ComposeContractCall_geistlos_verweigert_zeuge :
    ∃ (sread sret : World eD) (v : ErgVal eD (eD.erg eSetze)),
      ReqAmEintritt eP eSetze sread
        (evalArgs (((eSp.welt []).lese [] []).lese []
          ((.nil : Args eD [] [] (eD.params eSetze)).orte))
          (.nil : Args eD [] [] (eD.params eSetze))
          (((eSp.welt []).lese [] []).lese []
            ((.nil : Args eD [] [] (eD.params eSetze)).orte)) .nil) ∧
      RufEnsCheck eP eSetze sread sret
        (evalArgs (((eSp.welt []).lese [] []).lese []
          ((.nil : Args eD [] [] (eD.params eSetze)).orte))
          (.nil : Args eD [] [] (eD.params eSetze))
          (((eSp.welt []).lese [] []).lese []
            ((.nil : Args eD [] [] (eD.params eSetze)).orte)) .nil) v ∧
      torOkB schreibTor = true ∧
      RufErreichbarG eP eO 0 (RufStartG eP eSp eInit)
        (RufStartG eP eSp eInit) ∧
      ¬ rufSchluss eP eO 0 eHaupt eSetze []
        (evalArgs (((eSp.welt []).lese [] []).lese []
          ((.nil : Args eD [] [] (eD.params eSetze)).orte))
          (.nil : Args eD [] [] (eD.params eSetze))
          (((eSp.welt []).lese [] []).lese []
            ((.nil : Args eD [] [] (eD.params eSetze)).orte)) .nil)
        sread sret v [RufEreignisF.eintritt eHaupt .nil (eSp.welt [])]
        (RufStartG eP eSp eInit) eSp eInit schreibTor zeugenMoves zeugenStub
        [1] [(0, StubenWert.zahl 5), (1, StubenWert.zeiger 0x2000 8)] := by
  have hreq0 : wahr? (eval
      ((((eSp.welt []).lese [] []).lese []
        ((.nil : Args eD [] [] (eD.params eSetze)).orte)).lese
        (Signatur.anfang eD (eD.signatur eSetze)) (eP.requires eSetze).orte)
      (eP.requires eSetze)
      ((((eSp.welt []).lese [] []).lese []
        ((.nil : Args eD [] [] (eD.params eSetze)).orte)).lese
        (Signatur.anfang eD (eD.signatur eSetze)) (eP.requires eSetze).orte)
      (evalArgs (((eSp.welt []).lese [] []).lese []
        ((.nil : Args eD [] [] (eD.params eSetze)).orte))
        (.nil : Args eD [] [] (eD.params eSetze))
        (((eSp.welt []).lese [] []).lese []
          ((.nil : Args eD [] [] (eD.params eSetze)).orte)) .nil)) =
      true := by rfl
  have hok : ∃ σ₁ v, execEnd (V := vertragVon eD eSetze) eO 0
        (rufAt eP eO 0 0) (eP.rumpf eSetze)
        ((((eSp.welt []).lese [] []).lese []
          ((.nil : Args eD [] [] (eD.params eSetze)).orte)).lese
          (Signatur.anfang eD (eD.signatur eSetze)) (eP.requires eSetze).orte)
        (evalArgs (((eSp.welt []).lese [] []).lese []
          ((.nil : Args eD [] [] (eD.params eSetze)).orte))
          (.nil : Args eD [] [] (eD.params eSetze))
          (((eSp.welt []).lese [] []).lese []
            ((.nil : Args eD [] [] (eD.params eSetze)).orte)) .nil) =
        EndAusgang.zurueck σ₁ v ∧
      rufAt eP eO 0 1 eSetze
        (((eSp.welt []).lese [] []).lese []
          ((.nil : Args eD [] [] (eD.params eSetze)).orte))
        (evalArgs (((eSp.welt []).lese [] []).lese []
          ((.nil : Args eD [] [] (eD.params eSetze)).orte))
          (.nil : Args eD [] [] (eD.params eSetze))
          (((eSp.welt []).lese [] []).lese []
            ((.nil : Args eD [] [] (eD.params eSetze)).orte)) .nil) =
        RufAusgang.ok
          ((eD.invs.filter (schuldet eSetze)).foldl
            (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
            (σ₁.lese (vertragVon eD eSetze).ende (eP.ensures eSetze).orte))
          v := by
    refine ⟨_, _, rfl, rfl⟩
  obtain ⟨σ₁, v, hbody, h⟩ := hok
  have hret0 : σ₁.lese (vertragVon eD eSetze).ende
      (eP.ensures eSetze).orte =
      σ₁.lese (vertragVon eD eSetze).ende (eP.ensures eSetze).orte := rfl
  have hsinv0 : (eD.invs.filter (schuldet eSetze)).foldl
      (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
        (σ₁.lese (vertragVon eD eSetze).ende (eP.ensures eSetze).orte) =
      (eD.invs.filter (schuldet eSetze)).foldl
        (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
        (σ₁.lese (vertragVon eD eSetze).ende
          (eP.ensures eSetze).orte) := rfl
  have hinv0 : (eD.invs.find? (fun i => schuldet eSetze i &&
      !wahr? (eval ((eD.invs.filter (schuldet eSetze)).foldl
        (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
        (σ₁.lese (vertragVon eD eSetze).ende (eP.ensures eSetze).orte))
        (eP.invariante i)
        ((eD.invs.filter (schuldet eSetze)).foldl
          (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
          (σ₁.lese (vertragVon eD eSetze).ende
            (eP.ensures eSetze).orte)) .nil))) = none := by rfl
  have hens := (rufAt_ok_gibt_ens eP eO 0 0 eSetze _ _ _ rfl hreq0 _ _ hbody
    _ rfl _ rfl hinv0 _ h).1
  refine ⟨_, _, _, hreq0, hens, schreibTor_ok, RufErreichbarG.start, ?_⟩
  intro hschluss
  obtain ⟨_, _, _, hgeist, _, _⟩ := hschluss
  obtain ⟨_, _, _, _, hmem⟩ := hgeist
  simp at hmem

/- CUTS:
  - No per-access refinement: nothing here claims the admitted gate
    bytes execute the source call (decoder coupling, TSO per-access
    bridge into W/GX and layout correspondence stay with their owners;
    `budgetSimulationOffen`/`valX86_sound` are OPEN there, never
    assumed here).
  - No lowering: the shared IR (lane 287) is pending; no substitute
    IR, executor or duplicated `schritt` is invented here.
  - The closing carries the call's argument-resource list as the
    holdings (`Λa` shared between `hexec` and the inline discharge);
    split holdings need a separate frame rule, OPEN.
  - Direct `Stmt.call` only: indirect calls (`callInd`,
    `bindCallInd`) and value-carrying sites (`Block.bindCall`) have no
    closing form here (same cut as `ContractSites`).
  - The ghost half is the call's RETURN event visibility in the
    reached log; entry-event pairing across the inline boundary is
    `AufrufOpt.geistPaar` business and stays there.
  - No cost/budget transfer: `CostSummary`/`ValidationBudget`
    correspondence is untouched; bounds and timing are separate
    obligations.
  - Callee-side (obligation (c)) kernel/binding logic beyond the
    discharged `InlinePflicht` stays OPEN (same cut as `GateStub`).
-/

#print axioms ComposeContractCall_verbindung
#print axioms ComposeContractCall_ohne_geist_verweigert
#print axioms ComposeContractCall_verbindung_zeuge
#print axioms ComposeContractCall_geistlos_verweigert_zeuge

end Gabbro.Grammatik.X86
