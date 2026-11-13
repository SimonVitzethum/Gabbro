/-
  File:      stage0/Stage0/Senke/Sperre/Ticket/Offen.lean
  Subject:   What the switch of `locks_ok` to the ticket lock still needs (lock stage 2b, open items).
-/
module
@[expose] public section


namespace Gabbro.Stage0.Senke

/-- What the switch of `locks_ok` (in `Sperre/Satz.lean`) to the ticket lock still needs. Written so far, in the
    sibling files: `TicketKlasse`; `TicketOK`/`TicketSync` indexed by the held set `H` with `keepWords`,
    `agreeW`, `mono`, `call`, `me`; `AgreeK.ticketKlasse`, `AgreeK.ticketOK`, `TicketSync.nimmt` (`Lauf`);
    the tie `HeldIn` with `HeldIn.frei`, `HeldIn.nimmt`, `HeldIn.ruf`, `ueberBodenB` (`Frei`); the pair lemmas
    (`Paar`); the new code `locksCodeT` with `locksCodeT_len` and `locksT_at` (`Code`, `Lage`).
    - (a) **One atomic switch.** Once `AgreeW.sync` answers `TicketKlasse` (only next − serving and the
      waiters kept), no statement keeps the owner/count words of `SyncOK` any more; so `AgreeW.sync`,
      `Umf.sync`, the `SyncOK` premise of `FunSpec.run`, `BildLage.sync` and `locks_ok` change in ONE commit
      (`SyncOK.agreeW`, `.agree`, `.keep` are the consumers that break). `AgreeW.stark` gives the class by
      `TicketKlasse.ofLock` of its equal words; `refl`/`trans` by `TicketKlasse.refl`/`.trans`; `mono`,
      `widen`, `agreeW_sub` only re-type.
    - (b) **Freeness at `locks Lk`.** `nimmT_paar` needs next = serving at entry. The simulation today carries
      no tie between the lock words and `Λ`: `Umf.sync : SyncOK m L fp Ks` allows free OR mine for every
      lock, and the old code re-took a held lock by the hold count. The tie (`Frei.lean`):
      `TicketSync m L fp Ks H` (mine iff `Lk ∈ H`) together with
      `HeldIn H Λ bo := ∀ M, M ∈ H → Res.held M ∈ Λ ∨ ∃ c, bo = some c ∧ D.rang M < c`,
      `bo = (vertragVon D f).boden`. At `locks Lk hr body`, `HeldIn.frei` gives `Lk ∉ H` from `hr` and
      `∀ c, bo = some c → c ≤ D.rang Lk`; the latter is a new conjunct `ueberBodenB bo (D.rang Lk) = true` of
      the `locks` condition in `lowS` (`ueberBodenB_spec`), true for every program with `StufenOk`. The
      body runs under `Lk :: H` and `.held Lk :: Λ` (`TicketSync.nimmt`, `HeldIn.nimmt`). Threading needs:
      `H` as a parameter of `Umf` (`Rueckkehr/Call.lean`, about 50 files mention `Umf`); `HeldIn H Λ bo` as
      a premise beside `hu` in every case of the mutual `lowS_ok`/`lowB_ok` (`Anweisung/Satz/Teil5.lean`
      and the case files, 66 spelled-out induction hypotheses in 15 files); `FunSpec.run` taking
      `TicketSync m L fp Ks H` and `HeldIn H (Signatur.anfang D (D.signatur f)) (D.signatur f).boden`, met at
      every call by `TicketSync.call` and `HeldIn.ruf` from the call's `RufPasst`, and at the image start by
      `H = []` (all words zero: next = serving = 0, waiters 0).
    - (c) **Held sets only grow along a block.** The `Block.cons` case passes `HeldIn H Λ bo` to the rest
      typed at `Λ'`; this needs the syntactic lemma `Res.held M ∈ Λ → Res.held M ∈ Λ'` for every
      `Stmt D V l Γ Λ Λ'` (mutually for `Block`, `Arms`, `GrundArms`): every typing rule keeps `Λ`, or
      changes only marks (`nach`/`nachSig`, `Λ.erase (.marke …) ++ [.marke …]`, `Λ.erase (.marke …)`).
    - (d) **`locks_ok` on `locksCodeT`**: the body's exits at `(16 * 17, 16 * 34)` (were `(16 * 30, 16 * 60)`
      in `lowS` and in `lowS_ok_locks`), the `lit32` conditions `lit32 (16 + ex.1 + 16 * 17)` and
      `lit32 (16 + ex.2)`; the take by `nimmT_paar` from `Lk ∉ H`; the give on each way out by `gibT_paar`
      after the body's `TicketKlasse` (`a2.sync`); the result's class by `nimmT_gibT_klasse`, every other
      lock by `AgreeK.ticketKlasse` and `TicketKlasse.trans`. The bytes of the taken lock are NOT restored
      (both tickets are one higher), so the `b` field of the result's `AgreeW` excludes them by `InSync`
      (they lie in `[L.hi, L.sye)`), not by `lk_bytes`.
    - (e) **Contended paths, not proved (excluded in the sequential simulation):**
      the take from a lock another thread holds (`LS m0 m fp s a f n u w` with `n ≠ u` at the check at index
      10 of `nimmT`, so the `WAIT` block 12–34 and the jump back to 7) — excluded by `TicketSync` and
      `HeldIn.frei` (a lock not in `H` is free); the `cas` retry of `L0` (index 6 back to 0 when the `cas` at
      index 4 finds the next word changed) — excluded by `AgreeK` (no other writer between index 1 and 4);
      the give with waiters (`LS m0 m fp s a f (n + 1) n w` with `w ≠ 0`, so the `futex_wake` block 8–15 of
      `gibT`) — excluded by `TicketSync`'s waiters, zero by default. -/
def ticketOffen : True := trivial

end Gabbro.Stage0.Senke
