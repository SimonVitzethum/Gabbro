/-
  File:      stage0/Stage0/Senke/Sperre/Ticket/Bleibt.lean
  Subject:   The tie `HeldIn H Λ bo` survives a statement and a block: the static held set only grows along them.
              The model proves that no statement adds or drops a held lock (`Stmt.held_iff`, `Block.held_iff` in
              `Grammatik/Kern/Syntax/Satz/T2/Teil1b.lean`: every rule keeps `Λ`, or changes only marks by
              `nachSig`, `advances` and `retires`; `locks` runs its body under `.held Lk :: Λ` and ends in `Λ`); the
              thread's held set `H` is the same before and after a statement, so the tie passes on. An indirect call
              passes the tie to the callee's own signature (`HeldIn.passt`); a call passes it after the call (`HeldIn.sig`).
-/
module
public import Stage0.Senke.Sperre.Ticket.Frei
public import Grammatik.Kern.Syntax.Satz.T2.Teil1b
public import Grammatik.Kern.Syntax.Satz.T2.Teil1d
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik

variable {D : Deklaration}

/-- Where a statement starts: its `Λ` (so that the tie of a sub-statement can be named without its indices). -/
abbrev stmtAnf {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (_ : Stmt D V l Γ Λ Λ') : List (Res D) := Λ

/-- Where a block starts: its `Λ`. -/
abbrev blockAnf {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (_ : Block D V l Γ Λ Λ') : List (Res D) := Λ

/-- Where an end block starts: its `Λ`. -/
abbrev endAnf {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (_ : Endblock D V l Γ Λ) : List (Res D) := Λ

/-- A statement keeps the tie: what is held in `Λ` is held in `Λ'`. -/
theorem HeldIn.stmt {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {H : List D.Lock}
    {bo : Option Int} (s : Stmt D V l Γ Λ Λ') (h : HeldIn H Λ bo) : HeldIn H Λ' bo :=
  fun M hM => (h M hM).imp (fun hl => (s.held_iff M).mpr hl) id

/-- A block keeps the tie. -/
theorem HeldIn.block {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {H : List D.Lock}
    {bo : Option Int} (b : Block D V l Γ Λ Λ') (h : HeldIn H Λ bo) : HeldIn H Λ' bo :=
  fun M hM => (h M hM).imp (fun hl => (b.held_iff M).mpr hl) id

/-- The tie passes to a list that holds at least what `Λ` holds. -/
theorem HeldIn.mono {Λ Λ' : List (Res D)} {H : List D.Lock} {bo : Option Int} (h : HeldIn H Λ bo)
    (hm : ∀ M, Res.held M ∈ Λ → Res.held M ∈ Λ') : HeldIn H Λ' bo :=
  fun M hM => (h M hM).imp (hm M) id

/-- After a call with signature `S` the held locks are those before it. -/
theorem HeldIn.sig {S : Signatur D.Tab D.Glob D.Lock D.Marke} {Λ : List (Res D)} {H : List D.Lock}
    {bo : Option Int} (h : HeldIn H Λ bo) : HeldIn H (nachSig D S Λ) bo :=
  h.mono fun M hl => (held_nachSig_iff S Λ M).mpr hl

/-- An indirect call: the tie at the start of the pointer's signature `T` passes to the start of the callee's own
    signature `S`, which conforms to `T` (`SigPasst`): an extra lock the callee does not require ranks below its
    floor, and its floor is at least `T`'s. -/
theorem HeldIn.passt {S T : Signatur D.Tab D.Glob D.Lock D.Marke} {H : List D.Lock}
    (h : HeldIn H (Signatur.anfang D T) T.boden) (hp : SigPasst D.rang S T) :
    HeldIn H (Signatur.anfang D S) S.boden := fun M hM => by
  rcases h M hM with hl | ⟨c, hc, hlt⟩
  · have hT : M ∈ T.haelt := (held_anfang T M).mp hl
    by_cases hs : M ∈ S.haelt
    · exact Or.inl ((held_anfang S M).mpr hs)
    · exact Or.inr (hp.extra M hT hs)
  · obtain ⟨c', hc', hle⟩ := hp.boden c hc
    exact Or.inr ⟨c', hc', Int.lt_of_lt_of_le hlt hle⟩

end Gabbro.Stage0.Senke
