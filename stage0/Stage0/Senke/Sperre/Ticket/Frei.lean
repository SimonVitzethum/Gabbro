/-
  File:      stage0/Stage0/Senke/Sperre/Ticket/Frei.lean
  Subject:   Why a ticket lock is FREE at `locks Lk`: the tie `HeldIn H Λ bo` of the thread's held set `H` (the
              locks whose words read as mine, `TicketOK`) to the static held set `Λ` of the statement and the
              floor `bo` of its function. Every lock in `H` is held in `Λ` or ranks below the floor. The rank
              premise of `Stmt.locks` (`hr`) and the floor rule (`Stmt.ueberBoden`: `c ≤ D.rang Lk`) then exclude
              `Lk ∈ H` (`HeldIn.frei`). The tie grows with the taken lock (`HeldIn.nimmt`) and passes to a
              callee's start through `RufPasst` (`HeldIn.ruf`).
-/
module
public import Stage0.Senke.Sperre.Ticket.Sync
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik

variable {D : Deklaration}

/-- The tie of the thread's held ticket locks `H` to the static held set `Λ` and the floor `bo`: every lock the
    thread holds is held in `Λ` or ranks below the floor. -/
def HeldIn (H : List D.Lock) (Λ : List (Res D)) (bo : Option Int) : Prop :=
  ∀ M, M ∈ H → Res.held M ∈ Λ ∨ ∃ c, bo = some c ∧ D.rang M < c

/-- **Freeness at `locks Lk`**: a lock ranking above everything held in `Λ` (`Stmt.locks`'s `hr`) and at or above
    the floor is not held by the thread. -/
theorem HeldIn.frei {H : List D.Lock} {Λ : List (Res D)} {bo : Option Int} {Lk : D.Lock} (h : HeldIn H Λ bo)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang Lk) (hb : ∀ c, bo = some c → c ≤ D.rang Lk) : Lk ∉ H := by
  intro hin
  rcases h Lk hin with hl | ⟨c, hc, hlt⟩
  · exact Int.lt_irrefl _ (hr Lk hl)
  · exact Int.lt_irrefl _ (Int.lt_of_lt_of_le hlt (hb c hc))

/-- The body of `locks Lk`: the taken lock joins both held sets. -/
theorem HeldIn.nimmt {H : List D.Lock} {Λ : List (Res D)} {bo : Option Int} {Lk : D.Lock} (h : HeldIn H Λ bo) :
    HeldIn (Lk :: H) (Res.held Lk :: Λ) bo := fun M hM => by
  rcases List.mem_cons.mp hM with e | e
  · rw [e]
    exact Or.inl (List.mem_cons.mpr (Or.inl rfl))
  · rcases h M e with hl | hb
    · exact Or.inl (List.mem_cons.mpr (Or.inr hl))
    · exact Or.inr hb

/-- A call: what the caller holds is, at the callee's start, required by the callee or below the callee's floor. -/
theorem HeldIn.ruf {V : Vertrag D} {S : Signatur D.Tab D.Glob D.Lock D.Marke} {H : List D.Lock}
    {Λ : List (Res D)} (h : HeldIn H Λ V.boden) (hp : RufPasst D V S Λ) :
    HeldIn H (Signatur.anfang D S) S.boden := fun M hM => by
  rcases h M hM with hl | ⟨c, hc, hlt⟩
  · by_cases hs : M ∈ S.haelt
    · exact Or.inl (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨M, hs, rfl⟩)))
    · exact Or.inr (hp.hx M hl hs)
  · obtain ⟨c', hc', hle⟩ := hp.hb c hc
    exact Or.inr ⟨c', hc', Int.lt_of_lt_of_le hlt hle⟩

/-- The floor rule of `Stmt.ueberBoden` for one lock, as the compiler can check it. -/
def ueberBodenB (bo : Option Int) (r : Int) : Bool :=
  match bo with
  | some c => decide (c ≤ r)
  | none => true

theorem ueberBodenB_spec {bo : Option Int} {r : Int} (h : ueberBodenB bo r = true) :
    ∀ c, bo = some c → c ≤ r := by
  intro c hc
  subst hc
  simpa only [ueberBodenB, decide_eq_true_eq] using h

end Gabbro.Stage0.Senke
