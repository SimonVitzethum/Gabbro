/-
  File:      core/Core/Maschine/Ereignisse.lean
  Subject:   THE EVENT SHAPE OF A MACHINE STEP (step M4), from the two findings of S5:
             * LOCK EVENTS FOLLOW THE CHANGE OF THE OWNER (`sperrEreignisse`): a take of a free lock is an
               update (it reads the last operation on the lock), a hand-off to the next owner is one update,
               a release to nobody is a release write, and a step that does not change the owner records no
               lock event (`sperr_leer_iff`) -- a release of a lock not held is no lock operation.
             * WRITE EVENTS FOR FOOTPRINT CARRIERS (`schreibEreignisse`): the writes of a step are bounded by
               the footprint list, so a step records finitely many write events, one per footprint location it
               writes (`schreib_deckt`); no thread reads a location outside every footprint.
-/
module

public import Core.Maschine.Sperre
public import Core.Speicher

@[expose] public section

namespace Gabbro.Core.Maschine

open Gabbro.Core.Speicher

variable {Ort Wert : Type}

/-- The lock events of a change from owner `o` to owner `o'`. -/
def sperrE (o o' : Option Kontext) (ort : Ort) (v : Wert) : List (Etikett Ort Wert) :=
  match o, o' with
  | none, none => []
  | none, some _ => [⟨.rmw, ort, .ra, v, v⟩]
  | some _, none => [⟨.schreiben, ort, .ra, v, v⟩]
  | some c, some d => if c = d then [] else [⟨.rmw, ort, .ra, v, v⟩]

/-- **The lock events of an owner change** at the lock's location `ort` with value `v`. -/
def sperrEreignisse (s s' : SperrZustand) (ort : Ort) (v : Wert) : List (Etikett Ort Wert) :=
  sperrE s.besitzer s'.besitzer ort v

theorem sperrE_leer_iff (ort : Ort) (v : Wert) :
    ∀ o o' : Option Kontext, sperrE o o' ort v = [] ↔ ¬ o ≠ o'
  | none, none => ⟨fun _ h => h rfl, fun _ => rfl⟩
  | none, some _ => ⟨(fun h => nomatch h), fun h => absurd (fun e => nomatch e) h⟩
  | some _, none => ⟨(fun h => nomatch h), fun h => absurd (fun e => nomatch e) h⟩
  | some c, some d => by
    by_cases e : c = d
    · subst e
      exact ⟨fun _ h => h rfl, fun _ => by simp only [sperrE, ↓reduceIte]⟩
    · refine ⟨fun h => ?_, fun h => absurd (fun he => e (Option.some.inj he)) h⟩
      simp only [sperrE, e, ↓reduceIte, reduceCtorEq] at h

/-- **No lock event exactly when the owner stays.** -/
theorem sperr_leer_iff (s s' : SperrZustand) (ort : Ort) (v : Wert) :
    sperrEreignisse s s' ort v = [] ↔ ¬ SperrZustand.Wechsel s s' :=
  sperrE_leer_iff ort v s.besitzer s'.besitzer

/-- A take of a free lock records exactly one update. -/
theorem nimmt_ereignis {s s' : SperrZustand} {c : Kontext} (h : SperrZustand.Nimmt s c s')
    (ort : Ort) (v : Wert) : sperrEreignisse s s' ort v = [⟨.rmw, ort, .ra, v, v⟩] := by
  cases h
  rfl

/-- **The write events of a step**: one per footprint location the step writes. -/
def schreibEreignisse (fuss : List Ort) (schreibt : Ort → Bool) (modus : Ort → Modus) (v : Wert) :
    List (Etikett Ort Wert) :=
  (fuss.filter schreibt).map fun x => ⟨.schreiben, x, modus x, v, v⟩

/-- **Every written footprint location has its write event.** -/
theorem schreib_deckt (fuss : List Ort) (schreibt : Ort → Bool) (modus : Ort → Modus) (v : Wert)
    {x : Ort} (hx : x ∈ fuss) (hs : schreibt x = true) :
    ⟨.schreiben, x, modus x, v, v⟩ ∈ schreibEreignisse fuss schreibt modus v :=
  List.mem_map_of_mem (List.mem_filter.mpr ⟨hx, hs⟩)

/-- **Only written footprint locations have write events.** -/
theorem schreib_nur {fuss : List Ort} {schreibt : Ort → Bool} {modus : Ort → Modus} {v : Wert}
    {l : Etikett Ort Wert} (h : l ∈ schreibEreignisse fuss schreibt modus v) :
    l.ort ∈ fuss ∧ schreibt l.ort = true ∧ l.art = .schreiben := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  obtain ⟨h1, h2⟩ := List.mem_filter.mp hx
  exact ⟨h1, h2, rfl⟩

end Gabbro.Core.Maschine
