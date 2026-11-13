module
public import Bruecke.Nachbedingung
@[expose] public section


/-!
# Shared answer-table and ghost-counter definitions

Writer calls record a related answer while advancing the first written carrier's ghost.
`EintragGut`, `Oben` and `Schluessel` state the table's contract, ordering and key conditions.
The consolidated carried run simulation lives in `Kette/`.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-! ## 1. Ghost counters -/

def geistOrt (w : String) : Gabbro.Body.Place := .field w "#"

def gz (w : String) (W : Gabbro.Body.World) : Int :=
  match W (geistOrt w) with
  | .int n => n
  | _ => 0

def bump (w : String) (W : Gabbro.Body.World) : Gabbro.Body.World :=
  Gabbro.Body.store W (geistOrt w) (.int (gz w W + 1))

theorem gz_store_slot (w c : String) (k : Int) (fld : String) (W : Gabbro.Body.World)
    (v : Gabbro.Body.Value) : gz w (Gabbro.Body.store W (.slot c k fld) v) = gz w W := by
  simp [gz, geistOrt, Gabbro.Body.store]

theorem gz_store_global (w n : String) (W : Gabbro.Body.World) (v : Gabbro.Body.Value) :
    gz w (Gabbro.Body.store W (.global n) v) = gz w W := by
  simp only [gz, geistOrt, Gabbro.Body.store, reduceCtorEq, ↓reduceIte]

theorem gz_enc (w : String) (σ : World (declOf u)) (W : Gabbro.Body.World) :
    gz w (encG u σ W) = gz w W := by
  simp only [gz, geistOrt, encG, enc]

theorem gz_bump_self (w : String) (W : Gabbro.Body.World) : gz w (bump w W) = gz w W + 1 := by
  simp [gz, bump, Gabbro.Body.store]

theorem gz_bump_le (w w' : String) (W : Gabbro.Body.World) : gz w' W ≤ gz w' (bump w W) := by
  by_cases h : w' = w
  · subst h; rw [gz_bump_self]; omega
  · have : geistOrt w' ≠ geistOrt w := by simp [geistOrt, h]
    simp [gz, bump, Gabbro.Body.store, this]

theorem wgrel_bump {σ : World (declOf u)} {W : Gabbro.Body.World} (w : String)
    (h : WGRel u σ W) : WGRel u σ (bump w W) := by
  constructor
  · intro c k fld v hv
    have hp : Gabbro.Body.Place.slot c k fld ≠ geistOrt w := by intro e; cases e
    exact (Gabbro.Body.store_elsewhere _ _ _ _ hp).trans (h.1 c k fld v hv)
  · intro g v hv
    have hp : Gabbro.Body.Place.global g ≠ geistOrt w := by intro e; cases e
    exact (Gabbro.Body.store_elsewhere _ _ _ _ hp).trans (h.2 g v hv)

/-! ## 2. The answer table -/

structure Eintrag where
  name : String
  ein : Gabbro.Body.State
  aus : Gabbro.Body.State × Option Gabbro.Body.Value

/-- `ρB` answers every call of the table with the table's answer. -/
def Treu (A : List Eintrag) (ρB : Gabbro.Body.Env) : Prop := ∀ e ∈ A, ρB e.name e.ein = e.aus

/-- An entry keeps the callee's contract and its frame at the entry state. -/
def EintragGut (u : UProg) (e : Eintrag) : Prop :=
  ∀ gf, fnSuch u e.name = some gf →
    (preProp (wfU u) gf e.ein → (postU u (wfU u) gf e.ein e.aus.1 e.aus.2).getD False) ∧
    (∀ p, p.carrier ∉ (writesU gf) → e.aus.1.world p = e.ein.world p)

/-- The ghost carrier of a callee: its first written carrier. -/
def geistVon (u : UProg) (n : String) : Option String := (fnSuch u n).bind (fun gf => (writesU gf).head?)

/-- Every entry is a writer's, at an entry state whose ghost is at least the one of `W`. -/
def Oben (u : UProg) (A : List Eintrag) (W : Gabbro.Body.World) : Prop :=
  ∀ e ∈ A, ∃ w, geistVon u e.name = some w ∧ gz w W ≤ gz w e.ein.world

/-- No two entries share a key. -/
def Schluessel (A : List Eintrag) : Prop :=
  A.Pairwise (fun a b => ¬ (a.name = b.name ∧ a.ein = b.ein))

/-- Every declared frame, at the name a call resolves (`fnSuch`, the first function of the name). -/
def RahmenAlle (u : UProg) (ρB : Gabbro.Body.Env) : Prop :=
  ∀ n gf, fnSuch u n = some gf → Gabbro.Body.Frame ρB n (writesU gf)

/-! ## 3. The entry of one call -/

theorem reqAmEintritt_wahr {P : Programm (declOf u)} (G : Gesenkt u P) (f : Fin u.fns.length)
    (σ : World (declOf u)) (ρ : Env (declOf u) ((declOf u).params f)) : ReqAmEintritt P f σ ρ := by
  unfold ReqAmEintritt; rw [G.req f]; rfl

/-- The answer a writer's call point enters into the table: the G answer's world written over
    the entry world, the ghost of `w` bumped, and the G answer. -/
def antwort (w : String) (σ' : World (declOf u)) (t : Gabbro.Body.State) (r : Option Gabbro.Body.Value) :
    Gabbro.Body.State × Option Gabbro.Body.Value :=
  (⟨bump w (encG u σ' t.world), t.local'⟩, r)

/-! ## 4. The run -/

theorem oben_mono {A : List Eintrag} {W W' : Gabbro.Body.World}
    (h : ∀ w, gz w W ≤ gz w W') (hA : Oben u A W') : Oben u A W := by
  intro e he
  obtain ⟨w, hw, hle⟩ := hA e he
  exact ⟨w, hw, Int.le_trans (h w) hle⟩

end Gabbro.Bruecke
