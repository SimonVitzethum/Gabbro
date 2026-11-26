module

public import Core.Ast.Program.Execution
public import Core.Ast.Semantik.Runtime.Klasse.Schritt

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

/-- For each activation, the counters and range endpoints belong to their test
    sites and the measure belongs to its function. -/
structure KostenGrenzen where
  zaehler : Nat → Nat → Prop
  zaehlerKleiner : ∀ pc n m, m ≤ n → zaehler pc n → zaehler pc m
  obergrenze : Nat → Ganzzahl → Prop
  mass : Option Identifier → Nat → Prop

def KostenGrenzen.Felder (g : KostenGrenzen) (counts : Nat → Option Nat)
    (ends : Nat → Option Ganzzahl) (name : Option Identifier) (measure : Option Nat) : Prop :=
  (∀ pc n, counts pc = some n → g.zaehler pc n) ∧
  (∀ pc b, ends pc = some b → g.obergrenze pc b) ∧
  ∀ n, measure = some n → g.mass name n

def KostenGrenzen.RahmenGut (g : KostenGrenzen) (r : Rahmen) : Prop :=
  g.Felder r.zaehler r.obergrenzen r.funktion r.mass ∧
  ∀ k ∈ r.fortsetzungen, g.Felder k.zaehler k.obergrenzen k.funktion k.mass

/-- The obligations at instructions that install a new cost value.
    All other instructions preserve, decrease, save or restore existing values. -/
def KostenGrenzen.Einrichtung (g : KostenGrenzen) (b : Befehl) (r : Rahmen) : Prop :=
  match b with
  | .setzePasszahl src distance =>
    ∀ a, r.zahl src = some a → g.zaehler (r.pc + distance) a.zahl.wert.toNat
  | .forAnfang lower upper _ _ _ _ =>
    ∀ a b, r.zahl lower = some a → r.zahl upper = some b → a.zahl.wert < b.zahl.wert →
      g.zaehler (r.pc + 1) (b.zahl.wert - a.zahl.wert).toNat ∧ g.obergrenze (r.pc + 1) b
  | .pruefeMass slot =>
    ∀ name a, r.funktion = some name → r.zahl slot = some a → 0 ≤ a.zahl.wert →
      g.mass (some name) a.zahl.wert.toNat
  | _ => True

private theorem update_satisfies {values : Nat → Option α} {P : Nat → α → Prop}
    (old : ∀ i a, values i = some a → P i a) (new : ∀ a, value = some a → P key a) :
    ∀ i a, Function.update values key value i = some a → P i a := by
  intro i a read
  by_cases same : i = key
  · subst i
    exact new a (by simpa only [Function.update_self] using read)
  · exact old i a (by simpa only [Function.update_of_ne same] using read)

theorem KostenGrenzen.start (g : KostenGrenzen) (scope : Scope) : g.RahmenGut (Rahmen.start scope) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro _ _ h; cases h
  · intro _ _ h; cases h
  · intro _ h; cases h
  · intro _ h; cases h

variable {g : KostenGrenzen} {r : Rahmen} {b : Befehl}

private theorem KostenGrenzen.ruf (ok : g.RahmenGut r) (name : Identifier)
    (args : List (Ty .value)) (bind : Option (Ty .value)) : g.RahmenGut (r.ruf name args bind) := by
  have saved : ∀ (k : Fortsetzung), k ∈ r.fortsetzungen →
      g.Felder k.zaehler k.obergrenzen k.funktion k.mass := ok.2
  unfold Rahmen.ruf
  cases bind <;> simp only [Id.run]
  cases bind <;> simp only [Id.run]
  all_goals repeat' first | exact ok | split
  all_goals
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro _ _ h; cases h
    · intro _ _ h; cases h
    · intro _ h; cases h
    · intro k mem
      rcases List.mem_cons.mp mem with rfl | tail
      · exact ok.1
      · exact saved k tail

private theorem KostenGrenzen.eintrittArgumente {entry : Rahmen} {types : List (Ty .value)}
    (ok : g.RahmenGut r) (prepared : r.eintrittArgumente types = some entry) :
    g.RahmenGut entry := by
  unfold Rahmen.eintrittArgumente at prepared
  split at prepared
  · cases prepared; exact ok
  · split at prepared
    · cases prepared; exact ok
    · cases prepared

private theorem KostenGrenzen.rueckkehr (ok : g.RahmenGut r) (value : Option Dynamisch) :
    g.RahmenGut (r.rueckkehr value) := by
  unfold Rahmen.rueckkehr
  split
  · exact ok
  · rename_i k ks stack
    exact ⟨ok.2 k (stack ▸ List.mem_cons_self), fun item mem =>
      ok.2 item (stack ▸ List.mem_cons_of_mem k mem)⟩

private theorem KostenGrenzen.pass (ok : g.RahmenGut r) (test : Bool) (exit : Nat)
    (handler : Option Identifier) : g.RahmenGut (r.pass test exit handler) := by
  unfold Rahmen.pass
  split
  · exact ⟨⟨update_satisfies ok.1.1 (fun _ h => by cases h), ok.1.2⟩, ok.2⟩
  · split
    · rename_i n current
      refine ⟨⟨update_satisfies ok.1.1 ?_, ok.1.2⟩, ok.2⟩
      intro m eq
      cases eq
      exact g.zaehlerKleiner _ _ _ (Nat.le_succ _) (ok.1.1 _ _ current)
    · exact ok
    · exact ok

private theorem KostenGrenzen.bindeGelesen (ok : g.RahmenGut r) (slot : Nat) (ty : Ty .value) (v : Int) :
    g.RahmenGut (r.bindeGelesen slot ty v) := by
  unfold Rahmen.bindeGelesen
  split <;> exact ok

private theorem KostenGrenzen.zugriff (ok : g.RahmenGut r) (z : Zugriffsform) (v : Int) :
    g.RahmenGut (z.uebertrag r v) := by
  cases z <;> simp only [Zugriffsform.uebertrag]
  all_goals first | exact ok | exact KostenGrenzen.bindeGelesen ok _ _ _ | split
  all_goals first | exact ok | exact KostenGrenzen.bindeGelesen ok _ _ _

private theorem KostenGrenzen.faden (ok : g.RahmenGut r) (z : Fadenform) (v : Int) :
    g.RahmenGut (z.uebertrag r v) := by
  cases z <;> simp only [Fadenform.uebertrag] <;> first
    | exact ok
    | exact KostenGrenzen.bindeGelesen ok _ _ _

theorem KostenGrenzen.auswerten (ok : g.RahmenGut r) (install : g.Einrichtung b r)
    (live : Nat → Bool) : g.RahmenGut (b.auswerten r live) := by
  cases b <;> simp only [Befehl.auswerten, Id.run]
  all_goals try exact ok
  case rufe => exact KostenGrenzen.ruf ok _ _ _
  case zurueck => exact KostenGrenzen.rueckkehr ok _
  case rueckVoid => exact KostenGrenzen.rueckkehr ok _
  case starte =>
    repeat' first
    | exact ok
    | exact KostenGrenzen.ruf (KostenGrenzen.eintrittArgumente ok (by assumption)) _ _ _
    | split
  case pruefeMass =>
    simp only [Einrichtung] at install
    unfold Rahmen.setzeMass
    simp only [Id.run]
    repeat' first
    | exact ok
    | (refine ⟨⟨ok.1.1, ok.1.2.1, ?_⟩, ok.2⟩
       intro n installed
       cases installed
       have named : ∃ name, r.funktion = some name := ⟨_, by assumption⟩
       obtain ⟨name, eq⟩ := named
       rw [eq]
       exact install name _ eq (by assumption) (Int.le_of_not_gt (by assumption)))
    | split
  case setzePasszahl =>
    simp only [Einrichtung] at install
    split
    · exact ⟨⟨update_satisfies ok.1.1 (fun _ eq => by cases eq; exact install _ (by assumption)),
        ok.1.2⟩, ok.2⟩
    · exact ok
  case whileTest =>
    split
    · exact KostenGrenzen.pass ok _ _ _
    · exact ok
  case forAnfang =>
    simp only [Einrichtung] at install
    repeat' first
    | exact ok
    | (have h := install _ _ (by assumption) (by assumption) (Int.lt_of_not_ge (by assumption))
       refine ⟨⟨update_satisfies ok.1.1 ?_, update_satisfies ok.1.2.1 ?_, ok.1.2.2⟩, ok.2⟩ <;>
         intro _ eq <;> cases eq <;> first | exact h.1 | exact h.2)
    | split
  case forTest =>
    repeat' first | exact ok | exact KostenGrenzen.pass ok _ _ _ | split
  case bindeRegion =>
    simp only [Rahmen.bindeRegion, Id.run]
    repeat' first | exact ok | split
  case zugriff => exact KostenGrenzen.zugriff ok _ _
  case faden => exact KostenGrenzen.faden ok _ _
  all_goals repeat' first | exact ok | split

theorem KostenGrenzen.uebertrag (ok : g.RahmenGut r) (install : g.Einrichtung b r)
    (live : Nat → Bool) (value : Int) : g.RahmenGut (b.uebertrag r live value) := by
  cases b <;> simp only [Befehl.uebertrag] <;> first
    | exact KostenGrenzen.auswerten ok install live
    | exact KostenGrenzen.zugriff ok _ _
    | exact KostenGrenzen.faden ok _ _

theorem Rahmen.LaufN.kostenErhalt (walk : Rahmen.LaufN code n first last)
    (ok : g.RahmenGut first)
    (installs : ∀ r b, g.RahmenGut r → r.Aktiv → code[r.pc]? = some b → g.Einrichtung b r) :
    g.RahmenGut last := by
  induction walk with
  | null => exact ok
  | step live returned head _ ih =>
    exact ih (KostenGrenzen.auswerten ok (installs _ _ ok ⟨live, returned⟩ head) _)

end Gabbro.Core.Ast.Semantik
