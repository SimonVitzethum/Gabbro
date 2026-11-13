module

public import Grammatik.Niedrig.Bytes.Grants

@[expose] public section

namespace Gabbro.Grammatik.Niedrig.Bytes

/-- Stale access fails before consulting byte contents; no write is committed. -/
theorem veraltetVerweigert (table : GrantTable) (g : Grant) (i v : Nat)
    (s : ByteState) (scope : Option Nat) (h : ¬ live table g) :
    gebrauchLies table g i s scope = Except.error veraltet ∧
    gebrauchSchreib table g i v s scope = Except.error veraltet ∧
    zustandNach s (gebrauchSchreib table g i v s scope) = s := by
  have hl : gebrauchLies table g i s scope = Except.error veraltet := by
    unfold gebrauchLies
    rw [if_neg h]
  have hw : gebrauchSchreib table g i v s scope = Except.error veraltet := by
    unfold gebrauchSchreib
    rw [if_neg h]
  refine ⟨hl, hw, ?_⟩
  simp only [hw, zustandNach]

/-- Every successful grant write is an actual successful byte write. -/
theorem gebrauchSchreibByte {table : GrantTable} {g : Grant} {i v : Nat}
    {s next : ByteState} {scope : Option Nat}
    (h : gebrauchSchreib table g i v s scope = Except.ok next) :
    writeByte g.cap i v s = Except.ok next := by
  unfold gebrauchSchreib at h
  split at h
  · split at h
    · cases h
    · exact h
  · cases h

/-- Every successful grant read is an actual successful byte read. -/
theorem gebrauchLiesByte {table : GrantTable} {g : Grant} {i v : Nat}
    {s : ByteState} {scope : Option Nat}
    (h : gebrauchLies table g i s scope = Except.ok v) :
    readByte g.cap i s = Except.ok v := by
  unfold gebrauchLies at h
  split at h
  · split at h
    · cases h
    · exact h
  · cases h

/-- A successful revocation has exactly this generation update. -/
theorem widerrufTabelle {table next : GrantTable} {carrier : Nat}
    (h : widerrufe table carrier = Except.ok next) :
    next = { table with generation := fun t =>
      if t = carrier then table.generation t + 1 else table.generation t } := by
  unfold widerrufe at h
  split at h
  · cases h
  · cases h
    rfl

/-- All grants from the current or an earlier generation become stale. -/
theorem widerrufVeraltet {table next : GrantTable} {carrier : Nat}
    (h : widerrufe table carrier = Except.ok next) (g : Grant)
    (hc : g.cap.traeger = carrier)
    (hold : g.generation ≤ table.generation carrier) : ¬ live next g := by
  rw [widerrufTabelle h]
  change ¬ g.generation = (if g.cap.traeger = carrier then
    table.generation g.cap.traeger + 1 else table.generation g.cap.traeger)
  rw [hc, if_pos rfl]
  exact Nat.ne_of_lt (Nat.lt_succ_of_le hold)

/-- Revocation preserves every other carrier's generation. -/
theorem widerrufAndere {table next : GrantTable} {carrier other : Nat}
    (h : widerrufe table carrier = Except.ok next) (hne : other ≠ carrier) :
    next.generation other = table.generation other := by
  rw [widerrufTabelle h]
  exact if_neg hne

/-- No generation decreases under revocation. -/
theorem widerrufMonoton {table next : GrantTable} {carrier : Nat}
    (h : widerrufe table carrier = Except.ok next) (other : Nat) :
    table.generation other ≤ next.generation other := by
  rw [widerrufTabelle h]
  by_cases hc : other = carrier
  · simpa only [if_pos hc] using Nat.le_succ (table.generation other)
  · simpa only [if_neg hc] using Nat.le_refl (table.generation other)

/-- Any outstanding loan, including a read loan, prevents revocation. -/
theorem widerrufLeiheVerweigert (table : GrantTable) (l : Loan)
    (hm : l ∈ table.loans) :
    widerrufe table l.cap.traeger = Except.error leiheAktiv := by
  have ha : table.loans.any (fun a => decide (a.cap.traeger = l.cap.traeger)) = true :=
    List.any_eq_true.mpr ⟨l, hm, by simp⟩
  unfold widerrufe
  rw [if_pos ha]

/-- Successful lending records the exact lender, preserves generations,
    and checks carrier, range order, containment, and permission weakening. -/
theorem leiheFakten {table next : GrantTable} {g : Grant} {c : ByteCap}
    {id : Nat} {scope : Option Nat}
    (h : leihe table g c id scope = Except.ok next) :
    live table g ∧
    (c.traeger = g.cap.traeger ∧ g.cap.lo ≤ c.lo ∧ c.lo ≤ c.hi ∧ c.hi ≤ g.cap.hi) ∧
    schwaecher c.rechte g.cap.rechte = true ∧
    next =
      { table with
        loans :=
          { cap := c
            lender := g
            id := id } :: table.loans } := by
  unfold leihe at h
  split at h
  · rename_i hlive
    split at h
    · rename_i hrange
      split at h
      · rename_i hrights
        split at h
        · cases h
        · cases hp : pruefeLeihen table.loans g scope c with
          | error e =>
            rw [hp] at h
            cases h
          | ok unit =>
            rw [hp] at h
            cases h
            exact ⟨hlive, hrange, hrights, rfl⟩
      · cases h
    · cases h
  · cases h

/-- Every borrower right was already held by the lender. -/
theorem leiheRechteBeschraenkt {table next : GrantTable} {g : Grant} {c : ByteCap}
    {id : Nat} {scope : Option Nat}
    (h : leihe table g c id scope = Except.ok next) :
    (darfLesen c.rechte = true → darfLesen g.cap.rechte = true) ∧
    (darfSchreiben c.rechte = true → darfSchreiben g.cap.rechte = true) := by
  have hw := (leiheFakten h).2.2.1
  exact ⟨schwaecherLesen _ _ hw, schwaecherSchreiben _ _ hw⟩

/-- A successful loan never changes any generation. -/
theorem leiheGenerationen {table next : GrantTable} {g : Grant} {c : ByteCap}
    {id : Nat} {scope : Option Nat}
    (h : leihe table g c id scope = Except.ok next) :
    next.generation = table.generation := by
  rw [(leiheFakten h).2.2.2]

/-- A return changes only the loan stack, never generations. -/
theorem rueckgabeGenerationen {table next : GrantTable} {id : Nat}
    (h : gibZurueck table id = Except.ok next) :
    next.generation = table.generation := by
  unfold gibZurueck at h
  split at h
  · cases h
  · split at h
    · cases h
      rfl
    · cases h

/-- Lend and its immediate matching return restore the WHOLE table. -/
theorem leiheRueckgabe {table next : GrantTable} {g : Grant} {c : ByteCap}
    {id : Nat} {scope : Option Nat}
    (h : leihe table g c id scope = Except.ok next) :
    gibZurueck next id = Except.ok table := by
  rw [(leiheFakten h).2.2.2]
  change (if id = id then Except.ok table else Except.error leiheReihenfolge) =
    Except.ok table
  rw [if_pos rfl]

/-- The return must match the top, regardless of the carrier. -/
theorem rueckgabeNurInnen (table : GrantTable) (l : Loan) (rest : List Loan)
    (ht : table.loans = l :: rest) (id : Nat) (hne : id ≠ l.id) :
    gibZurueck table id = Except.error leiheReihenfolge := by
  unfold gibZurueck
  rw [ht]
  dsimp only
  rw [if_neg hne]

/-- An outstanding write loan conflicts with either access to its byte. -/
theorem schreibLeiheKonflikt (c d : ByteCap) (i : Nat) (p : Perm)
    (hc : c.traeger = d.traeger) (hi : c.lo ≤ i ∧ i < c.hi)
    (hw : darfSchreiben c.rechte = true) :
    konflikt c (punkt d i p) = true := by
  have hov : ueberlappt c (punkt d i p) = true := by
    apply decide_eq_true
    exact ⟨hc, Nat.lt_of_le_of_lt hi.1 hi.2, Nat.lt_succ_self i,
      Nat.lt_succ_of_le hi.1, hi.2⟩
  simp [konflikt, hov, hw]

/-- A write loan suspends its lender's reads and writes, including a lender
    that is itself a borrower. Lender and new borrower have distinct scopes. -/
theorem leiheSperrt {table next : GrantTable} {g : Grant} {c : ByteCap}
    {id : Nat} {scope : Option Nat}
    (h : leihe table g c id scope = Except.ok next)
    (hscope : scope ≠ Option.some id) (i v : Nat) (s : ByteState)
    (hi : c.lo ≤ i ∧ i < c.hi) (hw : darfSchreiben c.rechte = true) :
    gebrauchLies next g i s scope = Except.error leiheAktiv ∧
    gebrauchSchreib next g i v s scope = Except.error leiheAktiv := by
  obtain ⟨hl, hr, _, ht⟩ := leiheFakten h
  have hread := schreibLeiheKonflikt c g.cap i Perm.lese hr.1 hi hw
  have hwrite := schreibLeiheKonflikt c g.cap i Perm.schreibe hr.1 hi hw
  have hlive : g.generation = table.generation g.cap.traeger := hl
  rw [ht]
  simp [gebrauchLies, gebrauchSchreib, live, hlive,
    pruefeLeihen, hscope, hread, hwrite]

/-- Returning the loan restores exactly the lender's previous access checks,
    for the current byte state (including writes made during the loan). -/
theorem rueckgabeZugriff {table loaned restored : GrantTable} {g : Grant}
    {c : ByteCap} {id : Nat} {scope : Option Nat}
    (hl : leihe table g c id scope = Except.ok loaned)
    (hr : gibZurueck loaned id = Except.ok restored)
    (i v : Nat) (s : ByteState) :
    gebrauchLies restored g i s scope = gebrauchLies table g i s scope ∧
    gebrauchSchreib restored g i v s scope = gebrauchSchreib table g i v s scope := by
  have he : table = restored := Except.ok.inj ((leiheRueckgabe hl).symm.trans hr)
  rw [← he]
  exact ⟨rfl, rfl⟩

/-- Successful metadata histories. Reads and writes leave the table unchanged;
    refused metadata operations likewise commit no new table. -/
inductive Tabellenlauf : GrantTable → GrantTable → Prop
  | start (table : GrantTable) : Tabellenlauf table table
  | widerruf {initial table next : GrantTable} (lauf : Tabellenlauf initial table)
      (carrier : Nat) (h : widerrufe table carrier = Except.ok next) :
      Tabellenlauf initial next
  | leihen {initial table next : GrantTable} (lauf : Tabellenlauf initial table)
      (g : Grant) (c : ByteCap) (id : Nat) (scope : Option Nat)
      (h : leihe table g c id scope = Except.ok next) : Tabellenlauf initial next
  | rueckgabe {initial table next : GrantTable} (lauf : Tabellenlauf initial table)
      (id : Nat) (h : gibZurueck table id = Except.ok next) : Tabellenlauf initial next

/-- Generations never decrease, across arbitrary combinations of operations. -/
theorem generationenMonoton {initial table : GrantTable}
    (h : Tabellenlauf initial table) (carrier : Nat) :
    initial.generation carrier ≤ table.generation carrier := by
  induction h with
  | start => exact Nat.le_refl _
  | widerruf _ _ hw ih => exact Nat.le_trans ih (widerrufMonoton hw carrier)
  | leihen _ _ _ _ _ hl ih =>
      rw [leiheGenerationen hl]
      exact ih
  | rueckgabe _ _ hr ih =>
      rw [rueckgabeGenerationen hr]
      exact ih

#print axioms veraltetVerweigert
#print axioms widerrufVeraltet
#print axioms widerrufMonoton
#print axioms leiheFakten
#print axioms leiheSperrt
#print axioms leiheRueckgabe
#print axioms generationenMonoton

end Gabbro.Grammatik.Niedrig.Bytes
