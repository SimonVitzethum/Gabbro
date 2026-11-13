/-
  File:      Grammatik/Niedrig/Bytes/BytesSaetze.lean
  Subject:   THEOREMS OVER BYTE CAPABILITIES (L3a): the frame, read-after-write
    and initialisation discipline, split disjointness and cover, and that
    narrowing never grows rights.
-/
module

public import Grammatik.Niedrig.Bytes.Bytes

@[expose] public section


namespace Gabbro.Grammatik.Niedrig.Bytes

/-! ## A write changes no byte outside its capability -/

/-- A write through `cap` changes no byte outside `[lo, hi)` of its carrier
    and no other carrier: flags and values elsewhere are untouched. -/
theorem writeByteRahmen (c : ByteCap) (i v : Nat) (s s' : ByteState)
    (t' j : Nat)
    (h : writeByte c i v s = Except.ok s')
    (hfern : t' ≠ c.traeger ∨ j ≠ i) :
    s'.init t' j = s.init t' j ∧ s'.wert t' j = s.wert t' j := by
  unfold writeByte at h
  split at h
  · split at h
    · split at h
      · cases h
        have hcond : ¬ (t' = c.traeger ∧ j = i) := by
          cases hfern with
          | inl hne => exact fun hcon => hne hcon.1
          | inr hne => exact fun hcon => hne hcon.2
        exact ⟨schreibNachInitAnderer s c.traeger i v t' j hcond,
          schreibNachWertAnderer s c.traeger i v t' j hcond⟩
      · cases h
    · cases h
  · cases h

/-! ## Read-after-write and the initialisation discipline -/

/-- Read-after-write returns the written value. -/
theorem liesNachSchreib (c : ByteCap) (i v : Nat) (s s' : ByteState)
    (hread : darfLesen c.rechte = true)
    (h : writeByte c i v s = Except.ok s') :
    readByte c i s' = Except.ok v := by
  unfold writeByte at h
  by_cases hsch : darfSchreiben c.rechte = true
  · rw [if_pos hsch] at h
    by_cases hber : c.lo ≤ i ∧ i < c.hi
    · rw [if_pos hber] at h
      by_cases hv : v < 256
      · rw [if_pos hv] at h
        cases h
        have hinit : (schreibNach s c.traeger i v).init c.traeger i = true :=
          schreibNachInit s c.traeger i v
        unfold readByte
        rw [if_pos hread, if_pos hber, if_pos hinit,
          schreibNachWert s c.traeger i v]
      · rw [if_neg hv] at h
        cases h
    · rw [if_neg hber] at h
      cases h
  · rw [if_neg hsch] at h
    cases h

/-- A byte read successfully was written before: a successful read implies
    the initialised flag is set. -/
theorem gelesenInitialisiert (c : ByteCap) (i w : Nat) (s : ByteState)
    (h : readByte c i s = Except.ok w) :
    s.init c.traeger i = true := by
  unfold readByte at h
  split at h
  · split at h
    · split at h
      · rename_i hinit
        cases h
        exact hinit
      · cases h
    · cases h
  · cases h

/-- A write marks its byte initialised; together with the frame and the empty
    state (where no flag is set) this says flags come only from `writeByte`.
    The full trace over write sequences is L3b, not this package. -/
theorem geschriebenMarkiert (c : ByteCap) (i v : Nat) (s s' : ByteState)
    (h : writeByte c i v s = Except.ok s') :
    s'.init c.traeger i = true := by
  unfold writeByte at h
  split at h
  · split at h
    · split at h
      · cases h
        exact schreibNachInit s c.traeger i v
      · cases h
    · cases h
  · cases h

/-- A write keeps every stored value below 256. -/
theorem writeByteByteOk (c : ByteCap) (i v : Nat) (s s' : ByteState)
    (h : writeByte c i v s = Except.ok s') (hok : byteOk s) :
    byteOk s' := by
  unfold writeByte at h
  split at h
  · split at h
    · split at h
      · rename_i hklein
        cases h
        intro t j
        show (schreibNach s c.traeger i v).wert t j < 256
        by_cases hfern : t = c.traeger ∧ j = i
        · obtain ⟨rfl, rfl⟩ := hfern
          rw [schreibNachWert]
          exact hklein
        · rw [schreibNachWertAnderer s c.traeger i v t j hfern]
          exact hok t j
      · cases h
    · cases h
  · cases h

/-! ## The two halves of a split are disjoint and cover the original -/

/-- The halves carry the split point as their shared bound, carrier and
    rights unchanged. -/
theorem splitFelder (c : ByteCap) (k : Nat) (l r : ByteCap)
    (h : splitAt c k = Except.ok (l, r)) :
    l.hi = k ∧ r.lo = k ∧ l.traeger = c.traeger ∧ r.traeger = c.traeger ∧
      l.rechte = c.rechte ∧ r.rechte = c.rechte := by
  unfold splitAt at h
  split at h
  · cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases h

/-- The two halves are disjoint: no byte lies in both. -/
theorem splitGetrennt (c : ByteCap) (k : Nat) (l r : ByteCap)
    (h : splitAt c k = Except.ok (l, r)) (j : Nat)
    (hl : inBereich l j = true) (hr : inBereich r j = true) : False := by
  unfold splitAt at h
  split at h
  · cases h
    unfold inBereich at hl hr
    split at hl
    · rename_i hlj
      split at hr
      · rename_i hrj
        obtain ⟨_, hlt⟩ := hlj
        obtain ⟨hle, _⟩ := hrj
        have h1 : j < k := hlt
        have h2 : k ≤ j := hle
        exact Nat.lt_irrefl k (Nat.lt_of_le_of_lt h2 h1)
      · cases hr
    · cases hl
  · cases h

/-- The two halves cover the original: every byte in range lies in one half. -/
theorem splitDeckt (c : ByteCap) (k : Nat) (l r : ByteCap)
    (h : splitAt c k = Except.ok (l, r)) (j : Nat)
    (hj : inBereich c j = true) :
    inBereich l j = true ∨ inBereich r j = true := by
  unfold splitAt at h
  split at h
  · cases h
    unfold inBereich at hj
    split at hj
    · rename_i hcj
      by_cases hjk : j < k
      · left
        show (if c.lo ≤ j ∧ j < k then true else false) = true
        rw [if_pos ⟨hcj.1, hjk⟩]
      · right
        have hkj : k ≤ j := Nat.not_lt.mp hjk
        show (if k ≤ j ∧ j < c.hi then true else false) = true
        rw [if_pos ⟨hkj, hcj.2⟩]
    · cases hj
  · cases h

/-- The halves of a well-formed capability are well-formed. -/
theorem splitOk (c : ByteCap) (k : Nat) (l r : ByteCap)
    (h : splitAt c k = Except.ok (l, r)) :
    l.lo ≤ l.hi ∧ r.lo ≤ r.hi := by
  unfold splitAt at h
  split at h
  · rename_i hkk
    cases h
    obtain ⟨hlo, hhi⟩ := hkk
    exact ⟨hlo, hhi⟩
  · cases h

/-! ## Permissions never grow -/

/-- Weakening keeps every read right the new permission grants. -/
theorem schwaecherLesen (neu alt : Perm)
    (h : schwaecher neu alt = true) (hl : darfLesen neu = true) :
    darfLesen alt = true := by
  cases neu <;> cases alt
  case lese.lese => rfl
  case lese.schreibe => cases h
  case lese.beide => rfl
  case schreibe.lese => cases h
  case schreibe.schreibe => cases hl
  case schreibe.beide => cases hl
  case beide.lese => cases h
  case beide.schreibe => cases h
  case beide.beide => rfl

/-- Weakening keeps every write right the new permission grants. -/
theorem schwaecherSchreiben (neu alt : Perm)
    (h : schwaecher neu alt = true) (hl : darfSchreiben neu = true) :
    darfSchreiben alt = true := by
  cases neu <;> cases alt
  case lese.lese => cases hl
  case lese.schreibe => cases h
  case lese.beide => cases hl
  case schreibe.lese => cases h
  case schreibe.schreibe => rfl
  case schreibe.beide => rfl
  case beide.lese => cases h
  case beide.schreibe => cases h
  case beide.beide => rfl

/-- Narrowing never grows rights: every right the new permission grants, the
    old one granted too. -/
theorem narrowKeinWachstum (c c' : ByteCap) (p : Perm)
    (h : narrowPerm c p = Except.ok c') :
    (darfLesen p = true → darfLesen c.rechte = true) ∧
      (darfSchreiben p = true → darfSchreiben c.rechte = true) := by
  unfold narrowPerm at h
  split at h
  · rename_i hs
    cases h
    exact ⟨schwaecherLesen p c.rechte hs, schwaecherSchreiben p c.rechte hs⟩
  · cases h

/-- Narrowing installs the new permission. -/
theorem narrowRechte (c c' : ByteCap) (p : Perm)
    (h : narrowPerm c p = Except.ok c') : c'.rechte = p := by
  unfold narrowPerm at h
  split at h
  · cases h
    rfl
  · cases h

/-- Narrowing keeps carrier and range. -/
theorem narrowFelder (c c' : ByteCap) (p : Perm)
    (h : narrowPerm c p = Except.ok c') :
    c'.traeger = c.traeger ∧ c'.lo = c.lo ∧ c'.hi = c.hi := by
  unfold narrowPerm at h
  split at h
  · cases h
    exact ⟨rfl, rfl, rfl⟩
  · cases h

/-- Narrowing keeps a well-formed capability well-formed. -/
theorem narrowOk (c c' : ByteCap) (p : Perm)
    (h : narrowPerm c p = Except.ok c') (hok : capOk c) : capOk c' := by
  obtain ⟨_, hlo, hhi⟩ := narrowFelder c c' p h
  show c'.lo ≤ c'.hi
  rw [hlo, hhi]
  exact hok

#print axioms Gabbro.Grammatik.Niedrig.Bytes.writeByteRahmen
#print axioms Gabbro.Grammatik.Niedrig.Bytes.liesNachSchreib
#print axioms Gabbro.Grammatik.Niedrig.Bytes.gelesenInitialisiert
#print axioms Gabbro.Grammatik.Niedrig.Bytes.splitGetrennt
#print axioms Gabbro.Grammatik.Niedrig.Bytes.splitDeckt
#print axioms Gabbro.Grammatik.Niedrig.Bytes.narrowKeinWachstum

end Gabbro.Grammatik.Niedrig.Bytes
