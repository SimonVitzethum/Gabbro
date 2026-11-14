module

public import Grammatik.Niedrig.Bytes.GrantsSaetze

@[expose] public section

namespace Gabbro.Grammatik.Niedrig.Bytes

/-- `ByteState` is a plain structure. "Read implies written" is a property
    of reachable states, not of the type. Only successful byte writes extend
    this reachability derivation. Reads, lend, return and revocation return no
    byte state; grant writes below preserve reachability on both
    success and refusal. No initially supplied nonempty state is assumed. -/
inductive Erreichbar : ByteState → Prop
  | leer : Erreichbar leererZustand
  | schreib {s next : ByteState} (c : ByteCap) (i v : Nat)
      (vorher : Erreichbar s) (geschrieben : writeByte c i v s = Except.ok next) :
      Erreichbar next

/-- An actual successful write in a history ending at this exact state.
    `hier` supplies a reachable prefix; `weiter` retains the witness across
    subsequent writes. Thus this is provenance, not just a bound on values. -/
inductive Schreibspur : ByteState → Nat → Nat → Nat → Prop
  | hier {s next : ByteState} (c : ByteCap) (i v : Nat)
      (vorher : Erreichbar s) (geschrieben : writeByte c i v s = Except.ok next) :
      Schreibspur next c.traeger i v
  | weiter {s next : ByteState} {t j w : Nat} (c : ByteCap) (i v : Nat)
      (spur : Schreibspur s t j w) (geschrieben : writeByte c i v s = Except.ok next) :
      Schreibspur next t j w

/-- Successful byte writes expose their checked range and exact state. -/
theorem writeByteFakten {c : ByteCap} {i v : Nat} {s next : ByteState}
    (h : writeByte c i v s = Except.ok next) :
    (c.lo ≤ i ∧ i < c.hi) ∧ next = schreibNach s c.traeger i v := by
  unfold writeByte at h
  split at h
  · split at h
    · rename_i hrange
      split at h
      · cases h
        exact ⟨hrange, rfl⟩
      · cases h
    · cases h
  · cases h

/-- Reachability implies the full byte invariant, also at uninitialised cells. -/
theorem erreichbarByteOk {s : ByteState} (h : Erreichbar s) : byteOk s := by
  induction h with
  | leer =>
      intro _ _
      show (0 : Nat) < 256
      decide
  | schreib c i v _ hw ih => exact writeByteByteOk c i v _ _ hw ih

/-- Strong provenance form: each initialised cell has its CURRENT value
    written by a successful `writeByte` in a history ending at this state.
    The induction constructs that history from the reachability derivation. -/
theorem erreichbarSchreibspur {s : ByteState} (h : Erreichbar s) :
    ∀ t j, s.init t j = true → Schreibspur s t j (s.wert t j) := by
  induction h with
  | leer =>
      intro t j hi
      have hf : false = true := hi
      cases hf
  | @schreib s next c i v vorher hw ih =>
      intro t j hi
      have he := (writeByteFakten hw).2
      by_cases ht : t = c.traeger ∧ j = i
      · obtain ⟨rfl, hj⟩ := ht
        rw [hj]
        have hv : next.wert c.traeger i = v := by
          rw [he]
          exact schreibNachWert s c.traeger i v
        rw [hv]
        exact Schreibspur.hier c i v vorher hw
      · have hinit : s.init t j = true := by
          rw [he, schreibNachInitAnderer s c.traeger i v t j ht] at hi
          exact hi
        have hwert : next.wert t j = s.wert t j := by
          rw [he]
          exact schreibNachWertAnderer s c.traeger i v t j ht
        rw [hwert]
        exact Schreibspur.weiter c i v (ih t j hinit) hw

/-- Successful reads return exactly the stored value. -/
theorem readByteWert {c : ByteCap} {i v : Nat} {s : ByteState}
    (h : readByte c i s = Except.ok v) : s.wert c.traeger i = v := by
  unfold readByte at h
  split at h
  · split at h
    · split at h
      · cases h
        rfl
      · cases h
    · cases h
  · cases h

/-- A reachable successful read returns a byte written in its history. -/
theorem gelesenGeschrieben {s : ByteState} {c : ByteCap} {i v : Nat}
    (hr : Erreichbar s) (hl : readByte c i s = Except.ok v) :
    v < 256 ∧ Schreibspur s c.traeger i v := by
  have he := readByteWert hl
  rw [← he]
  exact ⟨erreichbarByteOk hr c.traeger i,
    erreichbarSchreibspur hr c.traeger i (gelesenInitialisiert c i v s hl)⟩

/-- Grant writes preserve reachability because they delegate to `writeByte`. -/
theorem gebrauchSchreibErreichbar {table : GrantTable} {g : Grant} {i v : Nat}
    {s next : ByteState} {scope : Option Nat} (hr : Erreichbar s)
    (hw : gebrauchSchreib table g i v s scope = Except.ok next) : Erreichbar next :=
  Erreichbar.schreib g.cap i v hr (gebrauchSchreibByte hw)

/-- The committed state remains reachable for every grant write outcome. -/
theorem gebrauchSchreibErhaelt {table : GrantTable} {g : Grant} {i v : Nat}
    {s : ByteState} {scope : Option Nat} (hr : Erreichbar s) :
    Erreichbar (zustandNach s (gebrauchSchreib table g i v s scope)) := by
  cases hw : gebrauchSchreib table g i v s scope with
  | error _ => exact hr
  | ok next => exact gebrauchSchreibErreichbar hr hw

/-- Grant reads inherit the same bound and write-history provenance. -/
theorem grantGelesenGeschrieben {table : GrantTable} {g : Grant} {i v : Nat}
    {s : ByteState} {scope : Option Nat} (hr : Erreichbar s)
    (hl : gebrauchLies table g i s scope = Except.ok v) :
    v < 256 ∧ Schreibspur s g.cap.traeger i v :=
  gelesenGeschrieben hr (gebrauchLiesByte hl)

/-- A loan write survives return and is read through the lender. The saved
    scope must previously permit reading this byte; unrelated escrows are
    retained, rather than silently discarded by the round trip. -/
theorem leiheSchreibLies {table loaned restored : GrantTable} {g : Grant}
    {c : ByteCap} {id i v : Nat} {scope : Option Nat} {s next : ByteState}
    (hl : leihe table g c id scope = Except.ok loaned)
    (hw : gebrauchSchreib loaned
      { cap := c
        generation := g.generation } i v s (Option.some id) = Except.ok next)
    (hr : gibZurueck loaned id = Except.ok restored)
    (hread : darfLesen g.cap.rechte = true)
    (hfree : pruefeLeihen table.loans g scope (punkt g.cap i Perm.lese) = Except.ok ()) :
    gebrauchLies restored g i next scope = Except.ok v := by
  have he : table = restored := Except.ok.inj ((leiheRueckgabe hl).symm.trans hr)
  rw [← he]
  obtain ⟨hlive, hrange, _, _⟩ := leiheFakten hl
  obtain ⟨hc, hlo, _, hhi⟩ := hrange
  have hf := writeByteFakten (gebrauchSchreibByte hw)
  have hber : g.cap.lo ≤ i ∧ i < g.cap.hi :=
    ⟨Nat.le_trans hlo hf.1.1, Nat.lt_of_lt_of_le hf.1.2 hhi⟩
  have hinit : next.init g.cap.traeger i = true := by
    rw [hf.2, ← hc]
    exact schreibNachInit s c.traeger i v
  have hwert : next.wert g.cap.traeger i = v := by
    rw [hf.2, ← hc]
    exact schreibNachWert s c.traeger i v
  unfold gebrauchLies
  rw [if_pos hlive, hfree]
  dsimp only
  unfold readByte
  rw [if_pos hread, if_pos hber, if_pos hinit, hwert]

#print axioms erreichbarByteOk
#print axioms erreichbarSchreibspur
#print axioms gelesenGeschrieben
#print axioms gebrauchSchreibErhaelt
#print axioms leiheSchreibLies

end Gabbro.Grammatik.Niedrig.Bytes
