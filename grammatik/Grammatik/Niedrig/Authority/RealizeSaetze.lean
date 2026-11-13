module

public import Grammatik.Niedrig.Authority.Realize

public section

namespace Gabbro.Grammatik.LowLevel

variable {D : Deklaration}

/-- Membership in a span uses bytes, with no hidden element scaling. -/
theorem span_range_drin_iff (span : Span D) (byte : Nat) :
    span.range.drin byte ↔ span.base ≤ byte ∧ byte < span.base + span.length :=
  Iff.rfl

/-- Exact bridge from the provider's byte interval to the carrier's scaled
    element interval. A span's subrange need not itself be element-aligned. -/
theorem CarrierReservation.drin_iff {lay : AdressLayout D} {table : D.Tab}
    {reservation : Anbieter.Strecke} (placement : CarrierReservation lay table reservation)
    (byte : Nat) : reservation.drin byte ↔
      lay.basis table + placement.first * lay.breite table ≤ byte ∧
      byte < lay.basis table + (placement.first + placement.elements) * lay.breite table := by
  unfold Anbieter.Strecke.drin
  rw [placement.start, placement.finish]

/-- Element placement converts to byte containment by multiplication with the
    carrier width. For a closed carrier the last element is bounded; for an
    OPEN carrier the layout region extends upward without a ceiling. -/
theorem CarrierReservation.byte_inside {lay : AdressLayout D} {table : D.Tab}
    {reservation : Anbieter.Strecke} (placement : CarrierReservation lay table reservation)
    {byte : Nat} (inside : reservation.drin byte) :
    lay.basis table ≤ byte ∧
      (D.offen table = true ∨ byte < lay.basis table +
        (D.count table).toNat * lay.breite table) := by
  have bounds := (placement.drin_iff byte).mp inside
  have low := bounds.1
  have high := bounds.2
  refine ⟨by omega, ?_⟩
  rcases placement.extent with hopen | hclosed
  · exact .inl hopen
  · have scaled := Nat.mul_le_mul_right (lay.breite table) hclosed
    right
    omega

/-- A nonempty span included in a placed reservation realizes the whole
    carrier extent, not just one chosen byte. Testing the first and last
    byte is essential: the upper bound of Realizes is non-strict. -/
theorem span_inside_carrier {span : Span D} {lay : AdressLayout D}
    {state : Anbieter.Zust} (positive : 0 < span.length)
    (coverage : ProviderSpan lay state span) : span.Realizes lay := by
  have first : span.range.drin span.base := by
    change span.base ≤ span.base ∧ span.base < span.base + span.length
    exact ⟨Nat.le_refl _, by omega⟩
  have last : span.range.drin (span.base + span.length - 1) := by
    change span.base ≤ span.base + span.length - 1 ∧
      span.base + span.length - 1 < span.base + span.length
    omega
  have low := (coverage.carrier.byte_inside (coverage.included _ first)).1
  have high := (coverage.carrier.byte_inside (coverage.included _ last)).2
  refine ⟨coverage.backing, low, ?_⟩
  rcases high with hopen | hclosed
  · exact .inl hopen
  · right
    omega

/-- The provider invariant is derived from the run, rather than supplied as
    an unrelated good final-state assumption. -/
theorem BootProviderRecord.good {P I : Type} {b : BootContract D P I}
    {a : Authority D} {lay : AdressLayout D} (record : BootProviderRecord b a lay) :
    Anbieter.Gut record.providerFinal :=
  Anbieter.lauf_gut Anbieter.gut_leer record.run

/-- Every resident span byte has a real commit event in the recorded run. -/
theorem BootProviderRecord.byte_committed {P I : Type} {b : BootContract D P I}
    {a : Authority D} {lay : AdressLayout D} (record : BootProviderRecord b a lay)
    {span : Span D} (member : span ∈ a.spans) {byte : Nat}
    (inside : span.range.drin byte) :
    ∃ lo hi, Anbieter.Ereig.fuell lo hi ∈ record.providerTrace ∧ lo ≤ byte ∧ byte < hi :=
  Anbieter.ram_nur_gefuellt record.run byte ((record.covers span member).resident byte inside)

/-- Ledger validity and actual ownership follow each exact mint/transfer
    equation from the initial firmware grant, including fresh grant handles. -/
theorem OwnerMintChain.owned {names : OwnerNamespace D} {initial final : OwnerState D}
    {root frame : ArenaOwnership.Frame} {grant token : OwnerToken D}
    (chain : OwnerMintChain names initial root grant final frame token)
    (valid : initial.ledger.valid) (owned : initial.owns names root grant) :
    final.ledger.valid ∧ final.owns names frame token := by
  induction chain with
  | initial => exact ⟨valid, owned⟩
  | mint prefix declaration minted ih =>
      have result := OwnerState.mint_grant ih.1 minted
      exact ⟨result.1, result.2.1⟩
  | handoff prefix moved ih =>
      have result := OwnerState.transfer_grant ih.1 moved
      exact ⟨result.1, result.2.1⟩

theorem BootProviderRecord.owned {P I : Type} {b : BootContract D P I}
    {a : Authority D} {lay : AdressLayout D} (record : BootProviderRecord b a lay) :
    record.owners.ledger.valid ∧ record.owners.owns a.names record.frame a.token := by
  apply record.mintChain.owned record.boot.valid.2.1
  rw [← record.names]
  exact record.boot.owned

/-- Discharge the existing realization premise. LayoutOk remains necessary
    for carrier separation, fields and nominal spaces, but is not needed for
    this numeric containment consequence of explicit carrier placements. -/
theorem realizes_of_provider_boot {P I : Type} {b : BootContract D P I}
    {a : Authority D} {lay : AdressLayout D} (record : BootProviderRecord b a lay)
    (valid : a.Valid) : a.Realizes lay := by
  intro span member
  exact span_inside_carrier (valid.2.2.1 span member).1.1 (record.covers span member)

/-- The existing view/layout theorem with its Realizes premise discharged
    by the provider/firmware record, for every byte of every issued view. -/
theorem ram_view_in_provider_layout {P I : Type} {b : BootContract D P I}
    {a : Authority D} {c : Context D P I} {lay : AdressLayout D}
    (record : BootProviderRecord b a lay)
    (valid : c.Valid a) (correct : LayoutOk lay) (result : ViewResult a c)
    {byte : Adresse} (inside : result.view.Contains byte) :
    lay.inTabelle result.view.span.table byte ∧
      lay.nominal byte.1 = D.tableSpace result.view.span.table :=
  ram_view_in_layout result lay correct (realizes_of_provider_boot record valid.1) inside

end Gabbro.Grammatik.LowLevel
