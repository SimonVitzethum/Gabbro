module

public import Grammatik.Niedrig.Witnesses.RealizeFixture

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.RealizeWitness

def reservation (table : Bool) : Anbieter.Strecke :=
  if table then ⟨160, 224⟩ else ⟨64, 128⟩

def reservedClosed : Anbieter.Zust :=
  { lebend := [reservation false]
    ram := fun _ => false }

def committedClosed : Anbieter.Zust :=
  { reservedClosed with
    ram := fun byte => reservedClosed.ram byte ||
      (decide (64 ≤ byte) && decide (byte < 128)) }

def reservedOpen : Anbieter.Zust :=
  { committedClosed with lebend := reservation true :: committedClosed.lebend }

def providerFinal : Anbieter.Zust :=
  { reservedOpen with
    ram := fun byte => reservedOpen.ram byte ||
      (decide (160 ≤ byte) && decide (byte < 224)) }

def providerTrace : List Anbieter.Ereig :=
  [.hole 64 64, .fuell 64 128, .hole 64 160, .fuell 160 224]

theorem provider_run : Anbieter.Lauf 8 Anbieter.Zust.leer providerTrace providerFinal := by
  have reserveClosed : Anbieter.PStep 8 Anbieter.Zust.leer (.hole 64 64) reservedClosed :=
    .hole (by decide) (by decide) (by decide)
      (by intro r member; cases member)
  have fillClosed : Anbieter.PStep 8 reservedClosed (.fuell 64 128) committedClosed :=
    .fuell (r := reservation false) (by exact List.mem_cons_self ..)
      (by decide) (by decide)
  have reserveOpen : Anbieter.PStep 8 committedClosed (.hole 64 160) reservedOpen := by
    apply Anbieter.PStep.hole (by decide) (by decide) (by decide)
    intro r member
    change r ∈ [reservation false] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst r
    exact .inr (by decide)
  have fillOpen : Anbieter.PStep 8 reservedOpen (.fuell 160 224) providerFinal :=
    .fuell (r := reservation true) (by exact List.mem_cons_self ..)
      (by decide) (by decide)
  exact .cons reserveClosed (.cons fillClosed (.cons reserveOpen (.cons fillOpen (.nil _))))

def placement (table : Bool) : CarrierReservation layout table (reservation table) :=
  { first := if table then 2 else 0
    elements := if table then 4 else 8
    positiveElements := by cases table <;> decide
    positiveWidth := by cases table <;> decide
    start := by cases table <;> rfl
    finish := by cases table <;> rfl
    extent := by cases table <;> decide }

theorem span_in_reservation (table : Bool) (byte : Nat)
    (inside : (span table).range.drin byte) : (reservation table).drin byte := by
  cases table with
  | false =>
      change 66 ≤ byte ∧ byte < 66 + 10 at inside
      change 64 ≤ byte ∧ byte < 128
      omega
  | true =>
      change 164 ≤ byte ∧ byte < 164 + 20 at inside
      change 160 ≤ byte ∧ byte < 224
      omega

def coverage (table : Bool) : ProviderSpan layout providerFinal (span table) :=
  { reservation := reservation table
    live := by
      cases table <;>
        simp [providerFinal, reservedOpen, committedClosed, reservedClosed]
    carrier := placement table
    backing := rfl
    included := span_in_reservation table
    resident := by
      intro byte inside
      have bounds := span_in_reservation table byte inside
      change (false || (decide (64 ≤ byte) && decide (byte < 128))) ||
        (decide (160 ≤ byte) && decide (byte < 224)) = true
      cases table with
      | false =>
          change 64 ≤ byte ∧ byte < 128 at bounds
          simp [bounds.1, bounds.2]
      | true =>
          change 160 ≤ byte ∧ byte < 224 at bounds
          simp [bounds.1, bounds.2] }

/-- Nonempty firmware-supplied memory is recorded without inventing program
    writes or asserting empty-rooted L3b reachability. -/
def firmwareMemory : FirmwareMemory authority :=
  { bytes :=
      { init := fun backing byte => decide
          ((backing = 7 ∧ 66 ≤ byte ∧ byte < 76) ∨
           (backing = 9 ∧ 164 ≤ byte ∧ byte < 184))
        wert := fun _ _ => 42 }
    byteValues := by
      intro backing byte
      change 42 < 256
      decide
    supplied := by
      intro s member initialized byte inside
      change s ∈ [span false, span true] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · change 66 ≤ byte ∧ byte < 76 at inside
        change decide ((7 = 7 ∧ 66 ≤ byte ∧ byte < 76) ∨
          (7 = 9 ∧ 164 ≤ byte ∧ byte < 184)) = true
        simp [inside.1, inside.2]
      · change 164 ≤ byte ∧ byte < 184 at inside
        change decide ((9 = 7 ∧ 66 ≤ byte ∧ byte < 76) ∨
          (9 = 9 ∧ 164 ≤ byte ∧ byte < 184)) = true
        simp [inside.1, inside.2]
    confined := by
      intro backing byte initialized
      change decide ((backing = 7 ∧ 66 ≤ byte ∧ byte < 76) ∨
        (backing = 9 ∧ 164 ≤ byte ∧ byte < 184)) = true at initialized
      have facts : (backing = 7 ∧ 66 ≤ byte ∧ byte < 76) ∨
          (backing = 9 ∧ 164 ≤ byte ∧ byte < 184) := of_decide_eq_true initialized
      rcases facts with closed | opened
      · exact ⟨span false, List.mem_cons_self .., closed.1.symm, rfl, closed.2⟩
      · exact ⟨span true, List.mem_cons_of_mem _ (List.mem_cons_self ..),
          opened.1.symm, rfl, opened.2⟩ }

/-- The final token is a real fresh-grant handoff, not the firmware handle. -/
noncomputable def record : BootProviderRecord contract handoff.authority layout :=
  { granule := 8
    positiveGranule := by decide
    providerTrace := providerTrace
    providerFinal := providerFinal
    run := provider_run
    covers := by
      intro s member
      change s ∈ [span false, span true] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      exact if closed : s = span false then
        closed.symm ▸ coverage false
      else by
        have opened : s = span true := by
          rcases member with equal | equal
          · exact False.elim (closed equal)
          · exact equal
        exact opened.symm ▸ coverage true
    firmwareAuthority := authority
    firmwareContext := initial
    boot := firmware_entry
    names := rfl
    firmwareMemory := firmwareMemory
    owners := handoff.owners
    frame := handoff.into
    mintChain := OwnerMintChain.handoff OwnerMintChain.initial handoff.moved }

theorem provider_realizes_zeuge : handoff.authority.Realizes layout :=
  realizes_of_provider_boot record (handoff_preserves initial_valid handoff).1

/-- Joint premises: real provider events, firmware entry without a realization
    premise, layout correctness, a fresh owner handoff and derived realization. -/
theorem provider_joint_zeuge :
    Anbieter.Lauf 8 Anbieter.Zust.leer providerTrace providerFinal ∧
    Anbieter.Gut providerFinal ∧ LayoutOk layout ∧
    FirmwareEntry contract authority initial ∧ handoff.next.Valid handoff.authority ∧
    handoff.authority.Realizes layout ∧
    handoff.owners.owns handoff.authority.names handoff.into handoff.authority.token :=
  ⟨provider_run, record.good, layout_correct, firmware_entry,
    handoff_preserves initial_valid handoff, provider_realizes_zeuge, record.owned.2⟩

theorem provider_nondegenerate_zeuge :
    (span false).space.backing ≠ (span true).space.backing ∧
    (span false).space.nominal ≠ (span true).space.nominal ∧
    D.offen true = true ∧ D.count true = 0 ∧
    0 < (span false).length ∧ 0 < (span true).length ∧
    (placement true).first = 2 ∧ (placement true).elements = 4 ∧
    firmwareMemory.bytes.init 9 164 = true ∧ firmwareMemory.bytes.wert 9 164 = 42 ∧
    handoff.authority.token.handle ≠ authority.token.handle := by
  have initialized : firmwareMemory.bytes.init 9 164 = true :=
    firmwareMemory.supplied (span true)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) rfl 164
      (by change 164 ≤ 164 ∧ 164 < 184; exact ⟨by decide, by decide⟩)
  refine ⟨?_, ?_, rfl, rfl, ?_, ?_, rfl, rfl, initialized, rfl, ?_⟩
  · change (7 : Nat) ≠ 9
    decide
  · change (0 : Nat) ≠ 1
    decide
  · change 0 < 10
    decide
  · change 0 < 20
    decide
  · intro equal
    have grants := congrArg ArenaOwnership.Handle.grant equal
    change (1 : Nat) = 0 at grants
    cases grants

theorem provider_commit_zeuge :
    ∃ lo hi, Anbieter.Ereig.fuell lo hi ∈ providerTrace ∧ lo ≤ 164 ∧ 164 < hi :=
  record.byte_committed
    (span := span true) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    (by change 164 ≤ 164 ∧ 164 < 184; decide)

theorem scaled_open_carrier_zeuge :
    (span true).Realizes layout ∧ layout.inTabelle true (9, 164) ∧
    layout.nominal 9 = D.tableSpace true := by
  refine ⟨span_inside_carrier (by decide) (coverage true), ?_, rfl⟩
  exact ⟨rfl, by decide, .inl rfl⟩

end Gabbro.Grammatik.LowLevel.RealizeWitness
