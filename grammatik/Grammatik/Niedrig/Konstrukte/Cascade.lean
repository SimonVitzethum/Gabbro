module

public import Grammatik.Niedrig.Konstrukte.Klassen.GeraetSaetze
public import Grammatik.Niedrig.Konstrukte.Klassen.Typisiert
public import Grammatik.Niedrig.Konstrukte.System.Erhaltung

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

/-!
FINAL APPENDED CONSTRUCTOR LIST FOR G6 (15; existing inductives unchanged here):

Ty (2): addr, viewRef.
Expr (6): addrLit, addrOff, narrowAddr, viewGet, arrSlice, strSlice.
Stmt (1): viewPut.
Block (3): bindView, bindCtx, viewRead.
Endblock (3): bindView, bindCtx, viewRead.

bindView takes a class (ordinaryRam/device), the declared span and SpacePairing
against the canonical layout; ClassViewResult is its actual escrow receipt.
Reserved spans are refused. BindClassViewOk + ClassSimRel are the generic
scope boundary; the earlier RAM-only SimRel embeds via classSimRel_of_simRel.
No device view is reclassified as RAM. All access rules retain liveness,
active borrower, permissions, lifetime, owner, lock and effect obligations.

viewGet is RAM-only: byte projection or a field of a declared typed layout.
Records and arrays reuse existing product/array value construction over those
fields; typedViewGetStep gives the whole interpreted family and confinement.
viewPut selects RAM typed store or declared MMIO register write by class.
MMIO preserves the D register class, rtyp, rzusage, exact bus width, alignment,
endianness and ordering. Devices never use ordinary slot reads/writes.

viewRead is device-only, with a strict/fallible mode in ONE constructor per
block kind. Its result is decoded using einpassen and D.rzusage. A strict
broken promise is Hardware.geraet; fallible mode returns its observed value
to the reason continuation. Ill-typed raw answers are Hardware.register in
both modes. Expr cannot encode these returning/hardware channels, hence the
two extra constructors relative to G1's original list of 13.

bindCtx remains the single linear target-binding call. Mmu install/switch,
mask changes and IRQ return specialize it (SystemCallOk, systemBindingStep).
The installed handler table fixes both handler identity and priority; incoming
IRQ mode is contextual, so kernel-mode nesting is inhabited. IrqReturnDuty
pins the saved incoming mode, mask and priority stacks of the continuation.
Page-table updates are viewPut with an explicit PageTableEncodingDuty over
the SAME G store; no abstract setEntry is mistaken for a physical write.
Mmu and IrqDelivery are exact unit-declared assumption identities, with
separate observation predicates. FirmwareEntry establishes the initial grant;
entry declarations and generated frame code remain software proof duties.
Firmware/IRQ entry is entry metadata, not another expression/statement kind.

G6 must retain the exact evaluated address/space/extent in the candidate,
instantiate named binding contracts and generated-entry duties, lift finite
value checks over admitted expression ranges, and connect scope/no-escape,
linear consumption, read tracing and GX induction. These modules supply step
semantics and preservation; they claim no newly admitted or compiling source
form, no target bytes, and no change to Spec.lean. The lead builds them.
-/

end Gabbro.Grammatik.LowLevel.Construct
