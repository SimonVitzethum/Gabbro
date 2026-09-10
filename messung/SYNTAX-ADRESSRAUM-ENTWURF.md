# SYNTAX address-space draft — user memory and the validated copy

*Design only, 2026-09-10, worktree lane-91 (base 536e118). This file is the
DRAFT for a SYNTAX.md section on user memory; it does NOT edit SYNTAX.md.
The Lean shapes it quotes live in grammatik/Grammatik/Adressraum.lean.
No builds happen in this lane.*

## Proposed SYNTAX.md text

### User memory — the seventh side and the validated copy

Section 3 closes the space alphabet at six sides and maps the whole concept
out of the grammar: the space of a carrier is a declaration fact and the
barrier follows from it. That reading holds for kernel carriers, whose bytes
no other party rewrites. It does not hold for bytes that live on the far side
of a user/kernel boundary, where a check of a range and the copy from that
range are two reads and the far side may rewrite the bytes between them. The
finding is measured in messung/TOCTOU-ADRESSRAUM.md with verdict GAP: no
user-memory region in the grammar or the world, no copy primitive binding
validation to copying, no shape refusing two reads of the same user bytes
with a check between them.

This section draws the missing shape and nothing else. The region check
itself still stands beside the run — see the closing paragraph.

#### The two sides

Every boundary-crossing copy names which side each end lives on, and there
are exactly two sides: kernel memory and user memory. The side is a property
of the copy datum, not of the pointer type: a pointer names a declared
carrier, while a copy names a user address, a kernel address, a byte count,
and the direction the bytes move. The two directions are the read from user
bytes and the write to user bytes; only the read direction carries the
re-read hazard, but both share the datatype so the check cannot be skipped
on the way out. A kernel step is then either pure, carrying no copy, or it
carries exactly one copy; a loop copying a range piece by piece is one such
step per piece, each checked. A statement crosses the boundary exactly when
it carries a copy, and a crossing statement travels together with the region
it was checked against and the check itself — the three are one datum, as
the validated copy below.

#### The user region, declared

A user-memory region is declared by name and consists of a base address and
a length in bytes, both fixed at the declaration. The check over such a
region is the proposition that a whole accessed interval lies inside it:
the base does not exceed the start address, and the end of the interval
does not exceed the end of the region. A validated copy is then a region, a
copy, and a proof of exactly that proposition about the copy's user range —
inseparable by shape, because the check and the copy name the same region,
the same address, and the same length. A check over one triple paired with
a copy over another triple is not of this shape; that pairing is the hazard
sequence below, not a validated copy. Read back off the shape, the checked
pair of address and length is what is copied, by construction.

#### The validated-copy rule

A validated copy runs as one copy through the checked handle. The checked
reading takes the copy's user address at check time; the copied reading
takes the same address at copy time — the same field of the same datum, so
a copy from another address cannot be written in this shape. The run is the
pair of the two readings, check first and copy second, ordered by position
and not by time. The rule states that the checked value is the copied
value: one snapshot, read once. The address part holds by the handle alone,
before any premise; the value part holds under the single-copy-atomicity
premise, which says that both snapshots agree at the checked address. That
premise is named explicitly and is satisfiable, never vacuous: one snapshot
agrees with itself. Without the premise the goal is unwritable — a run
whose snapshots differ at the copied address exhibits the hazard, and an
unvalidated crossing runs in exactly that shape, so nothing in this section
excludes its hazard. The witness with checked zero and copied one at the
same address shows that the handle alone does not exclude it; only the
snapshot premise does.

The same safety is proved a second time inside the model: the checked
address reads out of the world through the byte-carrier read path, the
write direction lands through the slot write path where the read looks,
and under the world form of the snapshot premise the two model reads agree.
A run whose model reads differ exhibits the hazard there as well.

#### Per-form mapping

| SYNTAX surface | reading | Lean def |
|---|---|---|
| the space alphabet of section 3 | closed at six sides; the missing seventh side is user memory | Seite with its two sides, kern and user |
| a user-memory region, declared by base and length | a named interval the far-side bytes live in | UserRegion with basis and laenge |
| the direction of a crossing copy | read from user bytes, or write to user bytes | Richtung with vonUser and nachUser |
| one boundary-crossing copy | user address, kernel address, byte count and direction in one datum | Kopie |
| the range check | the whole accessed interval lies inside the region | innerhalb, and validiert for the copy's user range |
| validation-then-copy, inseparable | the check and the copy name the same region, address and length | GepruefteKopie with region, kopie and gecheckt; bereich reads the checked pair back |
| one reading of user memory | the address and the value seen | Lesung |
| the check-then-copy sequence | the checked reading first, the copied reading second | PruefDannKopie with pruefung and kopie |
| no hazard | the checked value is the copied value | ohneToctou; snapshotAddr names the single address |
| a kernel statement | pure, or carrying exactly one copy | KernAnweisung with rein and kopie; kreuzt says when it crosses; getrageneKopie names the carried copy |
| a crossing with its validation | statement, region and check travelling together | GepruefterUebergang |
| user memory at a run | address to value, total | UserMem |
| the two readings of a run | the copy's user address at check time and at copy time | checkLesung and kopieLesung; laufSequenz pairs them |
| single-copy atomicity | both snapshots agree at the checked address | EinSnapshot; einSnapshot_refl shows it is satisfiable; laufSequenz_liestGeprueft shows the handle reads the validated address on both positions; gepruefteKopie_ohneToctou is the safety |
| the named gap | checked zero, copied one; a run whose snapshots differ | toctouZeuge with toctouZeuge_toctou; laufSequenz_toctou_ohneSnapshot |
| the model read behind the handle | user-address bytes out of the world through the byte-carrier read path | weltByte and weltBytes over World.bytesAb; weltBytes_istBytesAb states the identity; schreibSlot_liestSelbe lands the write where the read looks |
| the model run | check and copy readings from two worlds through one handle | modellPruefung, modellKopie and modellSequenz; EinSnapshotWelt is the premise over worlds; modellSequenz_liestGeprueft, einSnapshotWelt_gibtWertGleich, modellSequenz_ohneToctou and modellSequenz_toctou_ohneSnapshotWelt mirror the pure run |
| Exec access through a pointer, direct slot access, byte runs | unchanged; one read with one guard set | untouched — Expr.durch, Expr.slot, Expr.leseBytes keep their constructors |

#### What stays future work

The region check still stands beside the run. The world is one flat mapping
with no side partition, and no statement transition discharges the region
check — an out-of-region copy still reads and writes in the model, because
the model memory is total. The exact missing link is twofold: a range check
inside the run, i.e. a statement shape whose transition requires the region
proposition, and a user partition in the world it could check against. Both
are future work; this section specifies the shape they will discharge, not
the discharge.

## Placement proposal

Append the proposed text to dokumente/SYNTAX.md section 3 (Pointers and
address spaces — M3) as its closing subsection, after the bytes paragraph
and before the section rule. Reason: every mapped surface form except the
region declaration already lives in section 3, and the draft changes no
existing row — it adds the seventh side, the region, and the copy next to
the pointer rules. Second, add one row to the section 16.2 table naming the
user-copy hazard as future work with the two missing links (run-level range
check, world partition), so the C6 remainder is booked where the theorem
states what it does not cover.
