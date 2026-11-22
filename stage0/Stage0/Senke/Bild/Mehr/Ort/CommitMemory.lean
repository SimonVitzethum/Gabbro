module

public import Stage0.Senke.Bild.Mehr.Ort.Segment
public import Grammatik.Zielsatz.Atomar.AtomarZiel
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Gabbro.Grammatik Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildLauf Runner Runner.IR
open Gabbro.Grammatik.Zielsatz

variable {D : Deklaration}

/-- The bytes of all allocated cells belonging to the selected carriers. -/
def carrierFootprint (layout : Lay D) (carriers : D.Tab ⊕ D.Glob → Prop) (byte : W) : Prop :=
  ∃ cell : Zelle D, cell.da layout ∧ carriers (Zelle.carrier cell) ∧
    cell.adr layout ≤ byte.toNat ∧ byte.toNat < cell.adr layout + cell.bytes

theorem carrierFootprint_bounds {layout : Lay D} {carriers : D.Tab ⊕ D.Glob → Prop} {byte : W}
    (inside : LayIn layout) (covered : carrierFootprint layout carriers byte) :
    layout.lo ≤ byte.toNat ∧ byte.toNat < layout.hi := by
  obtain ⟨cell, allocated, _, first, last⟩ := covered
  have span : layout.lo ≤ cell.adr layout ∧ cell.adr layout + cell.bytes ≤ layout.hi := by
    cases cell with
    | glob global => exact inside.2.1 global
    | elem table field index => exact inside.1 table field index allocated
  exact ⟨span.1.trans first, last.trans_le span.2⟩

theorem carrierFootprint_iff {layout : Lay D} {carriers : D.Tab ⊕ D.Glob → Prop}
    (separated : LayDis layout) {cell : Zelle D} (allocated : cell.da layout) {byte : W}
    (first : cell.adr layout ≤ byte.toNat) (last : byte.toNat < cell.adr layout + cell.bytes) :
    carrierFootprint layout carriers byte ↔ carriers (Zelle.carrier cell) := by
  constructor
  · rintro ⟨other, present, selected, before, after⟩
    have same : cell = other := by
      by_contra ne
      rcases separated.spans cell other allocated present ne with left | right <;> omega
    exact same.symm ▸ selected
  · intro selected
    exact ⟨cell, allocated, selected, first, last⟩

/-- Unguarded plain cells are private to the declared root whose call
    graph can write their carrier. The assignment is independent of the
    current instruction, so it remains valid across delayed TSO flushes. -/
def plainWriterFootprint [DecidableEq D.Fn] (E : Einheit D) (fs : List D.Fn)
    (layout : Lay D.mitRuhe) (thread : Faden) : W → Prop :=
  carrierFootprint layout fun carrier =>
    (∀ lock, ¬ Bewacht carrier lock) ∧ ¬ AtomarAusgenommen carrier ∧
    ∃ fn, kVon E.P.mitRuhe (fsRuhe fs) (initRuhe E.starts) thread fn = true ∧
      TraegerSchreibt fn carrier = true

/-- The checker excludes access from every other root to a byte reserved
    by a plain writer. This covers both writes and footprint reads, even
    when two declared roots start the same function. -/
theorem plainWriterFootprint_access [DecidableEq D.Fn] {E : Einheit D}
    {fs : Aufzaehlung D.Fn} {ls : Aufzaehlung D.Lock} {cs : Aufzaehlung (D.Tab ⊕ D.Glob)}
    {layout : Lay D.mitRuhe} (hardware : RootNativeFloat.Hardware)
    (accepted : akzeptiertX_pruefer.akzeptiert E fs.1 ls.1 cs.1 = true) (duties : StartPflicht E)
    (separated : LayDis layout) {cell : Zelle D.mitRuhe} (allocated : cell.da layout)
    {byte : W} (first : cell.adr layout ≤ byte.toNat) (last : byte.toNat < cell.adr layout + cell.bytes)
    {writer accessor : Faden} (privateByte : plainWriterFootprint E fs.1 layout writer byte)
    {fn : D.mitRuhe.Fn} (reached : kVon E.P.mitRuhe (fsRuhe fs.1) (initRuhe E.starts) accessor fn = true)
    (access : Zelle.carrier cell ∈ fussOrteG E.P.mitRuhe fn ∨ TraegerSchreibt fn (Zelle.carrier cell) = true) :
    writer = accessor := by
  obtain ⟨unguarded, plain, writes, reachable, modifies⟩ :=
    (carrierFootprint_iff separated allocated first last).mp privateByte
  have valid := (akzeptiertX_pruefer.korrekt E fs ls cs hardware accepted).1
  have validIdle := akzeptiertSpecX_mitRuhe E.P fs.2 valid
  have start := startZulaessig_aus E fs.1 duties (laufzeit_initRuhe E)
  have graphApart := schreibGetrenntK_of start validIdle.einzeln unguarded plain (validIdle.renn _ unguarded plain)
  by_contra different
  obtain ⟨noWrite, noRead⟩ := graphApart writer accessor different writes reachable modifies fn reached
  exact access.elim noRead (fun write => Bool.noConfusion (noWrite.symm.trans write))

/-- A commit publishes the selected bytes and keeps the existing
    access permissions and all bytes outside the chosen carriers. -/
noncomputable def commitBytes (before after : Mem) (selected : W → Prop) : Mem := by
  classical
  exact { before with b := fun byte => if selected byte then after.b byte else before.b byte }

/-- A segment's physical writes can be committed using its carrier set.
    The exact typed values of every other carrier remain those of the
    current committed world, including nested aggregates and pointers. -/
theorem weltAt_commitBytes {layout : Lay D} {before after : Mem}
    {original observed committed : World D} {carriers : D.Tab ⊕ D.Glob → Prop}
    (inside : LayIn layout) (separated : LayDis layout)
    (beforeWorld : WeltAt before layout original)
    (afterWorld : WeltAt after layout observed)
    (reads : after.rd = before.rd)
    (changed : OrtGleich carriers observed committed)
    (unchanged : ∀ carrier, ¬ carriers carrier → TraegerGleich committed.speicher original.speicher carrier) :
    WeltAt (commitBytes before after (carrierFootprint layout carriers)) layout committed := by
  classical
  let memory := commitBytes before after (carrierFootprint layout carriers)
  have copy {cell : Zelle D} (allocated : cell.da layout) {ty : Ty} {value : Wert D ty}
      (size : cell.bytes = 8 * valueWords ty)
      (bound : cell.adr layout + cell.bytes < 2 ^ 64) :
      (if carriers (Zelle.carrier cell) then ValueAt layout after (BitVec.ofNat 64 (cell.adr layout)) 0 ty value
        else ValueAt layout before (BitVec.ofNat 64 (cell.adr layout)) 0 ty value) →
      ValueAt layout memory (BitVec.ofNat 64 (cell.adr layout)) 0 ty value := by
    intro encoded
    by_cases chosen : carriers (Zelle.carrier cell)
    · rw [if_pos chosen] at encoded
      apply ValueAt.congr_read_bytes (size ▸ bound) _ encoded
      intro byte first last
      have selected := (carrierFootprint_iff separated allocated first (size.symm ▸ last)).mpr chosen
      exact ⟨by simp only [memory, commitBytes, dif_pos selected, if_pos selected], congrFun reads.symm byte⟩
    · rw [if_neg chosen] at encoded
      apply ValueAt.congr_read_bytes (size ▸ bound) _ encoded
      intro byte first last
      have excluded := fun selected => chosen ((carrierFootprint_iff separated allocated first (size.symm ▸ last)).mp selected)
      exact ⟨by simp only [memory, commitBytes, dif_neg excluded, if_neg excluded], rfl⟩
  refine ⟨?_, ?_, beforeWorld.2.2⟩
  · intro table field index allocated
    apply copy (cell := .elem table field index) allocated rfl
      (Nat.lt_of_le_of_lt (inside.1 table field index allocated).2 (Nat.lt_trans inside.2.2 (by decide)))
    change if carriers (.inl table) then _ else _
    split
    · next selected => rw [← changed.slots table selected]; exact afterWorld.1 table field index allocated
    · next excluded =>
      have values := unchanged (.inl table) excluded
      change committed.slots table = original.slots table at values
      rw [values]
      exact beforeWorld.1 table field index allocated
  · intro global
    apply copy (cell := .glob global) trivial rfl
      (Nat.lt_of_le_of_lt (inside.2.1 global).2 (Nat.lt_trans inside.2.2 (by decide)))
    change if carriers (.inr global) then _ else _
    split
    · next selected => rw [← changed.globs global selected]; exact afterWorld.2.1 global
    · next excluded =>
      have value := unchanged (.inr global) excluded
      change committed.globs global = original.globs global at value
      rw [value]
      exact beforeWorld.2.1 global

private def endPosition (position : MLage D) (pc : W) (memory : Mem) (machine : RufMaschineG D)
    {Γ : Ctx} {Λ : List (Res D)} (rest : Endblock D (vertragVon D position.B.f) position.l Γ Λ)
    (world : World D) (env : Env D Γ) : MLage D :=
  { position with
    Γ := Γ
    Λ := Λ
    eb := rest
    σ := world
    ρ := env
    Γe := Γ
    Λe := Λ
    ebe := rest
    σe := world
    ρe := env
    pc := pc
    mb := memory
    M := mitSpeicher machine world.speicher }

private theorem reanchorCommitted [Kern] {P : Programm D} {O : Orakel D}
    {passes : Nat} {layout : Lay D} {program : PCfg} {source : FadenMaschine D}
    {snapshots : Nat → Option Solo} {positions : Nat → MLage D} {committed published : Mem}
    {thread : Nat} {snapshot : Solo} {machine : RufMaschineG D} {next : MLage D}
    (matched : MTRel P O passes layout program source snapshots positions committed)
    (registered : snapshots thread = some snapshot)
    (previous : ∀ other, other ≠ (positions thread).thr → machine.faeden other = source.m.faeden other)
    (world : WeltAt published layout (machine.speicher.welt []))
    (outside : ∀ byte, (∀ i s, snapshots i = some s → ¬ s.Wr byte) → GleichAt program.m published byte)
    (valid : next.Ok) (sameProgram : next.B.P = P ∧ next.B.O = O ∧ next.B.passes = passes ∧ next.B.L = layout)
    (sameThread : next.thr = (positions thread).thr)
    (sameHead : machine.faeden next.thr = next.M.faeden next.thr)
    (control : snapshot.r = .next next.start) (memory : snapshot.m = next.mb) :
    MTRel P O passes layout program { source with m := machine } snapshots
      (fun i => if i = thread then next else positions i) published := by
  let reset := fun i => if i = thread then next else positions i
  have identity (i : Nat) : (reset i).thr = (positions i).thr := by
    by_cases current : i = thread
    · subst i
      simpa only [reset, ite_true] using sameThread
    · simp only [reset, ite_eq_right current]
  refine {
    zustand := matched.zustand
    lebend := matched.lebend
    mem := matched.mem
    lage := ?_
    prog := ?_
    solo := ?_
    lebtG := ?_
    inj := ?_
    amRand := ?_
    welt := world
    aussen := outside }
  · intro i s found
    by_cases current : i = thread
    · subst i
      simpa only [reset, ite_true] using valid
    · simpa only [reset, ite_eq_right current] using matched.lage i s found
  · intro i s found
    by_cases current : i = thread
    · subst i
      simpa only [reset, ite_true] using sameProgram
    · simpa only [reset, ite_eq_right current] using matched.prog i s found
  · intro i s found
    by_cases current : i = thread
    · subst i
      have same : s = snapshot := Option.some.inj (found.symm.trans registered)
      subst s
      simp only [reset, ite_true, control, memory]
      exact soloLauf_start _ _
    · simpa only [reset, ite_eq_right current] using matched.solo i s found
  · intro i s found
    change source.lebt (reset i).thr = true ∧ source.wartet (reset i).thr = []
    rw [identity]
    exact matched.lebtG i s found
  · intro i j s t first second same
    change (reset i).thr = (reset j).thr at same
    rw [identity, identity] at same
    exact matched.inj i j s t first second same
  · intro i s found
    change machine.faeden (reset i).thr = (reset i).M.faeden (reset i).thr
    by_cases current : i = thread
    · subst i
      simpa only [reset, ite_true] using sameHead
    · simp only [reset, ite_eq_right current]
      have different : (positions i).thr ≠ (positions thread).thr :=
        fun same => current (matched.inj i thread s snapshot found registered same)
      exact (previous _ different).trans (matched.amRand i s found)

/-- The source commit and the byte-level commit agree on the same
    reachable GX machine. The committed memory takes the selected bytes
    from the actual IR projection and preserves all other bytes. -/
theorem MTRel.commit_world [Kern] {P : Programm D} {O : Orakel D}
    {passes : Nat} {layout : Lay D} {program : PCfg} {source : FadenMaschine D}
    {snapshots : Nat → Option Solo} {positions : Nat → MLage D} {committed : Mem}
    {thread : Nat} {snapshot : Solo}
    (matched : MTRel P O passes layout program source snapshots positions committed)
    (registered : snapshots thread = some snapshot)
    {shared carriers : D.Tab ⊕ D.Glob → Prop} {pc : W} {Γ : Ctx} {Λ : List (Res D)}
    {rest : Endblock D (vertragVon D (positions thread).B.f) (positions thread).l Γ Λ}
    {world : World D} {env : Env D Γ}
    (quiet : let x := positions thread
      Segment x.B.O x.B.passes x.B.R x.Agl x.Cg carriers x.eb x.σ x.ρ rest world env)
    (control : snapshot.r = .next ⟨pc, (positions thread).B.fp⟩)
    (boundary : let x := positions thread
      x.B.RandIR rest pc snapshot.m world env)
    (agree : let x := positions thread
      OrtGleich carriers x.σ (source.m.speicher.welt x.σ.spur))
    (free : FreiA (positions thread).Agl source.m (positions thread).thr)
    (inside : LayIn layout) (separated : LayDis layout)
    (covers : ∀ byte, carrierFootprint layout carriers byte → snapshot.F byte)
    (initialPermissions : (positions thread).mb.rd = committed.rd ∧
      (positions thread).mb.wr = committed.wr) :
    let position := positions thread
    let selected := carrierFootprint layout carriers
    let published := commitBytes committed snapshot.m selected
    ∃ (machine : RufMaschineG D) (world : World D) (next : MLage D),
      FadenErreichbarX P O passes shared source
        ⟨machine, source.lebt, source.wartet, source.rang, source.uhr⟩ ∧
      program.ths[thread]? = some (some (.next ⟨pc, position.B.fp⟩)) ∧
      RandG position.thr position.stapel position.B.f position.rho position.s0 position.Agl
        rest machine world env ∧
      WeltAt published layout (machine.speicher.welt []) ∧
      (∀ other, other ≠ position.thr → machine.faeden other = source.m.faeden other) ∧
      (∀ thread, offen (machine.faeden thread).spur = offen (source.m.faeden thread).spur) ∧
      PrivateSourceTrace source.m.lauf machine.lauf ∧
      (∀ byte, selected byte → GleichAt published program.m byte) ∧
      (∀ byte, ¬ selected byte → GleichAt published committed byte) ∧
      next.thr = position.thr ∧
      MTRel P O passes layout program { source with m := machine } snapshots
        (fun i => if i = thread then next else positions i) published := by
  classical
  intro position selected published
  obtain ⟨machine, finalWorld, reached, pointer, _, sourceBoundary, changes, preserved, holdings, trace, others⟩ :=
    matched.commit_segment registered (shared := shared) quiet control boundary agree free
  have exactLayout := (matched.prog thread snapshot registered).2.2.2
  obtain ⟨rd, wr⟩ := (matched.solo thread snapshot registered).permissions
  have reads := rd.trans initialPermissions.1
  have writes := wr.trans initialPermissions.2
  have afterWorld : WeltAt snapshot.m layout world := by
    obtain ⟨_, _, _, _, _, _, _, _, _, memory, _⟩ := boundary
    rwa [exactLayout] at memory
  have bytes : WeltAt published layout finalWorld := weltAt_commitBytes inside separated matched.welt afterWorld
    reads changes (by intro cell outside; simpa only [speicher_welt_speicher] using others cell outside)
  have store : machine.speicher = finalWorld.speicher := by
    obtain ⟨⟨_, state⟩, _, _⟩ := sourceBoundary
    exact state.2
  have exactBytes : WeltAt published layout (machine.speicher.welt []) := by
    rw [store]
    cases finalWorld
    exact bytes
  have updated : ∀ byte, selected byte → GleichAt published program.m byte := by
    intro byte chosen
    obtain ⟨value, read, write⟩ := matched.mem.gleich thread snapshot registered byte (covers byte chosen)
    exact ⟨by simpa only [published, commitBytes, ite_eq_left chosen] using value.symm,
      (congrFun reads.symm byte).trans read.symm, (congrFun writes.symm byte).trans write.symm⟩
  have unchanged : ∀ byte, ¬ selected byte → GleichAt published committed byte := fun byte excluded =>
    ⟨by simp only [published, commitBytes, ite_eq_right excluded], rfl, rfl⟩
  let next := endPosition position pc snapshot.m machine rest world env
  have held := (matched.lage thread snapshot registered)
  have valid : next.Ok := by
    refine ⟨held.tor, held.sicht, held.frame, held.ruf, .halt _ _ _, boundary, ?_⟩
    exact randG_umsetzen sourceBoundary changes.spur.symm rfl rfl sourceBoundary.2.2
  have outside byte
      (unwritten : ∀ i s, snapshots i = some s → ¬ s.Wr byte) : GleichAt program.m published byte := by
    by_cases chosen : selected byte
    · exact (updated byte chosen).symm
    · exact (matched.aussen byte unwritten).trans (unchanged byte chosen).symm
  have continued := reanchorCommitted matched registered preserved exactBytes outside valid
    (matched.prog thread snapshot registered) (show next.thr = position.thr from rfl) rfl control rfl
  exact ⟨machine, finalWorld, next, reached, pointer, sourceBoundary, exactBytes, preserved, holdings,
    trace, updated, unchanged, rfl, continued⟩

end Gabbro.Stage0.Senke.BildMehr
