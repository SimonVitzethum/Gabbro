module

public import Stage0.Senke.Bild.Ruf.RootAdmission
import Stage0.Senke.Bild.Ruf.StartSite
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildMehr Runner Runner.IR Runner.Beweis Runner.Mach

private theorem pending_root_phase [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {O : Orakel (declOf output.compiled.unit)} {history : List Ev} {before : Cfg imageTSO (Res T)}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {footprint : Nat → W → Prop} {body : List (Option (Res T))} {i : Nat} {r : Res T}
    (partition : ImageRuntimePartition footprint output E O history before state body)
    (pending : body[i]? = some none) (running : before.ths[i]? = some (some r)) :
    ImageRootPhase output E history (before.ms.1.view i) i r state := by
  rcases partition.2.2.2 i with same | ⟨control, _, live, phase⟩
  · rw [pending, running] at same
    cases same
  · rw [running] at live
    cases live
    exact phase

private theorem pending_root_progress [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {O : Orakel (declOf output.compiled.unit)} {history : List Ev} {before after : Cfg imageTSO (Res T)}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {footprint : Nat → W → Prop} {body : List (Option (Res T))} {i : Nat} {r : Res T}
    (partition : ImageRuntimePartition footprint output E O history before state body)
    (pending : body[i]? = some none) (threads : after.ths = before.ths.set i (some r))
    (phase : ImageRootPhase output E history (after.ms.1.view i) i r state)
    (views : ∀ j, j ≠ i → after.ms.1.view j = before.ms.1.view j)
    (buffers : PrivateBuffers footprint after.ms.1)
    (preserveWorld : WeltAt (projectSCState footprint before.ms).1 output.image.Y.withIdle (state.m.speicher.welt []) →
      WeltAt (projectSCState footprint after.ms).1 output.image.Y.withIdle (state.m.speicher.welt []))
    (preserveBodies : ∀ {snapshots positions committed},
      MTRel E.P.mitRuhe O.mitRuhe output.image.passes output.image.Y.withIdle
        ⟨(projectSCState footprint before.ms).1, body⟩ state snapshots positions committed →
      (∀ j s, snapshots j = some s → SoloFootprint footprint j s) →
      ∃ updated, MTRel E.P.mitRuhe O.mitRuhe output.image.passes output.image.Y.withIdle
        ⟨(projectSCState footprint after.ms).1, body⟩ state snapshots positions updated) :
    ImageRuntimePartition footprint output E O history after state body := by
  obtain ⟨_, length, admitted, roots⟩ := partition
  refine ⟨buffers, by rw [threads, List.length_set, length], ?_, ?_⟩
  · rcases admitted with ⟨empty, world⟩ | ⟨snapshots, positions, committed, related, indices⟩
    · exact .inl ⟨empty, preserveWorld world⟩
    · obtain ⟨updated, retained⟩ := preserveBodies related (fun j s known => (indices j s known).2)
      exact .inr ⟨snapshots, positions, updated, retained, indices⟩
  · intro j
    by_cases issuer : j = i
    · subst j
      have inside := length ▸ (List.getElem?_eq_some_iff.mp pending).1
      exact .inr ⟨r, pending, threads.symm ▸ List.getElem?_set_self inside, phase⟩
    · have unchanged : after.ths[j]? = before.ths[j]? := threads.symm ▸ List.getElem?_set_ne (Ne.symm issuer)
      rcases roots j with same | ⟨control, idle, live, phase⟩
      · exact .inl (same.trans unchanged.symm)
      · exact .inr ⟨control, idle, unchanged.trans live, by rw [views j issuer]; exact phase⟩

/-- Starting an installed instruction changes only the pending root's
    control. Its first request is the one selected by the Lean decoder. -/
theorem image_pending_root_begin [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {O : Orakel (declOf output.compiled.unit)} {history : List Ev} {before : Cfg imageTSO (Res T)}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {footprint : Nat → W → Prop} {body : List (Option (Res T))} {i : Nat} {pointer : T}
    (partition : ImageRuntimePartition footprint output E O history before state body)
    (pending : body[i]? = some none) (running : before.ths[i]? = some (some (.next pointer)))
    (site : ImageRootInstruction output i pointer) :
    let after : Cfg imageTSO (Res T) := ⟨before.ms, before.ths.set i (some (IR.step pointer))⟩
    ProcessStep imageTSO actI before [] after ∧ ImageRuntimePartition footprint output E O history after state body := by
  intro after
  have phase := pending_root_phase partition pending running
  have continued : ImageRootPhase output E history (after.ms.1.view i) i (IR.step pointer) state := by
    obtain ⟨_, loader, _⟩ | ⟨start, declared, head, code, frame, fits, args, _⟩ := phase
    · cases loader
    exact .inr ⟨start, declared, head, code, frame, fits, args, pointer, site,
      .inr (.inl (fun _ _ => RunP.refl _ _))⟩
  exact ⟨.priv running rfl, pending_root_progress partition pending rfl continued
    (fun _ _ => rfl) partition.1 (fun world => world) (fun related _ => ⟨_, related⟩)⟩

/-- A real scoped startup store advances the pending root in the shared
    runtime partition. Its byte effect is retained in the IR view and
    stays disjoint from all admitted bodies and the source world. -/
theorem image_pending_root_store [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {O : Orakel (declOf output.compiled.unit)} {history : List Ev} {before : Cfg imageTSO (Res T)}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe} {memory : imageTSO.St}
    {body : List (Option (Res T))} {i index : Nat} {next : T} {word : W} {answer : Ans}
    (partition : ImageRuntimePartition (imageStackFootprint output) output E O history before state body)
    (pending : body[i]? = some none)
    (declared : i ≤ output.starts.length) (inside : index < output.image.Ks)
    (successor : ImageRootInstruction output i next)
    (apart : ∀ start, E.starts[i]? = some start →
      ∀ n, n < (encodeEnv output.image.Y start.2).length → index ≠ FB + FB + n)
    (layout : LayIn output.image.Y.withIdle) :
    let fp := BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * i))
    let address := slot fp (BitVec.ofNat 64 index)
    before.ths[i]? = some (some (wr64 address word next)) →
    imageTSO.ans before.ms i (.wr address word) answer memory →
    let after : Cfg imageTSO (Res T) := ⟨memory, before.ths.set i (some (.next next))⟩
    ProcessStep imageTSO actI before [] after ∧
      ImageRuntimePartition (imageStackFootprint output) output E O history after state body := by
  intro fp address running answered after
  have atRoot := pending_root_phase partition pending running
  obtain ⟨success, phase, views⟩ :=
    ImageRootPhase.store declared inside successor apart atRoot answered
  subst answer
  have owns (byte : W) (written : fenster address byte) :
      imageStackFootprint output i byte ∧ ∀ j, imageStackFootprint output j byte → j = i := by
    have available := imageStackFootprint_slot (output := output) declared inside written
    exact ⟨available, fun j own => imageStackFootprint_disjoint own available⟩
  have buffered := PrivateBuffers.answer partition.1 (request := .wr address word) rfl answered.1 (by
    intro _ _ store byte changed
    cases store
    exact owns byte changed)
  have written := projectSCState_store answered.1 (imageStackFootprint output) owns
  have bytes : (projectSCState (imageStackFootprint output) memory).1 =
      Mem.write (projectSCState (imageStackFootprint output) before.ms).1 address 8 word.toNat := by
    rcases written with ⟨_, refused, _⟩ | ⟨m, placed, _, exactMemory⟩
    · cases refused
    · rw [wr64_eq] at placed
      split at placed
      · exact exactMemory.trans (Option.some.inj placed).symm
      · cases placed
  have room : fp.toNat + 8 * output.image.Ks ≤ output.image.Y.withIdle.lo := by
    have fits : output.image.Ks * (i + 1) ≤ output.image.Ks * (output.starts.length + 1) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right declared 1)
    have start : fp.toNat ≤ output.image.fp0 + 8 * (output.image.Ks * i) := by
      exact Nat.mod_le _ _
    have above := output.stackReservation_bounds.1
    rw [Nat.mul_add, Nat.mul_one] at fits
    change fp.toNat + 8 * output.image.Ks ≤ output.image.Y.lo
    omega
  have bound : fp.toNat + 8 * output.image.Ks ≤ 2 ^ 64 :=
    room.trans output.stackReservation_bounds.2.le
  have preserve {m : Mem} (world : WeltAt m output.image.Y.withIdle (state.m.speicher.welt [])) :
      WeltAt (Mem.write m address 8 word.toNat) output.image.Y.withIdle (state.m.speicher.welt []) :=
    weltAt_stab layout room _ _ world (agree_write bound (Nat.zero_le _) inside _)
  refine ⟨.ask running rfl rfl answered rfl, pending_root_progress partition pending rfl phase views buffered ?_ ?_⟩
  · rw [show after.ms = memory from rfl, bytes]
    exact preserve
  · intro snapshots positions committed related indices
    have disjoint (j : Nat) (s : Solo) (known : snapshots j = some s) (byte : W)
        (written : fenster address byte) (readable : s.F byte) : False := by
      have same := (indices j s known).read byte readable i (owns byte written).1
      subst j
      have live := related.zustand i s known
      change body[i]? = some (some s.r) at live
      rw [pending] at live
      cases live
    refine ⟨Mem.write committed address 8 word.toNat, ?_⟩
    rw [show after.ms = memory from rfl, bytes]
    exact related.commit_disjoint_store disjoint (preserve related.welt)

/-- A scoped startup read advances only the pending root, using the
    actual TSO response and leaving every body snapshot intact. -/
theorem image_pending_root_read [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {O : Orakel (declOf output.compiled.unit)} {history : List Ev} {before : Cfg imageTSO (Res T)}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe} {memory : imageTSO.St}
    {footprint : Nat → W → Prop} {body : List (Option (Res T))}
    {i width : Nat} {address : W} {resume : Ans → Res T} {answer : Ans}
    (partition : ImageRuntimePartition footprint output E O history before state body)
    (pending : body[i]? = some none)
    (running : before.ths[i]? = some (some (.ask (.rd width address) resume)))
    (pastLoader : i ≠ 0 ∨ Res.ask (.rd width address) resume ≠ Runner.Beweis.t4)
    (scope : ∀ byte, byteWindow (readWidth width) address byte → imageRootReads output i byte)
    (answered : imageTSO.ans before.ms i (.rd width address) answer memory) :
    let after : Cfg imageTSO (Res T) := ⟨memory, before.ths.set i (some (resume answer))⟩
    ProcessStep imageTSO actI before [] after ∧ ImageRuntimePartition footprint output E O history after state body := by
  intro after
  obtain ⟨unchanged, phase⟩ := ImageRootPhase.read (pending_root_phase partition pending running)
    pastLoader scope answered
  refine ⟨.ask running rfl rfl answered rfl, pending_root_progress partition pending rfl phase ?_ ?_ ?_ ?_⟩
  · intro j _
    rw [show after.ms = memory from rfl, unchanged]
  · rw [show after.ms = memory from rfl, unchanged]
    exact partition.1
  · rw [show after.ms = memory from rfl, unchanged]
    exact fun current => current
  · intro snapshots positions committed related _
    rw [show after.ms = memory from rfl, unchanged]
    exact ⟨committed, related⟩

end Gabbro.Stage0
