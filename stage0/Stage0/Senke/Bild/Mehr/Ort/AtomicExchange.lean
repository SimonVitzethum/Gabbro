module

public import Stage0.Senke.Sperre.Bindung.ImageCAS
public import Stage0.Senke.Welt.WordCell
public import Stage0.Senke.Anweisung.Atomara
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Gabbro.Grammatik Gabbro.Stage0.Senke.Faeden
  Runner Runner.IR Runner.Mem Runner.Mach Runner.Beweis

/-- The winning or retrying CAS of the actual emitted exchange reads the
    checked scratch values and addresses the declared shared global. -/
theorem image_exchange_prefix [Kern]
    {machine : Cfg imageTSO (Res T)} {code : List II} {base frame : W}
    {thread position scratch address : Nat} {calculation : List II} {expected new : W}
    (atCode : At code position (exC scratch address calculation))
    (encoded : CodeAt (machine.ms.1.view thread) base code)
    (sized : scratch + 3 < 2 ^ 31)
    (old : (machine.ms.1.view thread).rd64 (slot frame (BitVec.ofNat 64 scratch)) = some expected)
    (replacement : (machine.ms.1.view thread).rd64 (slot frame (BitVec.ofNat 64 (scratch + 1))) = some new)
    (location : (machine.ms.1.view thread).rd64 (slot frame (BitVec.ofNat 64 (scratch + 2))) =
      some (BitVec.ofNat 64 address))
    (running : machine.ths[thread]? = some (some (.next
      ⟨base + BitVec.ofNat 64 (16 * (position + (2 + calculation.length) + 1)), frame⟩))) :
    let pointer := T.mk (base + BitVec.ofNat 64 (16 * (position + (2 + calculation.length) + 1))) frame
    ProcessPrefix imageTSO actI machine [] 7
      ⟨machine.ms, machine.ths.set thread (some (.ask (.cas (BitVec.ofNat 64 address) expected new)
        (fun reply => opt reply fun pair => ret1 pointer pair.1)))⟩ := by
  have casCell : code[position + (2 + calculation.length) + 1]? =
      some (ci 22 ((scratch + 3 : Nat) : Int) ((scratch + 2 : Nat) : Int) scratch) := by
    let front := [ci 1 scratch address 0, ci 15 scratch scratch 0] ++ calculation
    let back := [ci 1 ((scratch + 2 : Nat) : Int) address 0,
      ci 22 ((scratch + 3 : Nat) : Int) ((scratch + 2 : Nat) : Int) scratch,
      ci 14 ((scratch + 3 : Nat) : Int) ((scratch + 3 : Nat) : Int) scratch,
      ci 19 ((scratch + 3 : Nat) : Int) (-(16 * ((calculation.length + 5 : Nat) : Int))) 0]
    have suffix := At.right (xs := front) (ys := back) atCode
    have cell := suffix.get (j := 1) (x := ci 22 ((scratch + 3 : Nat) : Int) ((scratch + 2 : Nat) : Int) scratch) rfl
    simpa only [front, List.length_append, List.length_cons, List.length_nil] using cell
  refine image_cas_at running encoded rfl casCell ?_ ?_ ?_
  · rw [sx_nat (by omega)]
    exact location
  · rw [sx_nat (by omega)]
    exact old
  · rw [sx_nat (by omega), slot_plus8]
    exact replacement

/-- The linearization point of an emitted atomic exchange is its real
    shared CAS. Failure returns the current word without publication.
    Success stores the typed replacement, even in the presence of
    other threads' pending private stores. -/
theorem image_atomic_word_CAS [Kern] {D : Deklaration} {layout : Senke.Lay D}
    {machine : Cfg imageTSO (Res T)} {memory : imageTSO.St} {reply : Ans} {resume : Ans → Res T}
    {thread : Nat} {global : D.Glob} {world : World D}
    {expected replacement : W} {value : Wert D (D.gtyp global)} {footprint : Nat → W → Prop}
    (single : aggregateFits (D.gtyp global) = true)
    (represented : WeltAt (projectSCState footprint machine.ms).1 layout world)
    (geometry : LayIn layout) (separate : LayDis layout)
    (encoded : Enc layout (D.gtyp global) (world.globs global) expected →
      Enc layout (D.gtyp global) value replacement)
    (buffers : PrivateBuffers footprint machine.ms.1)
    (outside : ∀ byte, fenster (BitVec.ofNat 64 (layout.ga global)) byte → ∀ owner, ¬ footprint owner byte)
    (writable : Mem.all machine.ms.1.m.wr (BitVec.ofNat 64 (layout.ga global)) 8 = true)
    (waiting : machine.ths[thread]? = some (some (.ask (.cas (BitVec.ofNat 64 (layout.ga global))
      expected replacement) resume)))
    (answered : imageTSO.ans machine.ms thread
      (.cas (BitVec.ofNat 64 (layout.ga global)) expected replacement) reply memory) :
    ProcessStep imageTSO actI machine [] ⟨memory, machine.ths.set thread (some (resume reply))⟩ ∧
    PrivateBuffers footprint memory.1 ∧ machine.ms.1.buf thread = [] ∧
    ∃ observed, reply = some (observed, 0) ∧ Enc layout (D.gtyp global) (world.globs global) observed ∧
      (observed = expected →
        WeltAt (projectSCState footprint memory).1 layout (world.storeGlob global value)) ∧
      (observed ≠ expected → projectSCState footprint memory = projectSCState footprint machine.ms) := by
  let address := BitVec.ofNat 64 (layout.ga global)
  let before := projectSCState footprint machine.ms
  let after := projectSCState footprint memory
  obtain ⟨observed, read, view⟩ := ValueAt.cellWord (aggregateFits_compat single) (represented.2.1 global)
  have agreement : GleichAuf (fenster address) before.1 machine.ms.1.m :=
    fun byte hit => mergedView_committed_at machine.ms.1 footprint byte
      (fun ⟨owner, claimed⟩ => outside byte hit owner claimed)
  have committed : machine.ms.1.m.rd64 address = some observed :=
    (gleich_rd64 agreement).symm.trans read
  obtain ⟨step, returned, written⟩ := image_CAS_reply committed writable waiting answered
  have pending : memory.1.buf = machine.ms.1.buf := by rw [written]
  have retained : PrivateBuffers footprint memory.1 := by
    intro owner store member byte hit
    rw [pending] at member
    exact buffers owner store member byte hit
  have projected := projectSCState_cas_shared answered.1 footprint outside
  have permission : Mem.all before.1.wr address 8 = true := (gleich_wr agreement).trans writable
  have actual := sc_memAns_cas projected
  change memAns before.1 (.cas address expected replacement) = some (reply, after.1) at actual
  have spec := cas_spec (e := expected) (n := replacement) read permission
  rw [memAns_cas, spec, returned] at actual
  have changed : after.1 =
      if observed = expected then Mem.write before.1 address 8 replacement.toNat else before.1 :=
    (congrArg Prod.snd (Option.some.inj actual)).symm
  refine ⟨step, retained, answered.1.1, observed, returned, view, ?_, ?_⟩
  · intro equal
    rw [ite_eq_left equal] at changed
    change WeltAt after.1 layout (world.storeGlob global value)
    rw [changed]
    exact weltAt_globWord (aggregateFits_width single) represented geometry separate (encoded (equal ▸ view))
  · intro different
    rw [ite_eq_right different] at changed
    exact Subtype.ext changed

/-- A winning physical CAS commits the checked exchange at the exact GX
    head. A stale expected value leaves GX at that head and supplies the
    changed actual word for retry. -/
theorem image_exchange_GX [Kern] {D : Deklaration} {layout : Senke.Lay D}
    {P : Programm D} {O : Orakel D} {passes : Nat} {shared : D.Tab ⊕ D.Glob → Prop}
    {machine : Cfg imageTSO (Res T)} {memory : imageTSO.St} {reply : Ans} {resume : Ans → Res T}
    {thread : Nat} {global : D.Glob} {source : FadenMaschine D}
    {expected replacement : W} {footprint : Nat → W → Prop}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {l : Bool}
    (expression : Expr D (D.gtyp global :: Γ) Λ (D.gtyp global))
    (write : (vertragVon D (source.m.faeden thread).kopf.f).gschreibt global = true)
    (allowed : gdarf D global Λ)
    (body : Block D (vertragVon D (source.m.faeden thread).kopf.f) l (D.gtyp global :: Γ) Λ Λ')
    (tail : GRest D (vertragVon D (source.m.faeden thread).kopf.f) l Γ Λ')
    (env : Env D Γ)
    (head : (source.m.faeden thread).kopf.rest =
      ⟨l, Γ, Λ, env, .dann (.exchange global expression write allowed body) tail⟩)
    (live : source.lebt thread = true) (ready : source.wartet thread = [])
    (held : Gabbro.Grammatik.HeldIn Λ (offen (source.m.faeden thread).spur))
    (single : aggregateFits (D.gtyp global) = true)
    (represented : WeltAt (projectSCState footprint machine.ms).1 layout (source.m.weltVon thread))
    (geometry : LayIn layout) (separate : LayDis layout)
    (computed :
      let input := source.m.weltVon thread
      let observed := input.lese Λ (.inr global :: expression.orte)
      Enc layout (D.gtyp global) (input.globs global) expected →
      Enc layout (D.gtyp global)
        (eval observed expression observed (.cons (observed.globs global) env)) replacement)
    (buffers : PrivateBuffers footprint machine.ms.1)
    (outside : ∀ byte, fenster (BitVec.ofNat 64 (layout.ga global)) byte → ∀ owner, ¬ footprint owner byte)
    (writable : Mem.all machine.ms.1.m.wr (BitVec.ofNat 64 (layout.ga global)) 8 = true)
    (waiting : machine.ths[thread]? = some (some (.ask (.cas (BitVec.ofNat 64 (layout.ga global))
      expected replacement) resume)))
    (answered : imageTSO.ans machine.ms thread
      (.cas (BitVec.ofNat 64 (layout.ga global)) expected replacement) reply memory) :
    let input := source.m.weltVon thread
    let read := input.lese Λ (.inr global :: expression.orte)
    let published := read.schreibGlob global Λ (eval read expression read (.cons (read.globs global) env))
    ProcessStep imageTSO actI machine [] ⟨memory, machine.ths.set thread (some (resume reply))⟩ ∧
    PrivateBuffers footprint memory.1 ∧
    ∃ observed, reply = some (observed, 0) ∧
      (observed = expected → ∃ next, FadenSchrittX P O passes shared source next ∧
        next.m.speicher = published.speicher ∧
        next.m.lauf = source.m.lauf ++ rufEigenG thread
          ([Ereignis.gzugriff global true Λ read.haelt] ++ leseEv input Λ (.inr global :: expression.orte)) ∧
        WeltAt (projectSCState footprint memory).1 layout published) ∧
      (observed ≠ expected → projectSCState footprint memory = projectSCState footprint machine.ms) := by
  intro input read published
  obtain ⟨ran, buffered, _, observed, returned, _, success, stale⟩ :=
    image_atomic_word_CAS single represented geometry separate computed buffers outside writable waiting answered
  refine ⟨ran, buffered, observed, returned, ?_, stale⟩
  intro equal
  let appended := [Ereignis.gzugriff global true Λ read.haelt] ++ leseEv input Λ (.inr global :: expression.orte)
  have trace : published.spur = appended ++ (source.m.faeden thread).spur := by
    change [Ereignis.gzugriff global true Λ read.haelt] ++ read.spur = _
    rw [show read.spur = leseEv input Λ (.inr global :: expression.orte) ++ input.spur from rfl]
    rw [List.append_assoc]
    rfl
  have step := RufSchrittG5.dannExchange (P := P) (O := O) (passes := passes)
    source.m thread l Γ Λ Λ' global expression write allowed body tail env head read rfl published rfl appended trace held
  have bytes : WeltAt (projectSCState footprint memory).1 layout published := success equal
  exact ⟨_, .lauf source thread _ live ready (gx_aus_g (.g5 step)), rfl, rfl, bytes⟩

end Gabbro.Stage0.Senke.BildMehr
