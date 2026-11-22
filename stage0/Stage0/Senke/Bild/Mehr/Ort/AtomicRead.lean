module

public import Stage0.Senke.Bild.Mehr.Ort.AtomicExchange

@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Gabbro.Grammatik Gabbro.Stage0.Senke.Faeden
  Runner Runner.IR Runner.Mem Runner.Mach Runner.Beweis

/-- The load cell of the emitted `awaits` reads the address from its
    destination slot, where the preceding instruction saved it. -/
theorem image_awaits_prefix [Kern]
    {machine : Cfg imageTSO (Res T)} {code tail : List II} {base frame : W}
    {thread position scratch address : Nat}
    (atCode : At code position ([ci 1 scratch address 0, ci 15 scratch scratch 0] ++ tail))
    (encoded : CodeAt (machine.ms.1.view thread) base code)
    (sized : scratch < 2 ^ 31)
    (saved : (machine.ms.1.view thread).rd64 (slot frame (BitVec.ofNat 64 scratch)) =
      some (BitVec.ofNat 64 address))
    (running : machine.ths[thread]? = some (some (.next
      ⟨base + BitVec.ofNat 64 (16 * (position + 1)), frame⟩))) :
    let pointer := T.mk (base + BitVec.ofNat 64 (16 * (position + 1))) frame
    ProcessPrefix imageTSO actI machine [] 4
      ⟨machine.ms, machine.ths.set thread
        (some (.ask (.rd 8 (BitVec.ofNat 64 address)) (fun reply => opt reply fun pair => ret1 pointer pair.1)))⟩ := by
  have cell : code[position + 1]? = some (ci 15 scratch scratch 0) :=
    atCode.get (j := 1) rfl
  refine image_load_at running encoded rfl cell ?_
  rw [sx_nat sized]
  exact saved

/-- The answer to the emitted publication load takes the corresponding
    GX step, binds the encoded value, and preserves the entire store. -/
theorem image_awaits_GX [Kern] {D : Deklaration} {layout : Senke.Lay D}
    {P : Programm D} {O : Orakel D} [SichtOK O] {passes : Nat} {shared : D.Tab ⊕ D.Glob → Prop}
    {machine : Cfg imageTSO (Res T)} {memory : imageTSO.St} {reply : Ans} {resume : Ans → Res T}
    {thread : Nat} {global : D.Glob} {source : FadenMaschine D} {footprint : Nat → W → Prop}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {l : Bool}
    (allowed : gdarf D global Λ) (atomic : D.atomar global = true)
    (body : Block D (vertragVon D (source.m.faeden thread).kopf.f) l (D.gtyp global :: Γ) Λ Λ')
    (tail : GRest D (vertragVon D (source.m.faeden thread).kopf.f) l Γ Λ')
    (env : Env D Γ)
    (head : (source.m.faeden thread).kopf.rest =
      ⟨l, Γ, Λ, env, .dann (.awaits global (D.nutzlast global) rfl allowed atomic body) tail⟩)
    (live : source.lebt thread = true) (ready : source.wartet thread = [])
    (held : Gabbro.Grammatik.HeldIn Λ (offen (source.m.faeden thread).spur))
    (single : aggregateFits (D.gtyp global) = true)
    (represented : WeltAt (projectSCState footprint machine.ms).1 layout (source.m.weltVon thread))
    (buffers : PrivateBuffers footprint machine.ms.1)
    (outside : ∀ byte, fenster (BitVec.ofNat 64 (layout.ga global)) byte → ∀ owner, ¬ footprint owner byte)
    (waiting : machine.ths[thread]? = some (some (.ask (.rd 8 (BitVec.ofNat 64 (layout.ga global))) resume)))
    (answered : imageTSO.ans machine.ms thread (.rd 8 (BitVec.ofNat 64 (layout.ga global))) reply memory) :
    let input := source.m.weltVon thread
    let question := input.fragt (.inr (.inr global))
    ProcessStep imageTSO actI machine [] ⟨memory, machine.ths.set thread (some (resume reply))⟩ ∧
    memory = machine.ms ∧
    (∃ word extra, reply = some (word, extra) ∧ Enc layout (D.gtyp global) (input.globs global) word) ∧
    ∃ next, FadenSchrittX P O passes shared source next ∧ next.m.speicher = source.m.speicher ∧
      next.m.lauf = source.m.lauf ++
        rufEigenG thread (leseEv question Λ [.inr global] ++ [.fremd (.inr (.inr global))]) ∧
      HEq (next.m.faeden thread).kopf.rest
        (⟨l, D.gtyp global :: Γ, Λ, .cons (input.globs global) env, .dann body (.schrumpf tail)⟩ :
          Σ linear : Bool, Σ types : Ctx, Σ resources : List (Res D),
            Env D types × GRest D (vertragVon D (source.m.faeden thread).kopf.f) linear types resources) := by
  intro input question
  let address := BitVec.ofNat 64 (layout.ga global)
  obtain ⟨word, read, encoded⟩ := ValueAt.cellWord (aggregateFits_compat single) (represented.2.1 global)
  have agrees : GleichAuf (fenster address) (projectSCState footprint machine.ms).1 machine.ms.1.m :=
    fun byte hit => mergedView_committed_at machine.ms.1 footprint byte
      (fun ⟨owner, claimed⟩ => outside byte hit owner claimed)
  have committed : machine.ms.1.m.rd64 address = some word := (gleich_rd64 agrees).symm.trans read
  obtain ⟨ran, unchanged, extra, returned⟩ :=
    image_shared_word_reply committed buffers (fun byte hit => outside byte hit thread) waiting answered
  let observed := question.lese Λ [.inr global]
  let appended := leseEv question Λ [.inr global] ++ [.fremd (.inr (.inr global))]
  have trace : observed.spur = appended ++ (source.m.faeden thread).spur := by
    change (question.lese Λ [.inr global]).spur = _
    rw [lese_spur] <;> rfl
  have step := RufSchrittG5.dannAwaits (P := P) (O := O) (passes := passes)
    source.m thread l Γ Λ Λ' global (D.nutzlast global) rfl allowed atomic body tail env head
    (SichtOK.sicht (O := O) (g := global) (σ := question)) observed rfl appended trace held
  refine ⟨ran, unchanged, ⟨word, extra, returned, encoded⟩, _, .lauf source thread _ live ready (gx_aus_g (.g5 step)),
    rfl, rfl, ?_⟩
  simp only [rufUpdateG_self] <;> rfl

end Gabbro.Stage0.Senke.BildMehr
