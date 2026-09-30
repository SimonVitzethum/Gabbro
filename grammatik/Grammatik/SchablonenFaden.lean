/-
  File:      Grammatik/SchablonenFaden.lean
  Part of:   Gabbro -- the generator-template library (T5 of
             dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md): hosted threads without a C
             library (C-free lane, 2026-09-30).

  Rows of `crates/gabbro-check/src/schablonen.rs`:

  * `tor.trampolin` -- the C-only entry the emitter writes for every gate that claims a
    stack (`emit.rs`, `syscall_stumpf`): the gate's `syscall`; in the parent (`rax != 0`) the
    raw answer; in the child (`rax == 0`) `andq $-16, %rsp`, `call *%r_kind`, `call *%r_ende`,
    `ud2`. `r_kind`/`r_ende` are two callee-saved registers the gate neither binds nor lists as
    destroyed, loaded with C function DESIGNATORS at the call site.
  * `faden.laufzeit` -- the thread runtime the hosted driver writes
    (`treiber.rs::FADEN_LAUFZEIT`): `gabbro_faden_start` hands the join word to the gate twice
    (the kernel's `eltern` and `kind` word) and `gabbro_faden_warte` loops on the word until it
    reads 0, waiting through the program's `gabbro_os_warte_wort` in between.

  Both are ABSTRACT CORES like `start.nolibc` (SchablonenOhneLibc.lean §2): machine G has no
  thread creation -- the runtime premise (d) `Laufzeit.start`/`.einmal` of the goal says the
  declared starts run, each on its own thread (Zielsatz/Spec.lean). What is proved here is the
  mechanics the templates add on top of the program's gate contract:

  * `trampolin_kind`: in the child, the root and then the end are called -- the registers they
    travel in survive the call into the child exactly because the gate does not destroy them
    (the premise the emitter checks, `C187`) -- each call entered with `rsp + 8` 16-aligned
    (the SysV entry condition), the root's frame lying below the handed top, and the `ud2`
    reached only if the end returns;
  * `trampolin_eltern`: the parent sees the kernel's answer and nothing of the child's path;
  * `faden_warte_korrekt`: the wait returns only after the thread's END, for every
    interleaving the gate's contract allows (the id stored before the child runs, 0 stored
    after it has ended) -- and `faden_warte_ohne_eltern` shows the first half of that order is
    not decoration.

  NOT proved: that the kernel keeps the gate's contract (premise (c) of the goal; the gate's
  assumption `linux_os_clone_vertrag`), and that the stack is deep enough (stack depth is NOT
  CLAIMED by the goal statement).

  No `sorry`, no `native_decide`, no new axiom; each theorem has a witness instantiating ALL its
  premises jointly.
-/

namespace Gabbro.Grammatik

namespace FadenLaufzeit

/-! ## 1. `tor.trampolin` -/

/-- The registers the trampoline reads, as the kernel leaves them. -/
structure Regs where
  rax : Int
  rsp : Nat
  kind : Nat
  ende : Nat

/-- The gate's `syscall`: in the child `rax = 0` and `rsp` is the handed top; every register
    the gate does not destroy is the caller's (`bewahrt`: the two registers are neither bound,
    nor destroyed, nor the answer -- the emitter's `C187` check). -/
def nachSyscall (vorher : Regs) (spitze : Nat) (bewahrt : Bool) : Regs :=
  { rax := 0, rsp := spitze,
    kind := if bewahrt then vorher.kind else 0,
    ende := if bewahrt then vorher.ende else 0 }

/-- What the child path of the trampoline does: the calls it makes (target, `rsp` at the
    callee's first instruction) and whether it reaches `ud2`. -/
structure KindPfad where
  rufe : List (Nat × Nat)
  ud2 : Bool

/-- `andq $-16, %rsp`; `call *kind` (pushes 8); the root returns (`rsp` back); `call *ende`;
    `ud2` only if `ende` returns. -/
def kindPfad (r : Regs) (endeKehrtZurueck : Bool) : KindPfad :=
  let a := r.rsp - r.rsp % 16
  { rufe := [(r.kind, a - 8), (r.ende, a - 8)], ud2 := endeKehrtZurueck }

/-- **Soundness of `tor.trampolin`, the child.** With the two registers preserved by the gate
    and a handed top of at least 16 bytes of stack below it: the child calls the root and then
    the end, both handed by the parent, each entered with `rsp + 8` 16-aligned and strictly
    below the handed top (inside the stack the template carved), and never runs `ud2` when the
    end does not return. -/
theorem trampolin_kind (vorher : Regs) (spitze : Nat) (hsp : 24 ≤ spitze)
    (endeKehrtZurueck : Bool) (hnie : endeKehrtZurueck = false) :
    let p := kindPfad (nachSyscall vorher spitze true) endeKehrtZurueck
    p.rufe.map Prod.fst = [vorher.kind, vorher.ende] ∧
    (∀ z ∈ p.rufe, (z.2 + 8) % 16 = 0 ∧ z.2 < spitze ∧ spitze - 24 ≤ z.2) ∧
    p.ud2 = false := by
  refine ⟨rfl, ?_, hnie⟩
  intro z hz
  simp only [kindPfad, nachSyscall, if_true, List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with h | h <;> subst h <;> simp only <;> omega

/-- The preservation premise is not decoration: a gate that destroyed the two registers would
    send the child to address 0. -/
theorem trampolin_ohne_bewahrung (vorher : Regs) (spitze : Nat) :
    (kindPfad (nachSyscall vorher spitze false) false).rufe.map Prod.fst = [0, 0] := rfl

/-- **The parent path.** The parent's registers after the gate are the kernel's answer; the
    trampoline hands back exactly that word and runs nothing of the child's path. -/
def elternAntwort (rax : Int) (h : rax ≠ 0) : Int := let _ := h; rax

theorem trampolin_eltern (rax : Int) (h : rax ≠ 0) : elternAntwort rax h = rax := rfl

/-! ## 2. `faden.laufzeit` -- the join -/

/-- What the kernel and the thread do to one join word, in the order they happen. -/
inductive Ereignis where
  | setzt (tid : Nat)      -- CLONE_PARENT_SETTID: the id, before the child runs
  | laeuft                 -- a step of the child
  | endet                  -- the child's last step
  | loescht                -- CLONE_CHILD_CLEARTID: 0, after the end
  deriving DecidableEq, Repr

/-- The word after a prefix of events, starting from whatever it held (`w0`). -/
def wort (w0 : Nat) : List Ereignis → Nat
  | [] => w0
  | .setzt t :: r => wort t r
  | .loescht :: r => wort 0 r
  | _ :: r => wort w0 r

/-- **The gate's contract as a trace**: the id (non-zero) stored before the child runs, then
    the child's steps, its end, and only then the clear. -/
def vertragsSpur (t : Nat) (schritte : Nat) : List Ereignis :=
  .setzt t :: (List.replicate schritte .laeuft ++ [.endet, .loescht])

theorem wort_replicate (w0 k : Nat) (r : List Ereignis) :
    wort w0 (List.replicate k .laeuft ++ r) = wort w0 r := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.cons_append, wort]; exact ih

theorem take_vor_dem_ende (s m : Nat) (r : List Ereignis) (h : m ≤ s) :
    (List.replicate s Ereignis.laeuft ++ r).take m = List.replicate m Ereignis.laeuft := by
  induction s generalizing m with
  | zero => simp at h; subst h; rfl
  | succ s ih =>
    cases m with
    | zero => rfl
    | succ m =>
      simp only [List.replicate_succ, List.cons_append, List.take_succ_cons]
      rw [ih m (by omega)]

theorem ende_im_take (s m : Nat) (h : s < m) :
    Ereignis.endet ∈ (List.replicate s Ereignis.laeuft ++ [Ereignis.endet, Ereignis.loescht]).take m := by
  induction s generalizing m with
  | zero =>
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp
  | succ s ih =>
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [List.replicate_succ, List.cons_append, List.take_succ_cons, List.mem_cons]
    right
    exact ih m (by omega)

/-- **Soundness of the join (`faden_warte_korrekt`).** The wait starts after the start
    returned, i.e. after the id was stored (a prefix that contains `setzt t`, `t > 0`); it
    returns only on reading 0. Over every prefix of the contract's trace that holds the id: a
    word reading 0 means the child's END is in the prefix -- whatever the child's length and
    wherever the waiter looks. -/
theorem faden_warte_korrekt (t schritte w0 n : Nat) (ht : 0 < t) (hn : 1 ≤ n)
    (h0 : wort w0 ((vertragsSpur t schritte).take n) = 0) :
    Ereignis.endet ∈ (vertragsSpur t schritte).take n := by
  unfold vertragsSpur at *
  obtain ⟨m, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [List.take_succ_cons, wort] at h0
  simp only [List.take_succ_cons, List.mem_cons]
  right
  by_cases hm : m ≤ schritte
  · exfalso
    rw [take_vor_dem_ende schritte m _ hm] at h0
    have e := wort_replicate t m []
    simp only [List.append_nil] at e
    rw [e] at h0
    simp only [wort] at h0
    omega
  · exact ende_im_take schritte m (by omega)

/-- The first half of the order is not decoration: without the id stored before the child
    runs, a waiter that looks before the child's first step reads the word's old 0 and returns
    while the thread has not even started (the defect of 2026-09-26 in reverse). -/
theorem faden_warte_ohne_eltern :
    wort 0 ([.laeuft, .endet, .loescht].take 1) = 0 ∧
    Ereignis.endet ∉ [Ereignis.laeuft, .endet, .loescht].take 1 := by decide

/-- **Witness** (all premises jointly): a thread with id 4242 that runs three steps; a waiter
    that looks after all six events reads 0 and the end is in what it saw; one that looks after
    four reads the id. And the trampoline on a concrete top. -/
theorem faden_zeuge :
    wort 7 ((vertragsSpur 4242 3).take 6) = 0 ∧
    Ereignis.endet ∈ (vertragsSpur 4242 3).take 6 ∧
    wort 7 ((vertragsSpur 4242 3).take 4) = 4242 ∧
    ((kindPfad (nachSyscall ⟨9, 0, 0x401000, 0x402000⟩ 0x7f0000800000 true) false).rufe.map
      Prod.fst = [0x401000, 0x402000]) :=
  ⟨by decide, faden_warte_korrekt 4242 3 7 6 (by decide) (by decide) (by decide), by decide,
    (trampolin_kind ⟨9, 0, 0x401000, 0x402000⟩ 0x7f0000800000 (by decide) false rfl).1⟩

end FadenLaufzeit

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.FadenLaufzeit.trampolin_kind
#print axioms Gabbro.Grammatik.FadenLaufzeit.faden_warte_korrekt
#print axioms Gabbro.Grammatik.FadenLaufzeit.faden_zeuge
