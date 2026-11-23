/-
  File:      Grammatik/Zielsatz/Ideal/Prototyp/Impl.lean
  Subject:   PROTOTYPE of S7: the implementation machine of the fragment, a miniature of G∞ over GX
             (`dokumente/PERFECT-MODEL.md` §3.5): every interleaving, units are NOT indivisible.

  A unit runs in fine-grained steps: a lock section is `acquire`, one step per body operation, `release`; a masked
  section is `mask`, its body, `unmask`. The interrupt handler enters whenever the mask of core 0 is clear --
  also in the middle of a lock section of thread 0, which it then PREEMPTS (thread 0 does not step while the
  handler runs). The handler runs under the mask (it sets it on entry and clears it on exit), so it does not nest.
  The device is outside: a `dev` read returns any value, and while a buffer is lent the device writes it at any
  time (`dma`, the arbitrary-change rely of §4); `takeBack` returns its content as an answer.
  Plain accesses execute on one memory with no race check (a racy program runs; that it is excluded is the job of
  the static discipline, the premise of the refinement theorem). Every step carries its CONTEXT (who stepped)
  and at most one outside ANSWER.
-/
module

public import Grammatik.Zielsatz.Ideal.Prototyp.Atomics

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.Ideal.Prototyp

/-- Who takes a step: a thread, the interrupt handler, or the outside device writing a lent buffer. -/
inductive Ctx where
  | thr (t : Fin 2)
  | irq
  | dma
  deriving DecidableEq

/-- The position inside a running unit: the remaining body of a lock section (holding lock `k`) or of a
    masked section. -/
inductive Cur where
  | lk (k : Nat) (rest : List Op)
  | mk (rest : List Op)

/-- A thread of the implementation. -/
structure Th where
  prog : List Seg
  cur : Option Cur
  regs : Regs
  view : View
  lent : Nat → Bool

/-- The implementation state. -/
structure S where
  th : Fin 2 → Th
  /-- the running handler: its remaining body and its registers -/
  hd : Option (List Op × Regs)
  mem : Mem
  owner : Nat → Option (Fin 2)
  lview : Nat → View
  /-- the interrupt mask of core 0 -/
  mask : Bool
  am : AMem

/-- The initial implementation state of a program. -/
def S.init (P : Prog) : S where
  th t := ⟨P.thread t, none, fun _ => 0, fun _ => 0, fun _ => false⟩
  hd := none
  mem _ := 0
  owner _ := none
  lview _ := fun _ => 0
  mask := false
  am := AMem.init

/-- Thread `t` may run: thread 0 is preempted while the handler runs on its core. -/
def Laeuft (s : S) (t : Fin 2) : Prop := t = 0 → s.hd = none

/-- Replace thread `t`. -/
def S.setTh (s : S) (t : Fin 2) (x : Th) : S := { s with th := upd s.th t x }

/-- One step of the implementation: context, answer (`some v` exactly when an outside question was answered). -/
inductive SStep (P : Prog) : S → Ctx → Option Int → S → Prop
  | acq {s t k body ps} : (s.th t).cur = none → (s.th t).prog = .lock k body :: ps → s.owner k = none →
      Laeuft s t →
      SStep P s (.thr t) none
        { (s.setTh t ⟨ps, some (.lk k body), (s.th t).regs, vjoin (s.th t).view (s.lview k), (s.th t).lent⟩) with
            owner := upd s.owner k (some t) }
  | lkOp {s t k op rest a ρ' m'} : (s.th t).cur = some (.lk k (op :: rest)) → Laeuft s t →
      opStep op a ((s.th t).regs, s.mem) = some (ρ', m') →
      SStep P s (.thr t) a { (s.setTh t { s.th t with cur := some (.lk k rest), regs := ρ' }) with mem := m' }
  | rel {s t k} : (s.th t).cur = some (.lk k []) → Laeuft s t →
      SStep P s (.thr t) none
        { (s.setTh t { s.th t with cur := none }) with
            owner := upd s.owner k none, lview := upd s.lview k (s.th t).view }
  | msk {s body ps} : (s.th 0).cur = none → (s.th 0).prog = .masked body :: ps → s.hd = none →
      SStep P s (.thr 0) none { (s.setTh 0 { s.th 0 with prog := ps, cur := some (.mk body) }) with mask := true }
  | mkOp {s op rest a ρ' m'} : (s.th 0).cur = some (.mk (op :: rest)) → s.hd = none →
      opStep op a ((s.th 0).regs, s.mem) = some (ρ', m') →
      SStep P s (.thr 0) a { (s.setTh 0 { s.th 0 with cur := some (.mk rest), regs := ρ' }) with mem := m' }
  | umsk {s} : (s.th 0).cur = some (.mk []) → s.hd = none →
      SStep P s (.thr 0) none { (s.setTh 0 { s.th 0 with cur := none }) with mask := false }
  | atom {s t o op ps w ρ' V' A'} : (s.th t).cur = none → (s.th t).prog = .atom o op :: ps → Laeuft s t →
      AStep o op (s.th t).regs (s.th t).view s.am w ρ' V' A' →
      SStep P s (.thr t) none { (s.setTh t { s.th t with prog := ps, regs := ρ', view := V' }) with am := A' }
  | lend {s t x ps} : (s.th t).cur = none → (s.th t).prog = .lend x :: ps → Laeuft s t →
      SStep P s (.thr t) none (s.setTh t { s.th t with prog := ps, lent := upd (s.th t).lent x true })
  | take {s t x ps} : (s.th t).cur = none → (s.th t).prog = .takeBack x :: ps → Laeuft s t →
      SStep P s (.thr t) (some (s.mem x)) (s.setTh t { s.th t with prog := ps, lent := upd (s.th t).lent x false })
  | set {s t r e ps} : (s.th t).cur = none → (s.th t).prog = .set r e :: ps → Laeuft s t →
      SStep P s (.thr t) none
        (s.setTh t { s.th t with prog := ps, regs := upd (s.th t).regs r (e.eval (s.th t).regs) })
  | irqIn {s} : s.hd = none → s.mask = false →
      SStep P s .irq none { s with hd := some (P.handler, fun _ => 0), mask := true }
  | hOp {s op rest ρ a ρ' m'} : s.hd = some (op :: rest, ρ) → opStep op a (ρ, s.mem) = some (ρ', m') →
      SStep P s .irq a { s with hd := some (rest, ρ'), mem := m' }
  | hEnd {s ρ} : s.hd = some ([], ρ) →
      SStep P s .irq none { s with hd := none, mask := false }
  | dma {s t x v} : (s.th t).lent x = true →
      SStep P s .dma none { s with mem := upd s.mem x v }

/-- Finite runs of the implementation with their trace of contexts and answers. -/
inductive SStar (P : Prog) : S → List (Ctx × Option Int) → S → Prop
  | refl (s : S) : SStar P s [] s
  | tail {s s' s'' tr c a} : SStar P s tr s' → SStep P s' c a s'' → SStar P s (tr ++ [(c, a)]) s''

end Gabbro.Grammatik.Zielsatz.Ideal.Prototyp
