/-
  File:      Grammatik/CNebenlaeufig.lean
  Subject:   THE CLOSING THEOREM, STAGE (b), GENERIC PART (plan
             `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §3 item 4 and §7):
             an interleaved, sequentially consistent semantics for the
             emitted C; the runtime's lock primitive and thread creation;
             the named premise DRF-SC as ONE proposition; data-race freedom
             of the C; and the transfer of machine G's conclusion to the C
             runs through a simulation certificate.

  THE SEMANTICS IN ONE PARAGRAPH
    A configuration (`KonfC`) is the shared C state of `CSpeicher.lean`
    (`CSt`), one thread state per `Faden`, and the holder of every lock of
    the runtime. A running thread (`CFaden.an k ρ`) is its root function's
    CONTINUATION -- a list of statements -- and its locals; a thread that
    was never created or has returned is `aus`. A step (`SchrittC`) is taken
    by ONE thread, chosen freely (every schedule is a run: the semantics is
    SC, an interleaving over one memory). It is one of: split a sequence
    (`teile`); leave the root body (`ende`); call the runtime's lock
    primitive (`sperre`: `L_nimm()` or `L_gib()`, a foreign call the
    unit's `sperre` table names, whose meaning is a PARAMETER `LP`); or run
    ONE synchronisation-free statement of the continuation as a BLOCK
    (`block`/`rueck`) with the existing sequential semantics (`Exec`,
    `CallAt`, `CFormen.lean`) -- calls inside it included.

  WHY BLOCKS BETWEEN SYNCHRONISATION POINTS, AND NOT ONE STEP PER ACCESS.
    (1) The sequential C semantics of the emitted subset is big-step
    (`Exec`); the block rule reuses it unchanged, with its determinism
    (`exec_det`) and every T4 correspondence lemma. (2) The C11 memory model
    gives meaning ONLY to data-race-free programs, and for those every
    execution is sequentially consistent AND serialisable at the
    granularity of synchronisation-free regions: two regions of different
    threads that touch a common object with a write are ordered by a
    release/acquire of a lock, so the accesses of an SC interleaving
    commute into one where every region runs without interruption (DRF-SC
    and the region-serialisability corollary: Adve and Hill 1990, Boehm and
    Adve 2008; for the C11 model Batty et al. 2011). The premise below
    (`DRFSC`) is stated at exactly this granularity, and its hypothesis is
    race freedom at the SAME granularity (`RennfreiC`). (3) Machine G itself
    runs a statement's leaf as one step; a C block corresponds to a
    contiguous segment of G steps of ONE thread, which is a G interleaving
    among others -- so the simulation is a forward simulation into G's
    interleavings, never a reordering argument.

  THE PREMISES (named, hypotheses of the theorem, never axioms)
    * `DRFSC E LP K0 Echt` -- the real memory model (C11 plus the hardware
      profile) is SC for race-free programs: if the C program is race free
      (`RennfreiC`), every observation of a real execution (`Echt`, a
      parameter, like the binary's behaviour `binEin` of stage (a)) is the
      observation of some SC interleaving.
    * `LaufzeitC` -- THE RUNTIME LIST, the same list as
      `NICHTINTERFERENZ.md` §10 and PLAN §5: thread creation only at declared
      roots, each at most once, from the declared initial memory, no lock
      held (`FadenStartC`); and the lock primitive (a ticket lock) behaves
      as `sperrAbstrakt`: `L_nimm` only when the lock is free, making the
      caller its holder; `L_gib` only by the holder, freeing it; program
      memory untouched; the step reads nothing but the lock's own holder
      entry (`sperrAbstrakt_rahmen`, `sperrAbstrakt_nur_eigen`: it reveals
      nothing but held or free). The NI-only entries of that list (the
      scheduler class, idle slots) are not premises here: the safety
      statement holds for EVERY schedule, since every interleaving is a run.

  WHAT IS PROVED HERE (generic, for every unit and every G program)
    * `sim_erreichbar`, `sim_lauf` -- a simulation certificate (`SimC`)
      lifts every C run to a G run, segment by segment.
    * `rennfreiC_aus_sim` -- if the certificate's segments cover the C
      footprints (`SegPasst`) and G is race free (`RennfreiBis`, a leg of
      the goal theorem), the C program is race free (`RennfreiC`). This is
      what makes the DRF-SC premise APPLICABLE: its hypothesis is proved.
    * `schluss_b` -- the closing schema: under the premises, the C program
      is race free, and every real observation is that of an SC run whose
      configuration is related to a reachable machine of G at which the
      goal theorem's conclusion `Ziel` holds.
  The program-specific part (the certificate for one corpus program, its
  witness) is `Schlusssatz124.lean`.
-/
import Grammatik.CFormenDet
import Grammatik.Zielsatz.Beweis

namespace Gabbro.Grammatik

open Zielsatz

/-! ## 1. The runtime's lock primitive -/

/-- One call of the runtime's lock primitive: `L_nimm()` takes lock `L`,
    `L_gib()` gives it back. -/
inductive SperrOp where
  | nimm (L : Nat)
  | gib (L : Nat)
  deriving DecidableEq, Repr

/-- The lock a primitive call is about. -/
def SperrOp.nr : SperrOp → Nat
  | .nimm L => L
  | .gib L => L

/-- Who holds which lock of the runtime (by lock number). -/
abbrev Halter := Nat → Option Faden

/-- One holder entry replaced. -/
def halterSetze (h : Halter) (L : Nat) (v : Option Faden) : Halter :=
  fun L' => if L' = L then v else h L'

/-- The meaning of one call of the lock primitive by thread `t`: the holder
    table before and after (program memory is untouched by construction:
    the primitive's own words are runtime objects, not program objects). -/
def SperrSem : Type := Faden → SperrOp → Halter → Halter → Prop

/-- **THE SPECIFICATION OF THE LOCK PRIMITIVE.** `L_nimm` fires only when
    `L` is free and makes the caller its holder; `L_gib` fires only when the
    caller holds `L` and frees it. A ticket lock meets it: `nimm` returns
    once the caller's ticket is served (the lock was released by the previous
    holder and not yet taken), `gib` serves the next ticket. -/
def sperrAbstrakt : SperrSem := fun t op h h' =>
  match op with
  | .nimm L => h L = none ∧ h' = halterSetze h L (some t)
  | .gib L => h L = some t ∧ h' = halterSetze h L none

/-- The primitive changes nothing but its own lock's holder entry. -/
theorem sperrAbstrakt_rahmen {t : Faden} {op : SperrOp} {h h' : Halter}
    (hs : sperrAbstrakt t op h h') (L : Nat) (hL : L ≠ op.nr) : h' L = h L := by
  cases op with
  | nimm K =>
      obtain ⟨_, rfl⟩ := hs
      exact if_neg hL
  | gib K =>
      obtain ⟨_, rfl⟩ := hs
      exact if_neg hL

/-- **It reveals nothing but held or free**: whether a call can proceed
    depends on the lock's own holder entry and on nothing else (the
    runtime entry of `NICHTINTERFERENZ.md` §10: a ticket lock reveals nothing
    but "held or not"). -/
theorem sperrAbstrakt_nur_eigen {t : Faden} {op : SperrOp} {h₁ h₂ : Halter}
    (e : h₁ op.nr = h₂ op.nr) :
    (∃ h', sperrAbstrakt t op h₁ h') ↔ (∃ h', sperrAbstrakt t op h₂ h') := by
  cases op with
  | nimm L =>
      have e' : h₁ L = h₂ L := e
      constructor
      · rintro ⟨_, hh, -⟩
        exact ⟨_, by rw [← e']; exact hh, rfl⟩
      · rintro ⟨_, hh, -⟩
        exact ⟨_, by rw [e']; exact hh, rfl⟩
  | gib L =>
      have e' : h₁ L = h₂ L := e
      constructor
      · rintro ⟨_, hh, -⟩
        exact ⟨_, by rw [← e']; exact hh, rfl⟩
      · rintro ⟨_, hh, -⟩
        exact ⟨_, by rw [e']; exact hh, rfl⟩

/-! ## 2. The unit and the interleaved semantics -/

/-- No foreign call other than the lock primitive has a meaning inside a
    block (a foreign call in a block is outside this stage: CUT). -/
def keinXR : CCallR := fun _ _ _ _ _ => False

theorem keinXR_funktional : keinXR.Funktional := fun _ _ _ _ _ _ _ h _ => h.elim

/-- **An emitted C unit, for the concurrent semantics**: layout, device
    answers, the functions, which foreign functions are the runtime's lock
    primitive (`L_nimm` of lock `L` is `sperre n = some (.nimm L)`), and the
    call depth a block runs with (`CallAt`'s depth, Gabbro's `rufAt` fuel). -/
structure CEinheit where
  L : CLayout
  orc : DevOrc
  Pr : CProg
  sperre : Nat → Option SperrOp
  tiefe : Nat

/-- A statement run as one block by the sequential semantics: the root frame
    is frame `tiefe + 1`, its callees run at depth `tiefe`. -/
def CEinheit.laeuft (E : CEinheit) (s : CS) (st : CSt) (ρ : CLok) (o : COut) : Prop :=
  Exec E.L E.orc (E.tiefe + 1) (CallAt E.L E.orc keinXR E.Pr E.tiefe) keinXR s st ρ o

/-- A block has ONE outcome (`exec_det`). -/
theorem CEinheit.laeuft_det (E : CEinheit) {s : CS} {st : CSt} {ρ : CLok} {o1 o2 : COut}
    (h1 : E.laeuft s st ρ o1) (h2 : E.laeuft s st ρ o2) : o1 = o2 :=
  exec_det (callAt_funktional E.L E.orc keinXR keinXR_funktional E.Pr E.tiefe)
    keinXR_funktional h1 h2

/-- A C thread: not running (never created, or returned from its root), or
    running with a continuation of statements and its locals. -/
inductive CFaden where
  | aus
  | an (k : List CS) (ρ : CLok)

/-- **A configuration of the concurrent C program**: the shared state, every
    thread, and the holder of every lock of the runtime. -/
structure KonfC where
  st : CSt
  faeden : Faden → CFaden
  halter : Halter

/-- One thread state replaced. -/
def fadenSetze (m : Faden → CFaden) (t : Faden) (c : CFaden) : Faden → CFaden :=
  fun u => if u = t then c else m u

theorem fadenSetze_eq (m : Faden → CFaden) (t : Faden) (c : CFaden) : fadenSetze m t c t = c :=
  if_pos rfl

theorem fadenSetze_ne (m : Faden → CFaden) (t u : Faden) (c : CFaden) (h : u ≠ t) :
    fadenSetze m t c u = m u :=
  if_neg h

/-- What a step did: nothing observable (`still`), one block `s`, or one call
    of the lock primitive. -/
inductive Etikett where
  | still
  | block (s : CS)
  | sperre (op : SperrOp)

/-- A sequence is split, never run as a block. -/
def CS.istSeq : CS → Bool
  | .seq _ _ => true
  | _ => false

/-- **THE SC STEP**: thread `t` takes one step of kind `ℓ`. Every other
    thread is untouched; which thread steps is free. -/
inductive SchrittC (E : CEinheit) (LP : SperrSem) : KonfC → Faden → Etikett → KonfC → Prop where
  /-- `a; b` at the head of the continuation: split it. -/
  | teile (K : KonfC) (t : Faden) (a b : CS) (k : List CS) (ρ : CLok)
      (h : K.faeden t = .an (.seq a b :: k) ρ) :
      SchrittC E LP K t .still ⟨K.st, fadenSetze K.faeden t (.an (a :: b :: k) ρ), K.halter⟩
  /-- The root body is done: the thread ends (a `void` root falls off its end). -/
  | ende (K : KonfC) (t : Faden) (ρ : CLok) (h : K.faeden t = .an [] ρ) :
      SchrittC E LP K t .still ⟨K.st, fadenSetze K.faeden t .aus, K.halter⟩
  /-- A synchronisation-free statement, run as ONE block, ends normally. -/
  | block (K : KonfC) (t : Faden) (s : CS) (k : List CS) (ρ : CLok) (st' : CSt) (ρ' : CLok)
      (h : K.faeden t = .an (s :: k) ρ) (hs : s.istSeq = false)
      (hx : E.laeuft s K.st ρ (.norm st' ρ')) :
      SchrittC E LP K t (.block s) ⟨st', fadenSetze K.faeden t (.an k ρ'), K.halter⟩
  /-- A block that returns from the root: the thread ends. -/
  | rueck (K : KonfC) (t : Faden) (s : CS) (k : List CS) (ρ : CLok) (st' : CSt) (v : Option CVal)
      (h : K.faeden t = .an (s :: k) ρ) (hs : s.istSeq = false)
      (hx : E.laeuft s K.st ρ (.ret st' v)) :
      SchrittC E LP K t (.block s) ⟨st', fadenSetze K.faeden t .aus, K.halter⟩
  /-- `L_nimm();` / `L_gib();`: the lock primitive, with meaning `LP`. -/
  | sperre (K : KonfC) (t : Faden) (n : Nat) (k : List CS) (ρ : CLok) (op : SperrOp) (h' : Halter)
      (h : K.faeden t = .an (.ext n [] none :: k) ρ) (ho : E.sperre n = some op)
      (hl : LP t op K.halter h') :
      SchrittC E LP K t (.sperre op) ⟨K.st, fadenSetze K.faeden t (.an k ρ), h'⟩

/-- A step of `t` leaves every other thread alone. -/
theorem schrittC_fremd {E : CEinheit} {LP : SperrSem} {K K' : KonfC} {t : Faden} {ℓ : Etikett}
    (h : SchrittC E LP K t ℓ K') (u : Faden) (hu : u ≠ t) : K'.faeden u = K.faeden u := by
  cases h <;> exact fadenSetze_ne _ _ _ _ hu

/-- **Inversion of a step**, by the head of the thread's continuation. -/
theorem schrittC_inv {E : CEinheit} {LP : SperrSem} {K K' : KonfC} {t : Faden} {ℓ : Etikett}
    (h : SchrittC E LP K t ℓ K') :
    (∃ a b k ρ, K.faeden t = .an (.seq a b :: k) ρ ∧ ℓ = .still ∧
      K' = ⟨K.st, fadenSetze K.faeden t (.an (a :: b :: k) ρ), K.halter⟩) ∨
    (∃ ρ, K.faeden t = .an [] ρ ∧ ℓ = .still ∧ K' = ⟨K.st, fadenSetze K.faeden t .aus, K.halter⟩) ∨
    (∃ s k ρ st' ρ', K.faeden t = .an (s :: k) ρ ∧ s.istSeq = false ∧
      E.laeuft s K.st ρ (.norm st' ρ') ∧ ℓ = .block s ∧
      K' = ⟨st', fadenSetze K.faeden t (.an k ρ'), K.halter⟩) ∨
    (∃ s k ρ st' v, K.faeden t = .an (s :: k) ρ ∧ s.istSeq = false ∧
      E.laeuft s K.st ρ (.ret st' v) ∧ ℓ = .block s ∧
      K' = ⟨st', fadenSetze K.faeden t .aus, K.halter⟩) ∨
    (∃ n k ρ op h', K.faeden t = .an (.ext n [] none :: k) ρ ∧ E.sperre n = some op ∧
      LP t op K.halter h' ∧ ℓ = .sperre op ∧ K' = ⟨K.st, fadenSetze K.faeden t (.an k ρ), h'⟩) := by
  cases h with
  | teile a b k ρ h => exact Or.inl ⟨a, b, k, ρ, h, rfl, rfl⟩
  | ende ρ h => exact Or.inr (Or.inl ⟨ρ, h, rfl, rfl⟩)
  | block s k ρ st' ρ' h hs hx => exact Or.inr (Or.inr (Or.inl ⟨s, k, ρ, st', ρ', h, hs, hx, rfl, rfl⟩))
  | rueck s k ρ st' v h hs hx =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, k, ρ, st', v, h, hs, hx, rfl, rfl⟩)))
  | sperre n k ρ op h' h ho hl =>
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨n, k, ρ, op, h', h, ho, hl, rfl, rfl⟩)))

/-- A thread that does not run takes no step. -/
theorem schrittC_aus {E : CEinheit} {LP : SperrSem} {K K' : KonfC} {t : Faden} {ℓ : Etikett}
    (h : SchrittC E LP K t ℓ K') (ha : K.faeden t = .aus) : False := by
  cases h <;> simp_all

/-- A smaller lock meaning gives fewer steps. -/
theorem schrittC_mono {E : CEinheit} {LP LP' : SperrSem}
    (hLP : ∀ t op h h', LP t op h h' → LP' t op h h') {K K' : KonfC} {t : Faden} {ℓ : Etikett}
    (h : SchrittC E LP K t ℓ K') : SchrittC E LP' K t ℓ K' := by
  cases h with
  | teile a b k ρ h => exact .teile _ _ a b k ρ h
  | ende ρ h => exact .ende _ _ ρ h
  | block s k ρ st' ρ' h hs hx => exact .block _ _ s k ρ st' ρ' h hs hx
  | rueck s k ρ st' v h hs hx => exact .rueck _ _ s k ρ st' v h hs hx
  | sperre n k ρ op h' h ho hl => exact .sperre _ _ n k ρ op h' h ho (hLP _ _ _ _ hl)

/-! ## 3. Runs -/

/-- Configurations reachable from `K0` under every schedule. -/
inductive ErreichbarC (E : CEinheit) (LP : SperrSem) (K0 : KonfC) : KonfC → Prop where
  | start : ErreichbarC E LP K0 K0
  | schritt {K K' : KonfC} {t : Faden} {ℓ : Etikett} (h : ErreichbarC E LP K0 K)
      (hs : SchrittC E LP K t ℓ K') : ErreichbarC E LP K0 K'

/-- A run of `n` steps by index: configuration `ks i`, actor `ts i`, kind `ls i`. -/
def LaufC (E : CEinheit) (LP : SperrSem) (K0 : KonfC) (ks : Nat → KonfC) (ts : Nat → Faden)
    (ls : Nat → Etikett) (n : Nat) : Prop :=
  ks 0 = K0 ∧ ∀ i, i < n → SchrittC E LP (ks i) (ts i) (ls i) (ks (i + 1))

theorem laufC_erreichbar {E : CEinheit} {LP : SperrSem} {K0 : KonfC} {ks : Nat → KonfC}
    {ts : Nat → Faden} {ls : Nat → Etikett} {n : Nat} (hl : LaufC E LP K0 ks ts ls n) :
    ∀ i, i ≤ n → ErreichbarC E LP K0 (ks i)
  | 0, _ => by rw [hl.1]; exact .start
  | i + 1, hi => .schritt (laufC_erreichbar hl i (by omega)) (hl.2 i (by omega))

theorem erreichbarC_mono {E : CEinheit} {LP LP' : SperrSem}
    (hLP : ∀ t op h h', LP t op h h' → LP' t op h h') {K0 K : KonfC}
    (h : ErreichbarC E LP K0 K) : ErreichbarC E LP' K0 K := by
  induction h with
  | start => exact .start
  | schritt _ hs ih => exact .schritt ih (schrittC_mono hLP hs)

/-! ## 4. Footprints

The objects a block may access, read off its SYNTAX: every object a pointer
expression names (`&obj`, the decay of a static object) in the statement and,
to the block's call depth, in the bodies of the functions it calls. The
write footprint is the part named in the target of a store. On the DIRECT
fragment (`CS.direkt` below: pointers are formed only from named objects,
never held in locals, never loaded from memory; no volatile, atomic or
foreign access) every load and store of an executed block hits an object of
its footprint -- the pointer an expression computes lies in an object it
names (`ev_zform_blk`), and every load or store of the fragment goes through
such an expression. That is why race freedom over these footprints
(`RennfreiC`) is at least as strong as the C11 notion over single accesses:
a write counts even when it stores the value already there. -/

/-- The objects an expression names. -/
def CX.obj : CX → List CBlk
  | .lit _ => []
  | .var _ => []
  | .cast _ e => e.obj
  | .bin _ _ l r => l.obj ++ r.obj
  | .cmp _ _ l r => l.obj ++ r.obj
  | .lnot e => e.obj
  | .land l r => l.obj ++ r.obj
  | .lor l r => l.obj ++ r.obj
  | .cond _ c a b => c.obj ++ a.obj ++ b.obj
  | .cpl _ e => e.obj
  | .szof _ => []
  | .addr b => [b]
  | .addrL _ => []
  | .fld p _ => p.obj
  | .slotA p i _ _ _ => p.obj ++ i.obj
  | .idx p i _ _ => p.obj ++ i.obj
  | .padd p k => p.obj ++ k.obj
  | .ld p _ => p.obj
  | .vld p _ => p.obj
  | .ald p _ _ => p.obj
  | .devH d _ => [.dev d]
  | .trap => []
  | .fbin _ _ l r => l.obj ++ r.obj
  | .fcmp _ _ l r => l.obj ++ r.obj
  | .fvon _ _ e => e.obj
  | .fin _ e => e.obj

def CX.objL : List CX → List CBlk
  | [] => []
  | e :: es => e.obj ++ CX.objL es

mutual
/-- The objects a statement names (callee bodies not included). -/
def CS.obj0 : CS → List CBlk
  | .skip => []
  | .seq a b => CS.obj0 a ++ CS.obj0 b
  | .expr e => e.obj
  | .set _ _ e => e.obj
  | .store p _ e => p.obj ++ e.obj
  | .vstore p _ e => p.obj ++ e.obj
  | .astore p _ _ e => p.obj ++ e.obj
  | .acas _ p _ ex des _ _ => p.obj ++ ex.obj ++ des.obj
  | .ite c a b => c.obj ++ CS.obj0 a ++ CS.obj0 b
  | .sw e arms => e.obj ++ CS.armsObj0 arms
  | .ret none => []
  | .ret (some (_, e)) => e.obj
  | .brk => []
  | .cont => []
  | .goto _ => []
  | .forC c s b _ => c.obj ++ CS.obj0 s ++ CS.obj0 b
  | .call _ args _ => CX.objL args
  | .ext _ args _ => CX.objL args
def CS.armsObj0 : List (Int × CS) → List CBlk
  | [] => []
  | (_, s) :: rest => CS.obj0 s ++ CS.armsObj0 rest
end

mutual
/-- The objects a statement names in the target of a store. -/
def CS.ziele0 : CS → List CBlk
  | .seq a b => CS.ziele0 a ++ CS.ziele0 b
  | .store p _ _ => p.obj
  | .vstore p _ _ => p.obj
  | .astore p _ _ _ => p.obj
  | .acas _ p _ ex _ _ _ => p.obj ++ ex.obj
  | .ite _ a b => CS.ziele0 a ++ CS.ziele0 b
  | .sw _ arms => CS.armsZiele0 arms
  | .forC _ s b _ => CS.ziele0 s ++ CS.ziele0 b
  | _ => []
def CS.armsZiele0 : List (Int × CS) → List CBlk
  | [] => []
  | (_, s) :: rest => CS.ziele0 s ++ CS.armsZiele0 rest
end

mutual
/-- The functions a statement calls. -/
def CS.rufe : CS → List Nat
  | .seq a b => CS.rufe a ++ CS.rufe b
  | .ite _ a b => CS.rufe a ++ CS.rufe b
  | .sw _ arms => CS.armsRufe arms
  | .forC _ s b _ => CS.rufe s ++ CS.rufe b
  | .call f _ _ => [f]
  | _ => []
def CS.armsRufe : List (Int × CS) → List Nat
  | [] => []
  | (_, s) :: rest => CS.rufe s ++ CS.armsRufe rest
end

/-- **The read footprint** of a statement at call depth `d`: what it names,
    and what the bodies of its callees name at depth `d - 1` (at depth `0` a
    call cannot run: `CallAt 0` is empty). -/
def fussR (Pr : CProg) : Nat → CS → List CBlk
  | 0, s => s.obj0
  | d + 1, s => s.obj0 ++ s.rufe.flatMap (fun f => match Pr f with
      | some F => fussR Pr d F.body
      | none => [])

/-- **The write footprint**, the same way over store targets. -/
def fussW (Pr : CProg) : Nat → CS → List CBlk
  | 0, s => s.ziele0
  | d + 1, s => s.ziele0 ++ s.rufe.flatMap (fun f => match Pr f with
      | some F => fussW Pr d F.body
      | none => [])

/-- The footprint of a step: a block's, and nothing for the others (the lock
    primitive touches no program object). -/
def Etikett.fussR (E : CEinheit) : Etikett → List CBlk
  | .block s => Gabbro.Grammatik.fussR E.Pr E.tiefe s
  | _ => []

def Etikett.fussW (E : CEinheit) : Etikett → List CBlk
  | .block s => Gabbro.Grammatik.fussW E.Pr E.tiefe s
  | _ => []

theorem Etikett.fussR_block {E : CEinheit} {ℓ : Etikett} {b : CBlk} (h : b ∈ ℓ.fussR E) :
    ∃ s, ℓ = .block s := by
  cases ℓ with
  | block s => exact ⟨s, rfl⟩
  | still => exact absurd h List.not_mem_nil
  | sperre _ => exact absurd h List.not_mem_nil

/-! ### The direct fragment -/

mutual
/-- A pointer expression rooted at a named object. -/
def CX.zform : CX → Bool
  | .addr _ => true
  | .fld p _ => CX.zform p
  | .slotA p i _ _ _ => CX.zform p && CX.wform i
  | .idx p i _ _ => CX.zform p && CX.wform i
  | .padd p k => CX.zform p && CX.wform k
  | _ => false
/-- A value expression: an integer, never a pointer, no observation. -/
def CX.wform : CX → Bool
  | .lit _ => true
  | .var _ => true
  | .cast _ e => CX.wform e
  | .bin _ _ l r => CX.wform l && CX.wform r
  | .cmp _ _ l r => CX.wform l && CX.wform r
  | .lnot e => CX.wform e
  | .land l r => CX.wform l && CX.wform r
  | .lor l r => CX.wform l && CX.wform r
  | .cond _ c a b => CX.wform c && CX.wform a && CX.wform b
  | .cpl _ e => CX.wform e
  | .szof _ => true
  | .ld p (.int _ _) => CX.zform p
  | .trap => true
  | .fbin _ _ l r => CX.wform l && CX.wform r
  | .fcmp _ _ l r => CX.wform l && CX.wform r
  | .fvon _ _ e => CX.wform e
  | .fin _ e => CX.wform e
  | _ => false
end

def CX.wformL : List CX → Bool
  | [] => true
  | e :: es => e.wform && CX.wformL es

/-- An integer cell type. -/
def CTy.istInt : CTy → Bool
  | .int _ _ => true
  | .ptr => false

mutual
/-- **The direct fragment** of statements: loads and stores through pointer
    expressions rooted at named objects, integer locals, no volatile, atomic
    or compare-exchange access, and no foreign call but the lock primitive
    (`sp n` names it), called with no arguments and no result. -/
def CS.direkt (sp : Nat → Option SperrOp) : CS → Bool
  | .skip => true
  | .seq a b => CS.direkt sp a && CS.direkt sp b
  | .expr e => e.wform
  | .set _ τ e => τ.istInt && e.wform
  | .store p τ e => τ.istInt && p.zform && e.wform
  | .ite c a b => c.wform && CS.direkt sp a && CS.direkt sp b
  | .sw e arms => e.wform && CS.armsDirekt sp arms
  | .ret none => true
  | .ret (some (τ, e)) => τ.istInt && e.wform
  | .brk => true
  | .cont => true
  | .goto _ => true
  | .forC c s b _ => c.wform && CS.direkt sp s && CS.direkt sp b
  | .call _ args dst => CX.wformL args && (match dst with
      | none => true
      | some (_, τ) => τ.istInt)
  | .ext n args dst => (sp n).isSome && args.isEmpty && dst.isNone
  | _ => false
def CS.armsDirekt (sp : Nat → Option SperrOp) : List (Int × CS) → Bool
  | [] => true
  | (_, s) :: rest => CS.direkt sp s && CS.armsDirekt sp rest
end

/-- The unit is direct on the functions `fs`: integer parameters, no
    address-taken locals (no stack objects, so the frame numbering of two
    threads cannot collide), direct bodies. -/
def CEinheit.direkt (E : CEinheit) (fs : List Nat) : Bool :=
  fs.all fun f => match E.Pr f with
    | some F => F.params.all (fun p => p.2.istInt) && F.locals.isEmpty && F.body.direkt E.sperre
    | none => true

/-- **The pointer a direct pointer expression computes lies in an object the
    expression names** (pointer arithmetic keeps its block, `ptrAdd_blk`). -/
theorem ev_zform_blk (L : CLayout) (orc : DevOrc) (fr : Nat) :
    ∀ (p : CX) (st : CSt) (ρ : CLok) (q : CPtr) (st' : CSt), p.zform = true →
      ev L orc fr p st ρ = some (.ptr q, st') → q.blk ∈ p.obj := by
  intro p
  induction p with
  | addr b =>
      intro st ρ q st' _ h
      simp only [ev, Option.some.injEq, Prod.mk.injEq, CVal.ptr.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact List.mem_singleton_self _
  | fld p off ih =>
      intro st ρ q st' hz h
      simp only [ev] at h
      simp only [CX.zform] at hz
      split at h
      · rename_i q0 st1 hp
        split at h
        · rename_i q' hq
          simp only [Option.some.injEq, Prod.mk.injEq, CVal.ptr.injEq] at h
          obtain ⟨rfl, -⟩ := h
          rw [(ptrAdd_blk hq).1]
          exact ih st ρ q0 st1 hz hp
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | slotA p i n ss off ihp ihi =>
      intro st ρ q st' hz h
      simp only [ev] at h
      simp only [CX.zform, Bool.and_eq_true] at hz
      split at h
      · rename_i q0 st1 hp
        split at h
        · rename_i k st2 hk
          split at h
          · split at h
            · rename_i q' hq
              simp only [Option.some.injEq, Prod.mk.injEq, CVal.ptr.injEq] at h
              obtain ⟨rfl, -⟩ := h
              rw [(ptrAdd_blk hq).1]
              exact List.mem_append_left _ (ihp st ρ q0 st1 hz.1 hp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | idx p i n es ihp ihi =>
      intro st ρ q st' hz h
      simp only [ev] at h
      simp only [CX.zform, Bool.and_eq_true] at hz
      split at h
      · rename_i q0 st1 hp
        split at h
        · rename_i k st2 hk
          split at h
          · split at h
            · rename_i q' hq
              simp only [Option.some.injEq, Prod.mk.injEq, CVal.ptr.injEq] at h
              obtain ⟨rfl, -⟩ := h
              rw [(ptrAdd_blk hq).1]
              exact List.mem_append_left _ (ihp st ρ q0 st1 hz.1 hp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | padd p k ihp ihk =>
      intro st ρ q st' hz h
      simp only [ev] at h
      simp only [CX.zform, Bool.and_eq_true] at hz
      split at h
      · rename_i q0 st1 hp
        split at h
        · rename_i m st2 hm
          split at h
          · rename_i q' hq
            simp only [Option.some.injEq, Prod.mk.injEq, CVal.ptr.injEq] at h
            obtain ⟨rfl, -⟩ := h
            rw [(ptrAdd_blk hq).1]
            exact List.mem_append_left _ (ihp st ρ q0 st1 hz.1 hp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | _ => intro st ρ q st' hz _; simp [CX.zform] at hz

/-! ## 5. Data-race freedom of the C program -/

/-- C steps `i` and `j` CONFLICT on object `b`: both footprints contain it and
    one of them writes it. -/
def KonfliktC (E : CEinheit) (ls : Nat → Etikett) (i j : Nat) (b : CBlk) : Prop :=
  b ∈ (ls i).fussR E ∧ b ∈ (ls j).fussR E ∧ (b ∈ (ls i).fussW E ∨ b ∈ (ls j).fussW E)

/-- **Happens-before through lock `L`** on a C run: the actor of step `i`
    releases `L` at a later step `r`, the actor of step `j` acquires it at a
    step `a` between `r` and `j` (release/acquire, the synchronises-with of
    the lock primitive). -/
def GeordnetC (ts : Nat → Faden) (ls : Nat → Etikett) (L : Nat) (i j : Nat) : Prop :=
  ∃ r a, i < r ∧ r < a ∧ a < j ∧ ts r = ts i ∧ ts a = ts j ∧
    ls r = .sperre (.gib L) ∧ ls a = .sperre (.nimm L)

/-- **DATA-RACE FREEDOM OF THE C PROGRAM** (the hypothesis of DRF-SC): on every
    SC run from `K0`, two conflicting steps of different threads are ordered
    through a lock. -/
def RennfreiC (E : CEinheit) (LP : SperrSem) (K0 : KonfC) : Prop :=
  ∀ (ks : Nat → KonfC) (ts : Nat → Faden) (ls : Nat → Etikett) (n : Nat),
    LaufC E LP K0 ks ts ls n →
    ∀ i j (b : CBlk), i < j → j < n → ts i ≠ ts j → KonfliktC E ls i j b →
      ∃ L, GeordnetC ts ls L i j

/-- Fewer runs, fewer races. -/
theorem rennfreiC_mono {E : CEinheit} {LP LP' : SperrSem}
    (hLP : ∀ t op h h', LP t op h h' → LP' t op h h') {K0 : KonfC}
    (h : RennfreiC E LP' K0) : RennfreiC E LP K0 :=
  fun ks ts ls n hl => h ks ts ls n ⟨hl.1, fun i hi => schrittC_mono hLP (hl.2 i hi)⟩

/-! ## 6. The premises -/

/-- What an execution shows at a moment: program memory, the observation
    trace (volatile and atomic accesses), and which threads still run. -/
structure BeobC where
  mem : CBlk → Nat → CVal
  obs : List CObs
  aktiv : Faden → Bool

def CFaden.aktiv : CFaden → Bool
  | .aus => false
  | .an _ _ => true

def beobC (K : KonfC) : BeobC := ⟨K.st.mem, K.st.obs, fun t => (K.faeden t).aktiv⟩

/-- **THE NAMED PREMISE DRF-SC** (one proposition, a hypothesis, never an
    axiom). `Echt` is what executions of the compiled program on the real
    machine -- the C11 memory model under the compiler, and the hardware
    profile -- can be observed to show (a parameter: the real machine is not
    a Lean object). The premise: if the C program is data-race free, every
    such observation is the observation of some SC interleaving of the C
    semantics, at the granularity of synchronisation-free blocks. Its
    content is the DRF-SC theorem of the C11 model (with the region
    corollary, see the file header) together with the correctness of the
    compiler's mapping of C11 atomics and fences to the hardware profile. -/
def DRFSC (E : CEinheit) (LP : SperrSem) (K0 : KonfC) (Echt : BeobC → Prop) : Prop :=
  RennfreiC E LP K0 → ∀ b, Echt b → ∃ K, ErreichbarC E LP K0 K ∧ beobC K = b

/-- The runtime's start of a thread in root function `f`: its body as the
    continuation, every local unwritten (the roots take no arguments). -/
def anStart (E : CEinheit) (f : Nat) : CFaden :=
  match E.Pr f with
  | some F => .an [F.body] (fun _ => .undef)
  | none => .aus

/-- The start configuration for a root assignment `w` (`none`: no thread). -/
def startC (E : CEinheit) (w : Faden → Option Nat) (st0 : CSt) : KonfC :=
  ⟨st0, fun t => match w t with
    | some f => anStart E f
    | none => .aus, fun _ => none⟩

/-- **Thread creation by the runtime** (A4 of stage (a), `Laufzeit` of the goal
    theorem, the first entry of NICHTINTERFERENZ §10): the loader establishes
    the declared initial memory `st0`; threads start ONLY at declared roots
    `wurzeln`, each root on at most one thread; no lock is held. -/
def FadenStartC (E : CEinheit) (wurzeln : List Nat) (st0 : CSt) (K0 : KonfC) : Prop :=
  ∃ w : Faden → Option Nat, K0 = startC E w st0 ∧ (∀ t f, w t = some f → f ∈ wurzeln) ∧
    ∀ t u f, w t = some f → w u = some f → t = u

/-- **THE RUNTIME LIST** -- one list, the same as NICHTINTERFERENZ §10 and
    PLAN §5: thread creation (`faeden`) and the lock primitive (`sperre`:
    every behaviour of the runtime's `L_nimm`/`L_gib` is a behaviour of
    `sperrAbstrakt`). The list's two scheduler entries (a fixed timetable or
    a rule reading only the observer's view; a blocked slot left idle) are
    premises of noninterference only: the statement here holds for EVERY
    schedule. -/
structure LaufzeitC (E : CEinheit) (wurzeln : List Nat) (st0 : CSt) (K0 : KonfC)
    (LP : SperrSem) : Prop where
  faeden : FadenStartC E wurzeln st0 K0
  sperre : ∀ t op h h', LP t op h h' → sperrAbstrakt t op h h'

/-! ## 7. The simulation certificate and its consequences -/

section Sim

variable {D : Deklaration}

/-- The C object of a carrier under the emitter's layout. -/
def EmitLay.objekt (EL : EmitLay D) : D.Tab ⊕ D.Glob → CBlk
  | .inl t => .tab (EL.tnr t)
  | .inr g => .glob (EL.gnr g)

theorem EmitLay.objekt_inj (EL : EmitLay D) :
    ∀ c c', EL.objekt c = EL.objekt c' → c = c'
  | .inl t, .inl t', h => by
      simp only [EmitLay.objekt, CBlk.tab.injEq] at h
      rw [EL.tnr_inj _ _ h]
  | .inr g, .inr g', h => by
      simp only [EmitLay.objekt, CBlk.glob.injEq] at h
      rw [EL.gnr_inj _ _ h]
  | .inl _, .inr _, h => by simp [EmitLay.objekt] at h
  | .inr _, .inl _, h => by simp [EmitLay.objekt] at h

/-- **A G segment fits a C step**: the segment `ms 0 … ms N` of thread `t`
    covers the C step's footprint (every object it names is a carrier some
    G step of the segment accesses; every object it writes, one some step
    writes), and releases or acquires a G lock only where the C step is the
    corresponding call of the lock primitive. -/
structure SegPasst (E : CEinheit) (EL : EmitLay D) (lnr : D.Lock → Nat) (t : Faden)
    (ℓ : Etikett) (ms : Nat → RufMaschineG D) (N : Nat) : Prop where
  liest : ∀ b ∈ ℓ.fussR E, ∃ c, EL.objekt c = b ∧ ¬ AtomarAusgenommen c ∧
    ∃ k, k < N ∧ ZugriffG (ms k) (ms (k + 1)) t c
  schreibt : ∀ b ∈ ℓ.fussW E, ∃ c, EL.objekt c = b ∧
    ∃ k, k < N ∧ SchreibG (ms k) (ms (k + 1)) t c
  gibt : ∀ k, k < N → ∀ L, GibtFrei (ms k) (ms (k + 1)) t L → ℓ = .sperre (.gib (lnr L))
  nimmt : ∀ k, k < N → ∀ L, NimmtAn (ms k) (ms (k + 1)) t L → ℓ = .sperre (.nimm (lnr L))

theorem SegPasst.congr {E : CEinheit} {EL : EmitLay D} {lnr : D.Lock → Nat} {t : Faden}
    {ℓ : Etikett} {ms ms' : Nat → RufMaschineG D} {N : Nat} (h : ∀ k, k ≤ N → ms k = ms' k)
    (hs : SegPasst E EL lnr t ℓ ms N) : SegPasst E EL lnr t ℓ ms' N where
  liest b hb := by
    obtain ⟨c, hc, ha, k, hk, hz⟩ := hs.liest b hb
    exact ⟨c, hc, ha, k, hk, by rw [← h k (by omega), ← h (k + 1) (by omega)]; exact hz⟩
  schreibt b hb := by
    obtain ⟨c, hc, k, hk, hz⟩ := hs.schreibt b hb
    exact ⟨c, hc, k, hk, by rw [← h k (by omega), ← h (k + 1) (by omega)]; exact hz⟩
  gibt k hk L hg := hs.gibt k hk L (by rw [h k (by omega), h (k + 1) (by omega)]; exact hg)
  nimmt k hk L hn := hs.nimmt k hk L (by rw [h k (by omega), h (k + 1) (by omega)]; exact hn)

/-- **THE SIMULATION CERTIFICATE** between the C unit `E` from `K0` and the G
    program `P` from `M0`: a relation `R`, holding at the starts, such that
    every SC step of the C from a reachable related pair is matched by a
    segment of G steps of the SAME thread (possibly empty) that ends related
    and fits the step (`SegPasst`). -/
structure SimC (E : CEinheit) (K0 : KonfC) (EL : EmitLay D) (lnr : D.Lock → Nat)
    (P : Programm D) (O : Orakel D) (passes : Nat) (M0 : RufMaschineG D) where
  R : KonfC → RufMaschineG D → Prop
  start : R K0 M0
  schritt : ∀ (K : KonfC) (M : RufMaschineG D) (t : Faden) (ℓ : Etikett) (K' : KonfC),
    ErreichbarC E sperrAbstrakt K0 K → RufErreichbarG P O passes M0 M → R K M →
    SchrittC E sperrAbstrakt K t ℓ K' →
    ∃ (ms : Nat → RufMaschineG D) (N : Nat), LaufG P O passes M ms (fun _ => t) N ∧
      R K' (ms N) ∧ SegPasst E EL lnr t ℓ ms N

variable {E : CEinheit} {K0 : KonfC} {EL : EmitLay D} {lnr : D.Lock → Nat}
  {P : Programm D} {O : Orakel D} {passes : Nat} {M0 : RufMaschineG D}

/-- Every reachable C configuration is related to a reachable G machine. -/
theorem sim_erreichbar (S : SimC E K0 EL lnr P O passes M0) {K : KonfC}
    (h : ErreichbarC E sperrAbstrakt K0 K) :
    ∃ M, RufErreichbarG P O passes M0 M ∧ S.R K M := by
  induction h with
  | start => exact ⟨M0, .start, S.start⟩
  | schritt hK hs ih =>
      obtain ⟨M, hM, hR⟩ := ih
      obtain ⟨ms, N, hl, hR', -⟩ := S.schritt _ _ _ _ _ hK hM hR hs
      refine ⟨ms N, ?_, hR'⟩
      have : ∀ k, k ≤ N → RufErreichbarG P O passes M0 (ms k) := by
        intro k
        induction k with
        | zero => intro _; rw [hl.1]; exact hM
        | succ k ihk => intro hk; exact .schritt _ _ _ (ihk (by omega)) (hl.2 k (by omega))
      exact this N (Nat.le_refl N)

/-- **A C run lifted to a G run**: G segment `i` is `[φ i, φ (i+1))`, run by
    the C step's thread, and fits the C step. -/
structure Gehoben (S : SimC E K0 EL lnr P O passes M0) (ks : Nat → KonfC) (ts : Nat → Faden)
    (ls : Nat → Etikett) (n : Nat) (ms : Nat → RufMaschineG D) (fs : Nat → Faden)
    (φ : Nat → Nat) : Prop where
  lauf : LaufG P O passes M0 ms fs (φ n)
  null : φ 0 = 0
  mono : ∀ i j, i ≤ j → j ≤ n → φ i ≤ φ j
  rel : ∀ i, i ≤ n → S.R (ks i) (ms (φ i))
  faden : ∀ i k, i < n → φ i ≤ k → k < φ (i + 1) → fs k = ts i
  passt : ∀ i, i < n →
    SegPasst E EL lnr (ts i) (ls i) (fun k => ms (φ i + k)) (φ (i + 1) - φ i)

/-- **Every C run lifts** (induction over its length, gluing G segments). -/
theorem sim_lauf (S : SimC E K0 EL lnr P O passes M0) :
    ∀ (n : Nat) (ks : Nat → KonfC) (ts : Nat → Faden) (ls : Nat → Etikett),
      LaufC E sperrAbstrakt K0 ks ts ls n →
      ∃ (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (φ : Nat → Nat),
        Gehoben S ks ts ls n ms fs φ := by
  intro n
  induction n with
  | zero =>
      intro ks ts ls hl
      refine ⟨fun _ => M0, fun _ => 0, fun _ => 0, ⟨⟨rfl, fun k hk => absurd hk (by omega)⟩,
        rfl, fun _ _ _ _ => Nat.le_refl _, fun i hi => ?_, fun i _ hi => absurd hi (by omega),
        fun i hi => absurd hi (by omega)⟩⟩
      have : i = 0 := by omega
      subst this
      rw [hl.1]
      exact S.start
  | succ n ih =>
      intro ks ts ls hl
      obtain ⟨ms, fs, φ, G⟩ := ih ks ts ls ⟨hl.1, fun i hi => hl.2 i (by omega)⟩
      have hK := laufC_erreichbar hl n (by omega)
      have hM := laufG_erreichbar G.lauf (φ n) (Nat.le_refl _)
      obtain ⟨ms', N, hl', hR', hP'⟩ :=
        S.schritt _ _ _ _ _ hK hM (G.rel n (Nat.le_refl _)) (hl.2 n (by omega))
      have hglue := laufG_verketten G.lauf hl'
      refine ⟨fun k => if k ≤ φ n then ms k else ms' (k - φ n),
        fun k => if k < φ n then fs k else ts n,
        fun i => if i ≤ n then φ i else φ n + N, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · rw [if_neg (by omega)]
        exact hglue
      · rw [if_pos (Nat.zero_le _)]
        exact G.null
      · intro i j hij hj
        by_cases hjn : j ≤ n
        · rw [if_pos (by omega), if_pos hjn]
          exact G.mono i j hij hjn
        · rw [if_neg hjn]
          by_cases hin : i ≤ n
          · rw [if_pos hin]
            have := G.mono i n hin (Nat.le_refl _)
            omega
          · rw [if_neg hin]
            exact Nat.le_refl _
      · intro i hi
        by_cases hin : i ≤ n
        · rw [if_pos hin]
          show S.R (ks i) (if φ i ≤ φ n then ms (φ i) else ms' (φ i - φ n))
          rw [if_pos (G.mono i n hin (Nat.le_refl _))]
          exact G.rel i hin
        · have e : i = n + 1 := by omega
          subst e
          rw [if_neg hin]
          show S.R (ks (n + 1)) (if φ n + N ≤ φ n then ms (φ n + N) else ms' (φ n + N - φ n))
          by_cases hN : N = 0
          · subst hN
            rw [if_pos (by omega)]
            have e0 : ms (φ n + 0) = ms' 0 := hl'.1.symm
            rw [e0]
            exact hR'
          · rw [if_neg (by omega), show φ n + N - φ n = N by omega]
            exact hR'
      · intro i k hi hk1 hk2
        by_cases hin : i + 1 ≤ n
        · rw [if_pos (by omega)] at hk1
          rw [if_pos hin] at hk2
          have := G.mono (i + 1) n hin (Nat.le_refl _)
          show (if k < φ n then fs k else ts n) = ts i
          rw [if_pos (by omega)]
          exact G.faden i k (by omega) hk1 hk2
        · have e : i = n := by omega
          subst e
          rw [if_pos (Nat.le_refl _)] at hk1
          show (if k < φ i then fs k else ts i) = ts i
          rw [if_neg (by omega)]
      · intro i hi
        by_cases hin : i + 1 ≤ n
        · rw [if_pos (by omega), if_pos hin]
          refine SegPasst.congr (fun k hk => ?_) (G.passt i (by omega))
          have := G.mono (i + 1) n hin (Nat.le_refl _)
          have := G.mono i (i + 1) (by omega) hin
          show ms (φ i + k) = (if φ i + k ≤ φ n then ms (φ i + k) else ms' (φ i + k - φ n))
          rw [if_pos (by omega)]
        · have e : i = n := by omega
          subst e
          rw [if_pos (Nat.le_refl _), if_neg hin, show φ i + N - φ i = N by omega]
          refine SegPasst.congr (fun k hk => ?_) hP'
          show ms' k = (if φ i + k ≤ φ i then ms (φ i + k) else ms' (φ i + k - φ i))
          by_cases hk0 : k = 0
          · subst hk0
            rw [if_pos (by omega)]
            exact hl'.1
          · rw [if_neg (by omega), show φ i + k - φ i = k by omega]

/-- Every G index below the end of a lifted run lies in one segment. -/
theorem segment_von (φ : Nat → Nat) (hnull : φ 0 = 0) :
    ∀ (n r : Nat), r < φ n → ∃ i, i < n ∧ φ i ≤ r ∧ r < φ (i + 1)
  | 0, r, h => by rw [hnull] at h; exact absurd h (Nat.not_lt_zero _)
  | n + 1, r, h => by
      by_cases hr : r < φ n
      · obtain ⟨i, hi, h1, h2⟩ := segment_von φ hnull n r hr
        exact ⟨i, by omega, h1, h2⟩
      · exact ⟨n, by omega, by omega, h⟩

/-- **THE RACE TRANSFER**: a C conflict lifts to a G conflict inside the
    segments (the footprint is covered), G orders it through a guard lock
    (`RennfreiBis`), and the G release and acquire lie in segments of C
    steps that ARE the release and the acquire of that lock (`SegPasst.gibt`,
    `.nimmt`). So the C program is race free because G is. -/
theorem rennfreiC_aus_sim (S : SimC E K0 EL lnr P O passes M0)
    (hR : ∀ M, RufErreichbarG P O passes M0 M → RennfreiBis P O passes M0 M) :
    RennfreiC E sperrAbstrakt K0 := by
  intro ks ts ls n hl i j b hij hjn hts hk
  obtain ⟨ms, fs, φ, G⟩ := sim_lauf S n ks ts ls hl
  have hin : i < n := by omega
  have si := G.passt i hin
  have sj := G.passt j hjn
  obtain ⟨hbi, hbj, hw⟩ := hk
  obtain ⟨si0, hlsi⟩ := Etikett.fussR_block hbi
  obtain ⟨sj0, hlsj⟩ := Etikett.fussR_block hbj
  -- the carrier and the two accessing G steps, the write first where it is
  obtain ⟨c, hcb, hca, -⟩ := si.liest b hbi
  obtain ⟨gi, gj, hgi1, hgi2, hgj1, hgj2, hzi, hzj, hsw⟩ :
      ∃ gi gj, φ i ≤ gi ∧ gi < φ (i + 1) ∧ φ j ≤ gj ∧ gj < φ (j + 1) ∧
        ZugriffG (ms gi) (ms (gi + 1)) (ts i) c ∧ ZugriffG (ms gj) (ms (gj + 1)) (ts j) c ∧
        (SchreibG (ms gi) (ms (gi + 1)) (ts i) c ∨ SchreibG (ms gj) (ms (gj + 1)) (ts j) c) := by
    rcases hw with hwi | hwj
    · obtain ⟨c1, hc1, k1, hk1, hs1⟩ := si.schreibt b hwi
      obtain ⟨c2, hc2, _, k2, hk2, hz2⟩ := sj.liest b hbj
      have e1 : c1 = c := EL.objekt_inj _ _ (hc1.trans hcb.symm)
      have e2 : c2 = c := EL.objekt_inj _ _ (hc2.trans hcb.symm)
      subst e1; subst e2
      refine ⟨φ i + k1, φ j + k2, by omega, by omega, by omega, by omega, ?_, hz2, Or.inl hs1⟩
      rcases hs1 with h | h
      · exact Or.inl ⟨true, h⟩
      · exact Or.inr h
    · obtain ⟨c1, hc1, k1, hk1, hs1⟩ := sj.schreibt b hwj
      obtain ⟨c2, hc2, _, k2, hk2, hz2⟩ := si.liest b hbi
      have e1 : c1 = c := EL.objekt_inj _ _ (hc1.trans hcb.symm)
      have e2 : c2 = c := EL.objekt_inj _ _ (hc2.trans hcb.symm)
      subst e1; subst e2
      refine ⟨φ i + k2, φ j + k1, by omega, by omega, by omega, by omega, hz2, ?_, Or.inr hs1⟩
      rcases hs1 with h | h
      · exact Or.inl ⟨true, h⟩
      · exact Or.inr h
  have hmij := G.mono (i + 1) j (by omega) (by omega)
  have hmjn := G.mono (j + 1) n (by omega) (Nat.le_refl _)
  have hfi : fs gi = ts i := G.faden i gi hin hgi1 hgi2
  have hfj : fs gj = ts j := G.faden j gj hjn hgj1 hgj2
  have hRB := hR (ms (φ n)) (laufG_erreichbar G.lauf (φ n) (Nat.le_refl _))
  obtain ⟨L, _, r, a, hr1, hr2, hr3, hfr, hfa, hgib, hnimm⟩ :=
    hRB ms fs (φ n) G.lauf rfl gi gj c (by omega) (by omega) (by rw [hfi, hfj]; exact hts)
      (by rw [hfi]; exact hzi) (by rw [hfj]; exact hzj)
      (by rw [hfi, hfj]; exact hsw) hca
  -- the C steps whose segments hold the release and the acquire
  obtain ⟨i', hi'n, hi'1, hi'2⟩ := segment_von φ G.null n r (by omega)
  obtain ⟨a', ha'n, ha'1, ha'2⟩ := segment_von φ G.null n a (by omega)
  have hfr' : fs r = ts i' := G.faden i' r hi'n hi'1 hi'2
  have hfa' : fs a = ts a' := G.faden a' a ha'n ha'1 ha'2
  have hti : ts i' = ts i := by rw [← hfr', hfr, hfi]
  have hta : ts a' = ts j := by rw [← hfa', hfa, hfj]
  have hlg : ls i' = .sperre (.gib (lnr L)) := by
    refine (G.passt i' hi'n).gibt (r - φ i') (by omega) L ?_
    show GibtFrei (ms (φ i' + (r - φ i'))) (ms (φ i' + (r - φ i') + 1)) (ts i') L
    rw [show φ i' + (r - φ i') = r by omega, hti, ← hfi]
    exact hgib
  have hln : ls a' = .sperre (.nimm (lnr L)) := by
    refine (G.passt a' ha'n).nimmt (a - φ a') (by omega) L ?_
    show NimmtAn (ms (φ a' + (a - φ a'))) (ms (φ a' + (a - φ a') + 1)) (ts a') L
    rw [show φ a' + (a - φ a') = a by omega, hta, ← hfj]
    exact hnimm
  -- the order of the four C steps
  have hii' : i < i' := by
    rcases Nat.lt_trichotomy i i' with h | h | h
    · exact h
    · subst h; rw [hlsi] at hlg; cases hlg
    · have := G.mono (i' + 1) i (by omega) (by omega); omega
  have ha'j : a' < j := by
    rcases Nat.lt_trichotomy a' j with h | h | h
    · exact h
    · subst h; rw [hlsj] at hln; cases hln
    · have := G.mono (j + 1) a' (by omega) (by omega); omega
  have hi'a' : i' < a' := by
    rcases Nat.lt_trichotomy i' a' with h | h | h
    · exact h
    · subst h; rw [hlg] at hln; cases hln
    · have := G.mono (a' + 1) i' (by omega) (by omega); omega
  exact ⟨lnr L, i', a', hii', hi'a', ha'j, hti, hta, hlg, hln⟩

/-- **THE CLOSING SCHEMA OF STAGE (b).** Given a simulation certificate, the
    goal theorem's conclusion on every reachable machine of G (`hZ`, from
    `gabbro_ziel`), the lock primitive's specification (`hLP`, the runtime
    list) and DRF-SC (`hDRF`):
    1. the C program is data-race free, under the real lock primitive too --
       proved from G, which makes DRF-SC applicable;
    2. every SC configuration of the C is related to a reachable machine of G
       at which `Ziel` holds;
    3. every REAL observation is the observation of such an SC configuration. -/
theorem schluss_b (S : SimC E K0 EL lnr P O passes M0) (Sinv : SperrInv D)
    (hZ : ∀ M, RufErreichbarG P O passes M0 M → Ziel P Sinv O passes M0 M)
    (LP : SperrSem) (hLP : ∀ t op h h', LP t op h h' → sperrAbstrakt t op h h')
    (Echt : BeobC → Prop) (hDRF : DRFSC E LP K0 Echt) :
    RennfreiC E LP K0 ∧
    (∀ K, ErreichbarC E LP K0 K →
      ∃ M, RufErreichbarG P O passes M0 M ∧ S.R K M ∧ Ziel P Sinv O passes M0 M) ∧
    ∀ b, Echt b → ∃ K M, ErreichbarC E LP K0 K ∧ beobC K = b ∧
      RufErreichbarG P O passes M0 M ∧ S.R K M ∧ Ziel P Sinv O passes M0 M := by
  have hRC : RennfreiC E LP K0 :=
    rennfreiC_mono hLP (rennfreiC_aus_sim S fun M hM => (hZ M hM).rennfrei)
  have hK : ∀ K, ErreichbarC E LP K0 K →
      ∃ M, RufErreichbarG P O passes M0 M ∧ S.R K M ∧ Ziel P Sinv O passes M0 M := by
    intro K hK
    obtain ⟨M, hM, hR⟩ := sim_erreichbar S (erreichbarC_mono hLP hK)
    exact ⟨M, hM, hR, hZ M hM⟩
  refine ⟨hRC, hK, fun b hb => ?_⟩
  obtain ⟨K, hKr, hKb⟩ := hDRF hRC b hb
  obtain ⟨M, hM, hR, hZM⟩ := hK K hKr
  exact ⟨K, M, hKr, hKb, hM, hR, hZM⟩

end Sim

#print axioms sperrAbstrakt_rahmen
#print axioms sperrAbstrakt_nur_eigen
#print axioms ev_zform_blk
#print axioms sim_erreichbar
#print axioms sim_lauf
#print axioms rennfreiC_aus_sim
#print axioms schluss_b

end Gabbro.Grammatik
