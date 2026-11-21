/-
  File:      stage0/Stage0/Senke/Bild/Mehr/SCSchritt.lean
  Subject:   The IR process over the runner's sequentially consistent memory model is the request-level process
             (multi-thread image theorem, package MT2). `SCSchritt L i` is a step of thread `i` of the IR process
             over `SC L` that the memory answers: the start of an instruction (`priv`) or a read, write or
             compare-and-swap (`ask`) -- the `priv` and `ask` rules of `Runner.Mach.Tr` with `actI`; a run of the
             process makes exactly these steps (`tr_scSchritt`: from a configuration a step reaches, every
             observation is one of the configuration before, with the same calls). System calls (exit, clone,
             futex) and native floating requests are the steps of later packages (MT5, MT6).
             THE BRIDGE (`sc_mSchritt`): with the thread's state read-blind (`Blind`), every such step is a step
             of the request-level process `MSchritt i` on the memory of the state: a write and a compare-and-swap
             are answered by `SC L` exactly as by the memory (`sc_memAns_wr`, `sc_memAns_cas`), and a read is
             answered up to its free second word, which a read-blind continuation ignores. Every thread of every
             state reached from read-blind threads stays read-blind (`alleBlind_schritt`), so every run of the
             process over `SC L` is a run of `MSchritt` (`sc_mErreichbar`).
-/
module
public import Stage0.Senke.Bild.Mehr.SC
public import Stage0.Senke.Bild.Mehr.Prozess
public import Stage0.Senke.Bild.Mehr.BlindOp
public import Stage0.Senke.Bild.Mehr.Schritt
@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Runner Runner.IR Runner.Beweis Runner.Mach
open Gabbro.Grammatik

/-- The requests the memory answers alone: read, write, compare-and-swap. -/
def istSpeicherOp : Op → Bool
  | .rd _ _ => true
  | .wr _ _ => true
  | .cas _ _ _ => true
  | _ => false

theorem special_speicherOp {o : Op} (h : istSpeicherOp o = true) : o.special = false := by
  cases o with
  | rd n x => rfl
  | wr a v => rfl
  | cas a e n => rfl
  | sys q => simp [istSpeicherOp] at h
  | fp k a b => simp [istSpeicherOp] at h

/-- **A step of thread `i` of the IR process over `SC L` that the memory answers.** -/
inductive SCSchritt (L : Lay) (i : Nat) : Cfg (SC L) (Res T) → Cfg (SC L) (Res T) → Prop
  | priv {c : Cfg (SC L) (Res T)} {t : T} :
      c.ths[i]? = some (some (.next t)) → SCSchritt L i c ⟨c.ms, c.ths.set i (some (step t))⟩
  | ask {c : Cfg (SC L) (Res T)} {o : Op} {k : Ans → Res T} {a : Ans} {ms : (SC L).St} :
      c.ths[i]? = some (some (.ask o k)) → istSpeicherOp o = true → (SC L).ans c.ms i o a ms →
      SCSchritt L i c ⟨ms, c.ths.set i (some (k a))⟩

/-- **The steps are the process's own**: whatever the process observes from the configuration a step reaches, it
    observes from the configuration before, one step longer and with no new system call. -/
theorem tr_scSchritt {L : Lay} {i : Nat} {c c' : Cfg (SC L) (Res T)} (hs : SCSchritt L i c c')
    {l : List Ev} {e : Ende} {n : Nat} (h : Tr (SC L) actI c' l e n) : Tr (SC L) actI c l e (n + 1) := by
  cases hs with
  | priv ht => exact Tr.priv ht rfl h
  | @ask o k a ms ht ho hans =>
    have h' := Tr.ask (act := actI) (t' := k a) ht rfl (special_speicherOp ho) hans rfl h
    have hl : lbl i o a = [] := by
      cases o with
      | rd n x => rfl
      | wr x v => rfl
      | cas x e n => rfl
      | sys q => simp [istSpeicherOp] at ho
      | fp k a b => simp [istSpeicherOp] at ho
    rw [hl, List.nil_append] at h'
    exact h'

/-- The answer of the memory to a read: the bytes read, the second word zero. -/
def rdA (m : Mem) (n : Nat) (x : W) : Ans := (rdN m n x).map (·, 0)

theorem rdA_snd {m : Mem} {n : Nat} {x v w : W} (e : rdA m n x = some (v, w)) : w = 0 := by
  unfold rdA at e
  cases h : rdN m n x with
  | none =>
    rw [h] at e
    cases e
  | some u =>
    rw [h] at e
    exact (Prod.mk.inj (Option.some.inj e)).2.symm

/-- **A read-blind continuation of a read takes the model's answer as the memory's.** -/
theorem blind_rd_antwort {m : Mem} {n : Nat} {x : W} {k : Ans → Res T}
    (hk : ∀ v w, k (some (v, w)) = k (some (v, 0))) (w : W) : k ((rdN m n x).map (·, w)) = k (rdA m n x) := by
  unfold rdA
  cases rdN m n x with
  | none => rfl
  | some u => exact hk u w

/-- **THE BRIDGE, one step.** A step of the IR process over `SC L` from a read-blind thread state is a step of the
    request-level process on the memory. -/
theorem sc_mSchritt {L : Lay} {i : Nat} {c c' : Cfg (SC L) (Res T)} (hs : SCSchritt L i c c')
    (hb : ∀ r, c.ths[i]? = some (some r) → Blind r) : MSchritt i ⟨c.ms.1, c.ths⟩ ⟨c'.ms.1, c'.ths⟩ := by
  cases hs with
  | priv ht => exact MSchritt.priv (c := ⟨c.ms.1, c.ths⟩) ht
  | @ask o k a ms ht ho hans =>
    have hB := hb _ ht
    cases o with
    | rd n x =>
      obtain ⟨rfl, w, rfl⟩ := hans
      obtain ⟨hn, hk⟩ := hB.lesen rfl
      have h0 : (SC L).ans c.ms i (.rd n x) (rdA c.ms.1 n x) c.ms := And.intro rfl ⟨0, rfl⟩
      have hm := sc_memAns_rd h0 hn fun _ _ e => rdA_snd e
      have hst := MSchritt.ask (c := ⟨c.ms.1, c.ths⟩) (k := k) ht hm
      rw [← blind_rd_antwort (m := c.ms.1) (n := n) (x := x) hk w] at hst
      exact hst
    | wr x v => exact MSchritt.ask (c := ⟨c.ms.1, c.ths⟩) ht (sc_memAns_wr hans)
    | cas x e n => exact MSchritt.ask (c := ⟨c.ms.1, c.ths⟩) ht (sc_memAns_cas hans)
    | sys q => simp [istSpeicherOp] at ho
    | fp kd x y => simp [istSpeicherOp] at ho

/-! ## Read-blind threads stay read-blind -/

/-- Every live thread is read-blind. -/
def AlleBlind (ths : List (Option (Res T))) : Prop := ∀ (j : Nat) (r : Res T), ths[j]? = some (some r) → Blind r

/-- Replacing a live thread's state by a read-blind one keeps every thread read-blind. -/
theorem alleBlind_set {ths : List (Option (Res T))} (h : AlleBlind ths) {i : Nat} {r0 r : Res T}
    (hi : ths[i]? = some (some r0)) (hr : Blind r) : AlleBlind (ths.set i (some r)) := by
  intro j r' hj
  by_cases e : j = i
  · subst e
    rw [set_selbst hi] at hj
    cases hj
    exact hr
  · rw [set_fremd ths (some r) e] at hj
    exact h j r' hj

/-- **A step keeps every thread read-blind.** -/
theorem alleBlind_schritt {L : Lay} {i : Nat} {c c' : Cfg (SC L) (Res T)} (hs : SCSchritt L i c c')
    (h : AlleBlind c.ths) : AlleBlind c'.ths := by
  cases hs with
  | priv ht => exact alleBlind_set h ht (blind_step _)
  | ask ht _ _ => exact alleBlind_set h ht ((h _ _ ht).weiter _)

/-! ## Runs -/

/-- The configurations the IR process over `SC L` reaches by steps the memory answers. -/
inductive SCErreichbar (L : Lay) (c0 : Cfg (SC L) (Res T)) : Cfg (SC L) (Res T) → Prop
  | start : SCErreichbar L c0 c0
  | schritt {c c' : Cfg (SC L) (Res T)} {i : Nat} :
      SCErreichbar L c0 c → SCSchritt L i c c' → SCErreichbar L c0 c'

/-- The configurations the request-level process reaches. -/
inductive MErreichbar (c0 : PCfg) : PCfg → Prop
  | start : MErreichbar c0 c0
  | schritt {c c' : PCfg} {i : Nat} : MErreichbar c0 c → MSchritt i c c' → MErreichbar c0 c'

/-- **THE BRIDGE, runs.** From read-blind threads, every configuration the process over `SC L` reaches by memory
    steps is reached by the request-level process on the memories, and its threads are read-blind. -/
theorem sc_mErreichbar {L : Lay} {c0 c : Cfg (SC L) (Res T)} (h0 : AlleBlind c0.ths) (h : SCErreichbar L c0 c) :
    MErreichbar ⟨c0.ms.1, c0.ths⟩ ⟨c.ms.1, c.ths⟩ ∧ AlleBlind c.ths := by
  induction h with
  | start => exact ⟨.start, h0⟩
  | schritt _ hs ih =>
    obtain ⟨hr, hb⟩ := ih
    exact ⟨.schritt hr (sc_mSchritt hs (hb _)), alleBlind_schritt hs hb⟩

/-- A memory-only SC path with private requests preserves the image relation
    and its thread footprints. Every prefix has the same committed G state. -/
theorem sc_private_runs_refine {D : Deklaration} [Kern] {hardwareLayout : Lay}
    {c0 c : Cfg (SC hardwareLayout) (Res T)}
    {P : Programm D} {O : Orakel D} {passes : Nat} {layout : Senke.Lay D}
    {K : FadenMaschine D} {initial : Nat → Option Solo} {positions : Nat → MLage D}
    {committed : Mem}
    (relation : MTRel P O passes layout ⟨c0.ms.1, c0.ths⟩ K initial positions committed)
    (blind : AlleBlind c0.ths)
    (access : ∀ {before after i}, SCErreichbar hardwareLayout c0 before →
      SCSchritt hardwareLayout i before after → ∀ {s o k},
      initial i = some s → before.ths[i]? = some (some (.ask o k)) →
      (∀ y, fussOp o y → s.F y) ∧ (schreibtOp o = true → ∀ y, fussOp o y → s.Wr y))
    (reached : SCErreichbar hardwareLayout c0 c) :
    ∃ snapshots, MTRel P O passes layout ⟨c.ms.1, c.ths⟩ K snapshots positions committed ∧
      AlleBlind c.ths ∧ ∀ i s, snapshots i = some s →
        ∃ original, initial i = some original ∧ s.F = original.F ∧ s.Wr = original.Wr := by
  induction reached with
  | start => exact ⟨initial, relation, blind, fun _ s found => ⟨s, found, rfl, rfl⟩⟩
  | @schritt before after i prefix step ih =>
    obtain ⟨snapshots, beforeRelation, beforeBlind, sameSets⟩ := ih
    have live : ∃ result, before.ths[i]? = some (some result) := by
      cases step with
      | priv found => exact ⟨_, found⟩
      | ask found _ _ => exact ⟨_, found⟩
    obtain ⟨result, live⟩ := live
    obtain ⟨s, found⟩ := beforeRelation.lebend i result live
    have privateRequest : ImFuss s := by
      intro o k request
      obtain ⟨original, originalFound, footprint, writes⟩ := sameSets i s found
      have pending := beforeRelation.zustand i s found
      rw [request] at pending
      simpa only [footprint, writes] using access prefix step originalFound pending
    obtain ⟨next, footprint, writes, afterRelation⟩ :=
      mtRel_schritt beforeRelation found privateRequest (sc_mSchritt step (beforeBlind i))
    refine ⟨setzeS snapshots i next, afterRelation, alleBlind_schritt step beforeBlind, ?_⟩
    intro j s' updated
    obtain ⟨beforeSnapshot, beforeFound, sameFootprint, sameWrites⟩ :=
      setzeS_fuss found footprint writes updated
    obtain ⟨original, originalFound, oldFootprint, oldWrites⟩ := sameSets j beforeSnapshot beforeFound
    exact ⟨original, originalFound, sameFootprint.trans oldFootprint, sameWrites.trans oldWrites⟩

/-- The start of a process: one thread at an instruction start, read-blind. -/
theorem alleBlind_start (t : T) : AlleBlind [some (.next t)] := by
  intro j r h
  cases j with
  | zero =>
    cases h
    exact Blind.next t
  | succ j => simp at h

end Gabbro.Stage0.Senke.BildMehr
