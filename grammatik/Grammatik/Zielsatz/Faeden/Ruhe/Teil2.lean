module

public import Grammatik.Zielsatz.Kern.Akzeptiert
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheStatisch
public import Grammatik.Zielsatz.Faeden.Ruhe.Teil1

@[expose] public section

namespace Gabbro.Grammatik
open Zielsatz
variable {D : Deklaration}
section Transfer
variable [DecidableEq D.Fn] (P : Programm D) {S : SperrInv D} {fs ws : List D.Fn}

/-- **The checker's Bool on `P.mitRuhe` follows from the Bool on `P`**
    (the member lists of locks and carriers are the same). -/
theorem akzeptiert_mitRuhe {ls : List D.Lock} {cs : List (D.Tab ⊕ D.Glob)}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls)
    (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) (h : Akzeptiert P S fs ls cs ws = true) :
    Akzeptiert P.mitRuhe S.mitRuhe (fsRuhe fs) ls cs (wsRuhe ws) = true :=
  (akzeptiert_iff (fsRuhe_voll hvoll) hls hcs []).mpr
    (akzeptiertSpec_mitRuhe P hvoll (akzeptiertSpec_of hvoll hls hcs [] h))

/-- **The root is an idle start of `P.mitRuhe`.** -/
theorem ruhig_mitRuhe : Ruhig P.mitRuhe (fsRuhe fs) none :=
  ⟨rfl, rfl, fun f' hf => by
    rw [reach_mitRuhe_ruhe_cases P hf]
    exact ⟨fussOrteG_mitRuhe_ruhe P, fun c => by cases c <;> rfl⟩⟩

end Transfer

/-! ## The admissible starts of `P.mitRuhe` -/

/-- **The runtime's start**: thread `t < aktiv.length` runs the declared
    start `aktiv[t]`, every other thread the idle root. -/
def initRuhe (aktiv : List (Σ w : D.Fn, Env D (D.params w))) :
    Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f) :=
  fun t => match aktiv[t]? with
    | some ⟨w, ρ⟩ => ⟨some w, envR ρ⟩
    | none => ⟨none, .nil⟩

section Start

variable [DecidableEq D.Fn] (P : Programm D) {S : SperrInv D} {fs ws : List D.Fn}

/-- **"Declared starts on their threads, the idle root everywhere else" is
    admissible on `P.mitRuhe`**: each declared start at most once, its
    `requires` at the start memory, every lock invariant at the start
    memory. -/
theorem startZulaessig_mitRuhe (aktiv : List (Σ w : D.Fn, Env D (D.params w)))
    (sp : Speicher D.mitRuhe) (hws : ∀ a ∈ aktiv, a.1 ∈ ws) (hnd : (aktiv.map (·.1)).Nodup)
    (hreq : ∀ a ∈ aktiv, ReqAmEintritt P.mitRuhe (some a.1) (sp.welt []) (envR a.2))
    (hS : ∀ L, S.inv L (speicherZ sp) = true) :
    StartZulaessig P.mitRuhe S.mitRuhe (fsRuhe fs) (wsRuhe ws) sp (initRuhe aktiv) where
  wurzel t := by
    unfold initRuhe
    cases h : aktiv[t]? with
    | none => exact Or.inr (ruhig_mitRuhe P)
    | some a => exact Or.inl (List.mem_map_of_mem (hws a (List.mem_of_getElem? h)))
  einmal t u htu he := by
    revert he
    unfold initRuhe
    cases ht : aktiv[t]? with
    | none => intro _; exact Or.inl (ruhig_mitRuhe P)
    | some a =>
        cases hu : aktiv[u]? with
        | none => intro he; cases he
        | some b =>
            intro he
            exfalso
            have hab : a.1 = b.1 := Option.some.inj he
            have ht' : (aktiv.map (·.1))[t]? = some a.1 := by rw [List.getElem?_map, ht]; rfl
            have hu' : (aktiv.map (·.1))[u]? = some b.1 := by rw [List.getElem?_map, hu]; rfl
            rw [hab] at ht'
            have hlt : t < (aktiv.map (·.1)).length := (List.getElem?_eq_some_iff.mp ht').1
            exact htu ((List.getElem?_inj hlt hnd).mp (ht'.trans hu'.symm))
  req t := by
    show ReqAmEintritt P.mitRuhe (initRuhe aktiv t).1 (sp.welt []) (initRuhe aktiv t).2
    unfold initRuhe
    cases h : aktiv[t]? with
    | none => rfl
    | some a => exact hreq a (List.mem_of_getElem? h)
  sperren := hS

/-- The idle root on every thread. -/
def ruheInit (D : Deklaration) : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f) :=
  fun _ => ⟨none, .nil⟩

/-- **The idle root on every thread is admissible on `P.mitRuhe`** as soon
    as the memory meets the lock invariants -- whatever `P` declares. -/
theorem startZulaessig_ruhe (sp : Speicher D.mitRuhe) (hS : ∀ L, S.inv L (speicherZ sp) = true) :
    StartZulaessig P.mitRuhe S.mitRuhe (fsRuhe fs) ws' sp (ruheInit D) where
  wurzel _ := Or.inr (ruhig_mitRuhe P)
  einmal _ _ _ _ := Or.inl (ruhig_mitRuhe P)
  req _ := by rfl
  sperren := hS

end Start

/-! ## The runtime's start (Spec's `Laufzeit`, A4) -/

section Laufzeit

/-- **The runtime's exact start meets A4**: the declared starts on threads
    `0 .. k-1` with their declared arguments, the root elsewhere, from the
    declared initial memory. Since fix lane F10 with NO side condition: two
    threads running one routine run two of its declared occurrences, so the
    routine is declared twice (`Mehrfach`, the pool case of `einmal`). Before,
    this needed distinct declared starts. -/
theorem laufzeit_initRuhe (E : Einheit D) :
    Laufzeit E (speicherR E.sp0) (initRuhe E.starts) where
  lader := by rfl
  start t := by
    unfold initRuhe
    rcases h : E.starts[t]? with _ | ⟨w, ρ⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨⟨w, ρ⟩, List.mem_append_left _ (List.mem_of_getElem? h), rfl⟩
  einmal t u htu he := by
    revert he
    unfold initRuhe
    cases ht : E.starts[t]? with
    | none => intro _; exact Or.inl rfl
    | some a =>
        cases hu : E.starts[u]? with
        | none => intro he; cases he
        | some b =>
            intro he
            have hab : a.1 = b.1 := Option.some.inj he
            have ht' : (E.starts.map (·.1))[t]? = some a.1 := by rw [List.getElem?_map, ht]; rfl
            have hu' : (E.starts.map (·.1))[u]? = some a.1 := by
              rw [List.getElem?_map, hu, hab]; rfl
            refine Or.inr ⟨a.1, rfl, ?_⟩
            have hsub : List.Sublist (E.starts.map (·.1)) E.ws := by
              unfold Einheit.ws
              rw [List.append_assoc, List.map_append]
              exact List.sublist_append_left _ _
            rcases Nat.lt_or_gt_of_ne htu with h | h
            · exact (mehrfach_of_getElem? h ht' hu').trans hsub
            · exact (mehrfach_of_getElem? h hu' ht').trans hsub

/-- The runtime's exact start is always in the class A4 describes (since fix
    lane F10 without a checker fact; the name is kept for its callers). -/
theorem laufzeit_voll (E : Einheit D) : Laufzeit E (speicherR E.sp0) (initRuhe E.starts) :=
  laufzeit_initRuhe E

/-- **Under A4 a thread runs only what the program declares** (verdict P2):
    a user function runs on a thread only if it is a declared start. -/
theorem laufzeit_nur_erklaert {E : Einheit D} {sp : Speicher D.mitRuhe}
    {init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)}
    (hL : Laufzeit E sp init) (t : Faden) (f : D.Fn) (hf : (init t).1 = some f) : f ∈ E.ws := by
  rcases hL.start t with h | ⟨a, ha, h⟩
  · rw [h] at hf
    cases hf
  · rw [h] at hf
    cases hf
    exact List.mem_map_of_mem (List.mem_append_left _ ha)

/-- A program that declares no start runs the root on every thread. -/
theorem laufzeit_ohne_starts {E : Einheit D} (h0 : E.starts = []) (h1 : E.gestartet = [])
    {sp : Speicher D.mitRuhe}
    {init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)}
    (hL : Laufzeit E sp init) (t : Faden) : (init t).1 = none := by
  rcases hL.start t with h | ⟨a, ha, _⟩
  · rw [h]
  · rw [h0, h1] at ha
    exact absurd ha List.not_mem_nil

/-- The runtime's root on every thread from the declared memory is always a
    start A4 admits: the conclusion's run class is never empty. -/
theorem laufzeit_ruhe (E : Einheit D) : Laufzeit E (speicherR E.sp0) (ruheInit D) where
  lader := by rfl
  start _ := Or.inl rfl
  einmal _ _ _ _ := Or.inl rfl

end Laufzeit

#print axioms Gabbro.Grammatik.mehrfach_map_inj
#print axioms Gabbro.Grammatik.mehrfach_of_getElem?
#print axioms Gabbro.Grammatik.einzelnPool_mitRuhe
#print axioms Gabbro.Grammatik.laufzeit_initRuhe
#print axioms Gabbro.Grammatik.laufzeit_voll
#print axioms Gabbro.Grammatik.laufzeit_nur_erklaert
#print axioms Gabbro.Grammatik.laufzeit_ohne_starts
#print axioms Gabbro.Grammatik.laufzeit_ruhe
#print axioms Gabbro.Grammatik.akzeptiertSpec_mitRuhe
#print axioms Gabbro.Grammatik.akzeptiert_mitRuhe
#print axioms Gabbro.Grammatik.ruhig_mitRuhe
#print axioms Gabbro.Grammatik.startZulaessig_mitRuhe
#print axioms Gabbro.Grammatik.startZulaessig_ruhe

end Gabbro.Grammatik
