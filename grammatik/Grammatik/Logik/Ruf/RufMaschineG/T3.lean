/- Part 3 of 7 of `RufMaschineG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufMaschineG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.RufMaschineG.T2

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 4. Reachability -/

/-- Take the locks `Ls` in list order on top of the trace `s`, each `nimmt`
    event carrying the locks held at that moment. -/
def nimmtAlle : List D.Lock → List (Ereignis D) → List (Ereignis D)
  | [], s => s
  | L :: Ls, s => nimmtAlle Ls (Ereignis.nimmt L (offen s) :: s)

theorem offen_nimmtAlle : ∀ (Ls : List D.Lock) (s : List (Ereignis D)) (L : D.Lock),
    L ∈ offen (nimmtAlle Ls s) ↔ L ∈ Ls ∨ L ∈ offen s
  | [], s, L => by simp [nimmtAlle]
  | K :: Ls, s, L => by
      rw [nimmtAlle, offen_nimmtAlle Ls _ L]
      simp only [offen, List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rintro ((h | h) | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

/-- The start trace of a thread entering `g`: its signature locks, taken. -/
def startSpur (g : D.Fn) : List (Ereignis D) := nimmtAlle (D.haelt g) []

theorem offen_startSpur (g : D.Fn) (L : D.Lock) : L ∈ offen (startSpur g) ↔ L ∈ D.haelt g := by
  rw [startSpur, offen_nimmtAlle]
  simp [offen]

/-- The start machine: every thread in its entry frame with the entry
    environment and an `ende` residue over the function body, HOLDING the
    signature locks of its start function (`startSpur`): a thread starts
    the way a callee is entered -- with `requires Held(L)` met. The bare
    `nimmt` step that used to take them after entry is gone. Exclusivity
    of these locks across threads is a fact about `init`
    (`StartExklusiv`). The entry event keeps the world `sp.welt []`:
    memory `sp`, the trace does not matter to any expression. -/
def RufStartG (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) :
    RufMaschineG D :=
  ⟨sp, fun f =>
    let ⟨g, rho⟩ := init f
    ⟨[], ⟨g, rho, sp.welt [],
      ⟨false, D.params g, Signatur.anfang D (D.signatur g),
       rho, .ende (P.rumpf g)⟩⟩,
     startSpur g, [RufEreignisF.eintritt g rho (sp.welt [])]⟩,
   [], sp.welt []⟩

/-- **The start fact about `init`**: no two threads start in functions
    holding a common lock by signature. -/
def StartExklusiv (init : Faden → Σ f : D.Fn, Env D (D.params f)) : Prop :=
  ∀ t u : Faden, t ≠ u → ∀ L : D.Lock, L ∈ D.haelt (init t).1 → L ∉ D.haelt (init u).1

/-- Reachable machines, generated from `M0` by the step relation. -/
inductive RufErreichbarG (P : Programm D) (O : Orakel D) (passes : Nat)
    (M0 : RufMaschineG D) : RufMaschineG D → Prop where
  | start : RufErreichbarG P O passes M0 M0
  | schritt (M M' : RufMaschineG D) (f : Faden)
      (h : RufErreichbarG P O passes M0 M) (hs : RufSchrittG P O passes M f M') :
      RufErreichbarG P O passes M0 M'

/-! ## 5. Matching entries and returns: the call-log invariant -/

/-- The key of a frame: function, actual parameters, entry world.
    Residue and local context are NOT part of the key. -/
def RufSchluesselG (r : RufRahmenG D) :
    Σ f : D.Fn, Env D (D.params f) × World D :=
  ⟨r.f, r.rho, r.s0⟩

/-- The key stack of a thread: head frame first. -/
def RufFadenSchluesselG (z : RufFadenG D) :
    List (Σ f : D.Fn, Env D (D.params f) × World D) :=
  (z.kopf :: z.stapel).map RufSchluesselG

/-- A log matches its key stack. -/
inductive RufLogPasstG :
    List (Σ f : D.Fn, Env D (D.params f) × World D) →
    List (RufEreignisF D) → Prop where
  | leer : RufLogPasstG [] []
  | eintritt (ks : List (Σ f : D.Fn, Env D (D.params f) × World D))
      (log : List (RufEreignisF D))
      (f : D.Fn) (rho : Env D (D.params f)) (s0 : World D)
      (h : RufLogPasstG ks log) :
      RufLogPasstG (⟨f, rho, s0⟩ :: ks)
        (RufEreignisF.eintritt f rho s0 :: log)
  | rueck (ks : List (Σ f : D.Fn, Env D (D.params f) × World D))
      (log : List (RufEreignisF D))
      (f : D.Fn) (rho : Env D (D.params f)) (s0 : World D)
      (v : ErgVal D (D.erg f)) (s1 : World D)
      (h : RufLogPasstG (⟨f, rho, s0⟩ :: ks) log) :
      RufLogPasstG ks
        (RufEreignisF.rueck f rho v s0 s1 :: log)
  | why (ks : List (Σ f : D.Fn, Env D (D.params f) × World D))
      (log : List (RufEreignisF D))
      (f : D.Fn) (rho : Env D (D.params f)) (s0 : World D)
      (r : Fin (D.gruende f)) (s1 : World D)
      (h : RufLogPasstG (⟨f, rho, s0⟩ :: ks) log) :
      RufLogPasstG ks
        (RufEreignisF.why f rho r s0 s1 :: log)

/-- A thread state satisfies the invariant: its log matches its key stack. -/
def RufFadenPasstG (z : RufFadenG D) : Prop :=
  RufLogPasstG (RufFadenSchluesselG z) z.log

/-- A `rueck` entry in the log carries matched data. -/
def rufRueckGedecktG (log : List (RufEreignisF D)) : Prop :=
  ∀ (g : D.Fn) (rho : Env D (D.params g)) (v : ErgVal D (D.erg g))
    (s0 s1 : World D),
    RufEreignisF.rueck g rho v s0 s1 ∈ log →
      RufEreignisF.eintritt g rho s0 ∈ log

/-- Auxiliary: every key ON the stack has its entry in the log. Every
    premise is used: `hmem` selects the stack side in each case. -/
theorem rufLogPasstG_mem_eintritt
    (ks : List (Σ f : D.Fn, Env D (D.params f) × World D))
    (log : List (RufEreignisF D)) (h : RufLogPasstG ks log)
    (k : Σ f : D.Fn, Env D (D.params f) × World D) (hmem : k ∈ ks) :
    RufEreignisF.eintritt k.1 k.2.1 k.2.2 ∈ log := by
  induction h with
  | leer =>
      simp at hmem
  | eintritt s l f rho s0 htail ih =>
      rw [List.mem_cons] at hmem
      rcases hmem with hmem | hmem
      · subst hmem
        exact List.mem_cons_self
      · have htailmem := ih hmem
        exact List.mem_cons_of_mem _ htailmem
  | rueck s l f rho s0 vv ss1 htail ih =>
      have htailmem := ih (List.mem_cons_of_mem _ hmem)
      exact List.mem_cons_of_mem _ htailmem
  | why s l f rho s0 rr ss1 htail ih =>
      have htailmem := ih (List.mem_cons_of_mem _ hmem)
      exact List.mem_cons_of_mem _ htailmem

/-- Every well-formed log stack ends in the matching entry. -/
theorem rufLogPasstG_eintritt_mem
    (ks : List (Σ f : D.Fn, Env D (D.params f) × World D))
    (log : List (RufEreignisF D)) (h : RufLogPasstG ks log)
    (k : Σ f : D.Fn, Env D (D.params f) × World D)
    (rest : List (Σ f : D.Fn, Env D (D.params f) × World D))
    (hcon : ks = k :: rest) :
    RufEreignisF.eintritt k.1 k.2.1 k.2.2 ∈ log := by
  have hmem : k ∈ ks := by rw [hcon]; exact List.mem_cons_self
  exact rufLogPasstG_mem_eintritt ks log h k hmem

/-- Every well-formed log has matched returns. -/
theorem rufLogPasstG_gedeckt
    (ks : List (Σ f : D.Fn, Env D (D.params f) × World D))
    (log : List (RufEreignisF D)) (h : RufLogPasstG ks log) :
    rufRueckGedecktG log := by
  induction h with
  | leer =>
      intro f rho v s0 s1 hm
      simp at hm
  | eintritt ks log f rho s0 htail ih =>
      intro g rho' v s0' s1 hm
      rw [List.mem_cons] at hm
      rcases hm with hm | hm
      · simp at hm
      · have hmem := ih g rho' v s0' s1 hm
        rw [List.mem_cons]
        exact Or.inr hmem
  | rueck ks log f rho s0 v s1 htail ih =>
      intro g rho' w s0' s1' hm
      rw [List.mem_cons] at hm
      rcases hm with hm | hm
      · cases hm
        have hmem : RufEreignisF.eintritt f rho s0 ∈ log :=
          rufLogPasstG_eintritt_mem (⟨f, rho, s0⟩ :: ks) log htail
            ⟨f, rho, s0⟩ ks rfl
        rw [List.mem_cons]
        exact Or.inr hmem
      · have hmem := ih g rho' w s0' s1' hm
        rw [List.mem_cons]
        exact Or.inr hmem
  | why ks log f rho s0 r s1 htail ih =>
      intro g rho' w s0' s1' hm
      rw [List.mem_cons] at hm
      rcases hm with hm | hm
      · simp at hm
      · have hmem := ih g rho' w s0' s1' hm
        rw [List.mem_cons]
        exact Or.inr hmem

/-! ## 6. Preservation of the invariant along steps -/

/-- Key-stack helper: a step that keeps function, parameters and entry
    world keeps the key stack. Both the kept triple and `h` feed the goal. -/
theorem rufFadenSchluesselG_behalte (z : RufFadenG D)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ' : Env D Γ)
    (rb : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (spur : List (Ereignis D)) :
    RufFadenSchluesselG
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, Λ, ρ', rb⟩⟩,
       spur, z.log⟩ =
      RufFadenSchluesselG z := by
  simp [RufFadenSchluesselG, RufSchluesselG]

/-- Invariant helper: a step that keeps the key triple and the log keeps
    a well-formed thread. Used by every non-call step below. -/
theorem rufFadenPasstG_behalte (z : RufFadenG D)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ' : Env D Γ)
    (rb : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (spur : List (Ereignis D)) (h : RufFadenPasstG z) :
    RufFadenPasstG
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, Λ, ρ', rb⟩⟩,
       spur, z.log⟩ := by
  unfold RufFadenPasstG
  rw [rufFadenSchluesselG_behalte]
  exact h

/-- The machine invariant: every thread's log matches its key stack. -/
def RufMaschinePasstG (M : RufMaschineG D) : Prop :=
  ∀ f, RufFadenPasstG (M.faeden f)

/-- The start machine satisfies the invariant. Every premise is used:
    `hlog` names the start log, `hkeys` the start key stack. -/
theorem rufStartG_passt (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) :
    RufMaschinePasstG (RufStartG P sp init) := by
  intro f
  have hpair : ∃ g rho, init f = (⟨g, rho⟩ : Σ f : D.Fn, Env D (D.params f)) :=
    ⟨(init f).1, (init f).2, by cases init f with | mk g rho => rfl⟩
  obtain ⟨g, rho, hif⟩ := hpair
  have hstart : (RufStartG (D := D) P sp init).faeden f =
      (match init f with
      | ⟨g', rho'⟩ =>
        (⟨[], (⟨g', rho', sp.welt [],
          ⟨false, D.params g', Signatur.anfang D (D.signatur g'),
           rho', .ende (P.rumpf g')⟩⟩ : RufRahmenG D),
         startSpur g', [RufEreignisF.eintritt g' rho' (sp.welt [])]⟩ :
          RufFadenG D)) := rfl
  have hlog : ((RufStartG P sp init).faeden f).log =
      [RufEreignisF.eintritt g rho (sp.welt [])] := by
    rw [hstart, hif]
  have hkeys : RufFadenSchluesselG ((RufStartG P sp init).faeden f) =
      [⟨g, rho, sp.welt []⟩] := by
    rw [hstart, hif]
    rfl
  unfold RufFadenPasstG
  rw [hkeys, hlog]
  exact RufLogPasstG.eintritt [] [] _ _ _ RufLogPasstG.leer

/-- Push helper: pushing a callee frame with its entry event keeps a
    well-formed thread well-formed, whatever residues either frame carries
    (keys ignore residues). `hcaller` fixes the pushed caller key,
    `hcallee` the callee key; both feed the rewrite `e`, `h` the log. -/
theorem rufPushG_passt (z : RufFadenG D)
    (caller callee : RufRahmenG D)
    (hcaller : RufSchluesselG caller = RufSchluesselG z.kopf)
    (g : D.Fn) (rho : Env D (D.params g)) (s0 : World D)
    (hcallee : RufSchluesselG callee = ⟨g, rho, s0⟩)
    (spur : List (Ereignis D))
    (h : RufFadenPasstG z) :
    RufFadenPasstG
      ⟨caller :: z.stapel, callee, spur,
       (RufEreignisF.eintritt g rho s0) :: z.log⟩ := by
  have e : RufFadenSchluesselG
      (⟨caller :: z.stapel, callee, spur,
        (RufEreignisF.eintritt g rho s0) :: z.log⟩ : RufFadenG D) =
      (⟨g, rho, s0⟩ :
        Σ f : D.Fn, Env D (D.params f) × World D) ::
        RufFadenSchluesselG z := by
    simp only [RufFadenSchluesselG, List.map_cons, hcallee, hcaller]
  unfold RufFadenPasstG
  rw [e]
  exact RufLogPasstG.eintritt _ _ g rho s0 h

/-- Pop helper: popping the head frame to a new head with the CALLER's key,
    logging the return, keeps a well-formed thread well-formed. `hpop`
    fixes the old stack, `hkeyNeu` the new head key, `hhead` the old head
    key; all three feed the rewrites, `h` the log. -/
theorem rufPopG_passt (z : RufFadenG D)
    (caller : RufRahmenG D) (rest : List (RufRahmenG D))
    (hpop : z.stapel = caller :: rest)
    (neu : RufRahmenG D)
    (hkeyNeu : RufSchluesselG neu = RufSchluesselG caller)
    (g : D.Fn) (rho : Env D (D.params g)) (v : ErgVal D (D.erg g))
    (s0 s1 : World D)
    (hhead : RufSchluesselG z.kopf =
      (⟨g, rho, s0⟩ : Σ f : D.Fn, Env D (D.params f) × World D))
    (spur : List (Ereignis D))
    (h : RufFadenPasstG z) :
    RufFadenPasstG
      ⟨rest, neu, spur,
       (RufEreignisF.rueck g rho v s0 s1) :: z.log⟩ := by
  have hk : RufFadenSchluesselG z =
      RufSchluesselG z.kopf ::
        ((caller :: rest).map RufSchluesselG) := by
    have e : RufFadenSchluesselG z =
        RufSchluesselG z.kopf ::
          ((z.stapel.map RufSchluesselG)) := by
      simp [RufFadenSchluesselG]
    rw [e, hpop]
  have htail : RufFadenSchluesselG
      (⟨rest, neu, spur,
        (RufEreignisF.rueck g rho v s0 s1) :: z.log⟩ : RufFadenG D) =
      (caller :: rest).map RufSchluesselG := by
    simp only [RufFadenSchluesselG, List.map_cons, hkeyNeu]
  unfold RufFadenPasstG at h ⊢
  rw [hk, hhead] at h
  rw [htail]
  exact RufLogPasstG.rueck _ _ g rho s0 v s1 h

/-- Pop helper for the error channel: popping the head frame with a
    `grund` event keeps a well-formed thread well-formed, exactly as
    `rufPopG_passt` does for `rueck`. -/
theorem rufPopGrundG_passt (z : RufFadenG D)
    (caller : RufRahmenG D) (rest : List (RufRahmenG D))
    (hpop : z.stapel = caller :: rest)
    (neu : RufRahmenG D)
    (hkeyNeu : RufSchluesselG neu = RufSchluesselG caller)
    (g : D.Fn) (rho : Env D (D.params g)) (r : Fin (D.gruende g))
    (s0 s1 : World D)
    (hhead : RufSchluesselG z.kopf =
      (⟨g, rho, s0⟩ : Σ f : D.Fn, Env D (D.params f) × World D))
    (spur : List (Ereignis D))
    (h : RufFadenPasstG z) :
    RufFadenPasstG
      ⟨rest, neu, spur,
       (RufEreignisF.why g rho r s0 s1) :: z.log⟩ := by
  have hk : RufFadenSchluesselG z =
      RufSchluesselG z.kopf ::
        ((caller :: rest).map RufSchluesselG) := by
    have e : RufFadenSchluesselG z =
        RufSchluesselG z.kopf ::
          ((z.stapel.map RufSchluesselG)) := by
      simp [RufFadenSchluesselG]
    rw [e, hpop]
  have htail : RufFadenSchluesselG
      (⟨rest, neu, spur,
        (RufEreignisF.why g rho r s0 s1) :: z.log⟩ : RufFadenG D) =
      (caller :: rest).map RufSchluesselG := by
    simp only [RufFadenSchluesselG, List.map_cons, hkeyNeu]
  unfold RufFadenPasstG at h ⊢
  rw [hk, hhead] at h
  rw [htail]
  exact RufLogPasstG.why _ _ g rho s0 r s1 h


end Gabbro.Grammatik
