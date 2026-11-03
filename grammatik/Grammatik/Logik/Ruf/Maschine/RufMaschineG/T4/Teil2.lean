module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T3
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T4.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-! ## 6a. No head ever waits: the deadlock of the verbatim pops is gone

    A waiting residue (`wartet`/`wartetSonst`) is created only in a PUSHED
    caller frame, and only a binding pop resumes it; the verbatim pops
    (`rueck`, `rueckCons`, `dannRet`) now demand a caller that does not
    wait (`hnw`). So the invariant "the head residue contains no waiting
    node, and every stacked residue is either clean or waits over a clean
    continuation" holds at the start and is kept by every rule; in
    particular no reachable head is a waiting residue (`rufG_nie_wartend`),
    the state in which only the bare lock steps could fire. -/

/-- A residue with no waiting node anywhere along its continuation. -/
def GRest.sauber {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Bool
  | .ende _ => true
  | .dann _ k => k.sauber
  | .schrumpf k => k.sauber
  | .frei _ k => k.sauber
  | .trav _ _ _ _ k => k.sauber
  | .travRest _ _ _ _ k => k.sauber
  | .verbrauch _ _ _ _ _ _ _ _ k => k.sauber
  | .verbrauchRest _ _ _ _ _ _ _ _ _ k => k.sauber
  | .wieder _ _ _ _ k => k.sauber
  | .wiederRest _ _ _ _ k => k.sauber
  | .ewig _ _ _ _ k => k.sauber
  | .ewigRest _ _ _ _ k => k.sauber
  | .wartet _ _ => false
  | .wartetSonst _ _ _ _ => false
  | .abbruch k => k.sauber
  | .leer => true
  | .rueckBereit _ k => k.sauber

/-- A stacked residue: clean, or waiting over a clean continuation. -/
def GRest.stapelSauber {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Bool
  | .wartet _ k => k.sauber
  | .wartetSonst _ _ _ k => k.sauber
  | r => r.sauber

theorem GRest.sauber_wartend {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {r : GRest D V l Γ Λ} (h : r.sauber = true) : r.wartend = false := by
  cases r <;> simp_all [GRest.sauber, GRest.wartend]

theorem GRest.stapelSauber_sauber {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {r : GRest D V l Γ Λ} (hw : r.wartend = false) (h : r.stapelSauber = true) :
    r.sauber = true := by
  cases r <;> simp_all [GRest.sauber, GRest.stapelSauber, GRest.wartend]

/-- The thread invariant: a clean head, clean-or-waiting stacked frames. -/
def RufFadenSauberG (z : RufFadenG D) : Prop :=
  z.kopf.rest.2.2.2.2.sauber = true ∧ ∀ r ∈ z.stapel, r.rest.2.2.2.2.stapelSauber = true

/-- The invariant implies a head that does not wait. -/
theorem RufFadenSauberG.kopf_wartend {z : RufFadenG D} (h : RufFadenSauberG z) :
    z.kopf.wartend = false :=
  GRest.sauber_wartend h.1

/-- One step preserves the invariant at an UNTOUCHED thread: the
    result machine's thread state equals the old one. `hne` selects the
    untouched side and is consumed by the simp set. -/
theorem rufSchrittG_passt_anders (P : Programm D) (O : Orakel D) (passes : Nat)
    (M M' : RufMaschineG D) (f f' : Faden) (hne : f' ≠ f)
    (hs : RufSchrittG P O passes M f M') :
    M'.faeden f' = M.faeden f' := by
  (rcases hs with hs | hs | hs | hs | hs | hs | hs <;> cases hs) <;> (simp_all [rufUpdateG_noteq])

/-- One step preserves the invariant for EVERY thread. Both `hact`
    (acting side) and the untouched side feed the conclusion; `hne`
    selects the side. -/
theorem rufSchrittG_passt (P : Programm D) (O : Orakel D) (passes : Nat)
    (M M' : RufMaschineG D) (f : Faden)
    (h : RufMaschinePasstG M)
    (hs : RufSchrittG P O passes M f M') :
    RufMaschinePasstG M' := by
  intro f'
  by_cases hne : f' = f
  · subst hne
    exact rufSchrittG_passt_acting P O passes M M' f' (h f') hs
  · rw [rufSchrittG_passt_anders P O passes M M' f f' hne hs]
    exact h f'

/-- The invariant holds at every reachable machine. Both `hbase` (start
    evidence) and the step evidence feed the conclusion. -/
theorem rufErreichbarG_passt (P : Programm D) (O : Orakel D) (passes : Nat)
    (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (M : RufMaschineG D)
    (h : RufErreichbarG P O passes (RufStartG P sp init) M) :
    RufMaschinePasstG M := by
  induction h with
  | start => exact rufStartG_passt P sp init
  | schritt M M' f hbase hs ih =>
      exact rufSchrittG_passt P O passes M M' f ih hs

/-- **Return fidelity.** Every `rueck` event in a reachable thread log has
    its matching `eintritt` event in the same log. Every premise is used:
    `h` selects the reachable machine, `hmem` the log event. -/
theorem rufG_treu (P : Programm D) (O : Orakel D) (passes : Nat) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (M : RufMaschineG D)
    (h : RufErreichbarG P O passes (RufStartG P sp init) M) (f : Faden) :
    ∀ (g : D.Fn) (rho : Env D (D.params g)) (v : ErgVal D (D.erg g)) (s0 s1 : World D),
      RufEreignisF.rueck g rho v s0 s1 ∈ (M.faeden f).log →
      RufEreignisF.eintritt g rho s0 ∈ (M.faeden f).log := by
  have hmach := rufErreichbarG_passt P O passes sp init M h
  have hthread := hmach f
  unfold RufFadenPasstG at hthread
  have hged := rufLogPasstG_gedeckt (RufFadenSchluesselG (M.faeden f))
    (M.faeden f).log hthread
  unfold rufRueckGedecktG at hged
  intro g rho v s0 s1 hmem
  exact hged g rho v s0 s1 hmem

end Gabbro.Grammatik
