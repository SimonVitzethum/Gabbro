/- Part 2 of 3 of `RufMaschineF` (split by instrumente/teile/lean-teilen.py; the umbrella `RufMaschineF.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Maschine.RufMaschineF.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- One step preserves the invariant for the ACTING thread.
    `blatt`/`nimmt`/`gibt` keep the key stack (the residue moves, the key
    does not) and the log; `ruf` pushes the callee key with its entry event;
    `rueck` pops the head key with its return event. Every premise of the
    step is used: `hhead`/`hΛ` fix the firing frame, `hstep`/`hrho`/`hv`
    the computed data, `hpop`/`hfg`/`hrho`/`hs0` the popped frame identity,
    `hneu`/`hs0`/`hs1` the trace threading. -/
theorem rufSchrittF_passt_acting (P : Programm D) (O : Orakel D) (passes : Nat)
    (M M' : RufMaschineF D) (f : Faden)
    (h : RufFadenPasstF (M.faeden f))
    (hs : RufSchrittF P O passes M f M') :
    RufFadenPasstF (M'.faeden f) := by
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      have hkeys : RufFadenPasstF
          (⟨(M.faeden f).stapel,
           ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
            ⟨l, Γ, Λ', ρ', rest⟩⟩,
           σ'.spur, (M.faeden f).log⟩ : RufFadenF D) := by
        have e : RufFadenSchluesselF
            (⟨(M.faeden f).stapel,
             ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, Λ', ρ', rest⟩⟩,
             σ'.spur, (M.faeden f).log⟩ : RufFadenF D) =
            RufFadenSchluesselF (M.faeden f) := by
          simp only [RufFadenSchluesselF, List.map_cons, RufSchluesselF]
        unfold RufFadenPasstF
        rw [e]
        exact h
      have heq : (⟨σ'.speicher,
          rufUpdateF M.faeden f
            ⟨(M.faeden f).stapel,
             ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, Λ', ρ', rest⟩⟩,
             σ'.spur, (M.faeden f).log⟩,
          M.lauf ++ rufEigenF f neu, M.start⟩ : RufMaschineF D).faeden f =
          (⟨(M.faeden f).stapel,
           ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
            ⟨l, Γ, Λ', ρ', rest⟩⟩,
           σ'.spur, (M.faeden f).log⟩ : RufFadenF D) := by
        simp only [rufUpdateF_self]
      rw [heq]
      exact hkeys
  | nimmt L hself hrang hfrei =>
      have hkeys : RufFadenPasstF
          (⟨(M.faeden f).stapel, (M.faeden f).kopf,
           Ereignis.nimmt L (offen (M.faeden f).spur) :: (M.faeden f).spur,
           (M.faeden f).log⟩ : RufFadenF D) := by
        have e : RufFadenSchluesselF
            (⟨(M.faeden f).stapel, (M.faeden f).kopf,
             Ereignis.nimmt L (offen (M.faeden f).spur) :: (M.faeden f).spur,
             (M.faeden f).log⟩ : RufFadenF D) =
            RufFadenSchluesselF (M.faeden f) := by
          simp only [RufFadenSchluesselF, List.map_cons]
        unfold RufFadenPasstF
        rw [e]
        exact h
      have heq : (⟨M.speicher,
          rufUpdateF M.faeden f
            ⟨(M.faeden f).stapel, (M.faeden f).kopf,
             Ereignis.nimmt L (offen (M.faeden f).spur) :: (M.faeden f).spur,
             (M.faeden f).log⟩,
          M.lauf ++ rufEigenF f [Ereignis.nimmt L (offen (M.faeden f).spur)],
          M.start⟩ : RufMaschineF D).faeden f =
          (⟨(M.faeden f).stapel, (M.faeden f).kopf,
           Ereignis.nimmt L (offen (M.faeden f).spur) :: (M.faeden f).spur,
           (M.faeden f).log⟩ : RufFadenF D) := by
        simp only [rufUpdateF_self]
      rw [heq]
      exact hkeys
  | gibt L hhaelt =>
      have hkeys : RufFadenPasstF
          (⟨(M.faeden f).stapel, (M.faeden f).kopf,
           Ereignis.gibt L :: (M.faeden f).spur, (M.faeden f).log⟩ :
            RufFadenF D) := by
        have e : RufFadenSchluesselF
            (⟨(M.faeden f).stapel, (M.faeden f).kopf,
             Ereignis.gibt L :: (M.faeden f).spur, (M.faeden f).log⟩ :
              RufFadenF D) =
            RufFadenSchluesselF (M.faeden f) := by
          simp only [RufFadenSchluesselF, List.map_cons]
        unfold RufFadenPasstF
        rw [e]
        exact h
      have heq : (⟨M.speicher,
          rufUpdateF M.faeden f
            ⟨(M.faeden f).stapel, (M.faeden f).kopf,
             Ereignis.gibt L :: (M.faeden f).spur, (M.faeden f).log⟩,
          M.lauf ++ rufEigenF f [Ereignis.gibt L], M.start⟩ :
          RufMaschineF D).faeden f =
          (⟨(M.faeden f).stapel, (M.faeden f).kopf,
           Ereignis.gibt L :: (M.faeden f).spur, (M.faeden f).log⟩ :
            RufFadenF D) := by
        simp only [rufUpdateF_self]
      rw [heq]
      exact hkeys
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      have hkeys : RufFadenPasstF
          (⟨(M.faeden f).kopf :: (M.faeden f).stapel,
           ⟨g, rho, s0,
            ⟨false, D.params g, Signatur.anfang D (D.signatur g),
             rho, P.rumpf g⟩⟩,
           s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
            RufFadenF D) := by
        have e : RufFadenSchluesselF
            (⟨(M.faeden f).kopf :: (M.faeden f).stapel,
             ⟨g, rho, s0,
              ⟨false, D.params g, Signatur.anfang D (D.signatur g),
               rho, P.rumpf g⟩⟩,
             s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
              RufFadenF D) =
            (⟨g, rho, s0⟩ :
              Σ f : D.Fn, Env D (D.params f) × World D) ::
              RufFadenSchluesselF (M.faeden f) := by
          simp only [RufFadenSchluesselF, List.map_cons, RufSchluesselF]
        unfold RufFadenPasstF
        rw [e]
        exact RufLogPasstF.eintritt _ _ g rho s0 h
      have heq : (⟨M.speicher,
          rufUpdateF M.faeden f
            ⟨(M.faeden f).kopf :: (M.faeden f).stapel,
             ⟨g, rho, s0,
              ⟨false, D.params g, Signatur.anfang D (D.signatur g),
               rho, P.rumpf g⟩⟩,
             s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenF f neu,
          M.start⟩ : RufMaschineF D).faeden f =
          (⟨(M.faeden f).kopf :: (M.faeden f).stapel,
           ⟨g, rho, s0,
            ⟨false, D.params g, Signatur.anfang D (D.signatur g),
             rho, P.rumpf g⟩⟩,
           s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
            RufFadenF D) := by
        simp only [rufUpdateF_self]
      rw [heq]
      exact hkeys
  | rueck caller rest hpop Γ Λ e hperm ρ hh g hfg rho hr s0 hs0 hΛ s1 hs1 v hv neu hneu =>
      have hkeys : RufFadenPasstF
          (⟨rest, caller, s1.spur,
           (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩ :
            RufFadenF D) := by
        have hhead : RufSchluesselF (M.faeden f).kopf =
            (⟨g, rho, s0⟩ : Σ f : D.Fn, Env D (D.params f) × World D) := by
          cases hfg
          simp_all [RufSchluesselF]
        have hk : RufFadenSchluesselF (M.faeden f) =
            RufSchluesselF (M.faeden f).kopf ::
              ((caller :: rest).map RufSchluesselF) := by
          have e : RufFadenSchluesselF (M.faeden f) =
              RufSchluesselF (M.faeden f).kopf ::
                ((M.faeden f).stapel.map RufSchluesselF) := by
            simp only [RufFadenSchluesselF, List.map_cons]
          rw [e, hpop]
        have htail : RufFadenSchluesselF
            (⟨rest, caller, s1.spur,
             (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩ :
              RufFadenF D) =
            (caller :: rest).map RufSchluesselF := by
          simp only [RufFadenSchluesselF, List.map_cons]
        unfold RufFadenPasstF at h ⊢
        rw [hk, hhead] at h
        rw [htail]
        exact RufLogPasstF.rueck _ _ g rho s0 v s1 h
      have heq : (⟨s1.speicher,
          rufUpdateF M.faeden f
            ⟨rest, caller, s1.spur,
             (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenF f neu,
          M.start⟩ : RufMaschineF D).faeden f =
          (⟨rest, caller, s1.spur,
           (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩ :
            RufFadenF D) := by
        simp only [rufUpdateF_self]
      rw [heq]
      exact hkeys

/-! ## 7. Preservation for all threads, reachability, the target -/

/-- One step preserves the invariant at an UNTOUCHED thread: the
    result machine's thread state equals the old one, since `rufUpdateF`
    only replaces the acting thread. Proved by case split on `hs` with
    `subst_vars` (learning `M'`'s shape) and `rufUpdateF_noteq`.
    `hne` selects the untouched side and is consumed by the simp set. -/
theorem rufSchrittF_passt_anders (P : Programm D) (O : Orakel D) (passes : Nat)
    (M M' : RufMaschineF D) (f f' : Faden) (hne : f' ≠ f)
    (hs : RufSchrittF P O passes M f M') :
    M'.faeden f' = M.faeden f' := by
  cases hs <;> (subst_vars; simp_all [rufUpdateF_noteq])

/-- One step preserves the invariant for EVERY thread: the acting thread by
    the case split above, every other thread by `rufSchrittF_passt_anders`.
    Both `hact` (acting side) and `hoth` (other side) feed the conclusion;
    `hne` selects the side. -/
theorem rufSchrittF_passt (P : Programm D) (O : Orakel D) (passes : Nat)
    (M M' : RufMaschineF D) (f : Faden)
    (h : RufMaschinePasstF M)
    (hs : RufSchrittF P O passes M f M') :
    RufMaschinePasstF M' := by
  intro f'
  by_cases hne : f' = f
  · subst hne
    exact rufSchrittF_passt_acting P O passes M M' f' (h f') hs
  · rw [rufSchrittF_passt_anders P O passes M M' f f' hne hs]
    exact h f'

/-- The invariant holds at every reachable machine: induction on `h`, with
    the start case by `rufStartF_passt` and the step case by
    `rufSchrittF_passt`. Both `hbase` (start evidence) and `hstep` (step
    evidence) feed the conclusion. -/
theorem rufErreichbarF_passt (P : Programm D) (O : Orakel D) (passes : Nat)
    (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (M : RufMaschineF D)
    (h : RufErreichbarF P O passes (RufStartF P sp init) M) :
    RufMaschinePasstF M := by
  induction h with
  | start => exact rufStartF_passt P sp init
  | schritt M M' f hbase hs ih =>
      exact rufSchrittF_passt P O passes M M' f ih hs

/-- **Return fidelity.** Every `rueck` event in a reachable thread log has
    its matching `eintritt` event in the same log. Proved by induction on
    `h` through the invariant: `rufErreichbarF_passt` gives the well-formed
    log, `rufLogPasstF_gedeckt` reads the match off it. Every premise is
    used: `h` selects the reachable machine, `hmem` the log event. -/
theorem rufF_treu (P : Programm D) (O : Orakel D) (passes : Nat) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (M : RufMaschineF D)
    (h : RufErreichbarF P O passes (RufStartF P sp init) M) (f : Faden) :
    ∀ (g : D.Fn) (rho : Env D (D.params g)) (v : ErgVal D (D.erg g)) (s0 s1 : World D),
      RufEreignisF.rueck g rho v s0 s1 ∈ (M.faeden f).log →
      RufEreignisF.eintritt g rho s0 ∈ (M.faeden f).log := by
  have hmach := rufErreichbarF_passt P O passes sp init M h
  have hthread := hmach f
  unfold RufFadenPasstF at hthread
  have hged := rufLogPasstF_gedeckt (RufFadenSchluesselF (M.faeden f))
    (M.faeden f).log hthread
  unfold rufRueckGedecktF at hged
  intro g rho v s0 s1 hmem
  exact hged g rho v s0 s1 hmem

/-! ## 8. Non-trivial witness: one table, a writing leaf, call and return -/

/-- The witness declaration: one table `Unit` with one field of type
    `.int 0 5` (written by the leaf), one function id (`Bool`), no locks,
    no globals, no axioms. The table gives the run a real memory write:
    `assignSlot` changes slots by construction of `execStmt`. -/
def rufDF : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 5
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Bool
  sig := fun | true => 0 | false => 1
  sigNr := fun _ =>
    { params := [.int 0 5]
      erg := some (.int 0 6)
      gruende := 0
      haelt := []
      schreibt := fun _ => true
      gschreibt := fun e => nomatch e
      konsumiert := []
      produziert := [] }
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp only [Bool.false_eq_true] at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

/-- The witness function id: `false` is the CALLER (its body calls
    `true`); `true` is the CALLEE (the writing body). -/
def rufCallerF : rufDF.Fn := show rufDF.Fn from false

def rufIncF : rufDF.Fn := show rufDF.Fn from true

/-- The `erg` of each function, by computation (case on the id). -/
theorem rufDF_erg (f : rufDF.Fn) :
    rufDF.erg f = some (.int 0 6) := by
  cases f with
  | true => rfl
  | false => rfl

/-- The `params` of each function, by computation (case on the id). -/
theorem rufDF_params (f : rufDF.Fn) :
    rufDF.params f = [.int 0 5] := by
  cases f with
  | true => rfl
  | false => rfl

/-- The single parameter environment: the value 2 in `.int 0 5`. -/
def rufRhoF : Env rufDF (rufDF.params rufIncF) :=
  (rufDF_params rufIncF).symm ▸ (.cons ⟨2, by decide, by decide⟩ .nil :
    Env rufDF [.int 0 5])

/-- The single result value: 3 in `.int 0 6`. -/
def rufVF : ErgVal rufDF (rufDF.erg rufIncF) :=
  (rufDF_erg rufIncF).symm ▸ (⟨3, by decide, by decide⟩ : ErgVal rufDF (some (.int 0 6)))

/-- The callee body: one writing leaf (`assignSlot` to slot 0, the
    parameter value), then `ret` of the parameter. The leaf is a `Stmt`
    under the callee contract with `hw : schreibt = true` (the signature
    writes) and `hL : darf` (no guards needed, `braucht = []`). -/
def rufRumpfF : Endblock rufDF (vertragVon rufDF rufIncF) false
    (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) :=
  .cons (.assignSlot () ()
    (.widen (by decide) (by decide) (.lit 0) :
      Expr rufDF (rufDF.params rufIncF)
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (.index (rufDF.count ())))
    ((.widen (by decide) (by decide) (.var .here) :
      Expr rufDF (rufDF.params rufIncF)
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (.int 0 5))) rfl (fun w => nomatch w))
    (.ret (.val ((.widen (by decide) (by decide) (.var .here) :
      Expr rufDF (rufDF.params rufIncF)
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (.int 0 6)))) (by decide))

/-- The call fits: callee writes nothing beyond the caller's rights (both
    write the one table), consumes nothing, holds nothing. -/
theorem rufHpF : RufPasst rufDF (vertragVon rufDF rufCallerF)
    (rufDF.signatur rufIncF) ([] : List (Res rufDF)) where
  hw := fun _ _ => rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], List.Sublist.slnil⟩
  hh := fun L => nomatch L

/-- The call arguments: the single parameter variable. -/
def rufArgsF : Args rufDF [Ty.int 0 5] [] (rufDF.params rufIncF) :=
  (rufDF_params rufCallerF).symm ▸ Args.cons (.var .here) Args.nil

/-- The caller body: a single `call` to the callee, returning to the empty
    end. Note the caller contract is `vertragVon rufDF rufCallerF` (same
    signature shape, so `params` coincide by `rufDF_params`). -/
def rufCallerRumpfF : Endblock rufDF (vertragVon rufDF rufCallerF) false
    (rufDF.params rufCallerF)
    (Signatur.anfang rufDF (rufDF.signatur rufCallerF)) :=
  (rufDF_params rufCallerF).symm ▸
    (.cons (.call rufIncF rufArgsF rufHpF rfl)
      (.ret (.val ((.widen (by decide) (by decide) (.var .here) :
        Expr rufDF (rufDF.params rufIncF) [] (.int 0 6)))) (by decide)) :
      Endblock rufDF (vertragVon rufDF rufCallerF) false
        (rufDF.params rufIncF) (nach rufDF rufIncF []))

/-- The program: the caller calls, the callee writes; contracts trivial
    (`wahr`). `requires`/`ensures` play no role in the witness -- only the
    memory move and the log events matter. -/
def rufPF : Programm rufDF where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf
    | true => rufRumpfF
    | false => rufCallerRumpfF

/-- The witness oracle: no axioms, no registers, nothing visible. -/
def rufOF : Orakel rufDF where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun g => nomatch g

/-- The empty world over the witness declaration. -/
def rufWeltF : World rufDF :=
  ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => Empty.elim g, []⟩

/-- Named pieces of the witness body: the writing leaf and the `ret`
    tail, so the `blatt` step can name them. -/
def leafSF : Stmt rufDF (vertragVon rufDF rufIncF) false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) :=
  .assignSlot () ()
    (.widen (by decide) (by decide) (.lit 0) :
      Expr rufDF (rufDF.params rufIncF)
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (.index (rufDF.count ())))
    ((.widen (by decide) (by decide) (.var .here) :
      Expr rufDF (rufDF.params rufIncF)
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (.int 0 5))) rfl (fun w => nomatch w)

def restF : Endblock rufDF (vertragVon rufDF rufIncF) false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) :=
  (.ret (.val ((.widen (by decide) (by decide) (.var .here) :
      Expr rufDF (rufDF.params rufIncF)
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (.int 0 6)))) (by decide))

theorem rufRumpfF_eq : rufRumpfF = Endblock.cons leafSF restF := rfl

/-- The leaf is a leaf. -/
theorem leafSF_blatt : leafSF.istBlatt = true := rfl

/-- The leaf writes: the outcome is `.ok` with a changed world and the same
    environment. The world changes because `assignSlot` stores the parameter
    value 2 at slot 0 (was 0); the trace gains the write event. -/
theorem leafSF_mem (σ' : World rufDF) (ρ' : Env rufDF (rufDF.params rufIncF))
    (h : (execStmt (V := vertragVon rufDF rufIncF) rufOF 0 keinRuf leafSF
      rufWeltF rufRhoF) = Ausgang.ok σ' ρ') :
    σ'.slots () 0 () = (⟨2, by decide, by decide⟩ : Wert rufDF (.int 0 5)) ∧
      ρ' = rufRhoF := by
  have hrfl : (execStmt (V := vertragVon rufDF rufIncF) rufOF 0 keinRuf leafSF
      rufWeltF rufRhoF) =
      Ausgang.ok (D := rufDF) (V := vertragVon rufDF rufIncF) _ rufRhoF := rfl
  rw [hrfl] at h
  cases h
  refine ⟨rfl, rfl⟩

/-- Start memory: slot 0 holds 0 (the leaf will write 2). -/
def spF : Speicher rufDF :=
  ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => Empty.elim g⟩

/-- The caller-side rho: the entry value 2, transported to the caller
    params (same shape, `rufDF_params`). -/
def rhoCallerF : Env rufDF (rufDF.params rufCallerF) :=
  (rufDF_params rufCallerF).symm ▸ rufRhoF

def initF : Faden → Σ f : rufDF.Fn, Env rufDF (rufDF.params f) :=
  fun _ => ⟨rufCallerF, rhoCallerF⟩

theorem initF_rho : initF 0 =
    (⟨rufCallerF, rhoCallerF⟩ :
      Σ f : rufDF.Fn, Env rufDF (rufDF.params f)) := rfl

def M0F : RufMaschineF rufDF := RufStartF rufPF spF initF

/-- The start head is the caller body with the entry environment.
    Proved by unfolding the start definition and the init function
    (`rfl` fails: the `match` on `initF 0` needs the equation). -/
theorem M0F_kopf :
    (M0F.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufCallerF,
     Signatur.anfang rufDF (rufDF.signatur rufCallerF),
     rhoCallerF, rufCallerRumpfF⟩ := by
  have hstart : (RufStartF (D := rufDF) rufPF spF initF).faeden 0 =
      (match initF 0 with
      | ⟨g', rho'⟩ =>
        (⟨[], (⟨g', rho', spF.welt [],
          ⟨false, rufDF.params g', Signatur.anfang rufDF (rufDF.signatur g'),
           rho', rufPF.rumpf g'⟩⟩ : RufRahmenF rufDF),
         [], [RufEreignisF.eintritt g' rho' (spF.welt [])]⟩ :
          RufFadenF rufDF)) := rfl
  have hif : initF 0 = (⟨rufCallerF, rhoCallerF⟩ :
      Σ f : rufDF.Fn, Env rufDF (rufDF.params f)) := by
    simp only [initF]
  have hM : M0F.faeden 0 =
      (⟨[], (⟨rufCallerF, rhoCallerF, spF.welt [],
        ⟨false, rufDF.params rufCallerF,
         Signatur.anfang rufDF (rufDF.signatur rufCallerF),
         rhoCallerF, rufPF.rumpf rufCallerF⟩⟩ : RufRahmenF rufDF),
       [], [RufEreignisF.eintritt rufCallerF rhoCallerF (spF.welt [])]⟩ :
        RufFadenF rufDF) := by
    simp only [M0F]
    rw [hstart, hif]
  have hrumpf : rufPF.rumpf rufCallerF = rufCallerRumpfF := rfl
  rw [hM, hrumpf]

/-- The start head function is the caller. -/
theorem M0F_fun : (M0F.faeden 0).kopf.f = rufCallerF := rfl

/-- Caller params unfold to the single int (needed to align `rufArgsF`). -/
theorem callerParamsF : rufDF.params rufCallerF = [.int 0 5] :=
  rufDF_params rufCallerF


end Gabbro.Grammatik
