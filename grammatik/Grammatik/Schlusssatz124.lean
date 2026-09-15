/-
  File:      Grammatik/Schlusssatz124.lean
  Subject:   THE CLOSING THEOREM, STAGE (b), FOR `beispiele/124-two-threads-private.gab`
             (plan `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §7):
             `schlusssatz_124`, and its witness with a contended lock.

  THE EMITTED C (`target/debug/gabbro emit beispiele/124-two-threads-private.gab`,
  binary built from this tree on 2026-09-15), function bodies:

      static void setze(uint32_t x) {
          konto_speicher.slots[0].stand = x;
          konto_speicher.slots[1].stand = x;
      }
      static uint32_t pruefeA(void) {
          return privA_speicher.slots[0].stand;
      }
      static void hauptA(void) {
          privA_speicher.slots[0].stand = 7;
          privA_speicher.slots[1].stand = 7;
          L_nimm();
          {
              setze(30);
          }
          L_gib();
          (void)pruefeA();
      }
      static void hauptB(void) {
          privB_speicher.slots[0].stand = 5;
          L_nimm();
          {
              setze(70);
          }
          L_gib();
      }

  with `typedef struct { uint32_t stand; } T_slot; typedef struct { T_slot
  slots[NSLOTS]; } T; static T T_speicher;` for `T` in `konto`, `privA`,
  `privB`, `NSLOTS = 2`, and `void L_nimm(void); void L_gib(void);` -- the
  runtime's lock primitive, not emitted. No thread is created by the emitted
  code: the runtime starts `hauptA` and `hauptB` (`concurrent { hauptA,
  hauptB }`), which is the premise `FadenStartC`.

  THE ENCODING AS DATA (`c124`): function `0` is `setze` (parameter `x` is
  local `0`), `1` `pruefeA`, `2` `hauptA`, `3` `hauptB`; objects `tab 0`,
  `tab 1`, `tab 2` are `konto_speicher`, `privA_speicher`, `privB_speicher`
  (layout `natLay 2 [uint32_t]`: record size 4, field at 0);
  `T_speicher.slots[k].stand` is `slotA (addr (tab T)) k 2 4 0`; foreign
  function `0` is `L_nimm`, `1` is `L_gib`; the braces `{ setze(30); }` are
  the call itself; `(void)pruefeA();` is the call with its answer dropped.
-/
import Grammatik.CNebenlaeufig
import Grammatik.Korpus124

namespace Gabbro.Grammatik

namespace K124

open Zielsatz

/-! ## 1. The emitted C, as data -/

/-- `uint32_t`. -/
def u32 : CTy := .int false .w32

/-- `T_speicher.slots[k].stand` as an address: record `k` of 2, 4 bytes
    apart, field at offset 0, in object `tab t`. -/
def cSlot (t k : Nat) : CX := .slotA (.addr (.tab t)) (.lit k) 2 4 0

def cSetzeBody : CS := .seq (.store (cSlot 0 0) u32 (.var 0)) (.store (cSlot 0 1) u32 (.var 0))
def cPruefeBody : CS := .ret (some (u32, .ld (cSlot 1 0) u32))
def cA0 : CS := .store (cSlot 1 0) u32 (.lit 7)
def cA1 : CS := .store (cSlot 1 1) u32 (.lit 7)
def cNimm : CS := .ext 0 [] none
def cGib : CS := .ext 1 [] none
def cSetzeA : CS := .call 0 [.lit 30] none
def cPruefe : CS := .call 1 [] none
def cRestA4 : CS := .seq cGib cPruefe
def cRestA3 : CS := .seq cSetzeA cRestA4
def cRestA2 : CS := .seq cNimm cRestA3
def cRestA1 : CS := .seq cA1 cRestA2
def cHauptA : CS := .seq cA0 cRestA1
def cB0 : CS := .store (cSlot 2 0) u32 (.lit 5)
def cSetzeB : CS := .call 0 [.lit 70] none
def cRestB2 : CS := .seq cSetzeB cGib
def cRestB1 : CS := .seq cNimm cRestB2
def cHauptB : CS := .seq cB0 cRestB1

/-- The functions of the unit. -/
def c124Prog : CProg
  | 0 => some ⟨[(0, u32)], [], cSetzeBody⟩
  | 1 => some ⟨[], [], cPruefeBody⟩
  | 2 => some ⟨[], [], cHauptA⟩
  | 3 => some ⟨[], [], cHauptB⟩
  | _ => none

/-- The objects of the unit: the three table objects, nothing else. -/
def c124Lay : CLayout := fun b =>
  match b with
  | .tab 0 => some ⟨kontoLay, .plain, 0⟩
  | .tab 1 => some ⟨kontoLay, .plain, 0⟩
  | .tab 2 => some ⟨kontoLay, .plain, 0⟩
  | _ => none

/-- `L_nimm` is foreign function 0, `L_gib` foreign function 1, both of lock 0. -/
def c124Sperre : Nat → Option SperrOp
  | 0 => some (.nimm 0)
  | 1 => some (.gib 0)
  | _ => none

/-- **The emitted unit of `beispiele/124`**, call depth 1 (`setze` and
    `pruefeA` call nothing). -/
def c124 : CEinheit := ⟨c124Lay, fun _ _ _ => 0, c124Prog, c124Sperre, 1⟩

/-- The unit is in the direct fragment: every footprint below covers every
    access (`ev_zform_blk`). -/
theorem c124_direkt : c124.direkt [0, 1, 2, 3] = true := by decide

/-- The declared initial memory of the C: static storage is zero
    (C11 6.7.9p10), every object alive, nothing observed. -/
def st0 : CSt := ⟨fun _ _ => .int 0, fun _ => true, []⟩

/-! ## 2. The emitter's layout of the G program -/

abbrev DR : Deklaration := kD.mitRuhe

def kTnr : KTab → Nat
  | .konto => 0
  | .privA => 1
  | .privB => 2

/-- `konto`, `privA`, `privB` are objects `tab 0`, `tab 1`, `tab 2`; `stand`
    is field 0 at `uint32_t` (which holds `0 .. 100`); no globals. -/
def kEL : EmitLay DR where
  lay := c124Lay
  tnr := kTnr
  tnr_inj := fun t t' h => by
    cases t <;> cases t' <;> first | rfl | exact absurd h (by decide)
  trec := fun _ => kontoLay
  lay_tab := fun t => by cases t <;> rfl
  trec_wf := fun _ => by decide
  trec_count := fun _ => rfl
  fnr := fun _ _ => 0
  fnr_lt := fun _ _ => by decide
  fnr_inj := fun _ f f' _ => by cases f; cases f'; rfl
  fnr_fits := fun _ _ => rfl
  gnr := fun g => nomatch g
  gnr_inj := fun g => nomatch g
  gty := fun g => nomatch g
  lay_glob := fun g => nomatch g
  gty_fits := fun g => nomatch g

/-- The G lock `L` is lock `0` of the runtime. -/
def lnr : DR.Lock → Nat := fun _ => 0

/-- The lock `L` of the G program. -/
def lL : DR.Lock := ()

/-! ## 3. The G states of the two threads, and the G segments -/

/-- The entry world of every root frame: the start memory, empty trace. -/
def s0R : World DR := (speicherR kSp).welt []

/-- The residues of a `hauptA` thread, in the order the run reaches them. -/
def restA : Nat → Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res DR),
    Env DR Γ × GRest DR (vertragVon DR (some kHauptA)) l Γ Λ
  | 0 => ⟨false, DR.params (some kHauptA), Signatur.anfang DR (DR.signatur (some kHauptA)), .nil,
      .ende (kP.mitRuhe.rumpf (some kHauptA))⟩
  | 1 => ⟨false, [], [], .nil, .ende (ruEnd (.cons kA1 (.cons kLocksA kRestA)))⟩
  | 2 => ⟨false, [], [], .nil, .ende (ruEnd (.cons kLocksA kRestA))⟩
  | 3 => ⟨false, [], [Res.held lL], .nil,
      .dann (ruB (.cons kRufA .nil)) (.frei lL (.dann .nil (.ende (ruEnd kRestA))))⟩
  | 4 => ⟨false, [], [Res.held lL], .nil, .frei lL (.dann .nil (.ende (ruEnd kRestA)))⟩
  | 5 => ⟨false, [], [], .nil, .ende (ruEnd kRestA)⟩
  | _ => ⟨false, [], [], .nil,
      .ende (ruEnd (V := vertragVon kD kHauptA) (l := false) (Γ := []) (Λ := [])
        (.ret .keine List.Perm.nil))⟩

def frA (j : Nat) : RufRahmenG DR := ⟨some kHauptA, .nil, s0R, restA j⟩

/-- The residues of a `hauptB` thread. -/
def restB : Nat → Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res DR),
    Env DR Γ × GRest DR (vertragVon DR (some kHauptB)) l Γ Λ
  | 0 => ⟨false, DR.params (some kHauptB), Signatur.anfang DR (DR.signatur (some kHauptB)), .nil,
      .ende (kP.mitRuhe.rumpf (some kHauptB))⟩
  | 1 => ⟨false, [], [], .nil, .ende (ruEnd (.cons kLocksB (.ret .keine List.Perm.nil)))⟩
  | 2 => ⟨false, [], [Res.held lL], .nil,
      .dann (ruB (.cons kRufB .nil)) (.frei lL (.dann .nil (.ende (ruEnd (V := vertragVon kD kHauptB)
        (l := false) (Γ := []) (Λ := []) (.ret .keine List.Perm.nil)))))⟩
  | 3 => ⟨false, [], [Res.held lL], .nil, .frei lL (.dann .nil (.ende (ruEnd
      (V := vertragVon kD kHauptB) (l := false) (Γ := []) (Λ := []) (.ret .keine List.Perm.nil))))⟩
  | _ => ⟨false, [], [], .nil,
      .ende (ruEnd (V := vertragVon kD kHauptB) (l := false) (Γ := []) (Λ := [])
        (.ret .keine List.Perm.nil))⟩

def frB (j : Nat) : RufRahmenG DR := ⟨some kHauptB, .nil, s0R, restB j⟩

section G

variable {passes : Nat}

abbrev PR : Programm DR := kP.mitRuhe
abbrev OR : Orakel DR := kO.mitRuhe

/-- A step that keeps the held locks of `t` neither releases nor acquires. -/
theorem kein_wechsel {M M' : RufMaschineG DR} {t : Faden}
    (h : offen (M'.faeden t).spur = offen (M.faeden t).spur) (L : DR.Lock) :
    ¬ GibtFrei M M' t L ∧ ¬ NimmtAn M M' t L :=
  ⟨fun hg => hg.2.1 (by rw [h]; exact hg.1), fun hn => hn.1 (by rw [← h]; exact hn.2.1)⟩

/-- An access event the step prepended is an access of the step. -/
theorem zugriff_ev {M M' : RufMaschineG DR} {t : Faden} {X : List (Ereignis DR)}
    (e : (M'.faeden t).spur = X ++ (M.faeden t).spur) {c : DR.Tab ⊕ DR.Glob} {w : Bool}
    (h : (c, w) ∈ X.filterMap zugriffVon) : (c, w) ∈ zugriffe M M' t := by
  rw [zugriffe_ereignisse, ereignisse_eq e]
  exact h

theorem heldIn_leer (o : List DR.Lock) : HeldIn ([] : List (Res DR)) o := fun _ h => nomatch h

theorem heldIn_L {o : List DR.Lock} (h : o = [lL]) : HeldIn [Res.held lL] o := by
  intro L _
  cases L
  rw [h]
  exact List.mem_singleton_self _

/-- **A leaf store of a root frame**: `T.slots[i].stand = e;` as one G step.
    The trace gains access events only (among them the write of `T`), and the
    memory is the store. -/
theorem gBlatt (fn : kD.Fn) (rho : Env DR (DR.params (some fn))) (tb : KTab)
    (i : Expr kD [] [] (.index 2)) (e : Expr kD [] [] (.int 0 100))
    (hw : (vertragVon kD fn).schreibt tb = true) (hL : darf kD tb [])
    (rest : Endblock kD (vertragVon kD fn) false [] [])
    (M : RufMaschineG DR) (t : Faden) (sp : List (Ereignis DR)) (log : List (RufEreignisF DR))
    (hz : M.faeden t = ⟨[], ⟨some fn, rho, s0R, ⟨false, [], [], .nil,
        .ende (ruEnd (.cons (.assignSlot tb () i e hw hL) rest))⟩⟩, sp, log⟩) :
    ∃ M1, RufSchrittG PR OR passes M t M1 ∧
      (∃ sp1, M1.faeden t = ⟨[], ⟨some fn, rho, s0R, ⟨false, [], [], .nil, .ende (ruEnd rest)⟩⟩,
        sp1, log⟩ ∧ offen sp1 = offen sp) ∧
      (Sum.inl tb, true) ∈ zugriffe M M1 t ∧
      M1.speicher = ((M.speicher.welt []).storeSlot tb
        (eval ((M.weltVon t).lese (List.map resR []) ((ruE i).orte ++ (ruE e).orte)) (ruE i)
          ((M.weltVon t).lese (List.map resR []) ((ruE i).orte ++ (ruE e).orte)) Env.nil).n ()
        (eval ((M.weltVon t).lese (List.map resR []) ((ruE i).orte ++ (ruE e).orte)) (ruE e)
          ((M.weltVon t).lese (List.map resR []) ((ruE i).orte ++ (ruE e).orte)) Env.nil)).speicher := by
  have herw := (Erw.lese (M.weltVon t) (List.map resR []) ((ruE i).orte ++ (ruE e).orte)).trans
    (Erw.schreibSlot _ tb (List.map resR []) (eval ((M.weltVon t).lese (List.map resR [])
      ((ruE i).orte ++ (ruE e).orte)) (ruE i) ((M.weltVon t).lese (List.map resR [])
      ((ruE i).orte ++ (ruE e).orte)) Env.nil).n () (eval ((M.weltVon t).lese (List.map resR [])
      ((ruE i).orte ++ (ruE e).orte)) (ruE e) ((M.weltVon t).lese (List.map resR [])
      ((ruE i).orte ++ (ruE e).orte)) Env.nil))
  obtain ⟨M1, s1, hZ1⟩ := w_blatt (P := PR) (O := OR) (passes := passes) hz
    (ruS (V := vertragVon kD fn) (l := false) (Stmt.assignSlot (V := vertragVon kD fn) (l := false)
      tb () i e hw hL)) (ruEnd rest) .nil rfl rfl (heldIn_leer _) _ _
    (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _) herw
  refine ⟨M1, s1, ⟨_, hZ1.1, ?_⟩, ?_, ?_⟩
  · have ho := herw.offen
    have hs : (M.weltVon t).spur = sp := by
      show (M.faeden t).spur = sp
      rw [hz]
    rw [hs] at ho
    exact ho
  · refine zugriff_ev (X := _ :: leseEv (M.weltVon t) (List.map resR []) ((ruE i).orte ++ (ruE e).orte))
      (by rw [hZ1.1]; rfl) ?_
    rw [List.filterMap_cons]
    exact List.mem_cons_self
  · rw [hZ1.2]
    rfl


/-- The pieces of `setze`'s body. -/
def kS0 : Stmt kD (vertragVon kD kSetze) false [.int 0 100] kL kL :=
  .assignSlot KTab.konto () kI0 (.var .hier) rfl kDarfK
def kS1 : Stmt kD (vertragVon kD kSetze) false [.int 0 100] kL kL :=
  .assignSlot KTab.konto () kI1 (.var .hier) rfl kDarfK
def kSRet : Endblock kD (vertragVon kD kSetze) false [.int 0 100] kL := .ret .keine (by rfl)

theorem kRumpfSetze_teile : kRumpfSetze = .cons kS0 (.cons kS1 kSRet) := rfl

/-- Nothing is held outside a lock: the rank side condition of `locks L`. -/
theorem kHr : ∀ M, Res.held M ∈ ([] : List (Res kD)) → kD.rang M < kD.rang () := fun _ h => nomatch h

/-- The start residue of a `hauptA` thread IS the leaf form `gBlatt` takes. -/
theorem frA0_form (M : RufMaschineG DR) (t : Faden) (sp : List (Ereignis DR))
    (log : List (RufEreignisF DR)) (hz : M.faeden t = ⟨[], frA 0, sp, log⟩) :
    M.faeden t = ⟨[], ⟨some kHauptA, .nil, s0R, ⟨false, [], [], .nil,
      .ende (ruEnd (.cons kA0 (.cons kA1 (.cons kLocksA kRestA))))⟩⟩, sp, log⟩ := hz

theorem frB0_form (M : RufMaschineG DR) (t : Faden) (sp : List (Ereignis DR))
    (log : List (RufEreignisF DR)) (hz : M.faeden t = ⟨[], frB 0, sp, log⟩) :
    M.faeden t = ⟨[], ⟨some kHauptB, .nil, s0R, ⟨false, [], [], .nil,
      .ende (ruEnd (.cons kB0 (.cons kLocksB (.ret .keine List.Perm.nil))))⟩⟩, sp, log⟩ := hz

/-- **The acquire**: `locks L { … }` at the head of a root frame, unfolded and
    taken -- two G steps; the second takes `L`. -/
theorem gNimm (fn : kD.Fn) (rho : Env DR (DR.params (some fn)))
    (body : Block kD (vertragVon kD fn) false [] kL kL)
    (rest : Endblock kD (vertragVon kD fn) false [] [])
    (M : RufMaschineG DR) (t : Faden) (sp : List (Ereignis DR)) (log : List (RufEreignisF DR))
    (hz : M.faeden t = ⟨[], ⟨some fn, rho, s0R, ⟨false, [], [], .nil,
        .ende (ruEnd (.cons (Stmt.locks () kHr body) rest))⟩⟩, sp, log⟩)
    (hoff : offen sp = []) (hfrei : RufFreiG M t lL) :
    ∃ M1 M2, RufSchrittG PR OR passes M t M1 ∧ RufSchrittG PR OR passes M1 t M2 ∧
      (M1.faeden t).spur = sp ∧
      (∃ sp2, M2.faeden t = ⟨[], ⟨some fn, rho, s0R, ⟨false, [], [Res.held lL], .nil,
        .dann (ruB body) (.frei lL (.dann .nil (.ende (ruEnd rest))))⟩⟩, sp2, log⟩ ∧
        offen sp2 = [lL]) ∧
      M1.speicher = M.speicher ∧ M2.speicher = M.speicher := by
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := PR) (O := OR) (passes := passes) hz
    (ruS (V := vertragVon kD fn) (l := false)
      (Stmt.locks (V := vertragVon kD fn) (l := false) () kHr body))
    (ruEnd rest) .nil rfl rfl
  have hs1 : (M1.faeden t).spur = sp := by rw [hZ1.1]; show (M.faeden t).spur = sp; rw [hz]
  have hfrei1 : RufFreiG M1 t lL := fun u hu => by
    rw [rufSchrittG_fremd s1 u hu]; exact hfrei u hu
  obtain ⟨M2, s2, hZ2⟩ := w_locks (P := PR) (O := OR) (passes := passes) hZ1.1 () _ (ruB body)
    .nil (.ende (ruEnd rest)) .nil rfl
    (fun L => by
      have : offen (M.weltVon t).spur = [] := by
        show offen (M.faeden t).spur = []; rw [hz]; exact hoff
      rw [this]; simp) hfrei1
  refine ⟨M1, M2, s1, s2, hs1, ⟨_, hZ2.1, ?_⟩, hZ1.2, ?_⟩
  · show lL :: offen (M1.weltVon t).spur = [lL]
    have : (M1.weltVon t).spur = sp := hs1
    rw [this, hoff]
  · rw [hZ2.2]
    show M1.speicher = M.speicher
    rw [hZ1.2]
    rfl

/-- **The critical section's call** `setze(e)`: call, both leaf writes of
    `konto`, return, and the empty rest -- five G steps of one thread, `L`
    held throughout. -/
theorem gSetze (fn : kD.Fn) (rho : Env DR (DR.params (some fn)))
    (hp : RufPasst kD (vertragVon kD fn) (kD.signatur kSetze) kL)
    (e : Expr kD [] kL (.int 0 100))
    (k : GRest DR (vertragVon DR (some fn)) false [] [])
    (M : RufMaschineG DR) (t : Faden) (sp : List (Ereignis DR)) (log : List (RufEreignisF DR))
    (hz : M.faeden t = ⟨[], ⟨some fn, rho, s0R, ⟨false, [], [Res.held lL], .nil,
        .dann (ruB (.cons (Stmt.call (V := vertragVon kD fn) (l := false) kSetze (.cons e .nil) hp rfl)
          .nil)) (.frei lL k)⟩⟩, sp, log⟩)
    (hoff : offen sp = [lL]) :
    ∃ M1 M2 M3 M4 M5, RufSchrittG PR OR passes M t M1 ∧ RufSchrittG PR OR passes M1 t M2 ∧
      RufSchrittG PR OR passes M2 t M3 ∧ RufSchrittG PR OR passes M3 t M4 ∧
      RufSchrittG PR OR passes M4 t M5 ∧
      offen (M1.faeden t).spur = [lL] ∧ offen (M2.faeden t).spur = [lL] ∧
      offen (M3.faeden t).spur = [lL] ∧ offen (M4.faeden t).spur = [lL] ∧
      (∃ sp5 log5, M5.faeden t = ⟨[], ⟨some fn, rho, s0R, ⟨false, [], [Res.held lL], .nil,
        .frei lL k⟩⟩, sp5, log5⟩ ∧ offen sp5 = [lL]) ∧
      (Sum.inl KTab.konto, true) ∈ zugriffe M1 M2 t ∧
      M5.speicher.slots = (((M.speicher.welt []).storeSlot KTab.konto 0 ()
        (eval ((M.weltVon t).lese [Res.held lL] (ruA (.cons e .nil)).orte) (ruE e)
          ((M.weltVon t).lese [Res.held lL] (ruA (.cons e .nil)).orte) Env.nil)).storeSlot
        KTab.konto 1 ()
        (eval ((M.weltVon t).lese [Res.held lL] (ruA (.cons e .nil)).orte) (ruE e)
          ((M.weltVon t).lese [Res.held lL] (ruA (.cons e .nil)).orte) Env.nil)).slots := by
  have hoff0 : offen (M.weltVon t).spur = [lL] := by
    show offen (M.faeden t).spur = [lL]; rw [hz]; exact hoff
  obtain ⟨M1, s1, hZ1⟩ := w_rufDann (P := PR) (O := OR) (passes := passes) hz (some kSetze)
    (ruA (.cons e .nil)) (rufPasstR hp) rfl .nil (.frei lL k) .nil rfl (heldIn_L hoff)
  have ho1 : offen (M1.faeden t).spur = [lL] := by
    rw [hZ1.1]; exact ((Erw.lese _ _ _).offen).trans hoff0
  obtain ⟨M2, s2, hZ2⟩ := w_blatt (P := PR) (O := OR) (passes := passes) hZ1.1
    (ruS kS0) (ruEnd (.cons kS1 kSRet))
    _ rfl rfl (heldIn_L (by have h := ho1; rw [hZ1.1] at h; exact h)) _ _
    (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _) ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have ho2 : offen (M2.faeden t).spur = [lL] := by
    rw [hZ2.1]; exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans ho1
  obtain ⟨M3, s3, hZ3⟩ := w_blatt (P := PR) (O := OR) (passes := passes) hZ2.1
    (ruS kS1) (ruEnd kSRet)
    _ rfl rfl (heldIn_L (by have h := ho2; rw [hZ2.1] at h; exact h)) _ _
    (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _) ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have ho3 : offen (M3.faeden t).spur = [lL] := by
    rw [hZ3.1]; exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans ho2
  obtain ⟨M4, s4, hG4⟩ := w_rueckP (P := PR) (O := OR) (passes := passes) hZ3.1 _ [] rfl
    (PopArt.wie rfl) .keine _ _ rfl (heldIn_L (by have h := ho3; rw [hZ3.1] at h; exact h))
  have ho4 : offen (M4.faeden t).spur = [lL] := by
    rw [hG4.1]; exact ((Erw.lese _ _ _).offen).trans ho3
  obtain ⟨M5, s5, hZ5⟩ := w_dannLeer (P := PR) (O := OR) (passes := passes) hG4.1 (.frei lL k) .nil rfl
  refine ⟨M1, M2, M3, M4, M5, s1, s2, s3, s4, s5, ho1, ho2, ho3, ho4,
    ⟨_, _, hZ5.1, by show offen (M4.faeden t).spur = [lL]; exact ho4⟩, ?_, ?_⟩
  · refine zugriff_ev (X := _ :: leseEv (M1.weltVon t) _ _) (by rw [hZ2.1]; rfl) ?_
    rw [List.filterMap_cons]
    exact List.mem_cons_self
  · have e5 : M5.speicher = M4.speicher := hZ5.2
    have e4 : M4.speicher = M3.speicher := hG4.2
    have e3 := hZ3.2
    have e2 := hZ2.2
    have e1 : M1.speicher = M.speicher := hZ1.2
    rw [e5, e4, e3]
    unfold RufMaschineG.weltVon
    rw [e2]
    unfold RufMaschineG.weltVon
    rw [e1]
    rfl


/-- **The release**: `L` given back at the end of the `locks` body, and the
    empty rest -- two G steps; the first releases `L`. -/
theorem gGib (fn : kD.Fn) (rho : Env DR (DR.params (some fn)))
    (rest : Endblock kD (vertragVon kD fn) false [] [])
    (M : RufMaschineG DR) (t : Faden) (sp : List (Ereignis DR)) (log : List (RufEreignisF DR))
    (hz : M.faeden t = ⟨[], ⟨some fn, rho, s0R, ⟨false, [], [Res.held lL], .nil,
        .frei lL (.dann .nil (.ende (ruEnd rest)))⟩⟩, sp, log⟩)
    (hoff : offen sp = [lL]) :
    ∃ M1 M2, RufSchrittG PR OR passes M t M1 ∧ RufSchrittG PR OR passes M1 t M2 ∧
      offen (M1.faeden t).spur = [] ∧
      (∃ sp2, M2.faeden t = ⟨[], ⟨some fn, rho, s0R, ⟨false, [], [], .nil,
        .ende (ruEnd rest)⟩⟩, sp2, log⟩ ∧ offen sp2 = []) ∧
      M1.speicher = M.speicher ∧ M2.speicher = M.speicher := by
  obtain ⟨M1, s1, hZ1⟩ := w_freiGib (P := PR) (O := OR) (passes := passes) hz lL
    (.dann .nil (.ende (ruEnd rest))) .nil rfl
  have ho1 : offen (M1.faeden t).spur = [] := by
    rw [hZ1.1]
    show (offen (M.faeden t).spur).erase lL = []
    rw [hz]
    show (offen sp).erase lL = []
    rw [hoff]
    rfl
  obtain ⟨M2, s2, hZ2⟩ := w_dannLeer (P := PR) (O := OR) (passes := passes) hZ1.1
    (.ende (ruEnd rest)) .nil rfl
  refine ⟨M1, M2, s1, s2, ho1, ⟨_, hZ2.1, by show offen (M1.faeden t).spur = []; exact ho1⟩,
    ?_, ?_⟩
  · rw [hZ1.2]; rfl
  · rw [hZ2.2]
    show M1.speicher = M.speicher
    rw [hZ1.2]; rfl

/-- **`pruefeA();`**: the call, and the callee's `return privA.slots[0].stand;`
    popping back -- two G steps; the second reads `privA`. -/
theorem gPruefe (M : RufMaschineG DR) (t : Faden) (sp : List (Ereignis DR))
    (log : List (RufEreignisF DR))
    (hz : M.faeden t = ⟨[], frA 5, sp, log⟩) (hoff : offen sp = []) :
    ∃ M1 M2, RufSchrittG PR OR passes M t M1 ∧ RufSchrittG PR OR passes M1 t M2 ∧
      offen (M1.faeden t).spur = [] ∧
      (∃ sp2 log2, M2.faeden t = ⟨[], frA 6, sp2, log2⟩ ∧ offen sp2 = []) ∧
      (Sum.inl KTab.privA, false) ∈ zugriffe M1 M2 t ∧
      M1.speicher = M.speicher ∧ M2.speicher = M.speicher := by
  have hoff0 : offen (M.weltVon t).spur = [] := by
    show offen (M.faeden t).spur = []; rw [hz]; exact hoff
  obtain ⟨M1, s1, hZ1⟩ := w_rufEnde (P := PR) (O := OR) (passes := passes) hz (some kPruefeA)
    (ruA .nil) (rufPasstR kHpPruefe) rfl (ruEnd (V := vertragVon kD kHauptA) (l := false) (Γ := [])
      (Λ := []) (.ret .keine List.Perm.nil)) .nil rfl (heldIn_leer _)
  have ho1 : offen (M1.faeden t).spur = [] := by
    rw [hZ1.1]; exact ((Erw.lese _ _ _).offen).trans hoff0
  obtain ⟨M2, s2, hG2⟩ := w_rueckP (P := PR) (O := OR) (passes := passes) hZ1.1 _ [] rfl
    (PopArt.wie rfl) _ _ _ rfl (heldIn_leer _)
  refine ⟨M1, M2, s1, s2, ho1, ⟨_, _, hG2.1, ?_⟩, ?_, hZ1.2, ?_⟩
  · exact ((Erw.lese _ _ _).offen).trans ho1
  · refine zugriff_ev (X := leseEv (M1.weltVon t) _ _) (by rw [hG2.1]; rfl) ?_
    rw [leseEv]
    exact List.mem_cons_self
  · rw [hG2.2]
    show M1.speicher = M.speicher
    rw [hZ1.2]; rfl

end G


/-! ## 4. The C blocks, from a related state -/

section C

/-- `corrW` reads only the slots (there are no globals). -/
theorem corrW_von {σ₁ σ₂ : World DR} {st : CSt} (h : corrW kEL σ₁ st)
    (hs : σ₁.slots = σ₂.slots) : corrW kEL σ₂ st :=
  ⟨fun t ht => by rw [← hs]; exact h.1 t ht, fun g => nomatch g⟩

/-- Entering and leaving a frame without stack objects keeps the relation
    (they touch only stack objects). -/
theorem corrW_enter {σ : World DR} {st : CSt} (h : corrW kEL σ st) (fr : Nat) (xs : List Nat) :
    corrW kEL σ (enterFrame st fr xs) := h

theorem corrW_leave {σ : World DR} {st : CSt} (h : corrW kEL σ st) (fr : Nat) :
    corrW kEL σ (leaveFrame st fr) := h

theorem conv_u32 {v : Int} (h : 0 ≤ v ∧ v ≤ 100) : convV u32 (.int v) = some (.int v) := by
  show (match conv ⟨false, .w32⟩ v with
    | some b => some (CVal.int b)
    | none => none) = _
  rw [conv_id (by show cLo false .w32 ≤ v ∧ v ≤ cHi false .w32; simp [cLo, cHi, CWidth.bits]; omega)]

theorem ev_ld {L : CLayout} {orc : DevOrc} {fr : Nat} {p : CX} {τ : CTy} {st st1 : CSt} {ρ : CLok}
    {q : CPtr} {v : CVal} (h1 : ev L orc fr p st ρ = some (.ptr q, st1))
    (h2 : bLoad L st1 q τ = some v) : ev L orc fr (.ld p τ) st ρ = some (v, st1) := by
  simp [ev, h1, h2]

/-- The emitted address `T_speicher.slots[k].stand` evaluates to the emitter's
    slot pointer. -/
theorem ev_cSlot (fr : Nat) (tb : KTab) (k : Nat) (hk : k < 2) (st : CSt) (ρ : CLok) :
    ev c124.L c124.orc fr (cSlot (kTnr tb) k) st ρ = some (.ptr (kEL.slotPtr tb k ()), st) := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> cases tb <;> rfl

/-- **A slot store** `T_speicher.slots[k].stand = e;` from a related state:
    it runs, and ends related to the Gabbro store (`corr_schreibSlot`). -/
theorem cStore_lauf (fr : Nat) (CR XR : CCallR) (tb : KTab) (k : Nat) (hk : k < 2) (ve : CX) (v : Int)
    (ρ : CLok) (hve : ∀ st, ev c124.L c124.orc fr ve st ρ = some (.int v, st))
    (hv : 0 ≤ v ∧ v ≤ 100) (σ : World DR) (st : CSt) (h : corrW kEL σ st)
    (Λ : List (Res DR)) (wz : Zahl 0 100) (hwz : wz.n = v) :
    ∃ st', Exec c124.L c124.orc fr CR XR (.store (cSlot (kTnr tb) k) u32 ve) st ρ (.norm st' ρ) ∧
      corrW kEL (σ.schreibSlot tb Λ k () wz) st' ∧ st'.obs = st.obs := by
  obtain ⟨st', hs, hc, ho⟩ := corr_schreibSlot kEL σ st h tb rfl Λ k () wz (by omega)
    (by show (k : Int) < 2; omega)
  have hs' : bStore c124.L st (kEL.slotPtr tb k ()) u32 (.int v) = some st' := by
    rw [← hwz]; exact hs
  exact ⟨st', .store (ev_cSlot fr tb k hk st ρ) (hve st) (conv_u32 hv) hs', hc, ho⟩

/-- **`setze(n);`** from a related state: it runs (`CallAt` depth 1), writes
    both `konto` slots, and ends related to the two Gabbro stores; the locals
    of the caller stay. -/
theorem cSetze_lauf (n : Int) (hn : 0 ≤ n ∧ n ≤ 100) (σ : World DR) (st : CSt) (h : corrW kEL σ st)
    (ρ : CLok) (Λ Λ' : List (Res DR)) (wz : Zahl 0 100) (hwz : wz.n = n) :
    ∃ st', c124.laeuft (.call 0 [.lit n] none) st ρ (.norm st' ρ) ∧
      corrW kEL ((σ.schreibSlot KTab.konto Λ 0 () wz).schreibSlot KTab.konto Λ' 1 () wz) st' := by
  have hρ0 : bindParams [(0, u32)] [.int n] = some (lokUpd (fun _ => .undef) 0 (.int n)) := by
    show (match convV u32 (.int n), bindParams [] [] with
      | some v', some ρ => some (lokUpd ρ 0 v')
      | _, _ => none) = _
    rw [conv_u32 hn]
    rfl
  have hve : ∀ st, ev c124.L c124.orc 1 (.var 0) st (lokUpd (fun _ => .undef) 0 (.int n)) =
      some (.int n, st) := fun _ => rfl
  obtain ⟨st1, hx1, hc1, -⟩ := cStore_lauf 1 (CallAt c124.L c124.orc keinXR c124.Pr 0) keinXR
    KTab.konto 0 (by decide) (.var 0) n _ hve hn σ (enterFrame st 1 []) (corrW_enter h 1 [])
    Λ wz hwz
  obtain ⟨st2, hx2, hc2, -⟩ := cStore_lauf 1 (CallAt c124.L c124.orc keinXR c124.Pr 0) keinXR
    KTab.konto 1 (by decide) (.var 0) n _ hve hn _ st1 hc1 Λ' wz hwz
  refine ⟨leaveFrame st2 1, .call (vs := [.int n]) (st1 := st) (rv := none) rfl ?_ rfl,
    corrW_leave hc2 1⟩
  exact ⟨⟨[(0, u32)], [], cSetzeBody⟩, _, _, rfl, hρ0, .seqN hx1 hx2, st2,
    Or.inr ⟨rfl, _, rfl⟩, rfl⟩

/-- **`(void)pruefeA();`** from a related state: it runs, reads `privA[0]`
    (initialised: the relation), and changes no program object. -/
theorem cPruefe_lauf (σ : World DR) (st : CSt) (h : corrW kEL σ st) (ρ : CLok) :
    c124.laeuft (.call 1 [] none) st ρ (.norm (leaveFrame (enterFrame st 1 []) 1) ρ) := by
  have hl := corr_leseSlot kEL σ (enterFrame st 1 []) (corrW_enter h 1 []) KTab.privA rfl 0 ()
    (by decide) (by decide)
  have hv : 0 ≤ encW (DR.typ KTab.privA ()) (σ.slots KTab.privA 0 ()) ∧
      encW (DR.typ KTab.privA ()) (σ.slots KTab.privA 0 ()) ≤ 100 :=
    ⟨(σ.slots KTab.privA 0 ()).lo_le, (σ.slots KTab.privA 0 ()).le_hi⟩
  refine .call (vs := []) (st1 := st) (rv := some (.int (encW (DR.typ KTab.privA ())
    (σ.slots KTab.privA 0 ())))) rfl ?_ rfl
  refine ⟨⟨[], [], cPruefeBody⟩, _, _, rfl, rfl, .retS ?_ (conv_u32 hv), _, Or.inl rfl, rfl⟩
  exact ev_ld (ev_cSlot 1 KTab.privA 0 (by decide) (enterFrame st 1 []) _) hl

end C


/-! ## 5. The simulation relation -/

/-- The locals of a root: none written (the roots take no argument). -/
def ρ0 : CLok := fun _ => .undef

/-- The C positions of a `hauptA` thread. -/
def posA : Nat → CFaden
  | 0 => .an [cHauptA] ρ0
  | 1 => .an [cA0, cRestA1] ρ0
  | 2 => .an [cRestA1] ρ0
  | 3 => .an [cA1, cRestA2] ρ0
  | 4 => .an [cRestA2] ρ0
  | 5 => .an [cNimm, cRestA3] ρ0
  | 6 => .an [cRestA3] ρ0
  | 7 => .an [cSetzeA, cRestA4] ρ0
  | 8 => .an [cRestA4] ρ0
  | 9 => .an [cGib, cPruefe] ρ0
  | 10 => .an [cPruefe] ρ0
  | 11 => .an [] ρ0
  | _ => .aus

/-- Which G residue a C position of `hauptA` corresponds to. -/
def gOfA : Nat → Nat
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 2 | 6 => 3 | 7 => 3 | 8 => 4 | 9 => 4
  | 10 => 5 | _ => 6

/-- The locks a `hauptA` thread holds at each G residue. -/
def heldGA : Nat → List DR.Lock
  | 3 => [lL] | 4 => [lL] | _ => []

def posB : Nat → CFaden
  | 0 => .an [cHauptB] ρ0
  | 1 => .an [cB0, cRestB1] ρ0
  | 2 => .an [cRestB1] ρ0
  | 3 => .an [cNimm, cRestB2] ρ0
  | 4 => .an [cRestB2] ρ0
  | 5 => .an [cSetzeB, cGib] ρ0
  | 6 => .an [cGib] ρ0
  | 7 => .an [] ρ0
  | _ => .aus

def gOfB : Nat → Nat
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 2 | 6 => 3 | _ => 4

def heldGB : Nat → List DR.Lock
  | 2 => [lL] | 3 => [lL] | _ => []

/-- A `hauptA` thread: C position `i` and the G thread at the corresponding
    residue, with the locks that residue holds. -/
def ThreadA (c : CFaden) (z : RufFadenG DR) : Prop :=
  ∃ (i : Nat) (sp : List (Ereignis DR)) (log : List (RufEreignisF DR)), i ≤ 12 ∧ c = posA i ∧
    z = ⟨[], frA (gOfA i), sp, log⟩ ∧ offen sp = heldGA (gOfA i)

def ThreadB (c : CFaden) (z : RufFadenG DR) : Prop :=
  ∃ (i : Nat) (sp : List (Ereignis DR)) (log : List (RufEreignisF DR)), i ≤ 8 ∧ c = posB i ∧
    z = ⟨[], frB (gOfB i), sp, log⟩ ∧ offen sp = heldGB (gOfB i)

/-- Thread `t` of the C and of G, by the root the runtime started on it. -/
def FadenRel : Option Nat → CFaden → RufFadenG DR → Prop
  | some 2, c, z => ThreadA c z
  | some 3, c, z => ThreadB c z
  | _, c, _ => c = .aus

/-- The C lock `0` is held by `u` exactly when the G thread `u` holds `L`. -/
def SperrRel (K : KonfC) (M : RufMaschineG DR) : Prop :=
  ∀ (L : Nat) (u : Faden), K.halter L = some u ↔ (L = 0 ∧ lL ∈ offen (M.faeden u).spur)

/-- **THE SIMULATION RELATION** of `beispiele/124` under a root assignment `w`:
    memory corresponds (`corrW`), locks correspond, and every thread is at
    corresponding positions. -/
def R124 (w : Faden → Option Nat) (K : KonfC) (M : RufMaschineG DR) : Prop :=
  corrW kEL (M.speicher.welt []) K.st ∧ SperrRel K M ∧
    ∀ t, FadenRel (w t) (K.faeden t) (M.faeden t)

section Sim

variable {passes : Nat}

/-! ### Segments of G steps -/

def seg1 (M M1 : RufMaschineG DR) : Nat → RufMaschineG DR
  | 0 => M
  | _ => M1

def seg2 (M M1 M2 : RufMaschineG DR) : Nat → RufMaschineG DR
  | 0 => M
  | 1 => M1
  | _ => M2

def seg5 (M M1 M2 M3 M4 M5 : RufMaschineG DR) : Nat → RufMaschineG DR
  | 0 => M
  | 1 => M1
  | 2 => M2
  | 3 => M3
  | 4 => M4
  | _ => M5

theorem lauf0 (M : RufMaschineG DR) (t : Faden) :
    LaufG PR OR passes M (fun _ => M) (fun _ => t) 0 :=
  ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩

theorem lauf1 {M M1 : RufMaschineG DR} {t : Faden} (s1 : RufSchrittG PR OR passes M t M1) :
    LaufG PR OR passes M (seg1 M M1) (fun _ => t) 1 :=
  ⟨rfl, fun k hk => by
    match k, hk with
    | 0, _ => exact s1
    | k + 1, hk => exact absurd hk (by omega)⟩

theorem lauf2 {M M1 M2 : RufMaschineG DR} {t : Faden} (s1 : RufSchrittG PR OR passes M t M1)
    (s2 : RufSchrittG PR OR passes M1 t M2) : LaufG PR OR passes M (seg2 M M1 M2) (fun _ => t) 2 :=
  ⟨rfl, fun k hk => by
    match k, hk with
    | 0, _ => exact s1
    | 1, _ => exact s2
    | k + 2, hk => exact absurd hk (by omega)⟩

theorem lauf5 {M M1 M2 M3 M4 M5 : RufMaschineG DR} {t : Faden}
    (s1 : RufSchrittG PR OR passes M t M1) (s2 : RufSchrittG PR OR passes M1 t M2)
    (s3 : RufSchrittG PR OR passes M2 t M3) (s4 : RufSchrittG PR OR passes M3 t M4)
    (s5 : RufSchrittG PR OR passes M4 t M5) :
    LaufG PR OR passes M (seg5 M M1 M2 M3 M4 M5) (fun _ => t) 5 :=
  ⟨rfl, fun k hk => by
    match k, hk with
    | 0, _ => exact s1
    | 1, _ => exact s2
    | 2, _ => exact s3
    | 3, _ => exact s4
    | 4, _ => exact s5
    | k + 5, hk => exact absurd hk (by omega)⟩

theorem fremd_ende {ms : Nat → RufMaschineG DR} {M : RufMaschineG DR} {t : Faden} {N : Nat}
    (hl : LaufG PR OR passes M ms (fun _ => t) N) (u : Faden) (hu : u ≠ t) :
    (ms N).faeden u = M.faeden u :=
  laufG_fremd hl u (fun _ _ h => hu h.symm) N (Nat.le_refl N)

/-! ### The lock relation along a step -/

theorem sperrRel_gleich {K K' : KonfC} {M M' : RufMaschineG DR} (t : Faden) (hS : SperrRel K M)
    (hh : K'.halter = K.halter) (ht : offen (M'.faeden t).spur = offen (M.faeden t).spur)
    (ho : ∀ u, u ≠ t → M'.faeden u = M.faeden u) : SperrRel K' M' := by
  intro L u
  rw [hh]
  by_cases hu : u = t
  · subst hu; rw [ht]; exact hS L u
  · rw [ho u hu]; exact hS L u

theorem sperrRel_nimm {K K' : KonfC} {M M' : RufMaschineG DR} (t : Faden) (hS : SperrRel K M)
    (h0 : K.halter 0 = none) (hh : K'.halter = halterSetze K.halter 0 (some t))
    (ht : offen (M'.faeden t).spur = [lL]) (ho : ∀ u, u ≠ t → M'.faeden u = M.faeden u) :
    SperrRel K' M' := by
  intro L u
  rw [hh]
  unfold halterSetze
  by_cases hL : L = 0
  · subst hL
    rw [if_pos rfl]
    by_cases hu : u = t
    · subst hu; rw [ht]; exact ⟨fun _ => ⟨rfl, List.mem_singleton_self _⟩, fun _ => rfl⟩
    · rw [ho u hu]
      constructor
      · intro h
        have e : t = u := Option.some.inj h
        exact absurd e.symm hu
      · rintro ⟨_, hmem⟩
        have := (hS 0 u).mpr ⟨rfl, hmem⟩
        rw [h0] at this
        cases this
  · rw [if_neg hL]
    by_cases hu : u = t
    · subst hu
      rw [ht]
      constructor
      · intro h; exact absurd ((hS L u).mp h).1 hL
      · rintro ⟨h, _⟩; exact absurd h hL
    · rw [ho u hu]; exact hS L u

theorem sperrRel_gib {K K' : KonfC} {M M' : RufMaschineG DR} (t : Faden) (hS : SperrRel K M)
    (h0 : K.halter 0 = some t) (hh : K'.halter = halterSetze K.halter 0 none)
    (ht : offen (M'.faeden t).spur = []) (ho : ∀ u, u ≠ t → M'.faeden u = M.faeden u) :
    SperrRel K' M' := by
  intro L u
  rw [hh]
  unfold halterSetze
  by_cases hL : L = 0
  · subst hL
    rw [if_pos rfl]
    by_cases hu : u = t
    · subst hu; rw [ht]; simp
    · rw [ho u hu]
      constructor
      · intro h; cases h
      · rintro ⟨_, hmem⟩
        have := (hS 0 u).mpr ⟨rfl, hmem⟩
        rw [h0] at this
        exact absurd (Option.some.inj this) (Ne.symm hu)
  · rw [if_neg hL]
    by_cases hu : u = t
    · subst hu
      rw [ht]
      constructor
      · intro h; exact absurd ((hS L u).mp h).1 hL
      · rintro ⟨h, _⟩; exact absurd h hL
    · rw [ho u hu]; exact hS L u

/-- The relation after a step of `t`, from its three parts. -/
theorem r124_neu (w : Faden → Option Nat) {K K' : KonfC} {M M' : RufMaschineG DR} (t : Faden)
    (hR : R124 w K M) (hC : corrW kEL (M'.speicher.welt []) K'.st) (hS : SperrRel K' M')
    (hkf : ∀ u, u ≠ t → K'.faeden u = K.faeden u) (hmf : ∀ u, u ≠ t → M'.faeden u = M.faeden u)
    (ht : FadenRel (w t) (K'.faeden t) (M'.faeden t)) : R124 w K' M' := by
  refine ⟨hC, hS, fun u => ?_⟩
  by_cases hu : u = t
  · subst hu; exact ht
  · rw [hkf u hu, hmf u hu]; exact hR.2.2 u

/-! ### The C step, inverted at a known head -/

/-- The goal of one simulation step. -/
def SchrittZiel (w : Faden → Option Nat) (M : RufMaschineG DR) (t : Faden) (ℓ : Etikett)
    (K' : KonfC) : Prop :=
  ∃ (ms : Nat → RufMaschineG DR) (N : Nat), LaufG PR OR passes M ms (fun _ => t) N ∧
    R124 w K' (ms N) ∧ SegPasst c124 kEL lnr t ℓ ms N

/-- A split: no G step. -/
theorem k_teile (w : Faden → Option Nat) {K K' : KonfC} {M : RufMaschineG DR} {t : Faden}
    {ℓ : Etikett} (hR : R124 w K M) {a b : CS} {k : List CS} {ρ : CLok}
    (hc : K.faeden t = .an (.seq a b :: k) ρ) (hs : SchrittC c124 sperrAbstrakt K t ℓ K')
    (hrel : FadenRel (w t) (.an (a :: b :: k) ρ) (M.faeden t)) :
    SchrittZiel (passes := passes) w M t ℓ K' := by
  rcases schrittC_inv hs with ⟨a', b', k', ρ', hK, hl, hK'⟩ | ⟨ρ', hK, -, -⟩ |
    ⟨s, k', ρ', st', ρ'', hK, hq, -, -, -⟩ | ⟨s, k', ρ', st', v', hK, hq, -, -, -⟩ |
    ⟨n, k', ρ', op, h', hK, -, -, -, -⟩
  · rw [hc] at hK
    cases hK
    subst hl; subst hK'
    refine ⟨fun _ => M, 0, lauf0 M t, r124_neu w t hR hR.1 (sperrRel_gleich t hR.2.1 rfl rfl
      (fun _ _ => rfl)) (fun u hu => fadenSetze_ne _ _ _ _ hu) (fun _ _ => rfl)
      (by show FadenRel (w t) (fadenSetze K.faeden t _ t) (M.faeden t)
          rw [fadenSetze_eq]; exact hrel), ⟨?_, ?_, ?_, ?_⟩⟩
    · intro b hb; exact absurd hb List.not_mem_nil
    · intro b hb; exact absurd hb List.not_mem_nil
    · intro k hk; exact absurd hk (Nat.not_lt_zero k)
    · intro k hk; exact absurd hk (Nat.not_lt_zero k)
  · rw [hc] at hK; cases hK
  · rw [hc] at hK; cases hK; cases hq
  · rw [hc] at hK; cases hK; cases hq
  · rw [hc] at hK; cases hK

/-- The end of a root body: no G step (G's root stands at its `return`). -/
theorem k_ende (w : Faden → Option Nat) {K K' : KonfC} {M : RufMaschineG DR} {t : Faden}
    {ℓ : Etikett} (hR : R124 w K M) {ρ : CLok}
    (hc : K.faeden t = .an [] ρ) (hs : SchrittC c124 sperrAbstrakt K t ℓ K')
    (hrel : FadenRel (w t) .aus (M.faeden t)) :
    SchrittZiel (passes := passes) w M t ℓ K' := by
  rcases schrittC_inv hs with ⟨a', b', k', ρ', hK, -, -⟩ | ⟨ρ', hK, hl, hK'⟩ |
    ⟨s, k', ρ', st', ρ'', hK, -, -, -, -⟩ | ⟨s, k', ρ', st', v', hK, -, -, -, -⟩ |
    ⟨n, k', ρ', op, h', hK, -, -, -, -⟩
  · rw [hc] at hK; cases hK
  · subst hl; subst hK'
    refine ⟨fun _ => M, 0, lauf0 M t, r124_neu w t hR hR.1 (sperrRel_gleich t hR.2.1 rfl rfl
      (fun _ _ => rfl)) (fun u hu => fadenSetze_ne _ _ _ _ hu) (fun _ _ => rfl)
      (by show FadenRel (w t) (fadenSetze K.faeden t _ t) (M.faeden t)
          rw [fadenSetze_eq]; exact hrel), ⟨?_, ?_, ?_, ?_⟩⟩
    · intro b hb; exact absurd hb List.not_mem_nil
    · intro b hb; exact absurd hb List.not_mem_nil
    · intro k hk; exact absurd hk (Nat.not_lt_zero k)
    · intro k hk; exact absurd hk (Nat.not_lt_zero k)
  · rw [hc] at hK; cases hK
  · rw [hc] at hK; cases hK
  · rw [hc] at hK; cases hK

end Sim


section Arten

variable {passes : Nat}

/-- A carrier of the program is never an `atomic` global (there are none). -/
theorem nicht_atomar (tb : KTab) : ¬ AtomarAusgenommen (D := DR) (.inl tb) :=
  fun ⟨_, h, _⟩ => by cases h

/-- **A slot store as a block**: one G leaf step (`gBlatt`). -/
theorem k_store (w : Faden → Option Nat) {K K' : KonfC} {M : RufMaschineG DR} {t : Faden}
    {ℓ : Etikett} (hR : R124 w K M) (tb : KTab) (kk : Nat) (hkk : kk < 2) (v : Int)
    (hv : 0 ≤ v ∧ v ≤ 100) (wz : Zahl 0 100) (hwz : wz.n = v) {k : List CS} {ρ : CLok}
    (hc : K.faeden t = .an (.store (cSlot (kTnr tb) kk) u32 (.lit v) :: k) ρ)
    (hs : SchrittC c124 sperrAbstrakt K t ℓ K')
    {M1 : RufMaschineG DR} (s1 : RufSchrittG PR OR passes M t M1)
    (hacc : (Sum.inl tb, true) ∈ zugriffe M M1 t)
    (hoff : offen (M1.faeden t).spur = offen (M.faeden t).spur)
    (hmem : M1.speicher.slots = ((M.speicher.welt []).storeSlot tb kk () wz).slots)
    (hrel : FadenRel (w t) (.an k ρ) (M1.faeden t)) :
    SchrittZiel (passes := passes) w M t ℓ K' := by
  obtain ⟨st1, hx1, hc1, -⟩ := cStore_lauf (c124.tiefe + 1)
    (CallAt c124.L c124.orc keinXR c124.Pr c124.tiefe) keinXR tb kk hkk (.lit v) v ρ
    (fun _ => rfl) hv (M.speicher.welt []) K.st hR.1 [] wz hwz
  rcases schrittC_inv hs with ⟨a', b', k', ρ', hK, -, -⟩ | ⟨ρ', hK, -, -⟩ |
    ⟨s, k', ρ', st', ρ'', hK, -, hx, hl, hK'⟩ | ⟨s, k', ρ', st', v', hK, -, hx, -, -⟩ |
    ⟨n, k', ρ', op, h', hK, -, -, -, -⟩
  · rw [hc] at hK; cases hK
  · rw [hc] at hK; cases hK
  · rw [hc] at hK
    cases hK
    have e := c124.laeuft_det hx hx1
    cases e
    subst hl; subst hK'
    refine ⟨seg1 M M1, 1, lauf1 s1, r124_neu w t hR ?_ ?_ ?_ ?_ ?_, ?_⟩
    · exact corrW_von hc1 (by show _ = M1.speicher.slots; rw [hmem]; rfl)
    · exact sperrRel_gleich t hR.2.1 rfl hoff (fun u hu => rufSchrittG_fremd s1 u hu)
    · exact fun u hu => fadenSetze_ne _ _ _ _ hu
    · exact fun u hu => rufSchrittG_fremd s1 u hu
    · show FadenRel (w t) (fadenSetze K.faeden t _ t) (M1.faeden t)
      rw [fadenSetze_eq]; exact hrel
    · refine ⟨fun b hb => ?_, fun b hb => ?_, fun k hk L hg => ?_, fun k hk L hn => ?_⟩
      · have hb' : b = .tab (kTnr tb) := by
          simpa [Etikett.fussR, fussR, CS.obj0, CS.rufe, cSlot, CX.obj, c124] using hb
        exact ⟨.inl tb, hb'.symm, nicht_atomar tb, 0, Nat.zero_lt_one, Or.inl ⟨true, hacc⟩⟩
      · have hb' : b = .tab (kTnr tb) := by
          simpa [Etikett.fussW, fussW, CS.ziele0, CS.rufe, cSlot, CX.obj, c124] using hb
        exact ⟨.inl tb, hb'.symm, 0, Nat.zero_lt_one, Or.inl hacc⟩
      · match k, hk with
        | 0, _ => exact absurd hg (kein_wechsel hoff L).1
      · match k, hk with
        | 0, _ => exact absurd hn (kein_wechsel hoff L).2
  · rw [hc] at hK
    cases hK
    cases (c124.laeuft_det hx hx1)
  · rw [hc] at hK; cases hK

/-- A foreign call has no meaning inside a block. -/
theorem ext_kein_block {n : Nat} {st : CSt} {ρ : CLok} {o : COut} :
    ¬ c124.laeuft (.ext n [] none) st ρ o := by
  intro h
  cases h with
  | ext _ hxr _ => exact hxr.elim

/-- At `L_nimm();` the C lock is free, and so is G's. -/
theorem nimm_frei (w : Faden → Option Nat) {K K' : KonfC} {M : RufMaschineG DR} {t : Faden}
    {ℓ : Etikett} (hR : R124 w K M) {k : List CS} {ρ : CLok}
    (hc : K.faeden t = .an (cNimm :: k) ρ) (hs : SchrittC c124 sperrAbstrakt K t ℓ K') :
    K.halter 0 = none ∧ RufFreiG M t lL := by
  have h0 : K.halter 0 = none := by
    rcases schrittC_inv hs with ⟨a', b', k', ρ', hK, -, -⟩ | ⟨ρ', hK, -, -⟩ |
      ⟨s, k', ρ', st', ρ'', hK, -, hx, -, -⟩ | ⟨s, k', ρ', st', v', hK, -, hx, -, -⟩ |
      ⟨n, k', ρ', op, h', hK, ho, hl, -, -⟩
    · rw [hc] at hK; cases hK
    · rw [hc] at hK; cases hK
    · rw [hc] at hK; cases hK; exact (ext_kein_block hx).elim
    · rw [hc] at hK; cases hK; exact (ext_kein_block hx).elim
    · rw [hc] at hK
      cases hK
      cases ho
      exact hl.1
  refine ⟨h0, fun u hu hL => ?_⟩
  have := (hR.2.1 0 u).mpr ⟨rfl, hL⟩
  rw [h0] at this
  cases this

/-- **`L_nimm();`**: the acquire -- two G steps (`gNimm`). -/
theorem k_nimm (w : Faden → Option Nat) {K K' : KonfC} {M : RufMaschineG DR} {t : Faden}
    {ℓ : Etikett} (hR : R124 w K M) {k : List CS} {ρ : CLok}
    (hc : K.faeden t = .an (cNimm :: k) ρ) (hs : SchrittC c124 sperrAbstrakt K t ℓ K')
    {M1 M2 : RufMaschineG DR} (s1 : RufSchrittG PR OR passes M t M1)
    (s2 : RufSchrittG PR OR passes M1 t M2)
    (h1 : (M1.faeden t).spur = (M.faeden t).spur) (h2 : offen (M2.faeden t).spur = [lL])
    (hm2 : M2.speicher = M.speicher) (h0 : offen (M.faeden t).spur = [])
    (hrel : FadenRel (w t) (.an k ρ) (M2.faeden t)) :
    SchrittZiel (passes := passes) w M t ℓ K' := by
  rcases schrittC_inv hs with ⟨a', b', k', ρ', hK, -, -⟩ | ⟨ρ', hK, -, -⟩ |
    ⟨s, k', ρ', st', ρ'', hK, -, hx, -, -⟩ | ⟨s, k', ρ', st', v', hK, -, hx, -, -⟩ |
    ⟨n, k', ρ', op, h', hK, ho, hl, hlab, hK'⟩
  · rw [hc] at hK; cases hK
  · rw [hc] at hK; cases hK
  · rw [hc] at hK; cases hK; exact (ext_kein_block hx).elim
  · rw [hc] at hK; cases hK; exact (ext_kein_block hx).elim
  · rw [hc] at hK
    cases hK
    cases ho
    obtain ⟨hh0, hh'⟩ := hl
    subst hlab; subst hK'
    have hl2 := lauf2 (passes := passes) s1 s2
    refine ⟨seg2 M M1 M2, 2, hl2, r124_neu w t hR ?_ ?_ ?_ ?_ ?_, ?_⟩
    · show corrW kEL (M2.speicher.welt []) K.st
      rw [hm2]; exact hR.1
    · exact sperrRel_nimm t hR.2.1 hh0 hh' h2 (fremd_ende hl2)
    · exact fun u hu => fadenSetze_ne _ _ _ _ hu
    · exact fremd_ende hl2
    · show FadenRel (w t) (fadenSetze K.faeden t _ t) (M2.faeden t)
      rw [fadenSetze_eq]; exact hrel
    · refine ⟨fun b hb => absurd hb List.not_mem_nil, fun b hb => absurd hb List.not_mem_nil,
        fun k hk L hg => ?_, fun _ _ _ _ => rfl⟩
      match k, hk with
      | 0, _ => exact absurd hg (kein_wechsel (by
          show offen (M1.faeden t).spur = offen (M.faeden t).spur; rw [h1]) L).1
      | 1, _ =>
          have := hg.1
          rw [show (seg2 M M1 M2 1) = M1 from rfl, h1, h0] at this
          exact absurd this List.not_mem_nil

/-- **`setze(n);`**: the call inside the lock -- five G steps (`gSetze`). -/
theorem k_setze (w : Faden → Option Nat) {K K' : KonfC} {M : RufMaschineG DR} {t : Faden}
    {ℓ : Etikett} (hR : R124 w K M) (n : Int) (hn : 0 ≤ n ∧ n ≤ 100) (wz : Zahl 0 100)
    (hwz : wz.n = n) {k : List CS} {ρ : CLok}
    (hc : K.faeden t = .an (.call 0 [.lit n] none :: k) ρ)
    (hs : SchrittC c124 sperrAbstrakt K t ℓ K')
    {M1 M2 M3 M4 M5 : RufMaschineG DR} (s1 : RufSchrittG PR OR passes M t M1)
    (s2 : RufSchrittG PR OR passes M1 t M2) (s3 : RufSchrittG PR OR passes M2 t M3)
    (s4 : RufSchrittG PR OR passes M3 t M4) (s5 : RufSchrittG PR OR passes M4 t M5)
    (ho1 : offen (M1.faeden t).spur = offen (M.faeden t).spur)
    (ho2 : offen (M2.faeden t).spur = offen (M.faeden t).spur)
    (ho3 : offen (M3.faeden t).spur = offen (M.faeden t).spur)
    (ho4 : offen (M4.faeden t).spur = offen (M.faeden t).spur)
    (ho5 : offen (M5.faeden t).spur = offen (M.faeden t).spur)
    (hacc : (Sum.inl KTab.konto, true) ∈ zugriffe M1 M2 t)
    (hmem : M5.speicher.slots =
      (((M.speicher.welt []).storeSlot KTab.konto 0 () wz).storeSlot KTab.konto 1 () wz).slots)
    (hrel : FadenRel (w t) (.an k ρ) (M5.faeden t)) :
    SchrittZiel (passes := passes) w M t ℓ K' := by
  obtain ⟨st1, hx1, hc1⟩ := cSetze_lauf n hn (M.speicher.welt []) K.st hR.1 ρ [] [] wz hwz
  rcases schrittC_inv hs with ⟨a', b', k', ρ', hK, -, -⟩ | ⟨ρ', hK, -, -⟩ |
    ⟨s, k', ρ', st', ρ'', hK, -, hx, hl, hK'⟩ | ⟨s, k', ρ', st', v', hK, -, hx, -, -⟩ |
    ⟨n', k', ρ', op, h', hK, -, -, -, -⟩
  · rw [hc] at hK; cases hK
  · rw [hc] at hK; cases hK
  · rw [hc] at hK
    cases hK
    have e := c124.laeuft_det hx hx1
    cases e
    subst hl; subst hK'
    have hl5 := lauf5 (passes := passes) s1 s2 s3 s4 s5
    refine ⟨seg5 M M1 M2 M3 M4 M5, 5, hl5, r124_neu w t hR ?_ ?_ ?_ ?_ ?_, ?_⟩
    · exact corrW_von hc1 (by show _ = M5.speicher.slots; rw [hmem]; rfl)
    · exact sperrRel_gleich t hR.2.1 rfl ho5 (fremd_ende hl5)
    · exact fun u hu => fadenSetze_ne _ _ _ _ hu
    · exact fremd_ende hl5
    · show FadenRel (w t) (fadenSetze K.faeden t _ t) (M5.faeden t)
      rw [fadenSetze_eq]; exact hrel
    · have hoffs : ∀ j, j < 5 → offen ((seg5 M M1 M2 M3 M4 M5 (j + 1)).faeden t).spur =
          offen ((seg5 M M1 M2 M3 M4 M5 j).faeden t).spur := by
        intro j hj
        match j, hj with
        | 0, _ => exact ho1
        | 1, _ => exact ho2.trans ho1.symm
        | 2, _ => exact ho3.trans ho2.symm
        | 3, _ => exact ho4.trans ho3.symm
        | 4, _ => exact ho5.trans ho4.symm
      refine ⟨fun b hb => ?_, fun b hb => ?_, fun j hj L hg => ?_, fun j hj L hn => ?_⟩
      · have hb' : b = .tab 0 := by
          simpa [Etikett.fussR, fussR, CS.obj0, CS.rufe, cSlot, CX.obj, CX.objL, c124, c124Prog,
            cSetzeBody] using hb
        exact ⟨.inl KTab.konto, hb'.symm, nicht_atomar _, 1, by decide, Or.inl ⟨true, hacc⟩⟩
      · have hb' : b = .tab 0 := by
          simpa [Etikett.fussW, fussW, CS.ziele0, CS.rufe, cSlot, CX.obj, c124, c124Prog,
            cSetzeBody] using hb
        exact ⟨.inl KTab.konto, hb'.symm, 1, by decide, Or.inl hacc⟩
      · exact absurd hg (kein_wechsel (hoffs j hj) L).1
      · exact absurd hn (kein_wechsel (hoffs j hj) L).2
  · rw [hc] at hK
    cases hK
    cases (c124.laeuft_det hx hx1)
  · rw [hc] at hK; cases hK

/-- **`L_gib();`**: the release -- two G steps (`gGib`). -/
theorem k_gib (w : Faden → Option Nat) {K K' : KonfC} {M : RufMaschineG DR} {t : Faden}
    {ℓ : Etikett} (hR : R124 w K M) {k : List CS} {ρ : CLok}
    (hc : K.faeden t = .an (cGib :: k) ρ) (hs : SchrittC c124 sperrAbstrakt K t ℓ K')
    {M1 M2 : RufMaschineG DR} (s1 : RufSchrittG PR OR passes M t M1)
    (s2 : RufSchrittG PR OR passes M1 t M2)
    (h0 : offen (M.faeden t).spur = [lL]) (h1 : offen (M1.faeden t).spur = [])
    (h2 : offen (M2.faeden t).spur = []) (hm2 : M2.speicher = M.speicher)
    (hrel : FadenRel (w t) (.an k ρ) (M2.faeden t)) :
    SchrittZiel (passes := passes) w M t ℓ K' := by
  rcases schrittC_inv hs with ⟨a', b', k', ρ', hK, -, -⟩ | ⟨ρ', hK, -, -⟩ |
    ⟨s, k', ρ', st', ρ'', hK, -, hx, -, -⟩ | ⟨s, k', ρ', st', v', hK, -, hx, -, -⟩ |
    ⟨n, k', ρ', op, h', hK, ho, hl, hlab, hK'⟩
  · rw [hc] at hK; cases hK
  · rw [hc] at hK; cases hK
  · rw [hc] at hK; cases hK; exact (ext_kein_block hx).elim
  · rw [hc] at hK; cases hK; exact (ext_kein_block hx).elim
  · rw [hc] at hK
    cases hK
    cases ho
    obtain ⟨hh0, hh'⟩ := hl
    subst hlab; subst hK'
    have hl2 := lauf2 (passes := passes) s1 s2
    refine ⟨seg2 M M1 M2, 2, hl2, r124_neu w t hR ?_ ?_ ?_ ?_ ?_, ?_⟩
    · show corrW kEL (M2.speicher.welt []) K.st
      rw [hm2]; exact hR.1
    · exact sperrRel_gib t hR.2.1 hh0 hh' h2 (fremd_ende hl2)
    · exact fun u hu => fadenSetze_ne _ _ _ _ hu
    · exact fremd_ende hl2
    · show FadenRel (w t) (fadenSetze K.faeden t _ t) (M2.faeden t)
      rw [fadenSetze_eq]; exact hrel
    · refine ⟨fun b hb => absurd hb List.not_mem_nil, fun b hb => absurd hb List.not_mem_nil,
        fun _ _ _ _ => rfl, fun k hk L hn => ?_⟩
      match k, hk with
      | 0, _ =>
          have := hn.1
          rw [show (seg2 M M1 M2 0) = M from rfl, h0] at this
          exact (this (by cases L; exact List.mem_singleton_self _)).elim
      | 1, _ => exact absurd hn (kein_wechsel (by rw [show (seg2 M M1 M2 2) = M2 from rfl,
          show (seg2 M M1 M2 1) = M1 from rfl, h1, h2]) L).2

/-- **`(void)pruefeA();`**: call and return -- two G steps (`gPruefe`). -/
theorem k_pruefe (w : Faden → Option Nat) {K K' : KonfC} {M : RufMaschineG DR} {t : Faden}
    {ℓ : Etikett} (hR : R124 w K M) {k : List CS} {ρ : CLok}
    (hc : K.faeden t = .an (.call 1 [] none :: k) ρ) (hs : SchrittC c124 sperrAbstrakt K t ℓ K')
    {M1 M2 : RufMaschineG DR} (s1 : RufSchrittG PR OR passes M t M1)
    (s2 : RufSchrittG PR OR passes M1 t M2)
    (h1 : offen (M1.faeden t).spur = offen (M.faeden t).spur)
    (h2 : offen (M2.faeden t).spur = offen (M.faeden t).spur)
    (hacc : (Sum.inl KTab.privA, false) ∈ zugriffe M1 M2 t) (hm2 : M2.speicher = M.speicher)
    (hrel : FadenRel (w t) (.an k ρ) (M2.faeden t)) :
    SchrittZiel (passes := passes) w M t ℓ K' := by
  have hx1 := cPruefe_lauf (M.speicher.welt []) K.st hR.1 ρ
  rcases schrittC_inv hs with ⟨a', b', k', ρ', hK, -, -⟩ | ⟨ρ', hK, -, -⟩ |
    ⟨s, k', ρ', st', ρ'', hK, -, hx, hl, hK'⟩ | ⟨s, k', ρ', st', v', hK, -, hx, -, -⟩ |
    ⟨n', k', ρ', op, h', hK, -, -, -, -⟩
  · rw [hc] at hK; cases hK
  · rw [hc] at hK; cases hK
  · rw [hc] at hK
    cases hK
    have e := c124.laeuft_det hx hx1
    cases e
    subst hl; subst hK'
    have hl2 := lauf2 (passes := passes) s1 s2
    refine ⟨seg2 M M1 M2, 2, hl2, r124_neu w t hR ?_ ?_ ?_ ?_ ?_, ?_⟩
    · show corrW kEL (M2.speicher.welt []) _
      rw [hm2]; exact corrW_leave (corrW_enter hR.1 1 []) 1
    · exact sperrRel_gleich t hR.2.1 rfl h2 (fremd_ende hl2)
    · exact fun u hu => fadenSetze_ne _ _ _ _ hu
    · exact fremd_ende hl2
    · show FadenRel (w t) (fadenSetze K.faeden t _ t) (M2.faeden t)
      rw [fadenSetze_eq]; exact hrel
    · have hoffs : ∀ j, j < 2 → offen ((seg2 M M1 M2 (j + 1)).faeden t).spur =
          offen ((seg2 M M1 M2 j).faeden t).spur := by
        intro j hj
        match j, hj with
        | 0, _ => exact h1
        | 1, _ => exact h2.trans h1.symm
      refine ⟨fun b hb => ?_, fun b hb => ?_, fun j hj L hg => ?_, fun j hj L hn => ?_⟩
      · have hb' : b = .tab 1 := by
          simpa [Etikett.fussR, fussR, CS.obj0, CS.rufe, cSlot, CX.obj, CX.objL, c124, c124Prog,
            cPruefeBody] using hb
        exact ⟨.inl KTab.privA, hb'.symm, nicht_atomar _, 1, by decide, Or.inl ⟨false, hacc⟩⟩
      · have hb' : False := by
          simpa [Etikett.fussW, fussW, CS.ziele0, CS.rufe, c124, c124Prog, cPruefeBody] using hb
        exact hb'.elim
      · exact absurd hg (kein_wechsel (hoffs j hj) L).1
      · exact absurd hn (kein_wechsel (hoffs j hj) L).2
  · rw [hc] at hK
    cases hK
    cases (c124.laeuft_det hx hx1)
  · rw [hc] at hK; cases hK

end Arten


section Positionen

variable {passes : Nat}

/-- **Every C step of a `hauptA` thread is simulated.** -/
theorem schrittA (w : Faden → Option Nat) {K K' : KonfC} {M : RufMaschineG DR} {t : Faden}
    {ℓ : Etikett} (hwt : w t = some 2) (hR : R124 w K M)
    (hs : SchrittC c124 sperrAbstrakt K t ℓ K') :
    SchrittZiel (passes := passes) w M t ℓ K' := by
  have hA : ThreadA (K.faeden t) (M.faeden t) := by
    have := hR.2.2 t; rw [hwt] at this; exact this
  have mk : ∀ (j : Nat) (c : CFaden) (z : RufFadenG DR), j ≤ 12 → c = posA j →
      (∃ (sp' : List (Ereignis DR)) (log' : List (RufEreignisF DR)),
        z = ⟨[], frA (gOfA j), sp', log'⟩ ∧ offen sp' = heldGA (gOfA j)) →
      FadenRel (w t) c z := by
    intro j c z hj hcj ⟨sp', log', hz', ho'⟩
    rw [hwt]
    exact ⟨j, sp', log', hj, hcj, hz', ho'⟩
  obtain ⟨i, sp, log, hi, hc, hz, hoff⟩ := hA
  match i, hi, hc, hz, hoff with
  | 0, _, hc, hz, hoff =>
      exact k_teile w hR (a := cA0) (b := cRestA1) (k := []) hc hs
        (mk 1 _ _ (by omega) rfl ⟨sp, log, hz, hoff⟩)
  | 1, _, hc, hz, hoff =>
      obtain ⟨M1, s1, ⟨sp1, hz1, ho1⟩, hacc, hmem⟩ := gBlatt (passes := passes) kHauptA .nil
        KTab.privA kI0 k7 rfl (kDarfA _) (.cons kA1 (.cons kLocksA kRestA)) M t sp log
        (frA0_form M t sp log hz)
      exact k_store w hR KTab.privA 0 (by decide) 7 (by decide) ⟨7, by decide, by decide⟩ rfl
        (k := [cRestA1]) (ρ := ρ0) hc hs s1 hacc (by rw [hz1, hz]; exact ho1)
        (by rw [hmem]; rfl) (mk 2 _ _ (by omega) rfl ⟨sp1, log, hz1, by rw [ho1, hoff]; rfl⟩)
  | 2, _, hc, hz, hoff =>
      exact k_teile w hR (a := cA1) (b := cRestA2) (k := []) hc hs
        (mk 3 _ _ (by omega) rfl ⟨sp, log, hz, hoff⟩)
  | 3, _, hc, hz, hoff =>
      obtain ⟨M1, s1, ⟨sp1, hz1, ho1⟩, hacc, hmem⟩ := gBlatt (passes := passes) kHauptA .nil
        KTab.privA kI1 k7 rfl (kDarfA _) (.cons kLocksA kRestA) M t sp log hz
      exact k_store w hR KTab.privA 1 (by decide) 7 (by decide) ⟨7, by decide, by decide⟩ rfl
        (k := [cRestA2]) (ρ := ρ0) hc hs s1 hacc (by rw [hz1, hz]; exact ho1)
        (by rw [hmem]; rfl) (mk 4 _ _ (by omega) rfl ⟨sp1, log, hz1, by rw [ho1, hoff]; rfl⟩)
  | 4, _, hc, hz, hoff =>
      exact k_teile w hR (a := cNimm) (b := cRestA3) (k := []) hc hs
        (mk 5 _ _ (by omega) rfl ⟨sp, log, hz, hoff⟩)
  | 5, _, hc, hz, hoff =>
      obtain ⟨_, hfrei⟩ := nimm_frei w hR (k := [cRestA3]) (ρ := ρ0) hc hs
      obtain ⟨M1, M2, s1, s2, hs1, ⟨sp2, hz2, ho2⟩, _, hm2⟩ := gNimm (passes := passes) kHauptA
        .nil (.cons kRufA .nil) kRestA M t sp log hz hoff hfrei
      exact k_nimm w hR (k := [cRestA3]) (ρ := ρ0) hc hs s1 s2 (hs1.trans (by rw [hz]))
        (by rw [hz2]; exact ho2) hm2 (by rw [hz]; exact hoff)
        (mk 6 _ _ (by omega) rfl ⟨sp2, log, hz2, ho2⟩)
  | 6, _, hc, hz, hoff =>
      exact k_teile w hR (a := cSetzeA) (b := cRestA4) (k := []) hc hs
        (mk 7 _ _ (by omega) rfl ⟨sp, log, hz, hoff⟩)
  | 7, _, hc, hz, hoff =>
      obtain ⟨M1, M2, M3, M4, M5, s1, s2, s3, s4, s5, o1, o2, o3, o4, ⟨sp5, log5, hz5, ho5⟩,
        hacc, hmem⟩ := gSetze (passes := passes) kHauptA .nil kHpSetzeA k30
          (.dann .nil (.ende (ruEnd kRestA))) M t sp log hz hoff
      have h0 : offen (M.faeden t).spur = [lL] := by rw [hz]; exact hoff
      exact k_setze w hR 30 (by decide) ⟨30, by decide, by decide⟩ rfl (k := [cRestA4]) (ρ := ρ0)
        hc hs s1 s2 s3 s4 s5 (o1.trans h0.symm) (o2.trans h0.symm) (o3.trans h0.symm)
        (o4.trans h0.symm) (by rw [hz5]; exact ho5.trans h0.symm) hacc (by rw [hmem]; rfl)
        (mk 8 _ _ (by omega) rfl ⟨sp5, log5, hz5, ho5⟩)
  | 8, _, hc, hz, hoff =>
      exact k_teile w hR (a := cGib) (b := cPruefe) (k := []) hc hs
        (mk 9 _ _ (by omega) rfl ⟨sp, log, hz, hoff⟩)
  | 9, _, hc, hz, hoff =>
      obtain ⟨M1, M2, s1, s2, ho1, ⟨sp2, hz2, ho2⟩, _, hm2⟩ := gGib (passes := passes) kHauptA
        .nil kRestA M t sp log hz hoff
      exact k_gib w hR (k := [cPruefe]) (ρ := ρ0) hc hs s1 s2 (by rw [hz]; exact hoff) ho1
        (by rw [hz2]; exact ho2) hm2 (mk 10 _ _ (by omega) rfl ⟨sp2, log, hz2, ho2⟩)
  | 10, _, hc, hz, hoff =>
      obtain ⟨M1, M2, s1, s2, ho1, ⟨sp2, log2, hz2, ho2⟩, hacc, _, hm2⟩ :=
        gPruefe (passes := passes) M t sp log hz hoff
      have h0 : offen (M.faeden t).spur = [] := by rw [hz]; exact hoff
      exact k_pruefe w hR (k := []) (ρ := ρ0) hc hs s1 s2 (ho1.trans h0.symm)
        (by rw [hz2]; exact ho2.trans h0.symm) hacc hm2
        (mk 11 _ _ (by omega) rfl ⟨sp2, log2, hz2, ho2⟩)
  | 11, _, hc, hz, hoff =>
      exact k_ende w hR (ρ := ρ0) hc hs (mk 12 _ _ (by omega) rfl ⟨sp, log, hz, hoff⟩)
  | 12, _, hc, _, _ => exact (schrittC_aus hs hc).elim

/-- **Every C step of a `hauptB` thread is simulated.** -/
theorem schrittB (w : Faden → Option Nat) {K K' : KonfC} {M : RufMaschineG DR} {t : Faden}
    {ℓ : Etikett} (hwt : w t = some 3) (hR : R124 w K M)
    (hs : SchrittC c124 sperrAbstrakt K t ℓ K') :
    SchrittZiel (passes := passes) w M t ℓ K' := by
  have hB : ThreadB (K.faeden t) (M.faeden t) := by
    have := hR.2.2 t; rw [hwt] at this; exact this
  have mk : ∀ (j : Nat) (c : CFaden) (z : RufFadenG DR), j ≤ 8 → c = posB j →
      (∃ (sp' : List (Ereignis DR)) (log' : List (RufEreignisF DR)),
        z = ⟨[], frB (gOfB j), sp', log'⟩ ∧ offen sp' = heldGB (gOfB j)) →
      FadenRel (w t) c z := by
    intro j c z hj hcj ⟨sp', log', hz', ho'⟩
    rw [hwt]
    exact ⟨j, sp', log', hj, hcj, hz', ho'⟩
  obtain ⟨i, sp, log, hi, hc, hz, hoff⟩ := hB
  match i, hi, hc, hz, hoff with
  | 0, _, hc, hz, hoff =>
      exact k_teile w hR (a := cB0) (b := cRestB1) (k := []) hc hs
        (mk 1 _ _ (by omega) rfl ⟨sp, log, hz, hoff⟩)
  | 1, _, hc, hz, hoff =>
      obtain ⟨M1, s1, ⟨sp1, hz1, ho1⟩, hacc, hmem⟩ := gBlatt (passes := passes) kHauptB .nil
        KTab.privB kI0 k5 rfl (kDarfB _) (.cons kLocksB (.ret .keine List.Perm.nil)) M t sp log
        (frB0_form M t sp log hz)
      exact k_store w hR KTab.privB 0 (by decide) 5 (by decide) ⟨5, by decide, by decide⟩ rfl
        (k := [cRestB1]) (ρ := ρ0) hc hs s1 hacc (by rw [hz1, hz]; exact ho1)
        (by rw [hmem]; rfl) (mk 2 _ _ (by omega) rfl ⟨sp1, log, hz1, by rw [ho1, hoff]; rfl⟩)
  | 2, _, hc, hz, hoff =>
      exact k_teile w hR (a := cNimm) (b := cRestB2) (k := []) hc hs
        (mk 3 _ _ (by omega) rfl ⟨sp, log, hz, hoff⟩)
  | 3, _, hc, hz, hoff =>
      obtain ⟨_, hfrei⟩ := nimm_frei w hR (k := [cRestB2]) (ρ := ρ0) hc hs
      obtain ⟨M1, M2, s1, s2, hs1, ⟨sp2, hz2, ho2⟩, _, hm2⟩ := gNimm (passes := passes) kHauptB
        .nil (.cons kRufB .nil) (.ret .keine List.Perm.nil) M t sp log hz hoff hfrei
      exact k_nimm w hR (k := [cRestB2]) (ρ := ρ0) hc hs s1 s2 (hs1.trans (by rw [hz]))
        (by rw [hz2]; exact ho2) hm2 (by rw [hz]; exact hoff)
        (mk 4 _ _ (by omega) rfl ⟨sp2, log, hz2, ho2⟩)
  | 4, _, hc, hz, hoff =>
      exact k_teile w hR (a := cSetzeB) (b := cGib) (k := []) hc hs
        (mk 5 _ _ (by omega) rfl ⟨sp, log, hz, hoff⟩)
  | 5, _, hc, hz, hoff =>
      obtain ⟨M1, M2, M3, M4, M5, s1, s2, s3, s4, s5, o1, o2, o3, o4, ⟨sp5, log5, hz5, ho5⟩,
        hacc, hmem⟩ := gSetze (passes := passes) kHauptB .nil kHpSetzeB k70
          (.dann .nil (.ende (ruEnd (V := vertragVon kD kHauptB) (l := false) (Γ := []) (Λ := [])
            (.ret .keine List.Perm.nil)))) M t sp log hz hoff
      have h0 : offen (M.faeden t).spur = [lL] := by rw [hz]; exact hoff
      exact k_setze w hR 70 (by decide) ⟨70, by decide, by decide⟩ rfl (k := [cGib]) (ρ := ρ0)
        hc hs s1 s2 s3 s4 s5 (o1.trans h0.symm) (o2.trans h0.symm) (o3.trans h0.symm)
        (o4.trans h0.symm) (by rw [hz5]; exact ho5.trans h0.symm) hacc (by rw [hmem]; rfl)
        (mk 6 _ _ (by omega) rfl ⟨sp5, log5, hz5, ho5⟩)
  | 6, _, hc, hz, hoff =>
      obtain ⟨M1, M2, s1, s2, ho1, ⟨sp2, hz2, ho2⟩, _, hm2⟩ := gGib (passes := passes) kHauptB
        .nil (.ret .keine List.Perm.nil) M t sp log hz hoff
      exact k_gib w hR (k := []) (ρ := ρ0) hc hs s1 s2 (by rw [hz]; exact hoff) ho1
        (by rw [hz2]; exact ho2) hm2 (mk 7 _ _ (by omega) rfl ⟨sp2, log, hz2, ho2⟩)
  | 7, _, hc, hz, hoff =>
      exact k_ende w hR (ρ := ρ0) hc hs (mk 8 _ _ (by omega) rfl ⟨sp, log, hz, hoff⟩)
  | 8, _, hc, _, _ => exact (schrittC_aus hs hc).elim

end Positionen


/-! ## 6. The start, the certificate, the theorem -/

section Satz

/-- The G start for a root assignment `w` of the runtime: `hauptA` where it
    started root 2, `hauptB` where root 3, the idle root elsewhere. -/
def kInit (w : Faden → Option Nat) : Faden → Σ f : DR.Fn, Env DR (DR.params f) := fun t =>
  match w t with
  | some 2 => ⟨some kHauptA, .nil⟩
  | some 3 => ⟨some kHauptB, .nil⟩
  | _ => ⟨none, .nil⟩

/-- The start machine of G for `w`, from the declared initial memory. -/
def M0 (w : Faden → Option Nat) : RufMaschineG DR := RufStartG PR (speicherR kSp) (kInit w)

/-- The root assignments `FadenStartC` admits: declared roots only, each once. -/
def Wurzeln (w : Faden → Option Nat) : Prop :=
  (∀ t f, w t = some f → f ∈ [2, 3]) ∧ ∀ t u f, w t = some f → w u = some f → t = u

theorem kInit_2 {w : Faden → Option Nat} {t : Faden} (h : w t = some 2) :
    kInit w t = ⟨some kHauptA, .nil⟩ := by
  unfold kInit; rw [h]; rfl

theorem kInit_3 {w : Faden → Option Nat} {t : Faden} (h : w t = some 3) :
    kInit w t = ⟨some kHauptB, .nil⟩ := by
  unfold kInit; rw [h]; rfl

theorem kInit_sonst {w : Faden → Option Nat} {t : Faden} (h2 : w t ≠ some 2)
    (h3 : w t ≠ some 3) : kInit w t = ⟨none, .nil⟩ := by
  unfold kInit
  split
  · rename_i h; exact absurd h h2
  · rename_i h; exact absurd h h3
  · rfl

theorem fadenRel_sonst {o : Option Nat} {c : CFaden} {z : RufFadenG DR} (h2 : o ≠ some 2)
    (h3 : o ≠ some 3) (h : FadenRel o c z) : c = .aus := by
  unfold FadenRel at h
  split at h
  · exact absurd rfl h2
  · exact absurd rfl h3
  · exact h

/-- **The runtime premise of the C (`FadenStartC`) gives the runtime premise
    (d) of the goal theorem** for the corresponding G start. -/
theorem laufzeit_w (w : Faden → Option Nat) (hw : Wurzeln w) :
    Laufzeit kE (speicherR kSp) (kInit w) where
  lader := rfl
  start t := by
    by_cases h2 : w t = some 2
    · exact Or.inr ⟨⟨kHauptA, .nil⟩, List.mem_cons_self, by rw [kInit_2 h2]; rfl⟩
    · by_cases h3 : w t = some 3
      · exact Or.inr ⟨⟨kHauptB, .nil⟩, List.mem_cons_of_mem _ List.mem_cons_self,
          by rw [kInit_3 h3]; rfl⟩
      · exact Or.inl (kInit_sonst h2 h3)
  einmal t u htu he := by
    have fall : ∀ v, (w v = some 2 ∧ (kInit w v).1 = some kHauptA) ∨
        (w v = some 3 ∧ (kInit w v).1 = some kHauptB) ∨ (kInit w v).1 = none := by
      intro v
      by_cases h2 : w v = some 2
      · exact Or.inl ⟨h2, by rw [kInit_2 h2]⟩
      · by_cases h3 : w v = some 3
        · exact Or.inr (Or.inl ⟨h3, by rw [kInit_3 h3]⟩)
        · exact Or.inr (Or.inr (by rw [kInit_sonst h2 h3]))
    rcases fall t with ⟨ht, et⟩ | ⟨ht, et⟩ | et
    · rcases fall u with ⟨hu, eu⟩ | ⟨hu, eu⟩ | eu
      · exact absurd (hw.2 t u 2 ht hu) htu
      · rw [et, eu] at he; cases he
      · rw [et, eu] at he; cases he
    · rcases fall u with ⟨hu, eu⟩ | ⟨hu, eu⟩ | eu
      · rw [et, eu] at he; cases he
      · exact absurd (hw.2 t u 3 ht hu) htu
      · rw [et, eu] at he; cases he
    · exact et

/-- The start trace of every start function the runtime uses holds no lock. -/
theorem start_offen (w : Faden → Option Nat) (u : Faden) :
    offen ((M0 w).faeden u).spur = [] := by
  rw [M0, start_faden]
  by_cases h2 : w u = some 2
  · rw [kInit_2 h2]; rfl
  · by_cases h3 : w u = some 3
    · rw [kInit_3 h3]; rfl
    · rw [kInit_sonst h2 h3]; rfl

/-- **The relation holds at the two starts.** -/
theorem r124_start (w : Faden → Option Nat) (hw : Wurzeln w) :
    R124 w (startC c124 w st0) (M0 w) := by
  refine ⟨⟨fun tb _ => ⟨rfl, fun k f _ _ => rfl⟩, fun g => nomatch g⟩, ?_, fun t => ?_⟩
  · intro L u
    show (none : Option Faden) = some u ↔ _
    constructor
    · intro h; cases h
    · rintro ⟨_, hm⟩
      rw [start_offen w u] at hm
      exact absurd hm List.not_mem_nil
  · by_cases h2 : w t = some 2
    · have e : FadenRel (w t) ((startC c124 w st0).faeden t) ((M0 w).faeden t) =
          ThreadA ((startC c124 w st0).faeden t) ((M0 w).faeden t) := by rw [h2]; rfl
      rw [e]
      refine ⟨0, startSpur (D := DR) (some kHauptA),
        [RufEreignisF.eintritt (D := DR) (some kHauptA) Env.nil ((speicherR kSp).welt [])],
        by omega, ?_, ?_, ?_⟩
      · show (match w t with
          | some f => anStart c124 f
          | none => .aus) = posA 0
        rw [h2]; rfl
      · rw [M0, start_faden, kInit_2 h2]; rfl
      · rfl
    · by_cases h3 : w t = some 3
      · have e : FadenRel (w t) ((startC c124 w st0).faeden t) ((M0 w).faeden t) =
            ThreadB ((startC c124 w st0).faeden t) ((M0 w).faeden t) := by rw [h3]; rfl
        rw [e]
        refine ⟨0, startSpur (D := DR) (some kHauptB),
          [RufEreignisF.eintritt (D := DR) (some kHauptB) Env.nil ((speicherR kSp).welt [])],
          by omega, ?_, ?_, ?_⟩
        · show (match w t with
            | some f => anStart c124 f
            | none => .aus) = posB 0
          rw [h3]; rfl
        · rw [M0, start_faden, kInit_3 h3]; rfl
        · rfl
      · have hs : (startC c124 w st0).faeden t = .aus := by
          show (match w t with
            | some f => anStart c124 f
            | none => .aus) = .aus
          rcases hwt : w t with _ | f
          · rfl
          · have := hw.1 t f hwt
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at this
            rcases this with rfl | rfl
            · exact absurd hwt h2
            · exact absurd hwt h3
        rcases hwt : w t with _ | f
        · show (startC c124 w st0).faeden t = .aus
          exact hs
        · have : f ≠ 2 := fun e => h2 (by rw [hwt, e])
          have : f ≠ 3 := fun e => h3 (by rw [hwt, e])
          unfold FadenRel
          split
          · rename_i h; cases h; contradiction
          · rename_i h; cases h; contradiction
          · exact hs

/-- **THE SIMULATION CERTIFICATE of `beispiele/124`**: every SC step of the
    emitted C, from every reachable related pair, is a segment of steps of the
    same thread of machine G that ends related and fits the step. -/
def sim124 (passes : Nat) (w : Faden → Option Nat) (hw : Wurzeln w) :
    SimC c124 (startC c124 w st0) kEL lnr PR OR passes (M0 w) where
  R := R124 w
  start := r124_start w hw
  schritt := fun K M t ℓ K' _ _ hR hs => by
    by_cases h2 : w t = some 2
    · exact schrittA w h2 hR hs
    · by_cases h3 : w t = some 3
      · exact schrittB w h3 hR hs
      · exact (schrittC_aus hs (fadenRel_sonst h2 h3 (hR.2.2 t))).elim

/-- **THE CLOSING THEOREM, STAGE (b), for `beispiele/124`.** For every
    `forever` budget, every meaning `LP` of the runtime's lock primitive,
    every start configuration `K0` of the C and every set `Echt` of real
    observations: if the runtime creates threads only at the declared roots
    and its lock primitive meets its specification (`LaufzeitC`, the runtime
    list) and the real memory model is SC for race-free programs (`DRFSC`),
    then there is the runtime's root assignment `w` with
    1. `K0` its start, and the goal theorem's runtime premise (d) for the
       corresponding G start;
    2. the emitted C DATA-RACE FREE (under the real lock primitive) -- PROVED
       from machine G, so DRF-SC applies;
    3. every SC configuration of the C related to a reachable machine of G
       (memory by `corrW`, locks, every thread) at which the goal theorem's
       conclusion `Ziel` holds;
    4. every real observation the observation of such a configuration. -/
theorem schlusssatz_124 (passes : Nat) (LP : SperrSem) (K0 : KonfC)
    (hLZ : LaufzeitC c124 [2, 3] st0 K0 LP) (Echt : BeobC → Prop)
    (hDRF : DRFSC c124 LP K0 Echt) :
    ∃ w : Faden → Option Nat, K0 = startC c124 w st0 ∧ Laufzeit kE (speicherR kSp) (kInit w) ∧
      RennfreiC c124 LP K0 ∧
      (∀ K, ErreichbarC c124 LP K0 K → ∃ M, RufErreichbarG PR OR passes (M0 w) M ∧
        R124 w K M ∧ Ziel PR kE.S.mitRuhe OR passes (M0 w) M) ∧
      ∀ b, Echt b → ∃ K M, ErreichbarC c124 LP K0 K ∧ beobC K = b ∧
        RufErreichbarG PR OR passes (M0 w) M ∧ R124 w K M ∧
        Ziel PR kE.S.mitRuhe OR passes (M0 w) M := by
  obtain ⟨w, hK0, hwf, hwi⟩ := hLZ.faeden
  have hw : Wurzeln w := ⟨hwf, hwi⟩
  subst hK0
  have hZ : ∀ M, RufErreichbarG PR OR passes (M0 w) M → Ziel PR kE.S.mitRuhe OR passes (M0 w) M :=
    fun M hM => k124_ziel kO kO_hw passes _ _ (laufzeit_w w hw) M hM
  obtain ⟨h1, h2, h3⟩ := schluss_b (sim124 passes w hw) kE.S.mitRuhe hZ LP hLZ.sperre Echt hDRF
  exact ⟨w, rfl, laufzeit_w w hw, h1, h2, h3⟩

end Satz

end K124

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.K124.schlusssatz_124
#print axioms Gabbro.Grammatik.K124.sim124
