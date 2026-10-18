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
import Grammatik.CBackend.Semantik.CNebenlaeufig
import Grammatik.Korrespondenz.Korpus.Korpus124

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
        (.ret .empty List.Perm.nil))⟩

def frA (j : Nat) : RufRahmenG DR := ⟨some kHauptA, .nil, s0R, restA j⟩

/-- The residues of a `hauptB` thread. -/
def restB : Nat → Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res DR),
    Env DR Γ × GRest DR (vertragVon DR (some kHauptB)) l Γ Λ
  | 0 => ⟨false, DR.params (some kHauptB), Signatur.anfang DR (DR.signatur (some kHauptB)), .nil,
      .ende (kP.mitRuhe.rumpf (some kHauptB))⟩
  | 1 => ⟨false, [], [], .nil, .ende (ruEnd (.cons kLocksB (.ret .empty List.Perm.nil)))⟩
  | 2 => ⟨false, [], [Res.held lL], .nil,
      .dann (ruB (.cons kRufB .nil)) (.frei lL (.dann .nil (.ende (ruEnd (V := vertragVon kD kHauptB)
        (l := false) (Γ := []) (Λ := []) (.ret .empty List.Perm.nil)))))⟩
  | 3 => ⟨false, [], [Res.held lL], .nil, .frei lL (.dann .nil (.ende (ruEnd
      (V := vertragVon kD kHauptB) (l := false) (Γ := []) (Λ := []) (.ret .empty List.Perm.nil))))⟩
  | _ => ⟨false, [], [], .nil,
      .ende (ruEnd (V := vertragVon kD kHauptB) (l := false) (Γ := []) (Λ := [])
        (.ret .empty List.Perm.nil))⟩

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
  .assignSlot KTab.konto () kI0 (.var .here) rfl kDarfK
def kS1 : Stmt kD (vertragVon kD kSetze) false [.int 0 100] kL kL :=
  .assignSlot KTab.konto () kI1 (.var .here) rfl kDarfK
def kSRet : Endblock kD (vertragVon kD kSetze) false [.int 0 100] kL := .ret .empty (by rfl)

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
      .ende (ruEnd (.cons kB0 (.cons kLocksB (.ret .empty List.Perm.nil))))⟩⟩, sp, log⟩ := hz

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
    (PopArt.wie rfl) .empty _ _ rfl (heldIn_L (by have h := ho3; rw [hZ3.1] at h; exact h))
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
      (Λ := []) (.ret .empty List.Perm.nil)) .nil rfl (heldIn_leer _)
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
  ⟨fun t ht => by rw [← hs]; exact h.1 t ht, And.intro (fun g => nomatch g) h.2.2⟩

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


