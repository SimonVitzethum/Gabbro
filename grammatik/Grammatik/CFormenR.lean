/-
  File:      Grammatik/CFormenR.lean
  Subject:   T4, the reason channel and what hangs on it: the error
             channel of `-> T or R` (`*_grund = F; return false;`,
             `*_wert = e; return true;`), the call site with its
             out-parameters (`R e; if (!f(a, &n, &e)) { … }`), `match` on
             a reason (`switch (e)`), `narrow` and the `where`/`requires`
             check (`if (!(c)) { … }`), `match` on a tagged union.

  THE STRUCTURAL PROBLEM THIS FILE SOLVES FIRST: an out-parameter is an
  ADDRESS-TAKEN local (`&n`, `&e`), and the C model keeps such a local in
  a stack block of the frame, not among the C locals `CLok` -- while the
  locals relation `EnvRel` of pass (i) puts every Gabbro variable in a C
  local. A Gabbro variable that lives in a C stack cell therefore had no
  relation at all.

  THE GHOST LOCAL. The certificate maps such a variable to a C local
  number `g` that the emitted C never mentions (a GHOST), and the
  relation reads the ghost's value out of the cell (`ghostify`): the
  Gabbro locals are related to `ghostify ρC st gs`, the C locals with
  every ghost replaced by its cell's content. Three facts make every
  lemma of passes (i)-(iii) reusable under it:
    * a C statement that does not mention a local runs the same with any
      value there (`exec_agree`, the frame rule for C locals);
    * reading the cell (`*(&n)`, the model's `ld (addrL n)`) is reading
      the ghost (`ev_zs`: a C expression with the ghost reads replaced by
      cell reads evaluates as the original under `ghostify`);
    * a statement that keeps the cells keeps the relation (`Keeps`, a
      premise per statement: the certificate proves that no store of the
      statement reaches the out-parameter cells).
  The judgements with ghosts and an error channel are `StmtCorrG`,
  `BlockSemG`, `EndSemG`; with no ghost and no channel they are pass
  (i)'s (`stmtCorr_G0`).

  THE ENCODING OF A REASON (a FINDING about the model's encoding): the
  model encodes reason `r : Fin n` as its index (`encW (.grund n) r = r`,
  CSpeicher.lean), the emitter as the DECLARED ordinal of the enum
  constant (`Buchfehler_Unbelegt = 1`, `beispiele/48`). This file keeps
  the channel generic in the constant (`Kanal.code`); where a reason
  meets `ValCorr` (a reason held in a C local or cell and read back), the
  two agree only if the elaboration numbers reasons by their declared
  ordinal (`gruende = largest ordinal + 1`, unused indices never
  produced) -- a convention stated as the premise `code = index`.
-/
import Grammatik.CFormenW

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The frame rule for C locals -/

/-- Does a C expression read local `y`? -/
def CX.liest (y : Nat) : CX → Bool
  | .lit _ => false
  | .var x => x == y
  | .cast _ e => e.liest y
  | .bin _ _ l r => l.liest y || r.liest y
  | .cmp _ _ l r => l.liest y || r.liest y
  | .lnot e => e.liest y
  | .land l r => l.liest y || r.liest y
  | .lor l r => l.liest y || r.liest y
  | .cond _ c a b => c.liest y || a.liest y || b.liest y
  | .cpl _ e => e.liest y
  | .szof _ => false
  | .addr _ => false
  | .addrL _ => false
  | .fld p _ => p.liest y
  | .slotA p i _ _ _ => p.liest y || i.liest y
  | .idx p i _ _ => p.liest y || i.liest y
  | .padd p k => p.liest y || k.liest y
  | .ld p _ => p.liest y
  | .vld p _ => p.liest y
  | .ald p _ _ => p.liest y
  | .devH _ _ => false
  | .trap => false

def CX.liestL (y : Nat) : List CX → Bool
  | [] => false
  | e :: es => e.liest y || CX.liestL y es

mutual
/-- Does a C statement mention local `y` (read it, or write it)? -/
def CS.nennt (y : Nat) : CS → Bool
  | .skip => false
  | .seq a b => CS.nennt y a || CS.nennt y b
  | .expr e => e.liest y
  | .set x _ e => x == y || e.liest y
  | .store p _ e => p.liest y || e.liest y
  | .vstore p _ e => p.liest y || e.liest y
  | .astore p _ _ e => p.liest y || e.liest y
  | .acas ok p _ ex des _ _ => ok == y || p.liest y || ex.liest y || des.liest y
  | .ite c a b => c.liest y || CS.nennt y a || CS.nennt y b
  | .sw e arms => e.liest y || CS.armsNennt y arms
  | .ret none => false
  | .ret (some (_, e)) => e.liest y
  | .brk => false
  | .cont => false
  | .goto _ => false
  | .forC c s b _ => c.liest y || CS.nennt y s || CS.nennt y b
  | .call _ args dst => CX.liestL y args || dstWrites y dst
  | .ext _ args dst => CX.liestL y args || dstWrites y dst
def CS.armsNennt (y : Nat) : List (Int × CS) → Bool
  | [] => false
  | (_, s) :: rest => CS.nennt y s || CS.armsNennt y rest
end

/-- Two C local environments agree off the list `S`. -/
def Agree (S : List Nat) (ρ1 ρ2 : CLok) : Prop := ∀ y, y ∉ S → ρ1 y = ρ2 y

theorem Agree.refl (S : List Nat) (ρ : CLok) : Agree S ρ ρ := fun _ _ => rfl

theorem Agree.upd {S : List Nat} {ρ1 ρ2 : CLok} (h : Agree S ρ1 ρ2) (x : Nat) (v : CVal) :
    Agree S (lokUpd ρ1 x v) (lokUpd ρ2 x v) := by
  intro y hy
  simp only [lokUpd]
  split
  · rfl
  · exact h y hy

/-- None of `S` is read. -/
def NichtIn (S : List Nat) (f : Nat → Bool) : Prop := ∀ y ∈ S, f y = false

variable {L : CLayout} {orc : DevOrc} {fr : Nat}

/-- AN EXPRESSION THAT READS NONE OF `S` evaluates the same under locals
    that agree off `S`. -/
theorem ev_agree (S : List Nat) : ∀ (c : CX) (st : CSt) (ρ1 ρ2 : CLok),
    NichtIn S (fun y => c.liest y) → Agree S ρ1 ρ2 → ev L orc fr c st ρ1 = ev L orc fr c st ρ2 := by
  intro c
  induction c with
  | lit v => intro _ _ _ _ _; rfl
  | var x =>
      intro st ρ1 ρ2 hn ha
      have hx : x ∉ S := by
        intro hm
        have := hn x hm
        simp [CX.liest] at this
      simp only [ev, ha x hx]
  | cast t e ih =>
      intro st ρ1 ρ2 hn ha
      have h := ih st ρ1 ρ2 (fun y hy => by have := hn y hy; simpa [CX.liest] using this) ha
      simp only [ev, h]
  | bin op t l r ihl ihr =>
      intro st ρ1 ρ2 hn ha
      have hl : ∀ st, ev L orc fr l st ρ1 = ev L orc fr l st ρ2 := fun st =>
        ihl st ρ1 ρ2 (fun y hy => by
          have := hn y hy; simp only [CX.liest, Bool.or_eq_false_iff] at this; exact this.1) ha
      have hr : ∀ st, ev L orc fr r st ρ1 = ev L orc fr r st ρ2 := fun st =>
        ihr st ρ1 ρ2 (fun y hy => by
          have := hn y hy; simp only [CX.liest, Bool.or_eq_false_iff] at this; exact this.2) ha
      simp only [ev, hl, hr]
  | cmp op t l r ihl ihr =>
      intro st ρ1 ρ2 hn ha
      have hl : ∀ st, ev L orc fr l st ρ1 = ev L orc fr l st ρ2 := fun st =>
        ihl st ρ1 ρ2 (fun y hy => by
          have := hn y hy; simp only [CX.liest, Bool.or_eq_false_iff] at this; exact this.1) ha
      have hr : ∀ st, ev L orc fr r st ρ1 = ev L orc fr r st ρ2 := fun st =>
        ihr st ρ1 ρ2 (fun y hy => by
          have := hn y hy; simp only [CX.liest, Bool.or_eq_false_iff] at this; exact this.2) ha
      simp only [ev, hl, hr]
  | lnot e ih =>
      intro st ρ1 ρ2 hn ha
      have h := ih st ρ1 ρ2 (fun y hy => by have := hn y hy; simpa [CX.liest] using this) ha
      simp only [ev, h]
  | land l r ihl ihr =>
      intro st ρ1 ρ2 hn ha
      have hl : ∀ st, ev L orc fr l st ρ1 = ev L orc fr l st ρ2 := fun st =>
        ihl st ρ1 ρ2 (fun y hy => by
          have := hn y hy; simp only [CX.liest, Bool.or_eq_false_iff] at this; exact this.1) ha
      have hr : ∀ st, ev L orc fr r st ρ1 = ev L orc fr r st ρ2 := fun st =>
        ihr st ρ1 ρ2 (fun y hy => by
          have := hn y hy; simp only [CX.liest, Bool.or_eq_false_iff] at this; exact this.2) ha
      simp only [ev, hl, hr]
  | lor l r ihl ihr =>
      intro st ρ1 ρ2 hn ha
      have hl : ∀ st, ev L orc fr l st ρ1 = ev L orc fr l st ρ2 := fun st =>
        ihl st ρ1 ρ2 (fun y hy => by
          have := hn y hy; simp only [CX.liest, Bool.or_eq_false_iff] at this; exact this.1) ha
      have hr : ∀ st, ev L orc fr r st ρ1 = ev L orc fr r st ρ2 := fun st =>
        ihr st ρ1 ρ2 (fun y hy => by
          have := hn y hy; simp only [CX.liest, Bool.or_eq_false_iff] at this; exact this.2) ha
      simp only [ev, hl, hr]
  | cond t c a b ihc iha ihb =>
      intro st ρ1 ρ2 hn ha
      have hc : ∀ st, ev L orc fr c st ρ1 = ev L orc fr c st ρ2 := fun st =>
        ihc st ρ1 ρ2 (fun y hy => by
          have := hn y hy; simp only [CX.liest, Bool.or_eq_false_iff] at this; exact this.1.1) ha
      have ha' : ∀ st, ev L orc fr a st ρ1 = ev L orc fr a st ρ2 := fun st =>
        iha st ρ1 ρ2 (fun y hy => by
          have := hn y hy; simp only [CX.liest, Bool.or_eq_false_iff] at this; exact this.1.2) ha
      have hb : ∀ st, ev L orc fr b st ρ1 = ev L orc fr b st ρ2 := fun st =>
        ihb st ρ1 ρ2 (fun y hy => by
          have := hn y hy; simp only [CX.liest, Bool.or_eq_false_iff] at this; exact this.2) ha
      simp only [ev, hc, ha', hb]
  | cpl t e ih =>
      intro st ρ1 ρ2 hn ha
      have h := ih st ρ1 ρ2 (fun y hy => by have := hn y hy; simpa [CX.liest] using this) ha
      simp only [ev, h]
  | szof n => intro _ _ _ _ _; rfl
  | addr b => intro _ _ _ _ _; rfl
  | addrL x => intro _ _ _ _ _; rfl
  | fld p off ih =>
      intro st ρ1 ρ2 hn ha
      have h := ih st ρ1 ρ2 (fun y hy => by have := hn y hy; simpa [CX.liest] using this) ha
      simp only [ev, h]
  | slotA p i n ss off ihp ihi =>
      intro st ρ1 ρ2 hn ha
      have hp : ∀ st, ev L orc fr p st ρ1 = ev L orc fr p st ρ2 := fun st =>
        ihp st ρ1 ρ2 (fun y hy => by
          have := hn y hy; simp only [CX.liest, Bool.or_eq_false_iff] at this; exact this.1) ha
      have hi : ∀ st, ev L orc fr i st ρ1 = ev L orc fr i st ρ2 := fun st =>
        ihi st ρ1 ρ2 (fun y hy => by
          have := hn y hy; simp only [CX.liest, Bool.or_eq_false_iff] at this; exact this.2) ha
      simp only [ev, hp, hi]
  | idx p i n es ihp ihi =>
      intro st ρ1 ρ2 hn ha
      have hp : ∀ st, ev L orc fr p st ρ1 = ev L orc fr p st ρ2 := fun st =>
        ihp st ρ1 ρ2 (fun y hy => by
          have := hn y hy; simp only [CX.liest, Bool.or_eq_false_iff] at this; exact this.1) ha
      have hi : ∀ st, ev L orc fr i st ρ1 = ev L orc fr i st ρ2 := fun st =>
        ihi st ρ1 ρ2 (fun y hy => by
          have := hn y hy; simp only [CX.liest, Bool.or_eq_false_iff] at this; exact this.2) ha
      simp only [ev, hp, hi]
  | padd p k ihp ihk =>
      intro st ρ1 ρ2 hn ha
      have hp : ∀ st, ev L orc fr p st ρ1 = ev L orc fr p st ρ2 := fun st =>
        ihp st ρ1 ρ2 (fun y hy => by
          have := hn y hy; simp only [CX.liest, Bool.or_eq_false_iff] at this; exact this.1) ha
      have hk : ∀ st, ev L orc fr k st ρ1 = ev L orc fr k st ρ2 := fun st =>
        ihk st ρ1 ρ2 (fun y hy => by
          have := hn y hy; simp only [CX.liest, Bool.or_eq_false_iff] at this; exact this.2) ha
      simp only [ev, hp, hk]
  | ld p τ ih =>
      intro st ρ1 ρ2 hn ha
      have h := ih st ρ1 ρ2 (fun y hy => by have := hn y hy; simpa [CX.liest] using this) ha
      simp only [ev, h]
  | vld p τ ih =>
      intro st ρ1 ρ2 hn ha
      have h := ih st ρ1 ρ2 (fun y hy => by have := hn y hy; simpa [CX.liest] using this) ha
      simp only [ev, h]
  | ald p τ o ih =>
      intro st ρ1 ρ2 hn ha
      have h := ih st ρ1 ρ2 (fun y hy => by have := hn y hy; simpa [CX.liest] using this) ha
      simp only [ev, h]
  | devH d a => intro _ _ _ _ _; rfl
  | trap => intro _ _ _ _ _; rfl

theorem evArgs_agree (S : List Nat) : ∀ (args : List CX) (st : CSt) (ρ1 ρ2 : CLok),
    NichtIn S (fun y => CX.liestL y args) → Agree S ρ1 ρ2 →
    evArgs L orc fr args st ρ1 = evArgs L orc fr args st ρ2
  | [], _, _, _, _, _ => rfl
  | e :: es, st, ρ1, ρ2, hn, ha => by
      have he : ∀ st, ev L orc fr e st ρ1 = ev L orc fr e st ρ2 := fun st =>
        ev_agree S e st ρ1 ρ2 (fun y hy => by
          have := hn y hy; simp only [CX.liestL, Bool.or_eq_false_iff] at this; exact this.1) ha
      have hs : ∀ st, evArgs L orc fr es st ρ1 = evArgs L orc fr es st ρ2 := fun st =>
        evArgs_agree S es st ρ1 ρ2 (fun y hy => by
          have := hn y hy; simp only [CX.liestL, Bool.or_eq_false_iff] at this; exact this.2) ha
      simp only [evArgs, he, hs]

/-- Two outcomes agree off `S`: the same kind, state and answer, and
    locals that agree off `S`. -/
def OutAgree (S : List Nat) : COut → COut → Prop
  | .norm s r, .norm s' r' => s = s' ∧ Agree S r r'
  | .ret s v, .ret s' v' => s = s' ∧ v = v'
  | .brk s r, .brk s' r' => s = s' ∧ Agree S r r'
  | .cont s r, .cont s' r' => s = s' ∧ Agree S r r'
  | .jump l s r, .jump l' s' r' => l = l' ∧ s = s' ∧ Agree S r r'
  | _, _ => False

theorem OutAgree.abrupt {S : List Nat} {o1 o2 : COut} (h : OutAgree S o1 o2) :
    o2.abrupt = o1.abrupt := by
  cases o1 <;> cases o2 <;> simp_all [OutAgree, COut.abrupt]

theorem OutAgree.unbreak {S : List Nat} {o1 o2 : COut} (h : OutAgree S o1 o2) :
    OutAgree S o1.unbreak o2.unbreak := by
  cases o1 <;> cases o2 <;> simp_all [OutAgree, COut.unbreak]

theorem OutAgree.weiter {S : List Nat} {o1 o2 : COut} (h : OutAgree S o1 o2) (m : Nat)
    {s : CSt} {r : CLok} (hw : o1.weiter m = some (s, r)) :
    ∃ r', o2.weiter m = some (s, r') ∧ Agree S r r' := by
  cases o1 with
  | norm s1 r1 =>
      cases o2 <;> simp only [OutAgree] at h
      obtain ⟨rfl, ha⟩ := h
      simp only [COut.weiter, Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨_, rfl, ha⟩
  | cont s1 r1 =>
      cases o2 <;> simp only [OutAgree] at h
      obtain ⟨rfl, ha⟩ := h
      simp only [COut.weiter, Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨_, rfl, ha⟩
  | jump l1 s1 r1 =>
      cases o2 <;> simp only [OutAgree] at h
      obtain ⟨rfl, rfl, ha⟩ := h
      cases l1 with
      | ende m' => simp [COut.weiter] at hw
      | weiter m' =>
          simp only [COut.weiter] at hw ⊢
          split at hw
          · rename_i hm
            simp only [Option.some.injEq, Prod.mk.injEq] at hw
            obtain ⟨rfl, rfl⟩ := hw
            exact ⟨_, by rw [if_pos hm], ha⟩
          · exact absurd hw (by simp)
  | ret s1 v1 => simp [COut.weiter] at hw
  | brk s1 r1 => simp [COut.weiter] at hw

theorem OutAgree.raus {S : List Nat} {o1 o2 : COut} (h : OutAgree S o1 o2) (m : Nat)
    {o : COut} (hx : o1.raus m = some o) : ∃ o', o2.raus m = some o' ∧ OutAgree S o o' := by
  cases o1 with
  | brk s1 r1 =>
      cases o2 <;> simp only [OutAgree] at h
      obtain ⟨rfl, ha⟩ := h
      simp only [COut.raus, Option.some.injEq] at hx
      subst hx
      refine ⟨_, rfl, ?_⟩
      exact ⟨rfl, ha⟩
  | ret s1 v1 =>
      cases o2 <;> simp only [OutAgree] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [COut.raus, Option.some.injEq] at hx
      subst hx
      refine ⟨_, rfl, ?_⟩
      exact ⟨rfl, rfl⟩
  | jump l1 s1 r1 =>
      cases o2 <;> simp only [OutAgree] at h
      obtain ⟨rfl, rfl, ha⟩ := h
      cases l1 with
      | ende m' =>
          simp only [COut.raus] at hx ⊢
          split at hx
          · rename_i hm
            simp only [Option.some.injEq] at hx
            subst hx
            rw [if_pos hm]
            refine ⟨_, rfl, ?_⟩
            exact ⟨rfl, ha⟩
          · rename_i hm
            simp only [Option.some.injEq] at hx
            subst hx
            rw [if_neg hm]
            refine ⟨_, rfl, ?_⟩
            exact ⟨rfl, rfl, ha⟩
      | weiter m' =>
          simp only [COut.raus] at hx ⊢
          split at hx
          · exact absurd hx (by simp)
          · rename_i hm
            simp only [Option.some.injEq] at hx
            subst hx
            rw [if_neg hm]
            refine ⟨_, rfl, ?_⟩
            exact ⟨rfl, rfl, ha⟩
  | norm s1 r1 => simp [COut.raus] at hx
  | cont s1 r1 => simp [COut.raus] at hx

theorem armsNennt_lookup (y : Nat) : ∀ (arms : List (Int × CS)) (k : Int) (s : CS),
    CS.armsNennt y arms = false → arms.lookup k = some s → s.nennt y = false
  | [], _, _, _, h => by simp at h
  | (k', s') :: rest, k, s, hw, hl => by
      simp only [CS.armsNennt, Bool.or_eq_false_iff] at hw
      rw [List.lookup_cons] at hl
      cases hk : (k == k') with
      | true => rw [hk] at hl; cases hl; exact hw.1
      | false => rw [hk] at hl; exact armsNennt_lookup y rest k s hw.2 hl

theorem putDst_agree {S : List Nat} {dst : Option (Nat × CTy)} {rv : Option CVal}
    {ρ1 ρ2 ρ1' : CLok} (hd : NichtIn S (fun y => dstWrites y dst)) (ha : Agree S ρ1 ρ2)
    (h : putDst dst rv ρ1 = some ρ1') : ∃ ρ2', putDst dst rv ρ2 = some ρ2' ∧ Agree S ρ1' ρ2' := by
  cases dst with
  | none =>
      simp only [putDst, Option.some.injEq] at h
      subst h
      exact ⟨ρ2, rfl, ha⟩
  | some p =>
      obtain ⟨x, τ⟩ := p
      cases rv with
      | none => simp [putDst] at h
      | some v =>
          simp only [putDst] at h ⊢
          split at h
          · rename_i v' hv
            simp only [Option.some.injEq] at h
            subst h
            exact ⟨_, rfl, ha.upd x v'⟩
          · exact absurd h (by simp)

section Rahmen

variable {CR XR : CCallR}

theorem nichtIn_or {S : List Nat} {f g : Nat → Bool} (h : NichtIn S (fun y => f y || g y)) :
    NichtIn S f ∧ NichtIn S g :=
  ⟨fun y hy => by have := h y hy; simp only [Bool.or_eq_false_iff] at this; exact this.1,
   fun y hy => by have := h y hy; simp only [Bool.or_eq_false_iff] at this; exact this.2⟩

theorem nichtIn_beq {S : List Nat} {x : Nat} (h : NichtIn S (fun y => x == y)) : x ∉ S := by
  intro hx
  have := h x hx
  simp at this

/-- THE FRAME RULE FOR C LOCALS: a statement that does not mention any
    local of `S` runs the same from locals that agree off `S`, and its
    outcome agrees off `S`. -/
theorem exec_agree (S : List Nat) {cs : CS} {st : CSt} {ρ1 : CLok} {o1 : COut}
    (h : Exec L orc fr CR XR cs st ρ1 o1) :
    NichtIn S (fun y => cs.nennt y) → ∀ ρ2, Agree S ρ1 ρ2 →
      ∃ o2, Exec L orc fr CR XR cs st ρ2 o2 ∧ OutAgree S o1 o2 := by
  induction h with
  | skip => intro _ ρ2 ha; exact ⟨_, Exec.skip, rfl, ha⟩
  | seqN _ _ iha ihb =>
      intro hn ρ2 ha
      obtain ⟨hna, hnb⟩ := nichtIn_or hn
      obtain ⟨o2, h2, hA⟩ := iha hna ρ2 ha
      cases o2 <;> simp only [OutAgree] at hA
      obtain ⟨rfl, hA'⟩ := hA
      obtain ⟨o3, h3, hB⟩ := ihb hnb _ hA'
      exact ⟨o3, Exec.seqN h2 h3, hB⟩
  | seqX _ hx iha =>
      intro hn ρ2 ha
      obtain ⟨hna, -⟩ := nichtIn_or hn
      obtain ⟨o2, h2, hA⟩ := iha hna ρ2 ha
      exact ⟨o2, Exec.seqX h2 (by rw [hA.abrupt]; exact hx), hA⟩
  | @expr e st ρ v st1 hev =>
      intro hn ρ2 ha
      refine ⟨_, Exec.expr (by rw [← ev_agree S e st ρ ρ2 hn ha]; exact hev), rfl, ha⟩
  | @set x τ e st ρ v st1 v' hev hc =>
      intro hn ρ2 ha
      obtain ⟨hx, he⟩ := nichtIn_or hn
      exact ⟨_, Exec.set (by rw [← ev_agree S e st ρ ρ2 he ha]; exact hev) hc, rfl, ha.upd x v'⟩
  | @store p τ e st ρ q st1 v st2 v' st3 hp he hc hs =>
      intro hn ρ2 ha
      obtain ⟨hnp, hne⟩ := nichtIn_or hn
      exact ⟨_, Exec.store (by rw [← ev_agree S p st ρ ρ2 hnp ha]; exact hp)
        (by rw [← ev_agree S e st1 ρ ρ2 hne ha]; exact he) hc hs, rfl, ha⟩
  | @vstore p τ e st ρ q st1 v st2 n st3 hp he hc hs =>
      intro hn ρ2 ha
      obtain ⟨hnp, hne⟩ := nichtIn_or hn
      exact ⟨_, Exec.vstore (by rw [← ev_agree S p st ρ ρ2 hnp ha]; exact hp)
        (by rw [← ev_agree S e st1 ρ ρ2 hne ha]; exact he) hc hs, rfl, ha⟩
  | @astore p τ o e st ρ q st1 v st2 n st3 hp he hc hs =>
      intro hn ρ2 ha
      obtain ⟨hnp, hne⟩ := nichtIn_or hn
      exact ⟨_, Exec.astore (by rw [← ev_agree S p st ρ ρ2 hnp ha]; exact hp)
        (by rw [← ev_agree S e st1 ρ ρ2 hne ha]; exact he) hc hs, rfl, ha⟩
  | @acas ok p τ ex des os of st ρ q st1 qx st2 v st3 d e0 b seen st4 st5 hp hx hd hc hl hcas hw =>
      intro hn ρ2 ha
      obtain ⟨h123, hnd⟩ := nichtIn_or hn
      obtain ⟨h12, hnx⟩ := nichtIn_or h123
      obtain ⟨hok, hnp⟩ := nichtIn_or h12
      exact ⟨_, Exec.acas (by rw [← ev_agree S p st ρ ρ2 hnp ha]; exact hp)
        (by rw [← ev_agree S ex st1 ρ ρ2 hnx ha]; exact hx)
        (by rw [← ev_agree S des st2 ρ ρ2 hnd ha]; exact hd) hc hl hcas hw, rfl, ha.upd ok _⟩
  | @iteT c a b st ρ v st1 o hc ht _ ih =>
      intro hn ρ2 ha
      obtain ⟨h12, -⟩ := nichtIn_or hn
      obtain ⟨hnc, hna⟩ := nichtIn_or h12
      obtain ⟨o2, h2, hA⟩ := ih hna ρ2 ha
      exact ⟨o2, Exec.iteT (by rw [← ev_agree S c st ρ ρ2 hnc ha]; exact hc) ht h2, hA⟩
  | @iteF c a b st ρ v st1 o hc ht _ ih =>
      intro hn ρ2 ha
      obtain ⟨h12, hnb⟩ := nichtIn_or hn
      obtain ⟨hnc, -⟩ := nichtIn_or h12
      obtain ⟨o2, h2, hA⟩ := ih hnb ρ2 ha
      exact ⟨o2, Exec.iteF (by rw [← ev_agree S c st ρ ρ2 hnc ha]; exact hc) ht h2, hA⟩
  | @swHit e arms st ρ k st1 s o he hl _ ih =>
      intro hn ρ2 ha
      obtain ⟨hne, hnarms⟩ := nichtIn_or hn
      have hns : NichtIn S (fun y => s.nennt y) := fun y hy =>
        armsNennt_lookup y arms k s (hnarms y hy) hl
      obtain ⟨o2, h2, hA⟩ := ih hns ρ2 ha
      exact ⟨_, Exec.swHit (by rw [← ev_agree S e st ρ ρ2 hne ha]; exact he) hl h2, hA.unbreak⟩
  | @swMiss e arms st ρ k st1 he hl =>
      intro hn ρ2 ha
      obtain ⟨hne, -⟩ := nichtIn_or hn
      exact ⟨_, Exec.swMiss (by rw [← ev_agree S e st ρ ρ2 hne ha]; exact he) hl, rfl, ha⟩
  | retN => intro _ ρ2 _; exact ⟨_, Exec.retN, rfl, rfl⟩
  | @retS τ e st ρ v st1 v' he hc =>
      intro hn ρ2 ha
      exact ⟨_, Exec.retS (by rw [← ev_agree S e st ρ ρ2 hn ha]; exact he) hc, rfl, rfl⟩
  | brk => intro _ ρ2 ha; exact ⟨_, Exec.brk, rfl, ha⟩
  | cont => intro _ ρ2 ha; exact ⟨_, Exec.cont, rfl, ha⟩
  | goto => intro _ ρ2 ha; exact ⟨_, Exec.goto, rfl, rfl, ha⟩
  | @forDone c step body m st ρ v st1 hc hf =>
      intro hn ρ2 ha
      obtain ⟨h12, -⟩ := nichtIn_or hn
      obtain ⟨hnc, -⟩ := nichtIn_or h12
      exact ⟨_, Exec.forDone (by rw [← ev_agree S c st ρ ρ2 hnc ha]; exact hc) hf, rfl, ha⟩
  | @forStep c step body m st ρ v st1 o1 st2 ρ2' st3 ρ3 o hc ht _ hw _ _ ihb ihs ihr =>
      intro hn ρ2 ha
      have hn' := hn
      obtain ⟨h12, hnb⟩ := nichtIn_or hn
      obtain ⟨hnc, hns⟩ := nichtIn_or h12
      obtain ⟨o1', hb', hA1⟩ := ihb hnb ρ2 ha
      obtain ⟨r', hw', hA2⟩ := hA1.weiter m hw
      obtain ⟨o3, hs', hA3⟩ := ihs hns r' hA2
      cases o3 <;> simp only [OutAgree] at hA3
      obtain ⟨rfl, hA3'⟩ := hA3
      obtain ⟨o4, hr', hA4⟩ := ihr hn' _ hA3'
      exact ⟨o4, Exec.forStep (by rw [← ev_agree S c st ρ ρ2 hnc ha]; exact hc) ht hb' hw' hs' hr',
        hA4⟩
  | @forExit c step body m st ρ v st1 o1 o hc ht _ hx ihb =>
      intro hn ρ2 ha
      obtain ⟨h12, hnb⟩ := nichtIn_or hn
      obtain ⟨hnc, -⟩ := nichtIn_or h12
      obtain ⟨o1', hb', hA1⟩ := ihb hnb ρ2 ha
      obtain ⟨o', hx', hA2⟩ := hA1.raus m hx
      exact ⟨o', Exec.forExit (by rw [← ev_agree S c st ρ ρ2 hnc ha]; exact hc) ht hb' hx', hA2⟩
  | @call f args dst st ρ vs st1 st2 rv ρ' hargs hcr hd =>
      intro hn ρ2 ha
      obtain ⟨hna, hnd⟩ := nichtIn_or hn
      obtain ⟨ρ2', hd', hA⟩ := putDst_agree hnd ha hd
      exact ⟨_, Exec.call (by rw [← evArgs_agree S args st ρ ρ2 hna ha]; exact hargs) hcr hd',
        rfl, hA⟩
  | @ext n args dst st ρ vs st1 st2 rv ρ' hargs hcr hd =>
      intro hn ρ2 ha
      obtain ⟨hna, hnd⟩ := nichtIn_or hn
      obtain ⟨ρ2', hd', hA⟩ := putDst_agree hnd ha hd
      exact ⟨_, Exec.ext (by rw [← evArgs_agree S args st ρ ρ2 hna ha]; exact hargs) hcr hd',
        rfl, hA⟩

end Rahmen

/-! ## 2. Ghost locals: address-taken locals read through their cells -/

/-- The ghosts of a function body: `(g, e, τ)` -- ghost C local `g`
    stands for the address-taken local `e` of the frame, a cell of C
    type `τ` at `&e`. -/
abbrev GList := List (Nat × Nat × CTy)

/-- The content of `e`'s cell (`undef` where it cannot be read). -/
def zellWert (L : CLayout) (fr : Nat) (st : CSt) (e : Nat) (τ : CTy) : CVal :=
  match bLoad L st ⟨.stk fr e, 0⟩ τ with
  | some v => v
  | none => .undef

/-- The C locals with every ghost replaced by its cell's content. -/
def ghostify (L : CLayout) (fr : Nat) : GList → CLok → CSt → CLok
  | [], ρ, _ => ρ
  | (g, e, τ) :: gs, ρ, st => lokUpd (ghostify L fr gs ρ st) g (zellWert L fr st e τ)

/-- The cell a ghost stands for (the first entry). -/
def gsFind : GList → Nat → Option (Nat × CTy)
  | [], _ => none
  | (g, e, τ) :: gs, y => if y = g then some (e, τ) else gsFind gs y

/-- The ghost locals. -/
def geister (gs : GList) : List Nat := gs.map (·.1)

theorem ghostify_at (L : CLayout) (fr : Nat) : ∀ (gs : GList) (ρ : CLok) (st : CSt) (y : Nat),
    ghostify L fr gs ρ st y =
      match gsFind gs y with
      | some (e, τ) => zellWert L fr st e τ
      | none => ρ y
  | [], _, _, _ => rfl
  | (g, e, τ) :: gs, ρ, st, y => by
      simp only [ghostify, gsFind, lokUpd]
      by_cases hy : y = g
      · rw [if_pos hy, if_pos hy]
      · rw [if_neg hy, if_neg hy]
        exact ghostify_at L fr gs ρ st y

theorem gsFind_none : ∀ (gs : GList) (y : Nat), y ∉ geister gs → gsFind gs y = none
  | [], _, _ => rfl
  | (g, e, τ) :: gs, y, h => by
      simp only [geister, List.map_cons, List.mem_cons, not_or] at h
      simp only [gsFind, if_neg h.1]
      exact gsFind_none gs y h.2

/-- `ghostify` changes only the ghosts. -/
theorem ghostify_agree (L : CLayout) (fr : Nat) (gs : GList) (ρ : CLok) (st : CSt) :
    Agree (geister gs) ρ (ghostify L fr gs ρ st) := by
  intro y hy
  rw [ghostify_at, gsFind_none gs y hy]

/-- Two states with the same memory and lifetimes load the same. -/
theorem bLoad_sameML {L : CLayout} {st st' : CSt} (h : SameML st st') (p : CPtr) (τ : CTy) :
    bLoad L st' p τ = bLoad L st p τ := by
  obtain ⟨hm, hl⟩ := h
  unfold bLoad accOk
  rw [hm, hl]

theorem zellWert_sameML {L : CLayout} {fr : Nat} {st st' : CSt} (h : SameML st st') (e : Nat)
    (τ : CTy) : zellWert L fr st' e τ = zellWert L fr st e τ := by
  unfold zellWert
  rw [bLoad_sameML h]

theorem ghostify_sameML {L : CLayout} {fr : Nat} {st st' : CSt} (h : SameML st st') (gs : GList)
    (ρ : CLok) : ghostify L fr gs ρ st' = ghostify L fr gs ρ st := by
  funext y
  rw [ghostify_at, ghostify_at]
  split
  · exact zellWert_sameML h _ _
  · rfl

theorem bLoad_ne_undef {L : CLayout} {st : CSt} {p : CPtr} {τ : CTy} {v : CVal}
    (h : bLoad L st p τ = some v) : v ≠ .undef := by
  unfold bLoad at h
  split at h
  · split at h
    · exact absurd h (by simp)
    · rename_i w hw
      simp only [Option.some.injEq] at h
      subst h
      exact hw
  · exact absurd h (by simp)

/-- The ghost reads of a C expression replaced by reads of the cells:
    the emitted C reads the address-taken local `n` as `*(&n)`. -/
def CX.zs (gs : GList) : CX → CX
  | .lit v => .lit v
  | .var y =>
      match gsFind gs y with
      | some (e, τ) => .ld (.addrL e) τ
      | none => .var y
  | .cast t e => .cast t (e.zs gs)
  | .bin op t l r => .bin op t (l.zs gs) (r.zs gs)
  | .cmp op t l r => .cmp op t (l.zs gs) (r.zs gs)
  | .lnot e => .lnot (e.zs gs)
  | .land l r => .land (l.zs gs) (r.zs gs)
  | .lor l r => .lor (l.zs gs) (r.zs gs)
  | .cond t c a b => .cond t (c.zs gs) (a.zs gs) (b.zs gs)
  | .cpl t e => .cpl t (e.zs gs)
  | .szof n => .szof n
  | .addr b => .addr b
  | .addrL x => .addrL x
  | .fld p off => .fld (p.zs gs) off
  | .slotA p i n ss off => .slotA (p.zs gs) (i.zs gs) n ss off
  | .idx p i n es => .idx (p.zs gs) (i.zs gs) n es
  | .padd p k => .padd (p.zs gs) (k.zs gs)
  | .ld p τ => .ld (p.zs gs) τ
  | .vld p τ => .vld (p.zs gs) τ
  | .ald p τ o => .ald (p.zs gs) τ o
  | .devH d a => .devH d a
  | .trap => .trap

/-- READING THE CELL IS READING THE GHOST: from any state with the memory
    and lifetimes of `st0`, the expression with cell reads evaluates as
    the original under the ghostified locals of `st0`. -/
theorem ev_zs (gs : GList) : ∀ (c : CX) (st0 st : CSt) (ρ : CLok), SameML st0 st →
    ev L orc fr (c.zs gs) st ρ = ev L orc fr c st (ghostify L fr gs ρ st0) := by
  intro c
  induction c with
  | lit v => intro _ _ _ _; rfl
  | var y =>
      intro st0 st ρ h
      simp only [CX.zs]
      cases hf : gsFind gs y with
      | none =>
          simp only [ev]
          rw [ghostify_at, hf]
      | some p =>
          obtain ⟨e, τ⟩ := p
          simp only [ev]
          rw [ghostify_at, hf]
          simp only []
          rw [← zellWert_sameML h]
          unfold zellWert
          cases hb : bLoad L st ⟨.stk fr e, 0⟩ τ with
          | none => rfl
          | some v =>
              have hv := bLoad_ne_undef hb
              cases v with
              | undef => exact absurd rfl hv
              | int n => rfl
              | ptr q => rfl
  | cast t e ih =>
      intro st0 st ρ h
      simp only [CX.zs, ev]
      rw [ih st0 st ρ h]
  | bin op t l r ihl ihr =>
      intro st0 st ρ h
      simp only [CX.zs, ev]
      rw [ihl st0 st ρ h]
      cases h1 : ev L orc fr l st (ghostify L fr gs ρ st0) with
      | none => rfl
      | some p =>
          obtain ⟨v, st1⟩ := p
          have h' := h.trans (ev_same L orc fr l st _ v st1 h1)
          cases v <;> simp only [] <;> rw [ihr st0 st1 ρ h']
  | cmp op t l r ihl ihr =>
      intro st0 st ρ h
      simp only [CX.zs, ev]
      rw [ihl st0 st ρ h]
      cases h1 : ev L orc fr l st (ghostify L fr gs ρ st0) with
      | none => rfl
      | some p =>
          obtain ⟨v, st1⟩ := p
          have h' := h.trans (ev_same L orc fr l st _ v st1 h1)
          cases v <;> simp only [] <;> rw [ihr st0 st1 ρ h']
  | lnot e ih =>
      intro st0 st ρ h
      simp only [CX.zs, ev]
      rw [ih st0 st ρ h]
  | land l r ihl ihr =>
      intro st0 st ρ h
      simp only [CX.zs, ev]
      rw [ihl st0 st ρ h]
      cases h1 : ev L orc fr l st (ghostify L fr gs ρ st0) with
      | none => rfl
      | some p =>
          obtain ⟨v, st1⟩ := p
          have h' := h.trans (ev_same L orc fr l st _ v st1 h1)
          simp only []
          rw [ihr st0 st1 ρ h']
  | lor l r ihl ihr =>
      intro st0 st ρ h
      simp only [CX.zs, ev]
      rw [ihl st0 st ρ h]
      cases h1 : ev L orc fr l st (ghostify L fr gs ρ st0) with
      | none => rfl
      | some p =>
          obtain ⟨v, st1⟩ := p
          have h' := h.trans (ev_same L orc fr l st _ v st1 h1)
          simp only []
          rw [ihr st0 st1 ρ h']
  | cond t c a b ihc iha ihb =>
      intro st0 st ρ h
      simp only [CX.zs, ev]
      rw [ihc st0 st ρ h]
      cases h1 : ev L orc fr c st (ghostify L fr gs ρ st0) with
      | none => rfl
      | some p =>
          obtain ⟨v, st1⟩ := p
          have h' := h.trans (ev_same L orc fr c st _ v st1 h1)
          simp only []
          rw [iha st0 st1 ρ h', ihb st0 st1 ρ h']
  | cpl t e ih =>
      intro st0 st ρ h
      simp only [CX.zs, ev]
      rw [ih st0 st ρ h]
  | szof n => intro _ _ _ _; rfl
  | addr b => intro _ _ _ _; rfl
  | addrL x => intro _ _ _ _; rfl
  | fld p off ih =>
      intro st0 st ρ h
      simp only [CX.zs, ev]
      rw [ih st0 st ρ h]
  | slotA p i n ss off ihp ihi =>
      intro st0 st ρ h
      simp only [CX.zs, ev]
      rw [ihp st0 st ρ h]
      cases h1 : ev L orc fr p st (ghostify L fr gs ρ st0) with
      | none => rfl
      | some q =>
          obtain ⟨v, st1⟩ := q
          have h' := h.trans (ev_same L orc fr p st _ v st1 h1)
          cases v <;> simp only [] <;> rw [ihi st0 st1 ρ h']
  | idx p i n es ihp ihi =>
      intro st0 st ρ h
      simp only [CX.zs, ev]
      rw [ihp st0 st ρ h]
      cases h1 : ev L orc fr p st (ghostify L fr gs ρ st0) with
      | none => rfl
      | some q =>
          obtain ⟨v, st1⟩ := q
          have h' := h.trans (ev_same L orc fr p st _ v st1 h1)
          cases v <;> simp only [] <;> rw [ihi st0 st1 ρ h']
  | padd p k ihp ihk =>
      intro st0 st ρ h
      simp only [CX.zs, ev]
      rw [ihp st0 st ρ h]
      cases h1 : ev L orc fr p st (ghostify L fr gs ρ st0) with
      | none => rfl
      | some q =>
          obtain ⟨v, st1⟩ := q
          have h' := h.trans (ev_same L orc fr p st _ v st1 h1)
          cases v <;> simp only [] <;> rw [ihk st0 st1 ρ h']
  | ld p τ ih =>
      intro st0 st ρ h
      simp only [CX.zs, ev]
      rw [ih st0 st ρ h]
  | vld p τ ih =>
      intro st0 st ρ h
      simp only [CX.zs, ev]
      rw [ih st0 st ρ h]
  | ald p τ o ih =>
      intro st0 st ρ h
      simp only [CX.zs, ev]
      rw [ih st0 st ρ h]
  | devH d a => intro _ _ _ _; rfl
  | trap => intro _ _ _ _; rfl

/-! ## 3. The judgements with ghosts and an error channel -/

/-- THE ERROR CHANNEL of the current function (`-> T or R`, emitted as
    `bool f(…, T *_wert, R *_grund)`): the C locals of the two pointer
    parameters, the caller's cells they point to, the cells' C types, and
    the enum constant of each reason. A channel without a result has no
    `_wert`; its certificate sets `wx = gx`, `wp = gp`, `τw = τg`. -/
structure Kanal where
  wx : Nat
  gx : Nat
  wp : CPtr
  gp : CPtr
  τw : CTy
  τg : CTy
  code : Nat → Int

/-- What a function body's correspondence is stated under beyond pass
    (i): its ghosts, and its error channel if it has one. -/
structure GCtx where
  gs : GList
  kan : Option Kanal

/-- The empty context: pass (i)'s judgements. -/
def G0 : GCtx := ⟨[], none⟩

/-- The channel's pointers are in their C locals and the caller's cells
    can be written. -/
def KanalIn (L : CLayout) (κ : Kanal) (st : CSt) (ρ : CLok) : Prop :=
  ρ κ.wx = .ptr κ.wp ∧ ρ κ.gx = .ptr κ.gp ∧ accOk L st κ.wp κ.τw .wr = true ∧
    accOk L st κ.gp κ.τg .wr = true

def KanalOk (L : CLayout) : Option Kanal → CSt → CLok → Prop
  | none, _, _ => True
  | some κ, st, ρ => KanalIn L κ st ρ

/-- The ghost cells are alive (their frame is). -/
def ZellenLeben (X : TVCtx D) (G : GCtx) (st : CSt) : Prop :=
  ∀ q ∈ G.gs, st.live (.stk X.fr q.2.1) = true

/-- THE LOCALS RELATION WITH GHOSTS: pass (i)'s relation against the
    ghostified locals, and the channel. -/
def EnvRelG (X : TVCtx D) (G : GCtx) {Γ : Ctx} (K : CEnvLay D Γ) (ρG : Env D Γ) (ρC : CLok)
    (st : CSt) : Prop :=
  EnvRel X.EL K ρG (ghostify X.EL.lay X.fr G.gs ρC st) ∧ KanalOk X.EL.lay G.kan st ρC ∧
    ZellenLeben X G st

/-- The answer of a channel function through `*_wert`. -/
def WertIn (EL : EmitLay D) (κ : Kanal) : (e : Option Ty) → ErgVal D e → CSt → Prop
  | none, _, _ => True
  | some τ, v, st => ValCorr EL τ v (st.mem κ.wp.blk κ.wp.off.toNat)

/-- A Gabbro `return`: pass (i)'s `return e;`, or, with a channel,
    `*_wert = e; return true;`. -/
def ZurG (X : TVCtx D) (G : GCtx) {V : Vertrag D} (σ' : World D) (v : ErgVal D V.erg)
    (o : COut) : Prop :=
  match G.kan with
  | none => ∃ st' cv, o = .ret st' cv ∧ corrW X.EL σ' st' ∧ RetCorr X.EL V.erg v cv
  | some κ => ∃ st', o = .ret st' (some (.int 1)) ∧ corrW X.EL σ' st' ∧ WertIn X.EL κ V.erg v st'

/-- A Gabbro reason return: only with a channel, `*_grund = F; return
    false;`. -/
def GruG (X : TVCtx D) (G : GCtx) {V : Vertrag D} (σ' : World D) (r : Fin V.gruende)
    (o : COut) : Prop :=
  match G.kan with
  | none => False
  | some κ => ∃ st', o = .ret st' (some (.int 0)) ∧ corrW X.EL σ' st' ∧
      st'.mem κ.gp.blk κ.gp.off.toNat = .int (κ.code r)

/-- THE OUTCOME RELATION with ghosts and a channel. -/
def StOutG (X : TVCtx D) (m : Nat) (G : GCtx) {Γ : Ctx} (K : CEnvLay D Γ) {V : Vertrag D}
    {l : Bool} : Ausgang V l Γ → COut → Prop
  | .ok σ' ρG', o => ∃ st' ρC', o = .norm st' ρC' ∧ corrW X.EL σ' st' ∧ EnvRelG X G K ρG' ρC' st'
  | .zurueck σ' v, o => ZurG X G σ' v o
  | .grund σ' r, o => GruG X G σ' r o
  | .leave _ σ' ρG', o =>
      ∃ st' ρC', o = .jump (.ende m) st' ρC' ∧ corrW X.EL σ' st' ∧ EnvRelG X G K ρG' ρC' st'
  | .next _ σ' ρG', o =>
      ∃ st' ρC', o = .jump (.weiter m) st' ρC' ∧ corrW X.EL σ' st' ∧ EnvRelG X G K ρG' ρC' st'
  | .logik _, _ => False
  | .hardware _, _ => False

/-- STATEMENT CORRESPONDENCE with ghosts and a channel. -/
def StmtCorrG (X : TVCtx D) (m : Nat) (G : GCtx) {Γ : Ctx} (K : CEnvLay D Γ) {V : Vertrag D}
    {l : Bool} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (cs : CS) : Prop :=
  ∀ (σ : World D) (st : CSt) (ρG : Env D Γ) (ρC : CLok), corrW X.EL σ st →
    EnvRelG X G K ρG ρC st → (execStmt X.O X.passes X.R s σ ρG).istFehler = false →
    ∃ o, Exec X.EL.lay X.orc X.fr X.CR X.XR cs st ρC o ∧
      StOutG X m G K (execStmt X.O X.passes X.R s σ ρG) o

/-- BLOCK CORRESPONDENCE with ghosts and a channel. -/
def BlockSemG (X : TVCtx D) (m : Nat) (G : GCtx) {Γ : Ctx} (K : CEnvLay D Γ) {V : Vertrag D}
    {l : Bool} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (cs : CS) : Prop :=
  ∀ (σ : World D) (st : CSt) (ρG : Env D Γ) (ρC : CLok), corrW X.EL σ st →
    EnvRelG X G K ρG ρC st → (execBlock X.O X.passes X.R b σ ρG).istFehler = false →
    ∃ o, Exec X.EL.lay X.orc X.fr X.CR X.XR cs st ρC o ∧
      StOutG X m G K (execBlock X.O X.passes X.R b σ ρG) o

/-- The outcome relation of a terminal block. `top`: falling off the end
    of a `void` body without a channel is `return;`. -/
def EndOutG (X : TVCtx D) (m : Nat) (top : Bool) (G : GCtx) {Γ : Ctx} (K : CEnvLay D Γ)
    {V : Vertrag D} {l : Bool} : EndAusgang V l Γ → COut → Prop
  | .zurueck σ' v, o => ZurG X G σ' v o ∨
      (top = true ∧ G.kan = none ∧ V.erg = none ∧ ∃ st' ρC', o = .norm st' ρC' ∧ corrW X.EL σ' st')
  | .grund σ' r, o => GruG X G σ' r o
  | .leave _ σ' ρG', o =>
      ∃ st' ρC', o = .jump (.ende m) st' ρC' ∧ corrW X.EL σ' st' ∧ EnvRelG X G K ρG' ρC' st'
  | .next _ σ' ρG', o =>
      ∃ st' ρC', o = .jump (.weiter m) st' ρC' ∧ corrW X.EL σ' st' ∧ EnvRelG X G K ρG' ρC' st'
  | .logik _, _ => False
  | .hardware _, _ => False

def EndSemG (X : TVCtx D) (m : Nat) (top : Bool) (G : GCtx) {Γ : Ctx} (K : CEnvLay D Γ)
    {V : Vertrag D} {l : Bool} {Λ : List (Res D)} (b : Endblock D V l Γ Λ) (cs : CS) : Prop :=
  ∀ (σ : World D) (st : CSt) (ρG : Env D Γ) (ρC : CLok), corrW X.EL σ st →
    EnvRelG X G K ρG ρC st → (execEnd X.O X.passes X.R b σ ρG).istFehler = false →
    ∃ o, Exec X.EL.lay X.orc X.fr X.CR X.XR cs st ρC o ∧
      EndOutG X m top G K (execEnd X.O X.passes X.R b σ ρG) o

/-! ### With no ghost and no channel, the judgements are pass (i)'s -/

theorem envRelG0 (X : TVCtx D) {Γ : Ctx} (K : CEnvLay D Γ) (ρG : Env D Γ) (ρC : CLok) (st : CSt) :
    EnvRelG X G0 K ρG ρC st ↔ EnvRel X.EL K ρG ρC :=
  ⟨fun h => h.1, fun h => ⟨h, trivial, fun q hq => by simp [G0] at hq⟩⟩

theorem stOutG0 (X : TVCtx D) (m : Nat) {Γ : Ctx} (K : CEnvLay D Γ) {V : Vertrag D} {l : Bool}
    (a : Ausgang V l Γ) (o : COut) : StOutG X m G0 K a o ↔ StOut X m K a o := by
  cases a with
  | ok σ ρ =>
      simp only [StOutG, StOut, envRelG0]
  | zurueck σ v => exact Iff.rfl
  | grund σ r => exact Iff.rfl
  | leave h σ ρ => simp only [StOutG, StOut, envRelG0]
  | next h σ ρ => simp only [StOutG, StOut, envRelG0]
  | logik e => exact Iff.rfl
  | hardware e => exact Iff.rfl

theorem stmtCorr_G0 (X : TVCtx D) (m : Nat) {Γ : Ctx} (K : CEnvLay D Γ) {V : Vertrag D}
    {l : Bool} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (cs : CS) :
    StmtCorrG X m G0 K s cs ↔ StmtCorr X m K s cs := by
  constructor
  · intro h σ st ρG ρC hc hr hnf
    obtain ⟨o, hx, hO⟩ := h σ st ρG ρC hc ((envRelG0 X K ρG ρC st).mpr hr) hnf
    exact ⟨o, hx, (stOutG0 X m K _ o).mp hO⟩
  · intro h σ st ρG ρC hc hr hnf
    obtain ⟨o, hx, hO⟩ := h σ st ρG ρC hc ((envRelG0 X K ρG ρC st).mp hr) hnf
    exact ⟨o, hx, (stOutG0 X m K _ o).mpr hO⟩

theorem blockSem_G0 (X : TVCtx D) (m : Nat) {Γ : Ctx} (K : CEnvLay D Γ) {V : Vertrag D}
    {l : Bool} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (cs : CS) :
    BlockSemG X m G0 K b cs ↔ BlockSem X m K b cs := by
  constructor
  · intro h σ st ρG ρC hc hr hnf
    obtain ⟨o, hx, hO⟩ := h σ st ρG ρC hc ((envRelG0 X K ρG ρC st).mpr hr) hnf
    exact ⟨o, hx, (stOutG0 X m K _ o).mp hO⟩
  · intro h σ st ρG ρC hc hr hnf
    obtain ⟨o, hx, hO⟩ := h σ st ρG ρC hc ((envRelG0 X K ρG ρC st).mp hr) hnf
    exact ⟨o, hx, (stOutG0 X m K _ o).mpr hO⟩

theorem endOutG0 (X : TVCtx D) (m : Nat) (top : Bool) {Γ : Ctx} (K : CEnvLay D Γ)
    {V : Vertrag D} {l : Bool} (a : EndAusgang V l Γ) (o : COut) :
    EndOutG X m top G0 K a o ↔ EndOut X m top K a o := by
  cases a with
  | zurueck σ v =>
      simp only [EndOutG, EndOut, ZurG, G0, true_and]
      constructor
      · rintro (⟨st', cv, ho, hc, hr⟩ | ⟨ht, hV, st', ρ', ho, hc⟩)
        · exact ⟨st', hc, Or.inl ⟨cv, ho, hr⟩⟩
        · exact ⟨st', hc, Or.inr ⟨ht, hV, ρ', ho⟩⟩
      · rintro ⟨st', hc, ⟨cv, ho, hr⟩ | ⟨ht, hV, ρ', ho⟩⟩
        · exact Or.inl ⟨st', cv, ho, hc, hr⟩
        · exact Or.inr ⟨ht, hV, st', ρ', ho, hc⟩
  | grund σ r => exact Iff.rfl
  | leave h σ ρ => simp only [EndOutG, EndOut, envRelG0]
  | next h σ ρ => simp only [EndOutG, EndOut, envRelG0]
  | logik e => exact Iff.rfl
  | hardware e => exact Iff.rfl

theorem endSem_G0 (X : TVCtx D) (m : Nat) (top : Bool) {Γ : Ctx} (K : CEnvLay D Γ)
    {V : Vertrag D} {l : Bool} {Λ : List (Res D)} (b : Endblock D V l Γ Λ) (cs : CS) :
    EndSemG X m top G0 K b cs ↔ EndSem X m top K b cs := by
  constructor
  · intro h σ st ρG ρC hc hr hnf
    obtain ⟨o, hx, hO⟩ := h σ st ρG ρC hc ((envRelG0 X K ρG ρC st).mpr hr) hnf
    exact ⟨o, hx, (endOutG0 X m top K _ o).mp hO⟩
  · intro h σ st ρG ρC hc hr hnf
    obtain ⟨o, hx, hO⟩ := h σ st ρG ρC hc ((envRelG0 X K ρG ρC st).mp hr) hnf
    exact ⟨o, hx, (endOutG0 X m top K _ o).mpr hO⟩

/-! ## 4. Lifting a statement of passes (i)-(iii) under ghosts -/

mutual
theorem writesV_of_nennt (y : Nat) : ∀ cs : CS, cs.nennt y = false → cs.writesV y = false
  | .skip, _ => rfl
  | .seq a b, h => by
      simp only [CS.nennt, Bool.or_eq_false_iff] at h
      simp only [CS.writesV, writesV_of_nennt y a h.1, writesV_of_nennt y b h.2, Bool.or_false]
  | .expr _, _ => rfl
  | .set x _ e, h => by
      simp only [CS.nennt, Bool.or_eq_false_iff] at h
      simp only [CS.writesV, h.1]
  | .store _ _ _, _ => rfl
  | .vstore _ _ _, _ => rfl
  | .astore _ _ _ _, _ => rfl
  | .acas ok _ _ _ _ _ _, h => by
      simp only [CS.nennt, Bool.or_eq_false_iff] at h
      simp only [CS.writesV, h.1.1.1]
  | .ite c a b, h => by
      simp only [CS.nennt, Bool.or_eq_false_iff] at h
      simp only [CS.writesV, writesV_of_nennt y a h.1.2, writesV_of_nennt y b h.2, Bool.or_false]
  | .sw e arms, h => by
      simp only [CS.nennt, Bool.or_eq_false_iff] at h
      simp only [CS.writesV]
      exact armsWritesV_of_nennt y arms h.2
  | .ret _, _ => rfl
  | .brk, _ => rfl
  | .cont, _ => rfl
  | .goto _, _ => rfl
  | .forC c s b _, h => by
      simp only [CS.nennt, Bool.or_eq_false_iff] at h
      simp only [CS.writesV, writesV_of_nennt y s h.1.2, writesV_of_nennt y b h.2, Bool.or_false]
  | .call _ _ dst, h => by
      simp only [CS.nennt, Bool.or_eq_false_iff] at h
      simp only [CS.writesV, h.2]
  | .ext _ _ dst, h => by
      simp only [CS.nennt, Bool.or_eq_false_iff] at h
      simp only [CS.writesV, h.2]
theorem armsWritesV_of_nennt (y : Nat) : ∀ arms : List (Int × CS),
    CS.armsNennt y arms = false → CS.armsWritesV y arms = false
  | [], _ => rfl
  | (_, s) :: rest, h => by
      simp only [CS.armsNennt, Bool.or_eq_false_iff] at h
      simp only [CS.armsWritesV, writesV_of_nennt y s h.1, armsWritesV_of_nennt y rest h.2,
        Bool.or_false]
end

theorem Agree.symm {S : List Nat} {ρ1 ρ2 : CLok} (h : Agree S ρ1 ρ2) : Agree S ρ2 ρ1 :=
  fun y hy => (h y hy).symm

/-- The state an outcome ends in. -/
def COut.zst : COut → CSt
  | .norm s _ => s
  | .ret s _ => s
  | .brk s _ => s
  | .cont s _ => s
  | .jump _ s _ => s

/-- A statement's run KEEPS the ghost cells (their block's contents and
    lifetime) and the lifetime of the channel's cells. -/
def Keeps (X : TVCtx D) (G : GCtx) (st st' : CSt) : Prop :=
  (∀ q ∈ G.gs, st'.mem (.stk X.fr q.2.1) = st.mem (.stk X.fr q.2.1) ∧
    st'.live (.stk X.fr q.2.1) = st.live (.stk X.fr q.2.1)) ∧
  (∀ κ, G.kan = some κ → st'.live κ.wp.blk = st.live κ.wp.blk ∧
    st'.live κ.gp.blk = st.live κ.gp.blk)

theorem keeps_sameML (X : TVCtx D) (G : GCtx) {st st' : CSt} (h : SameML st st') :
    Keeps X G st st' :=
  ⟨fun q _ => ⟨by rw [h.1], by rw [h.2]⟩, fun κ _ => ⟨by rw [h.2], by rw [h.2]⟩⟩

/-- The per-statement premise of the lift: every run from related states
    keeps the cells. -/
def KeepsG (X : TVCtx D) (G : GCtx) {Γ : Ctx} (K : CEnvLay D Γ) (cs : CS) : Prop :=
  ∀ (σ : World D) (st : CSt) (ρG : Env D Γ) (ρC : CLok) (o : COut), corrW X.EL σ st →
    EnvRelG X G K ρG ρC st → Exec X.EL.lay X.orc X.fr X.CR X.XR cs st ρC o → Keeps X G st o.zst

theorem gsFind_some_mem : ∀ (gs : GList) (y e : Nat) (τ : CTy), gsFind gs y = some (e, τ) →
    ∃ q ∈ gs, q.2.1 = e
  | [], _, _, _, h => by simp [gsFind] at h
  | (g, e', τ') :: gs, y, e, τ, h => by
      simp only [gsFind] at h
      by_cases hy : y = g
      · rw [if_pos hy] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨(g, e', τ'), List.mem_cons_self .., h.1⟩
      · rw [if_neg hy] at h
        obtain ⟨q, hq, he⟩ := gsFind_some_mem gs y e τ h
        exact ⟨q, List.mem_cons_of_mem _ hq, he⟩

theorem gsFind_none_not : ∀ (gs : GList) (y : Nat), gsFind gs y = none → y ∉ geister gs
  | [], _, _ => by simp [geister]
  | (g, e, τ) :: gs, y, h => by
      simp only [gsFind] at h
      by_cases hy : y = g
      · rw [if_pos hy] at h; exact absurd h (by simp)
      · rw [if_neg hy] at h
        have := gsFind_none_not gs y h
        simp only [geister, List.map_cons, List.mem_cons, not_or] at this ⊢
        exact ⟨hy, this⟩

theorem zellWert_keep {L : CLayout} {fr : Nat} {st st' : CSt} {e : Nat} (τ : CTy)
    (hm : st'.mem (.stk fr e) = st.mem (.stk fr e)) (hl : st'.live (.stk fr e) = st.live (.stk fr e)) :
    zellWert L fr st' e τ = zellWert L fr st e τ := by
  unfold zellWert bLoad accOk
  show (match (if (match L (CBlk.stk fr e) with
      | none => false
      | some B => st'.live (.stk fr e) && B.kind.permits .rd && decide (0 ≤ (0 : Int)) &&
          decide (B.lay.cell (0 : Int).toNat = some τ)) = true then
        (match st'.mem (.stk fr e) (0 : Int).toNat with | .undef => none | v => some v) else none) with
      | some v => v | none => .undef) = _
  rw [hm, hl]
  rfl

theorem accOk_live {L : CLayout} {st st' : CSt} {p : CPtr} {τ : CTy} {md : AccMode}
    (h : st'.live p.blk = st.live p.blk) : accOk L st' p τ md = accOk L st p τ md := by
  unfold accOk
  rw [h]

/-- The ghosts come back: after a run of a statement that does not
    mention them, the ghostified outcome locals are the outcome locals of
    the run under the ghostified entry locals. -/
theorem ghostify_back (L : CLayout) (fr : Nat) (gs : GList) (ρC ρ' r2 : CLok) (st st' : CSt)
    (hA : Agree (geister gs) ρ' r2)
    (hg : ∀ y ∈ geister gs, ρ' y = ghostify L fr gs ρC st y)
    (hk : ∀ q ∈ gs, st'.mem (.stk fr q.2.1) = st.mem (.stk fr q.2.1) ∧
      st'.live (.stk fr q.2.1) = st.live (.stk fr q.2.1)) :
    ghostify L fr gs r2 st' = ρ' := by
  funext y
  cases hf : gsFind gs y with
  | none =>
      rw [ghostify_at, hf]
      exact (hA y (gsFind_none_not gs y hf)).symm
  | some p =>
      obtain ⟨e, τ⟩ := p
      have hy : y ∈ geister gs := by
        cases hn : decide (y ∈ geister gs) with
        | true => exact of_decide_eq_true hn
        | false =>
            have := gsFind_none gs y (of_decide_eq_false hn)
            rw [hf] at this; exact absurd this (by simp)
      rw [ghostify_at, hf, hg y hy, ghostify_at, hf]
      obtain ⟨q, hq, hqe⟩ := gsFind_some_mem gs y e τ hf
      obtain ⟨h1, h2⟩ := hk q hq
      rw [hqe] at h1 h2
      exact zellWert_keep τ h1 h2

/-- Is a Gabbro outcome the normal one? -/
def Ausgang.istOk {V : Vertrag D} {l : Bool} {Γ : Ctx} : Ausgang V l Γ → Bool
  | .ok _ _ => true
  | _ => false

/-- Is a Gabbro outcome a `return`? -/
def Ausgang.istRueck {V : Vertrag D} {l : Bool} {Γ : Ctx} : Ausgang V l Γ → Bool
  | .zurueck _ _ => true
  | _ => false

section Heben

variable (X : TVCtx D) (m : Nat) (G : GCtx) {Γ : Ctx} (K : CEnvLay D Γ) {V : Vertrag D}
  {l : Bool}

/-- The locals part of the lift, for outcomes that carry locals. -/
theorem envRelG_nach {ρG' : Env D Γ} {ρC ρ' r2 : CLok} {st st' : CSt} {cs : CS}
    (hr' : EnvRel X.EL K ρG' ρ') (hA : Agree (geister G.gs) ρ' r2)
    (hn : NichtIn (geister G.gs) (fun y => cs.nennt y))
    (hxv : ∀ y, cs.writesV y = false → ρ' y = ghostify X.EL.lay X.fr G.gs ρC st y)
    (hxr : ∀ y, cs.writesV y = false → r2 y = ρC y)
    (hkw : ∀ κ, G.kan = some κ → cs.writesV κ.wx = false ∧ cs.writesV κ.gx = false)
    (hke : Keeps X G st st') (hk : KanalOk X.EL.lay G.kan st ρC) (hz : ZellenLeben X G st) :
    EnvRelG X G K ρG' r2 st' := by
  refine ⟨?_, ?_, fun q hq => by rw [(hke.1 q hq).2]; exact hz q hq⟩
  · rw [ghostify_back X.EL.lay X.fr G.gs ρC ρ' r2 st st' hA
      (fun y hy => hxv y (writesV_of_nennt y cs (hn y hy))) hke.1]
    exact hr'
  · revert hk
    cases hkan : G.kan with
    | none => intro _; trivial
    | some κ =>
        intro hk
        obtain ⟨hw, hg⟩ := hkw κ hkan
        obtain ⟨hl1, hl2⟩ := hke.2 κ hkan
        obtain ⟨k1, k2, k3, k4⟩ := hk
        exact ⟨by rw [hxr _ hw, k1], by rw [hxr _ hg, k2], by rw [accOk_live hl1, k3],
          by rw [accOk_live hl2, k4]⟩

/-- THE LIFT: a statement correspondence of passes (i)-(iii) holds under
    ghosts and a channel, when its C mentions no ghost, does not write
    the channel's locals, keeps the cells, and -- in a channel function --
    does not `return` (a `return` there has the channel's C form,
    `kcorr_ret`). -/
theorem liftG {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'} {cs : CS} (h : StmtCorr X m K s cs)
    (hn : NichtIn (geister G.gs) (fun y => cs.nennt y))
    (hkw : ∀ κ, G.kan = some κ → cs.writesV κ.wx = false ∧ cs.writesV κ.gx = false)
    (hkeep : KeepsG X G K cs)
    (hret : G.kan ≠ none → ∀ σ ρG, (execStmt X.O X.passes X.R s σ ρG).istRueck = false) :
    StmtCorrG X m G K s cs := by
  intro σ st ρG ρC hc hrel hnf
  obtain ⟨hr, hk, hz⟩ := hrel
  obtain ⟨o, hx, hO⟩ := h σ st ρG _ hc hr hnf
  obtain ⟨o2, hx2, hA⟩ := exec_agree (geister G.gs) hx hn ρC
    (ghostify_agree X.EL.lay X.fr G.gs ρC st).symm
  have hke := hkeep σ st ρG ρC o2 hc ⟨hr, hk, hz⟩ hx2
  refine ⟨o2, hx2, ?_⟩
  cases ha : execStmt X.O X.passes X.R s σ ρG with
  | ok σ' ρG' =>
      rw [ha] at hO
      obtain ⟨st', ρ', ho, hc', hr'⟩ := hO
      subst ho
      cases o2 with
      | norm s2 r2 =>
          obtain ⟨hs, hA'⟩ := hA
          subst hs
          exact ⟨st', r2, rfl, hc', envRelG_nach X G K hr' hA' hn
            (fun y hy => exec_keeps y hx hy ρ' rfl) (fun y hy => exec_keeps y hx2 hy r2 rfl)
            hkw hke hk hz⟩
      | _ => exact hA.elim
  | zurueck σ' v =>
      rw [ha] at hO
      obtain ⟨st', cv, ho, hc', hrc⟩ := hO
      subst ho
      cases o2 with
      | ret s2 v2 =>
          obtain ⟨hs, hv⟩ := hA
          subst hs; subst hv
          show ZurG X G σ' v (.ret st' cv)
          cases hkan : G.kan with
          | none =>
              simp only [ZurG, hkan]
              exact ⟨st', cv, rfl, hc', hrc⟩
          | some κ =>
              have := hret (by rw [hkan]; simp) σ ρG
              rw [ha] at this
              exact absurd this (by simp [Ausgang.istRueck])
      | _ => exact hA.elim
  | grund σ' r => rw [ha] at hO; exact hO.elim
  | leave hl σ' ρG' =>
      rw [ha] at hO
      obtain ⟨st', ρ', ho, hc', hr'⟩ := hO
      subst ho
      cases o2 with
      | jump l2 s2 r2 =>
          obtain ⟨hl2, hs, hA'⟩ := hA
          subst hl2; subst hs
          exact ⟨st', r2, rfl, hc', envRelG_nach X G K hr' hA' hn
            (fun y hy => exec_keeps y hx hy ρ' rfl) (fun y hy => exec_keeps y hx2 hy r2 rfl)
            hkw hke hk hz⟩
      | _ => exact hA.elim
  | next hl σ' ρG' =>
      rw [ha] at hO
      obtain ⟨st', ρ', ho, hc', hr'⟩ := hO
      subst ho
      cases o2 with
      | jump l2 s2 r2 =>
          obtain ⟨hl2, hs, hA'⟩ := hA
          subst hl2; subst hs
          exact ⟨st', r2, rfl, hc', envRelG_nach X G K hr' hA' hn
            (fun y hy => exec_keeps y hx hy ρ' rfl) (fun y hy => exec_keeps y hx2 hy r2 rfl)
            hkw hke hk hz⟩
      | _ => exact hA.elim
  | logik e => rw [ha] at hnf; exact Bool.noConfusion hnf
  | hardware e => rw [ha] at hnf; exact Bool.noConfusion hnf

end Heben

/-! ## 5. Cell reads in statements, and the block theorems with ghosts -/

/-- A leaf statement with its ghost reads replaced by cell reads (a
    compound statement is left as it is: its lemma substitutes in its own
    parts). -/
def CS.zs (gs : GList) : CS → CS
  | .expr e => .expr (e.zs gs)
  | .set x τ e => .set x τ (e.zs gs)
  | .store p τ e => .store (p.zs gs) τ (e.zs gs)
  | .vstore p τ e => .vstore (p.zs gs) τ (e.zs gs)
  | .astore p τ o e => .astore (p.zs gs) τ o (e.zs gs)
  | .acas ok p τ ex des os of => .acas ok (p.zs gs) τ (ex.zs gs) (des.zs gs) os of
  | .ret (some (τ, e)) => .ret (some (τ, e.zs gs))
  | .call f args dst => .call f (args.map (CX.zs gs)) dst
  | .ext n args dst => .ext n (args.map (CX.zs gs)) dst
  | cs => cs

/-- The leaves `CS.zs` rewrites. -/
def CS.blatt : CS → Bool
  | .skip => true
  | .expr _ => true
  | .set _ _ _ => true
  | .store _ _ _ => true
  | .vstore _ _ _ => true
  | .astore _ _ _ _ => true
  | .acas _ _ _ _ _ _ _ => true
  | .ret _ => true
  | .brk => true
  | .cont => true
  | .goto _ => true
  | .call _ _ _ => true
  | .ext _ _ _ => true
  | _ => false

theorem evArgs_zs {L : CLayout} {orc : DevOrc} {fr : Nat} (gs : GList) :
    ∀ (args : List CX) (st0 st : CSt) (ρ : CLok), SameML st0 st →
      evArgs L orc fr (args.map (CX.zs gs)) st ρ = evArgs L orc fr args st (ghostify L fr gs ρ st0)
  | [], _, _, _, _ => rfl
  | e :: es, st0, st, ρ, h => by
      simp only [List.map_cons, evArgs]
      rw [ev_zs gs e st0 st ρ h]
      cases h1 : ev L orc fr e st (ghostify L fr gs ρ st0) with
      | none => rfl
      | some p =>
          obtain ⟨v, st1⟩ := p
          have h' := h.trans (ev_same L orc fr e st _ v st1 h1)
          simp only []
          rw [evArgs_zs gs es st0 st1 ρ h']

theorem evArgs_same {L : CLayout} {orc : DevOrc} {fr : Nat} :
    ∀ (args : List CX) (st : CSt) (ρ : CLok) (vs : List CVal) (st' : CSt),
      evArgs L orc fr args st ρ = some (vs, st') → SameML st st'
  | [], st, _, _, st', h => by
      simp only [evArgs, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact SameML.refl _
  | e :: es, st, ρ, vs, st', h => by
      simp only [evArgs] at h
      split at h
      · rename_i v st1 h1
        split at h
        · rename_i vs' st2 h2
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.2]
          exact (ev_same L orc fr e st ρ v st1 h1).trans (evArgs_same es st1 ρ vs' st2 h2)
        · exact absurd h (by simp)
      · exact absurd h (by simp)

/-- A LEAF RUNS THE SAME with cell reads from the real locals as with ghost
    reads from the ghostified locals. -/
theorem exec_zs_blatt {L : CLayout} {orc : DevOrc} {fr : Nat} {CR XR : CCallR} (gs : GList)
    {cs : CS} (hb : cs.blatt = true) {st : CSt} {ρ : CLok} {o : COut}
    (h : Exec L orc fr CR XR cs st (ghostify L fr gs ρ st) o)
    (hw : ∀ y ∈ geister gs, cs.writesV y = false) :
    ∃ o', Exec L orc fr CR XR (cs.zs gs) st ρ o' ∧ OutAgree (geister gs) o o' := by
  have hA : Agree (geister gs) (ghostify L fr gs ρ st) ρ := (ghostify_agree L fr gs ρ st).symm
  cases h with
  | skip => exact ⟨_, Exec.skip, rfl, hA⟩
  | seqN _ _ => simp [CS.blatt] at hb
  | seqX _ _ => simp [CS.blatt] at hb
  | expr he =>
      exact ⟨_, Exec.expr (by rw [ev_zs gs _ st st ρ (SameML.refl _)]; exact he), rfl, hA⟩
  | @set x τ e _ _ v st1 v' he hc =>
      have hx : x ∉ geister gs := by
        intro hm; have := hw x hm; simp [CS.writesV] at this
      exact ⟨_, Exec.set (by rw [ev_zs gs _ st st ρ (SameML.refl _)]; exact he) hc, rfl, hA.upd x v'⟩
  | @store p τ e _ _ q st1 v st2 v' st3 hp he hc hs =>
      have h1 := ev_same L orc fr p st _ _ st1 hp
      exact ⟨_, Exec.store (by rw [ev_zs gs _ st st ρ (SameML.refl _)]; exact hp)
        (by rw [ev_zs gs _ st st1 ρ h1]; exact he) hc hs, rfl, hA⟩
  | @vstore p τ e _ _ q st1 v st2 n st3 hp he hc hs =>
      have h1 := ev_same L orc fr p st _ _ st1 hp
      exact ⟨_, Exec.vstore (by rw [ev_zs gs _ st st ρ (SameML.refl _)]; exact hp)
        (by rw [ev_zs gs _ st st1 ρ h1]; exact he) hc hs, rfl, hA⟩
  | @astore p τ o e _ _ q st1 v st2 n st3 hp he hc hs =>
      have h1 := ev_same L orc fr p st _ _ st1 hp
      exact ⟨_, Exec.astore (by rw [ev_zs gs _ st st ρ (SameML.refl _)]; exact hp)
        (by rw [ev_zs gs _ st st1 ρ h1]; exact he) hc hs, rfl, hA⟩
  | @acas ok p τ ex des os of _ _ q st1 qx st2 v st3 d e0 b seen st4 st5 hp hx hd hc hl hcas hwr =>
      have h1 := ev_same L orc fr p st _ _ st1 hp
      have h2 := h1.trans (ev_same L orc fr ex st1 _ _ st2 hx)
      exact ⟨_, Exec.acas (by rw [ev_zs gs _ st st ρ (SameML.refl _)]; exact hp)
        (by rw [ev_zs gs _ st st1 ρ h1]; exact hx) (by rw [ev_zs gs _ st st2 ρ h2]; exact hd)
        hc hl hcas hwr, rfl, hA.upd ok _⟩
  | iteT _ _ _ => simp [CS.blatt] at hb
  | iteF _ _ _ => simp [CS.blatt] at hb
  | swHit _ _ _ => simp [CS.blatt] at hb
  | swMiss _ _ => simp [CS.blatt] at hb
  | retN => exact ⟨_, Exec.retN, rfl, rfl⟩
  | retS he hc =>
      exact ⟨_, Exec.retS (by rw [ev_zs gs _ st st ρ (SameML.refl _)]; exact he) hc, rfl, rfl⟩
  | brk => exact ⟨_, Exec.brk, rfl, hA⟩
  | cont => exact ⟨_, Exec.cont, rfl, hA⟩
  | goto => exact ⟨_, Exec.goto, rfl, rfl, hA⟩
  | forDone _ _ => simp [CS.blatt] at hb
  | forStep _ _ _ _ _ _ => simp [CS.blatt] at hb
  | forExit _ _ _ _ => simp [CS.blatt] at hb
  | @call f args dst _ _ vs st1 st2 rv ρ' ha hc hd =>
      have hnd : NichtIn (geister gs) (fun y => dstWrites y dst) := fun y hy => by
        have := hw y hy; simpa [CS.writesV] using this
      obtain ⟨ρ2', hd', hA'⟩ := putDst_agree hnd hA hd
      exact ⟨_, Exec.call (by rw [evArgs_zs gs args st st ρ (SameML.refl _)]; exact ha) hc hd',
        rfl, hA'⟩
  | @ext n args dst _ _ vs st1 st2 rv ρ' ha hc hd =>
      have hnd : NichtIn (geister gs) (fun y => dstWrites y dst) := fun y hy => by
        have := hw y hy; simpa [CS.writesV] using this
      obtain ⟨ρ2', hd', hA'⟩ := putDst_agree hnd hA hd
      exact ⟨_, Exec.ext (by rw [evArgs_zs gs args st st ρ (SameML.refl _)]; exact ha) hc hd',
        rfl, hA'⟩

theorem writesV_zs (gs : GList) (cs : CS) (y : Nat) : (cs.zs gs).writesV y = cs.writesV y := by
  cases cs with
  | ret r => cases r with
    | none => rfl
    | some p => obtain ⟨τ, e⟩ := p; rfl
  | _ => rfl

section Blatt

variable (X : TVCtx D) (m : Nat) (G : GCtx) {Γ : Ctx} (K : CEnvLay D Γ) {V : Vertrag D}
  {l : Bool}

/-- THE LIFT FOR A LEAF THAT READS CELLS: a leaf's correspondence with
    ghost reads is the correspondence of the emitted leaf with cell
    reads. -/
theorem liftG_zs {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'} {cs : CS} (h : StmtCorr X m K s cs)
    (hb : cs.blatt = true) (hw : ∀ y ∈ geister G.gs, cs.writesV y = false)
    (hkw : ∀ κ, G.kan = some κ → cs.writesV κ.wx = false ∧ cs.writesV κ.gx = false)
    (hkeep : KeepsG X G K (cs.zs G.gs))
    (hret : G.kan ≠ none → ∀ σ ρG, (execStmt X.O X.passes X.R s σ ρG).istRueck = false) :
    StmtCorrG X m G K s (cs.zs G.gs) := by
  intro σ st ρG ρC hc hrel hnf
  obtain ⟨hr, hk, hz⟩ := hrel
  obtain ⟨o, hx, hO⟩ := h σ st ρG _ hc hr hnf
  obtain ⟨o2, hx2, hA⟩ := exec_zs_blatt G.gs hb hx hw
  have hke := hkeep σ st ρG ρC o2 hc ⟨hr, hk, hz⟩ hx2
  have hkw' : ∀ κ, G.kan = some κ → (cs.zs G.gs).writesV κ.wx = false ∧
      (cs.zs G.gs).writesV κ.gx = false := fun κ hκ => by
    rw [writesV_zs, writesV_zs]; exact hkw κ hκ
  refine ⟨o2, hx2, ?_⟩
  have hnach : ∀ {ρG' : Env D Γ} {ρ' r2 : CLok} {st' : CSt}, EnvRel X.EL K ρG' ρ' →
      Agree (geister G.gs) ρ' r2 → (∀ y, cs.writesV y = false → ρ' y = ghostify X.EL.lay X.fr G.gs ρC st y) →
      (∀ y, (cs.zs G.gs).writesV y = false → r2 y = ρC y) → Keeps X G st st' →
      EnvRelG X G K ρG' r2 st' := by
    intro ρG' ρ' r2 st' hr' hA' hxv hxr hke'
    refine ⟨?_, ?_, fun q hq => by rw [(hke'.1 q hq).2]; exact hz q hq⟩
    · rw [ghostify_back X.EL.lay X.fr G.gs ρC ρ' r2 st st' hA' (fun y hy => hxv y (hw y hy)) hke'.1]
      exact hr'
    · revert hk
      cases hkan : G.kan with
      | none => intro _; trivial
      | some κ =>
          intro hk
          obtain ⟨hw1, hg1⟩ := hkw' κ hkan
          obtain ⟨hl1, hl2⟩ := hke'.2 κ hkan
          obtain ⟨k1, k2, k3, k4⟩ := hk
          exact ⟨by rw [hxr _ hw1, k1], by rw [hxr _ hg1, k2], by rw [accOk_live hl1, k3],
            by rw [accOk_live hl2, k4]⟩
  cases ha : execStmt X.O X.passes X.R s σ ρG with
  | ok σ' ρG' =>
      rw [ha] at hO
      obtain ⟨st', ρ', ho, hc', hr'⟩ := hO
      subst ho
      cases o2 with
      | norm s2 r2 =>
          obtain ⟨hs, hA'⟩ := hA
          subst hs
          exact ⟨st', r2, rfl, hc', hnach hr' hA' (fun y hy => exec_keeps y hx hy ρ' rfl)
            (fun y hy => exec_keeps y hx2 hy r2 rfl) hke⟩
      | _ => exact hA.elim
  | zurueck σ' v =>
      rw [ha] at hO
      obtain ⟨st', cv, ho, hc', hrc⟩ := hO
      subst ho
      cases o2 with
      | ret s2 v2 =>
          obtain ⟨hs, hv⟩ := hA
          subst hs; subst hv
          show ZurG X G σ' v (.ret st' cv)
          cases hkan : G.kan with
          | none =>
              simp only [ZurG, hkan]
              exact ⟨st', cv, rfl, hc', hrc⟩
          | some κ =>
              have := hret (by rw [hkan]; simp) σ ρG
              rw [ha] at this
              exact absurd this (by simp [Ausgang.istRueck])
      | _ => exact hA.elim
  | grund σ' r => rw [ha] at hO; exact hO.elim
  | leave hl σ' ρG' =>
      rw [ha] at hO
      obtain ⟨st', ρ', ho, hc', hr'⟩ := hO
      subst ho
      cases o2 with
      | jump l2 s2 r2 =>
          obtain ⟨hl2, hs, hA'⟩ := hA
          subst hl2; subst hs
          exact ⟨st', r2, rfl, hc', hnach hr' hA' (fun y hy => exec_keeps y hx hy ρ' rfl)
            (fun y hy => exec_keeps y hx2 hy r2 rfl) hke⟩
      | _ => exact hA.elim
  | next hl σ' ρG' =>
      rw [ha] at hO
      obtain ⟨st', ρ', ho, hc', hr'⟩ := hO
      subst ho
      cases o2 with
      | jump l2 s2 r2 =>
          obtain ⟨hl2, hs, hA'⟩ := hA
          subst hl2; subst hs
          exact ⟨st', r2, rfl, hc', hnach hr' hA' (fun y hy => exec_keeps y hx hy ρ' rfl)
            (fun y hy => exec_keeps y hx2 hy r2 rfl) hke⟩
      | _ => exact hA.elim
  | logik e => rw [ha] at hnf; exact Bool.noConfusion hnf
  | hardware e => rw [ha] at hnf; exact Bool.noConfusion hnf

end Blatt

/-! ## 6. The channel's forms, the structural rules, and the block theorems -/

/-- C `bool` (`_Bool`, one byte). -/
def cBoolTy : CTy := .int false .w8

/-- `*_grund = F; return false;` -/
def retGrundCS (κ : Kanal) (r : Nat) : CS :=
  .seq (.store (.var κ.gx) κ.τg (.lit (κ.code r))) (.ret (some (cBoolTy, .lit 0)))

/-- `*_wert = e; return true;`, or `return true;` without a result. -/
def retKCS (κ : Kanal) (gs : GList) : Option CX → CS
  | none => .ret (some (cBoolTy, .lit 1))
  | some ce => .seq (.store (.var κ.wx) κ.τw (ce.zs gs)) (.ret (some (cBoolTy, .lit 1)))

theorem envRelG_same {X : TVCtx D} {G : GCtx} {Γ : Ctx} {K : CEnvLay D Γ} {ρG : Env D Γ}
    {ρC : CLok} {st st' : CSt} (hs : SameML st st') (h : EnvRelG X G K ρG ρC st) :
    EnvRelG X G K ρG ρC st' := by
  refine ⟨by rw [ghostify_sameML hs]; exact h.1, ?_, fun q hq => by rw [hs.2]; exact h.2.2 q hq⟩
  have hk := h.2.1
  revert hk
  cases G.kan with
  | none => intro _; trivial
  | some κ =>
      intro hk
      obtain ⟨k1, k2, k3, k4⟩ := hk
      exact ⟨k1, k2, (accOk_live (L := X.EL.lay) (st := st) (st' := st') (p := κ.wp) (τ := κ.τw)
        (md := .wr) (by rw [hs.2])).trans k3, (accOk_live (L := X.EL.lay) (st := st) (st' := st')
        (p := κ.gp) (τ := κ.τg) (md := .wr) (by rw [hs.2])).trans k4⟩

/-- A store into a stack block does not touch the memory relation. -/
theorem corrW_memUpd_stk {EL : EmitLay D} {σ : World D} {st : CSt} (h : corrW EL σ st)
    {f x : Nat} (o : Nat) (v : CVal) :
    corrW EL σ { st with mem := memUpd st.mem (.stk f x) o v } := by
  refine ⟨fun t ht => ?_, fun g hg => ?_⟩
  · obtain ⟨hl, hc⟩ := h.1 t ht
    refine ⟨hl, fun k fl hk0 hk => ?_⟩
    dsimp only
    rw [memUpd_other _ _ _ _ _ _ (by intro e; cases e.1)]
    exact hc k fl hk0 hk
  · obtain ⟨hl, hc⟩ := h.2 g hg
    refine ⟨hl, ?_⟩
    dsimp only
    rw [memUpd_other _ _ _ _ _ _ (by intro e; cases e.1)]
    exact hc

theorem valFits_of_convV {τ : CTy} {v v' : CVal} (h : convV τ v = some v') : valFits τ v' = true := by
  cases τ with
  | int s w =>
      cases v with
      | int n =>
          simp only [convV] at h
          split at h
          · rename_i b hb
            simp only [Option.some.injEq] at h
            subst h
            simp only [valFits, decide_eq_true_eq]
            unfold conv at hb
            by_cases hr : (⟨s, w⟩ : CIT).lo ≤ n ∧ n ≤ (⟨s, w⟩ : CIT).hi
            · rw [if_pos hr] at hb
              simp only [Option.some.injEq] at hb
              subst hb
              exact hr
            · rw [if_neg hr] at hb
              by_cases hs : (⟨s, w⟩ : CIT).sgn = true
              · rw [if_pos hs] at hb; exact absurd hb (by simp)
              · rw [if_neg hs] at hb
                have hs' : s = false := by simpa using hs
                subst hs'
                obtain ⟨r, hr', h0, h1⟩ := conv_u (t := ⟨false, w⟩) rfl n
                unfold conv at hr'
                rw [if_neg hr, if_neg (by simp)] at hr'
                simp only [Option.some.injEq] at hb hr'
                rw [← hb, hr']
                exact ⟨by show cLo false w ≤ r; unfold cLo; simp; exact h0, h1⟩
          · exact absurd h (by simp)
      | ptr p => simp [convV] at h
      | undef => simp [convV] at h
  | ptr =>
      cases v with
      | ptr p =>
          simp only [convV, Option.some.injEq] at h
          subst h; rfl
      | int n => simp [convV] at h
      | undef => simp [convV] at h

section Kanalformen

variable {L : CLayout} {orc : DevOrc} {fr : Nat} {CR XR : CCallR}

/-- The run of `*_grund = F; return false;`. -/
theorem retGrund_run (κ : Kanal) (r : Nat) {st : CSt} {ρC : CLok} {EL : EmitLay D} {σ : World D}
    (hk : KanalIn L κ st ρC) (hfit : valFits κ.τg (.int (κ.code r)) = true)
    {f x : Nat} (hstk : κ.gp.blk = .stk f x) (hc : corrW EL σ st) :
    ∃ st', Exec L orc fr CR XR (retGrundCS κ r) st ρC (.ret st' (some (.int 0))) ∧
      corrW EL σ st' ∧ st'.mem κ.gp.blk κ.gp.off.toNat = .int (κ.code r) := by
  obtain ⟨-, k2, -, k4⟩ := hk
  have hs := bStore_progress L st κ.gp κ.τg (.int (κ.code r)) k4 hfit
  refine ⟨_, Exec.seqN (Exec.store (by simp only [ev, k2]) rfl (convV_of_valFits _ _ hfit) hs)
    (Exec.retS rfl rfl), ?_, memUpd_same _ _ _ _⟩
  rw [hstk]
  exact corrW_memUpd_stk hc _ _

/-- The run of `*_wert = c; return true;` (`c` already evaluated). -/
theorem retWert_run (κ : Kanal) {st st1 : CSt} {ρC : CLok} {EL : EmitLay D} {σ : World D}
    {ce : CX} {c c' : CVal} (hk : KanalIn L κ st ρC) (he : ev L orc fr ce st ρC = some (c, st1))
    (hs1 : SameML st st1) (hcv : convV κ.τw c = some c') {f x : Nat} (hstk : κ.wp.blk = .stk f x)
    (hc : corrW EL σ st1) :
    ∃ st', Exec L orc fr CR XR (.seq (.store (.var κ.wx) κ.τw ce) (.ret (some (cBoolTy, .lit 1))))
        st ρC (.ret st' (some (.int 1))) ∧
      corrW EL σ st' ∧ st'.mem κ.wp.blk κ.wp.off.toNat = c' := by
  obtain ⟨k1, -, k3, -⟩ := hk
  have k3' : accOk L st1 κ.wp κ.τw .wr = true :=
    (accOk_live (L := L) (st := st) (st' := st1) (p := κ.wp) (τ := κ.τw) (md := .wr)
      (by rw [hs1.2])).trans k3
  have hs := bStore_progress L st1 κ.wp κ.τw c' k3' (valFits_of_convV hcv)
  refine ⟨_, Exec.seqN (Exec.store (by simp only [ev, k1]) he hcv hs) (Exec.retS rfl rfl), ?_,
    memUpd_same _ _ _ _⟩
  rw [hstk]
  exact corrW_memUpd_stk hc _ _

end Kanalformen

section Struktur

variable (X : TVCtx D) (m : Nat) (G : GCtx) {V : Vertrag D} {l : Bool}

/-- The channel's answer of a `return`: none, or a corresponding
    expression that fits `*_wert`'s type. -/
def ErgCorrK {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ) (τw : CTy) :
    {e : Option Ty} → ErgExpr D Γ Λ e → Option CX → Prop
  | _, .keine, cr => cr = none
  | some τ, .wert e, cr => ∃ ce, cr = some ce ∧ ExprCorr X K ce e ∧ declOk τ τw = true

/-- A channel `return`, run. -/
theorem retK_run {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ) (κ : Kanal)
    (hkan : G.kan = some κ) {r : ErgExpr D Γ Λ V.erg} {cr : Option CX}
    (h : ErgCorrK X K κ.τw r cr) {f x : Nat} (hstk : κ.wp.blk = .stk f x)
    {σ : World D} {st : CSt} {ρG : Env D Γ} {ρC : CLok} (hc : corrW X.EL σ st)
    (hr : EnvRelG X G K ρG ρC st) :
    ∃ st', Exec X.EL.lay X.orc X.fr X.CR X.XR (retKCS κ G.gs cr) st ρC (.ret st' (some (.int 1))) ∧
      corrW X.EL σ st' ∧ WertIn X.EL κ V.erg (evalErg σ r σ ρG) st' := by
  have hk : KanalIn X.EL.lay κ st ρC := by have := hr.2.1; rw [hkan] at this; exact this
  revert h
  generalize V.erg = eg at r
  intro h
  cases r with
  | keine =>
      have hcr : cr = none := h
      subst hcr
      exact ⟨st, Exec.retS rfl rfl, hc, trivial⟩
  | wert e =>
      obtain ⟨ce, hcr, he, hd⟩ := h
      subst hcr
      obtain ⟨v, st1, h1, hv, hc1⟩ := he.run X K hc hr.1
      have h1' : ev X.EL.lay X.orc X.fr (ce.zs G.gs) st ρC = some (v, st1) := by
        rw [ev_zs G.gs ce st st ρC (SameML.refl _)]; exact h1
      have hs1 := ev_same X.EL.lay X.orc X.fr ce st _ v st1 h1
      obtain ⟨st', hx, hc', hm⟩ := retWert_run κ hk h1' hs1 (convV_of_valCorr hv hd) hstk hc1
      refine ⟨st', hx, hc', ?_⟩
      show ValCorr X.EL _ _ (st'.mem κ.wp.blk κ.wp.off.toNat)
      rw [hm]
      exact hv

variable {Γ : Ctx} (K : CEnvLay D Γ)

/-- K1. `*_grund = F; return false;` against `return R::F;`. The cell
    `*_grund` lives in a stack block of the caller. -/
theorem kcorr_retGrund {Λ : List (Res D)} (κ : Kanal) (hkan : G.kan = some κ)
    (r : Fin V.gruende) (hΛ : Λ.Perm V.ende) (hfit : valFits κ.τg (.int (κ.code r)) = true)
    {f x : Nat} (hstk : κ.gp.blk = .stk f x) :
    StmtCorrG X m G K (Stmt.retGrund (l := l) (Γ := Γ) r hΛ) (retGrundCS κ r) := by
  intro σ st ρG ρC hc hr _
  have hk : KanalIn X.EL.lay κ st ρC := by have := hr.2.1; rw [hkan] at this; exact this
  obtain ⟨st', hx, hc', hm⟩ := retGrund_run κ r hk hfit hstk hc
  refine ⟨_, hx, ?_⟩
  show GruG X G σ r _
  simp only [GruG, hkan]
  exact ⟨st', rfl, hc', hm⟩

/-- K2. `*_wert = e; return true;` (or `return true;`) against `return e;`
    in a channel function. -/
theorem kcorr_ret {Λ : List (Res D)} (κ : Kanal) (hkan : G.kan = some κ)
    {r : ErgExpr D Γ Λ V.erg} {cr : Option CX} (hΛ : Λ.Perm V.ende) (h : ErgCorrK X K κ.τw r cr)
    {f x : Nat} (hstk : κ.wp.blk = .stk f x) :
    StmtCorrG X m G K (Stmt.ret (l := l) r hΛ) (retKCS κ G.gs cr) := by
  intro σ st ρG ρC hc hr _
  obtain ⟨st', hx, hc', hw⟩ := retK_run X G K κ hkan h hstk
    ((corrW_lese _ _ _ _ _).mpr hc : corrW X.EL (σ.lese Λ r.orte) st) hr
  refine ⟨_, hx, ?_⟩
  show ZurG X G _ _ _
  simp only [ZurG, hkan]
  exact ⟨st', rfl, hc', hw⟩

/-- S6 with ghosts: `if (c) { … } else { … }`, the condition reading the
    cells. -/
theorem gcorr_ite {Λ Λ' : List (Res D)} {c : Expr D Γ Λ .bool} {t e : Block D V l Γ Λ Λ'}
    {cc : CX} {ct ce : CS} (hc : ExprCorr X K cc c) (ht : BlockSemG X m G K t ct)
    (he : BlockSemG X m G K e ce) :
    StmtCorrG X m G K (Stmt.ite c t e) (.ite (cc.zs G.gs) ct ce) := by
  intro σ st ρG ρC hcw hr hnf
  have hc' : corrW X.EL (σ.lese Λ c.orte) st := (corrW_lese _ _ _ _ _).mpr hcw
  obtain ⟨st1, h1, hc1⟩ := hc.runB X K hc' hr.1
  have hs1 := ev_same X.EL.lay X.orc X.fr cc st _ _ st1 h1
  have h1' : ev X.EL.lay X.orc X.fr (cc.zs G.gs) st ρC =
      some (.int (b2i (wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρG))), st1) := by
    rw [ev_zs G.gs cc st st ρC (SameML.refl _)]; exact h1
  have hr1 := envRelG_same hs1 hr
  have hex : execStmt X.O X.passes X.R (Stmt.ite c t e) σ ρG =
      if wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρG) then
        execBlock X.O X.passes X.R t (σ.lese Λ c.orte) ρG
      else execBlock X.O X.passes X.R e (σ.lese Λ c.orte) ρG := rfl
  rw [hex] at hnf ⊢
  cases hb : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρG) with
  | true =>
      rw [hb] at h1'
      simp only [hb, if_true] at hnf ⊢
      obtain ⟨o, hx, hO⟩ := ht _ st1 ρG ρC hc1 hr1 hnf
      exact ⟨o, Exec.iteT h1' (truth_b2i true) hx, hO⟩
  | false =>
      rw [hb] at h1'
      simp only [hb, Bool.false_eq_true, if_false] at hnf ⊢
      obtain ⟨o, hx, hO⟩ := he _ st1 ρG ρC hc1 hr1 hnf
      exact ⟨o, Exec.iteF h1' (truth_b2i false) hx, hO⟩

end Struktur

theorem ghostify_upd (L : CLayout) (fr : Nat) (gs : GList) (ρ : CLok) (st : CSt) {x : Nat}
    (hx : x ∉ geister gs) (c : CVal) :
    ghostify L fr gs (lokUpd ρ x c) st = lokUpd (ghostify L fr gs ρ st) x c := by
  funext y
  rw [ghostify_at]
  simp only [lokUpd]
  cases hf : gsFind gs y with
  | none =>
      simp only []
      rw [ghostify_at, hf]
  | some p =>
      obtain ⟨e, τ⟩ := p
      have hy : y ≠ x := by
        intro hyx
        subst hyx
        have := gsFind_none gs y hx
        rw [hf] at this; exact absurd this (by simp)
      simp only [if_neg hy]
      rw [ghostify_at, hf]

theorem envRelG_push {X : TVCtx D} {G : GCtx} {Γ : Ctx} {K : CEnvLay D Γ} (hK : K.okB = true)
    {x : Nat} (hf : K.freshB x = true) (hg : x ∉ geister G.gs)
    (hkx : ∀ κ, G.kan = some κ → x ≠ κ.wx ∧ x ≠ κ.gx)
    {ρG : Env D Γ} {ρC : CLok} {st : CSt} (h : EnvRelG X G K ρG ρC st) {τ : Ty} (v : Wert D τ)
    (c : CVal) (hv : ValCorr X.EL τ v c) :
    EnvRelG X G (K.push τ x) (.cons v ρG) (lokUpd ρC x c) st := by
  refine ⟨?_, ?_, h.2.2⟩
  · rw [ghostify_upd X.EL.lay X.fr G.gs ρC st hg c]
    exact envRel_push hK hf h.1 v c hv
  · have hk := h.2.1
    revert hk hkx
    cases G.kan with
    | none => intro _ _; trivial
    | some κ =>
        intro hkx hk
        obtain ⟨hx1, hx2⟩ := hkx κ rfl
        obtain ⟨k1, k2, k3, k4⟩ := hk
        refine ⟨?_, ?_, k3, k4⟩
        · simp only [lokUpd]; rw [if_neg (Ne.symm hx1)]; exact k1
        · simp only [lokUpd]; rw [if_neg (Ne.symm hx2)]; exact k2

theorem envRelG_pop {X : TVCtx D} {G : GCtx} {Γ : Ctx} {K : CEnvLay D Γ} {τ : Ty} {x : Nat}
    {ρG : Env D (τ :: Γ)} {ρC : CLok} {st : CSt} (h : EnvRelG X G (K.push τ x) ρG ρC st) :
    EnvRelG X G K ρG.tail ρC st :=
  ⟨envRel_pop h.1, h.2⟩

theorem stOutG_schrumpf (X : TVCtx D) (m : Nat) (G : GCtx) {Γ : Ctx} {K : CEnvLay D Γ} {τ : Ty}
    {x : Nat} {V : Vertrag D} {l : Bool} (a : Ausgang V l (τ :: Γ)) (o : COut)
    (h : StOutG X m G (K.push τ x) a o) : StOutG X m G K a.schrumpf o := by
  cases a with
  | ok σ ρ =>
      obtain ⟨st', ρC', ho, hc, hr⟩ := h
      exact ⟨st', ρC', ho, hc, envRelG_pop hr⟩
  | zurueck σ v => exact h
  | grund σ r => exact h
  | leave hl σ ρ =>
      obtain ⟨st', ρC', ho, hc, hr⟩ := h
      exact ⟨st', ρC', ho, hc, envRelG_pop hr⟩
  | next hl σ ρ =>
      obtain ⟨st', ρC', ho, hc, hr⟩ := h
      exact ⟨st', ρC', ho, hc, envRelG_pop hr⟩
  | logik e => exact h.elim
  | hardware e => exact h.elim

theorem zurG_abrupt {X : TVCtx D} {G : GCtx} {V : Vertrag D} {σ' : World D} {v : ErgVal D V.erg}
    {o : COut} (h : ZurG X G σ' v o) : o.abrupt = true := by
  unfold ZurG at h
  split at h
  · obtain ⟨st', cv, ho, -⟩ := h; subst ho; rfl
  · obtain ⟨st', ho, -⟩ := h; subst ho; rfl

theorem gruG_abrupt {X : TVCtx D} {G : GCtx} {V : Vertrag D} {σ' : World D} {r : Fin V.gruende}
    {o : COut} (h : GruG X G σ' r o) : o.abrupt = true := by
  unfold GruG at h
  split at h
  · exact h.elim
  · obtain ⟨st', ho, -⟩ := h; subst ho; rfl

/-- THE BLOCK CORRESPONDENCE WITH GHOSTS, as a certificate states it. -/
inductive BlockCorrG (X : TVCtx D) (m : Nat) (G : GCtx) {V : Vertrag D} {l : Bool} :
    {Γ : Ctx} → {Λ Λ' : List (Res D)} → CEnvLay D Γ → Block D V l Γ Λ Λ' → CS → Prop where
  | nil {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ} :
      BlockCorrG X m G K (Block.nil (Λ := Λ)) .skip
  | cons {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} {K : CEnvLay D Γ} {s : Stmt D V l Γ Λ Λ'}
      {rest : Block D V l Γ Λ' Λ''} {cs cr : CS} (hs : StmtCorrG X m G K s cs)
      (hr : BlockCorrG X m G K rest cr) : BlockCorrG X m G K (.cons s rest) (.seq cs cr)
  | bind {Γ : Ctx} {Λ Λ' : List (Res D)} {K : CEnvLay D Γ} {τ : Ty} {e : Expr D Γ Λ τ}
      {rest : Block D V l (τ :: Γ) Λ Λ'} {x : Nat} {τc : CTy} {ce : CX} {cr : CS}
      (hK : K.okB = true) (hf : K.freshB x = true) (hg : x ∉ geister G.gs)
      (hkx : ∀ κ, G.kan = some κ → x ≠ κ.wx ∧ x ≠ κ.gx) (he : ExprCorr X K ce e)
      (hd : declOk τ τc = true) (hr : BlockCorrG X m G (K.push τ x) rest cr) :
      BlockCorrG X m G K (.bind e rest) (.seq (.set x τc (ce.zs G.gs)) cr)
  | pre {Γ : Ctx} {Λ Λ' Λ0 : List (Res D)} {K : CEnvLay D Γ} {b : Block D V l Γ Λ Λ'}
      {τ0 : Ty} {e0 : Expr D Γ Λ0 τ0} {ce : CX} {cr : CS} (he : ExprCorr X K ce e0)
      (hr : BlockCorrG X m G K b cr) : BlockCorrG X m G K b (.seq (.expr (ce.zs G.gs)) cr)
  | sem {Γ : Ctx} {Λ Λ' : List (Res D)} {K : CEnvLay D Γ} {b : Block D V l Γ Λ Λ'} {cb : CS}
      (h : BlockSemG X m G K b cb) : BlockCorrG X m G K b cb

/-- THE BLOCK THEOREM WITH GHOSTS. -/
theorem cCorrG_block (X : TVCtx D) (m : Nat) (G : GCtx) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {K : CEnvLay D Γ} {b : Block D V l Γ Λ Λ'} {cb : CS}
    (h : BlockCorrG X m G K b cb) : BlockSemG X m G K b cb := by
  induction h with
  | nil =>
      intro σ st ρG ρC hc hr _
      exact ⟨_, Exec.skip, st, ρC, rfl, hc, hr⟩
  | @cons Γ Λ Λ' Λ'' K s rest cs cr hs _ ih =>
      intro σ st ρG ρC hc hr hnf
      have hex : execBlock X.O X.passes X.R (Block.cons s rest) σ ρG =
          match execStmt X.O X.passes X.R s σ ρG with
          | .ok σ' ρ' => execBlock X.O X.passes X.R rest σ' ρ'
          | o => o := rfl
      rw [hex] at hnf ⊢
      cases hs' : execStmt X.O X.passes X.R s σ ρG with
      | ok σ' ρ' =>
          rw [hs'] at hnf
          obtain ⟨o1, h1, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          obtain ⟨st1, ρC1, ho1, hc1, hr1⟩ := hO
          subst ho1
          obtain ⟨o2, h2, hO2⟩ := ih σ' st1 ρ' ρC1 hc1 hr1 hnf
          exact ⟨o2, Exec.seqN h1 h2, hO2⟩
      | zurueck σ' v =>
          obtain ⟨o1, h1, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          exact ⟨o1, Exec.seqX h1 (zurG_abrupt hO), hO⟩
      | grund σ' r =>
          obtain ⟨o1, h1, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          exact ⟨o1, Exec.seqX h1 (gruG_abrupt hO), hO⟩
      | leave hl σ' ρ' =>
          obtain ⟨o1, h1, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          obtain ⟨st1, ρC1, ho1, hc1, hr1⟩ := hO
          subst ho1
          exact ⟨_, Exec.seqX h1 rfl, st1, ρC1, rfl, hc1, hr1⟩
      | next hl σ' ρ' =>
          obtain ⟨o1, h1, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          obtain ⟨st1, ρC1, ho1, hc1, hr1⟩ := hO
          subst ho1
          exact ⟨_, Exec.seqX h1 rfl, st1, ρC1, rfl, hc1, hr1⟩
      | logik e => rw [hs'] at hnf; exact Bool.noConfusion hnf
      | hardware e => rw [hs'] at hnf; exact Bool.noConfusion hnf
  | @bind Γ Λ Λ' K τ e rest x τc ce cr hK hf hg hkx he hd _ ih =>
      intro σ st ρG ρC hc hr hnf
      have hex : execBlock X.O X.passes X.R (Block.bind e rest) σ ρG =
          (execBlock X.O X.passes X.R rest (σ.lese Λ e.orte)
            (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG) ρG)).schrumpf := rfl
      rw [hex] at hnf ⊢
      rw [istFehler_schrumpf] at hnf
      have hc' : corrW X.EL (σ.lese Λ e.orte) st := (corrW_lese _ _ _ _ _).mpr hc
      obtain ⟨v, st1, h1, hv, hc1⟩ := he.run X K hc' hr.1
      have hs1 := ev_same X.EL.lay X.orc X.fr ce st _ v st1 h1
      have h1' : ev X.EL.lay X.orc X.fr (ce.zs G.gs) st ρC = some (v, st1) := by
        rw [ev_zs G.gs ce st st ρC (SameML.refl _)]; exact h1
      have hr1 := envRelG_push hK hf hg hkx (envRelG_same hs1 hr) _ v hv
      obtain ⟨o, h2, hO⟩ := ih _ st1 _ (lokUpd ρC x v) hc1 hr1 hnf
      exact ⟨o, Exec.seqN (Exec.set h1' (convV_of_valCorr hv hd)) h2,
        stOutG_schrumpf X m G _ o hO⟩
  | @pre Γ Λ Λ' Λ0 K b τ0 e0 ce cr he _ ih =>
      intro σ st ρG ρC hc hr hnf
      obtain ⟨v, st1, h1, -, hc1⟩ := he.run X K hc hr.1
      have hs1 := ev_same X.EL.lay X.orc X.fr ce st _ v st1 h1
      have h1' : ev X.EL.lay X.orc X.fr (ce.zs G.gs) st ρC = some (v, st1) := by
        rw [ev_zs G.gs ce st st ρC (SameML.refl _)]; exact h1
      obtain ⟨o, h2, hO⟩ := ih σ st1 ρG ρC hc1 (envRelG_same hs1 hr) hnf
      exact ⟨o, Exec.seqN (Exec.expr h1') h2, hO⟩
  | sem h => exact h

theorem endIstFehler_schrumpfG {V : Vertrag D} {l : Bool} {Γ : Ctx} {τ : Ty}
    (a : EndAusgang V l (τ :: Γ)) : a.schrumpf.istFehler = a.istFehler := by
  cases a <;> rfl

theorem endOutG_schrumpf (X : TVCtx D) (m : Nat) (top : Bool) (G : GCtx) {Γ : Ctx}
    {K : CEnvLay D Γ} {τ : Ty} {x : Nat} {V : Vertrag D} {l : Bool} (a : EndAusgang V l (τ :: Γ))
    (o : COut) (h : EndOutG X m top G (K.push τ x) a o) : EndOutG X m top G K a.schrumpf o := by
  cases a with
  | zurueck σ v => exact h
  | grund σ r => exact h
  | leave hl σ ρ =>
      obtain ⟨st', ρC', ho, hc, hr⟩ := h
      exact ⟨st', ρC', ho, hc, envRelG_pop hr⟩
  | next hl σ ρ =>
      obtain ⟨st', ρC', ho, hc, hr⟩ := h
      exact ⟨st', ρC', ho, hc, envRelG_pop hr⟩
  | logik e => exact h.elim
  | hardware e => exact h.elim

/-- THE TERMINAL-BLOCK CORRESPONDENCE WITH GHOSTS AND A CHANNEL. -/
inductive EndCorrG (X : TVCtx D) (m : Nat) (top : Bool) (G : GCtx) {V : Vertrag D} {l : Bool} :
    {Γ : Ctx} → {Λ : List (Res D)} → CEnvLay D Γ → Endblock D V l Γ Λ → CS → Prop where
  /-- `return e;` without a channel (the answer may read a cell). -/
  | ret {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ} {r : ErgExpr D Γ Λ V.erg}
      {cr : Option (CTy × CX)} (hkan : G.kan = none) (hΛ : Λ.Perm V.ende) (h : ErgCorr X K r cr) :
      EndCorrG X m top G K (.ret r hΛ) ((CS.ret cr).zs G.gs)
  /-- The end of a `void` body without a channel. -/
  | retEnd {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ} {r : ErgExpr D Γ Λ V.erg}
      (hkan : G.kan = none) (hΛ : Λ.Perm V.ende) (htop : top = true) (hV : V.erg = none) :
      EndCorrG X m top G K (.ret r hΛ) .skip
  /-- K2 as a terminal block: `*_wert = e; return true;`. -/
  | retK {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ} {r : ErgExpr D Γ Λ V.erg}
      {cr : Option CX} (κ : Kanal) (hkan : G.kan = some κ) (hΛ : Λ.Perm V.ende)
      (h : ErgCorrK X K κ.τw r cr) {f x : Nat} (hstk : κ.wp.blk = .stk f x) :
      EndCorrG X m top G K (.ret r hΛ) (retKCS κ G.gs cr)
  /-- K1 as a terminal block: `*_grund = F; return false;`. -/
  | retGrund {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ} (κ : Kanal) (hkan : G.kan = some κ)
      (r : Fin V.gruende) (hΛ : Λ.Perm V.ende) (hfit : valFits κ.τg (.int (κ.code r)) = true)
      {f x : Nat} (hstk : κ.gp.blk = .stk f x) :
      EndCorrG X m top G K (.retGrund r hΛ) (retGrundCS κ r)
  | leave {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ} (hl : l = true) :
      EndCorrG X m top G K (Endblock.leave (Λ := Λ) hl) (.goto (.ende m))
  | next {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ} (hl : l = true) :
      EndCorrG X m top G K (Endblock.next (Λ := Λ) hl) (.goto (.weiter m))
  | cons {Γ : Ctx} {Λ Λ' : List (Res D)} {K : CEnvLay D Γ} {s : Stmt D V l Γ Λ Λ'}
      {rest : Endblock D V l Γ Λ'} {cs cr : CS} (hs : StmtCorrG X m G K s cs)
      (hr : EndCorrG X m top G K rest cr) : EndCorrG X m top G K (.cons s rest) (.seq cs cr)
  | bind {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ} {τ : Ty} {e : Expr D Γ Λ τ}
      {rest : Endblock D V l (τ :: Γ) Λ} {x : Nat} {τc : CTy} {ce : CX} {cr : CS}
      (hK : K.okB = true) (hf : K.freshB x = true) (hg : x ∉ geister G.gs)
      (hkx : ∀ κ, G.kan = some κ → x ≠ κ.wx ∧ x ≠ κ.gx) (he : ExprCorr X K ce e)
      (hd : declOk τ τc = true) (hr : EndCorrG X m top G (K.push τ x) rest cr) :
      EndCorrG X m top G K (.bind e rest) (.seq (.set x τc (ce.zs G.gs)) cr)
  | pre {Γ : Ctx} {Λ Λ0 : List (Res D)} {K : CEnvLay D Γ} {b : Endblock D V l Γ Λ}
      {τ0 : Ty} {e0 : Expr D Γ Λ0 τ0} {ce : CX} {cr : CS} (he : ExprCorr X K ce e0)
      (hr : EndCorrG X m top G K b cr) : EndCorrG X m top G K b (.seq (.expr (ce.zs G.gs)) cr)
  | sem {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ} {b : Endblock D V l Γ Λ} {cb : CS}
      (h : EndSemG X m top G K b cb) : EndCorrG X m top G K b cb
  /-- A statement that never completes normally ends the block: what
      follows it is unreachable and has no C (`locks … { … return …; }`,
      a `match` whose every arm returns or fails). -/
  | endet {Γ : Ctx} {Λ Λ' : List (Res D)} {K : CEnvLay D Γ} {s : Stmt D V l Γ Λ Λ'}
      {rest : Endblock D V l Γ Λ'} {cs : CS} (hs : StmtCorrG X m G K s cs)
      (hne : ∀ σ ρG, (execStmt X.O X.passes X.R s σ ρG).istOk = false) :
      EndCorrG X m top G K (.cons s rest) cs

/-- THE TERMINAL-BLOCK THEOREM WITH GHOSTS AND A CHANNEL. -/
theorem cCorrG_end (X : TVCtx D) (m : Nat) (top : Bool) (G : GCtx) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ} {b : Endblock D V l Γ Λ} {cb : CS}
    (h : EndCorrG X m top G K b cb) : EndSemG X m top G K b cb := by
  induction h with
  | @ret Γ Λ K r cr hkan hΛ hrc =>
      intro σ st ρG ρC hc hr _
      have hc' : corrW X.EL (σ.lese Λ r.orte) st := (corrW_lese _ _ _ _ _).mpr hc
      obtain ⟨st', cv, hx, hc1, hret⟩ := ergCorr_run X K hrc hc' hr.1
      obtain ⟨o', hx', hA⟩ := exec_zs_blatt G.gs rfl hx (fun _ _ => rfl)
      cases o' with
      | ret s2 v2 =>
          obtain ⟨hs, hv⟩ := hA
          subst hs; subst hv
          refine ⟨_, hx', Or.inl ?_⟩
          simp only [ZurG, hkan]
          exact ⟨_, _, rfl, hc1, hret⟩
      | _ => exact hA.elim
  | @retEnd Γ Λ K r hkan hΛ htop hV =>
      intro σ st ρG ρC hc hr _
      exact ⟨_, Exec.skip, Or.inr ⟨htop, hkan, hV, st, ρC, rfl, (corrW_lese _ _ _ _ _).mpr hc⟩⟩
  | @retK Γ Λ K r cr κ hkan hΛ hrc f x hstk =>
      intro σ st ρG ρC hc hr _
      obtain ⟨st', hx, hc', hw⟩ := retK_run X G K κ hkan hrc hstk
        ((corrW_lese _ _ _ _ _).mpr hc : corrW X.EL (σ.lese Λ r.orte) st) hr
      refine ⟨_, hx, Or.inl ?_⟩
      simp only [ZurG, hkan]
      exact ⟨st', rfl, hc', hw⟩
  | @retGrund Γ Λ K κ hkan r hΛ hfit f x hstk =>
      intro σ st ρG ρC hc hr _
      have hk : KanalIn X.EL.lay κ st ρC := by have := hr.2.1; rw [hkan] at this; exact this
      obtain ⟨st', hx, hc', hm⟩ := retGrund_run κ r hk hfit hstk hc
      refine ⟨_, hx, ?_⟩
      show GruG X G σ r _
      simp only [GruG, hkan]
      exact ⟨st', rfl, hc', hm⟩
  | leave hl =>
      intro σ st ρG ρC hc hr _
      exact ⟨_, Exec.goto, st, ρC, rfl, hc, hr⟩
  | next hl =>
      intro σ st ρG ρC hc hr _
      exact ⟨_, Exec.goto, st, ρC, rfl, hc, hr⟩
  | @cons Γ Λ Λ' K s rest cs cr hs _ ih =>
      intro σ st ρG ρC hc hr hnf
      have hex : execEnd X.O X.passes X.R (Endblock.cons s rest) σ ρG =
          match execStmt X.O X.passes X.R s σ ρG with
          | .ok σ' ρ' => execEnd X.O X.passes X.R rest σ' ρ'
          | .zurueck σ' v => .zurueck σ' v
          | .grund σ' r => .grund σ' r
          | .leave h σ' ρ' => .leave h σ' ρ'
          | .next h σ' ρ' => .next h σ' ρ'
          | .logik e => .logik e
          | .hardware e => .hardware e := rfl
      rw [hex] at hnf ⊢
      cases hs' : execStmt X.O X.passes X.R s σ ρG with
      | ok σ' ρ' =>
          rw [hs'] at hnf
          obtain ⟨o1, h1, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          obtain ⟨st1, ρC1, ho1, hc1, hr1⟩ := hO
          subst ho1
          obtain ⟨o2, h2, hO2⟩ := ih σ' st1 ρ' ρC1 hc1 hr1 hnf
          exact ⟨o2, Exec.seqN h1 h2, hO2⟩
      | zurueck σ' v =>
          obtain ⟨o1, h1, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          exact ⟨o1, Exec.seqX h1 (zurG_abrupt hO), Or.inl hO⟩
      | grund σ' r =>
          obtain ⟨o1, h1, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          exact ⟨o1, Exec.seqX h1 (gruG_abrupt hO), hO⟩
      | leave hl σ' ρ' =>
          obtain ⟨o1, h1, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          obtain ⟨st1, ρC1, ho1, hc1, hr1⟩ := hO
          subst ho1
          exact ⟨_, Exec.seqX h1 rfl, st1, ρC1, rfl, hc1, hr1⟩
      | next hl σ' ρ' =>
          obtain ⟨o1, h1, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          obtain ⟨st1, ρC1, ho1, hc1, hr1⟩ := hO
          subst ho1
          exact ⟨_, Exec.seqX h1 rfl, st1, ρC1, rfl, hc1, hr1⟩
      | logik e => rw [hs'] at hnf; exact Bool.noConfusion hnf
      | hardware e => rw [hs'] at hnf; exact Bool.noConfusion hnf
  | @bind Γ Λ K τ e rest x τc ce cr hK hf hg hkx he hd _ ih =>
      intro σ st ρG ρC hc hr hnf
      have hex : execEnd X.O X.passes X.R (Endblock.bind e rest) σ ρG =
          (execEnd X.O X.passes X.R rest (σ.lese Λ e.orte)
            (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG) ρG)).schrumpf := rfl
      rw [hex] at hnf ⊢
      rw [endIstFehler_schrumpfG] at hnf
      have hc' : corrW X.EL (σ.lese Λ e.orte) st := (corrW_lese _ _ _ _ _).mpr hc
      obtain ⟨v, st1, h1, hv, hc1⟩ := he.run X K hc' hr.1
      have hs1 := ev_same X.EL.lay X.orc X.fr ce st _ v st1 h1
      have h1' : ev X.EL.lay X.orc X.fr (ce.zs G.gs) st ρC = some (v, st1) := by
        rw [ev_zs G.gs ce st st ρC (SameML.refl _)]; exact h1
      have hr1 := envRelG_push hK hf hg hkx (envRelG_same hs1 hr) _ v hv
      obtain ⟨o, h2, hO⟩ := ih _ st1 _ (lokUpd ρC x v) hc1 hr1 hnf
      exact ⟨o, Exec.seqN (Exec.set h1' (convV_of_valCorr hv hd)) h2,
        endOutG_schrumpf X m top G _ o hO⟩
  | @pre Γ Λ Λ0 K b τ0 e0 ce cr he _ ih =>
      intro σ st ρG ρC hc hr hnf
      obtain ⟨v, st1, h1, -, hc1⟩ := he.run X K hc hr.1
      have hs1 := ev_same X.EL.lay X.orc X.fr ce st _ v st1 h1
      have h1' : ev X.EL.lay X.orc X.fr (ce.zs G.gs) st ρC = some (v, st1) := by
        rw [ev_zs G.gs ce st st ρC (SameML.refl _)]; exact h1
      obtain ⟨o, h2, hO⟩ := ih σ st1 ρG ρC hc1 (envRelG_same hs1 hr) hnf
      exact ⟨o, Exec.seqN (Exec.expr h1') h2, hO⟩
  | sem h => exact h
  | @endet Γ Λ Λ' K s rest cs hs hne =>
      intro σ st ρG ρC hc hr hnf
      have hex : execEnd X.O X.passes X.R (Endblock.cons s rest) σ ρG =
          match execStmt X.O X.passes X.R s σ ρG with
          | .ok σ' ρ' => execEnd X.O X.passes X.R rest σ' ρ'
          | .zurueck σ' v => .zurueck σ' v
          | .grund σ' r => .grund σ' r
          | .leave h σ' ρ' => .leave h σ' ρ'
          | .next h σ' ρ' => .next h σ' ρ'
          | .logik e => .logik e
          | .hardware e => .hardware e := rfl
      rw [hex] at hnf ⊢
      have hne' := hne σ ρG
      cases hs' : execStmt X.O X.passes X.R s σ ρG with
      | ok σ' ρ' => rw [hs'] at hne'; exact absurd hne' (by simp [Ausgang.istOk])
      | zurueck σ' v =>
          obtain ⟨o1, h1, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          exact ⟨o1, h1, Or.inl hO⟩
      | grund σ' r =>
          obtain ⟨o1, h1, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          exact ⟨o1, h1, hO⟩
      | leave hl σ' ρ' =>
          obtain ⟨o1, h1, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          exact ⟨o1, h1, hO⟩
      | next hl σ' ρ' =>
          obtain ⟨o1, h1, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          exact ⟨o1, h1, hO⟩
      | logik e => rw [hs'] at hnf; exact Bool.noConfusion hnf
      | hardware e => rw [hs'] at hnf; exact Bool.noConfusion hnf

/-! ### Statements that hold a block: `breaking`, `locks`, a release -/

section Rahmenformen

variable (X : TVCtx D) (m : Nat) (G : GCtx) {Γ : Ctx} (K : CEnvLay D Γ) {V : Vertrag D}
  {l : Bool}

/-- `breaking I { … }` is a plain C block (emit.rs 9523: "at run time the
    region is nothing but its statements"). -/
theorem gcorr_breaking {Λ Λ' : List (Res D)} (i : D.Inv) {body : Block D V l Γ Λ Λ'} {cb : CS}
    (hb : BlockSemG X m G K body cb) : StmtCorrG X m G K (Stmt.breaking i body) cb :=
  fun σ st ρG ρC hc hr hnf => hb σ st ρG ρC hc hr hnf

/-- M8 with ghosts: a release before a statement (`L_gib(); return …;`). -/
theorem gcorr_extPre {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'} {cs : CS} (n : Nat)
    (hx : ExtNoop X.XR n) (hs : StmtCorrG X m G K s cs) :
    StmtCorrG X m G K s (.seq (.ext n [] none) cs) := by
  intro σ st ρG ρC hc hr hnf
  obtain ⟨st1, h1, hs1⟩ := exec_extNoop X hx st ρC
  obtain ⟨o, h2, hO⟩ := hs σ st1 ρG ρC (corrW_same hc hs1) (envRelG_same hs1 hr) hnf
  exact ⟨o, Exec.seqN h1 h2, hO⟩

/-- M8 with ghosts: `L_nimm(); { body } L_gib();`. -/
theorem gcorr_locks {Λ : List (Res D)} (L : D.Lock) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (.held L :: Λ) (.held L :: Λ)) {cb : CS} (nimm gib : Nat)
    (hN : ExtNoop X.XR nimm) (hG : ExtNoop X.XR gib) (hb : BlockSemG X m G K body cb) :
    StmtCorrG X m G K (Stmt.locks L hr body) (.seq (.ext nimm [] none) (.seq cb (.ext gib [] none))) := by
  intro σ st ρG ρC hc hrel hnf
  have hex : execStmt X.O X.passes X.R (Stmt.locks L hr body) σ ρG =
      (execBlock X.O X.passes X.R body (σ.nimmt L) ρG).mapWelt (·.gibt L) := rfl
  rw [hex, istFehler_mapWelt] at hnf
  rw [hex]
  obtain ⟨st1, h1, hs1⟩ := exec_extNoop X hN st ρC
  have hc1 : corrW X.EL (σ.nimmt L) st1 := corrW_same hc hs1
  obtain ⟨o, h2, hO⟩ := hb _ st1 ρG ρC hc1 (envRelG_same hs1 hrel) hnf
  cases hB : execBlock X.O X.passes X.R body (σ.nimmt L) ρG with
  | ok σ' ρ' =>
      rw [hB] at hO
      obtain ⟨st2, ρC2, ho, hc2, hr2⟩ := hO
      subst ho
      obtain ⟨st3, h3, hs3⟩ := exec_extNoop X hG st2 ρC2
      exact ⟨_, Exec.seqN h1 (Exec.seqN h2 h3), st3, ρC2, rfl,
        (corrW_same hc2 hs3 : corrW X.EL (σ'.gibt L) st3), envRelG_same hs3 hr2⟩
  | zurueck σ' v =>
      rw [hB] at hO
      refine ⟨o, Exec.seqN h1 (Exec.seqX h2 (zurG_abrupt hO)), ?_⟩
      have hO : ZurG X G σ' v o := hO
      show ZurG X G (σ'.gibt L) v o
      unfold ZurG at hO ⊢
      split at hO
      · obtain ⟨st2, cv, ho, hc2, hrc⟩ := hO
        exact ⟨st2, cv, ho, (hc2 : corrW X.EL (σ'.gibt L) st2), hrc⟩
      · obtain ⟨st2, ho, hc2, hw⟩ := hO
        exact ⟨st2, ho, (hc2 : corrW X.EL (σ'.gibt L) st2), hw⟩
  | grund σ' r =>
      rw [hB] at hO
      refine ⟨o, Exec.seqN h1 (Exec.seqX h2 (gruG_abrupt hO)), ?_⟩
      have hO : GruG X G σ' r o := hO
      show GruG X G (σ'.gibt L) r o
      unfold GruG at hO ⊢
      split at hO
      · exact hO.elim
      · obtain ⟨st2, ho, hc2, hm⟩ := hO
        exact ⟨st2, ho, (hc2 : corrW X.EL (σ'.gibt L) st2), hm⟩
  | leave hl σ' ρ' =>
      rw [hB] at hO
      obtain ⟨st2, ρC2, ho, hc2, hr2⟩ := hO
      subst ho
      exact ⟨_, Exec.seqN h1 (Exec.seqX h2 rfl), st2, ρC2, rfl,
        (hc2 : corrW X.EL (σ'.gibt L) st2), hr2⟩
  | next hl σ' ρ' =>
      rw [hB] at hO
      obtain ⟨st2, ρC2, ho, hc2, hr2⟩ := hO
      subst ho
      exact ⟨_, Exec.seqN h1 (Exec.seqX h2 rfl), st2, ρC2, rfl,
        (hc2 : corrW X.EL (σ'.gibt L) st2), hr2⟩
  | logik e => rw [hB] at hnf; exact Bool.noConfusion hnf
  | hardware e => rw [hB] at hnf; exact Bool.noConfusion hnf

end Rahmenformen


theorem ValCorr.ne_undef' {EL : EmitLay D} {τ : Ty} {v : Wert D τ} {c : CVal}
    (h : ValCorr EL τ v c) : c ≠ .undef := fun e => ValCorr.ne_undef (e ▸ h)

/-- The answer through a result pointer. -/
def WertInP (EL : EmitLay D) (wp : CPtr) : (e : Option Ty) → ErgVal D e → CSt → Prop
  | none, _, _ => True
  | some τ, v, st => ValCorr EL τ v (st.mem wp.blk wp.off.toNat)

theorem wertIn_wertInP {EL : EmitLay D} {κ : Kanal} : ∀ {e : Option Ty} (v : ErgVal D e)
    {st st' : CSt}, st'.mem = st.mem → WertIn EL κ e v st → WertInP EL κ.wp e v st'
  | none, _, _, _, _, _ => trivial
  | some τ, v, st, st', hm, h => by
      show ValCorr EL τ v (st'.mem κ.wp.blk κ.wp.off.toNat)
      rw [hm]; exact h

theorem wertInP_ergWert {EL : EmitLay D} {wp : CPtr} {τ : Ty} :
    ∀ {e : Option Ty} (he : e = some τ) (v : ErgVal D e) (st : CSt),
      WertInP EL wp e v st → ValCorr EL τ (ergWert he v) (st.mem wp.blk wp.off.toNat) := by
  intro e he v st h
  subst he
  exact h

/-- THE OUTCOME OF A CALL TO A CHANNEL FUNCTION: `true` and the answer in
    `*_wert`, or `false` and the reason's constant in `*_grund`. -/
def RufOutK (EL : EmitLay D) (wp gp : CPtr) (code : Nat → Int) {f : D.Fn} :
    RufAusgang f → CSt → Option CVal → Prop
  | .ok σ' v, st', rv => corrW EL σ' st' ∧ rv = some (.int 1) ∧ WertInP EL wp (D.erg f) v st'
  | .grund σ' r, st', rv => corrW EL σ' st' ∧ rv = some (.int 0) ∧
      st'.mem gp.blk gp.off.toNat = .int (code r)
  | _, _, _ => False

/-- THE CALLEE RELATION OF A CHANNEL FUNCTION: C function `fc` with
    parameters `ps`, whose locals `wx`/`gx` receive the caller's cells;
    the callee runs in frame `fcf`, so the caller's cells lie elsewhere. -/
def FnCorrK (EL : EmitLay D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (CR : CCallR) (f : D.Fn) (fc : Nat) (ps : List (Nat × CTy)) (Kf : CEnvLay D (D.params f))
    (wx gx : Nat) (τw τg : CTy) (code : Nat → Int) (fcf : Nat) : Prop :=
  ∀ (σ : World D) (st : CSt) (ρG : Env D (D.params f)) (vs : List CVal) (ρ0 : CLok) (wp gp : CPtr),
    corrW EL σ st → bindParams ps vs = some ρ0 → EnvRel EL Kf ρG ρ0 →
    ρ0 wx = .ptr wp → ρ0 gx = .ptr gp →
    accOk EL.lay st wp τw .wr = true → accOk EL.lay st gp τg .wr = true →
    (∀ x, wp.blk ≠ .stk fcf x) → (∀ x, gp.blk ≠ .stk fcf x) →
    (∃ f' x', wp.blk = .stk f' x') → (∃ f' x', gp.blk = .stk f' x') →
    (R f σ ρG).istFehler = false →
    ∃ st' rv, CR fc st vs st' rv ∧ RufOutK EL wp gp code (R f σ ρG) st' rv

theorem enterFrame_live_ne (st : CSt) (fr : Nat) (xs : List Nat) {b : CBlk}
    (h : ∀ x, b ≠ .stk fr x) : (enterFrame st fr xs).live b = st.live b := by
  cases b with
  | stk f x =>
      show (if f = fr ∧ x ∈ xs then true else st.live (.stk f x)) = _
      rw [if_neg (fun hc => h x (by rw [hc.1]))]
  | _ => rfl

/-- A relation whose C positions are no ghosts survives ghostifying. -/
theorem envRel_ghostify_frei {EL : EmitLay D} {Γ : Ctx} {K : CEnvLay D Γ} (hK : K.okB = true)
    (L : CLayout) (fr : Nat) (gs : GList)
    (hgs : ∀ g ∈ geister gs, g ∉ K.vm ∧ (∀ q ∈ K.pp, q.1 ≠ g) ∧ (∀ q ∈ K.ks, q.1 ≠ g))
    {ρG : Env D Γ} {ρ : CLok} (h : EnvRel EL K ρG ρ) (st : CSt) :
    EnvRel EL K ρG (ghostify L fr gs ρ st) := by
  obtain ⟨hl, -, -⟩ := okB_spec hK
  have hA := ghostify_agree L fr gs ρ st
  have hnot : ∀ y, (y ∈ geister gs → False) → ghostify L fr gs ρ st y = ρ y :=
    fun y hy => (hA y hy).symm
  refine ⟨fun τ x => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · rw [hnot _ (fun hg => (hgs _ hg).1 (loc_mem hl x))]
    exact h.1 τ x
  · rw [hnot _ (fun hg => (hgs _ hg).2.1 q hq rfl)]
    exact h.2.1 q hq
  · rw [hnot _ (fun hg => (hgs _ hg).2.2 q hq rfl)]
    exact h.2.2 q hq

/-- K3, THE CALLEE: `rufAt` of a channel function against `CallAt`, from
    its body's correspondence under the channel (for every pair of
    caller cells in stack blocks). -/
theorem cCorr_rufK (EL : EmitLay D) (orc : DevOrc) (XR : CCallR) (P : Programm D) (O : Orakel D)
    (passes n : Nat) (Pr : CProg) (f : D.Fn) (fc : Nat) (F : CFun) (hPr : Pr fc = some F)
    (Kf : CEnvLay D (D.params f)) (hKf : Kf.okB = true) (m : Nat) (wx gx : Nat) (τw τg : CTy)
    (code : Nat → Int) (gs : GList)
    (hgs : ∀ g ∈ geister gs, g ∉ Kf.vm ∧ (∀ q ∈ Kf.pp, q.1 ≠ g) ∧ (∀ q ∈ Kf.ks, q.1 ≠ g))
    (hloc : ∀ q ∈ gs, q.2.1 ∈ F.locals)
    (hbody : ∀ wp gp : CPtr, (∃ f' x', wp.blk = .stk f' x') → (∃ f' x', gp.blk = .stk f' x') →
      EndSemG ⟨EL, orc, n + 1, CallAt EL.lay orc XR Pr n, XR, O, passes, rufAt P O passes n⟩ m
        true ⟨gs, some ⟨wx, gx, wp, gp, τw, τg, code⟩⟩ Kf (P.rumpf f) F.body) :
    FnCorrK EL (rufAt P O passes (n + 1)) (CallAt EL.lay orc XR Pr (n + 1)) f fc F.params Kf
      wx gx τw τg code (n + 1) := by
  intro σ st ρG vs ρ0 wp gp hc hb hr hw hg haw hag hdw hdg hsw hsg hnf
  simp only [rufAt] at hnf ⊢
  by_cases hq : wahr? (eval (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
      (P.requires f) (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρG) = false
  · rw [if_pos hq] at hnf; exact Bool.noConfusion hnf
  rw [if_neg hq] at hnf ⊢
  have hc1 : corrW EL (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
      (enterFrame st (n + 1) F.locals) := corrW_enterFrame (n + 1) F.locals hc
  have hrel : EnvRelG ⟨EL, orc, n + 1, CallAt EL.lay orc XR Pr n, XR, O, passes, rufAt P O passes n⟩
      ⟨gs, some ⟨wx, gx, wp, gp, τw, τg, code⟩⟩ Kf ρG ρ0 (enterFrame st (n + 1) F.locals) := by
    refine ⟨envRel_ghostify_frei hKf _ _ gs hgs hr _, ⟨hw, hg, ?_, ?_⟩, ?_⟩
    · rw [accOk_live (enterFrame_live_ne st (n + 1) F.locals hdw)]; exact haw
    · rw [accOk_live (enterFrame_live_ne st (n + 1) F.locals hdg)]; exact hag
    · intro q hq
      show (if n + 1 = n + 1 ∧ q.2.1 ∈ F.locals then true else _) = true
      rw [if_pos ⟨rfl, hloc q hq⟩]
  cases hE : execEnd (V := vertragVon D f) O passes (rufAt P O passes n) (P.rumpf f)
      (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρG with
  | zurueck σ' v =>
      rw [hE] at hnf
      obtain ⟨o, hx, hO⟩ := hbody wp gp hsw hsg _ _ ρG ρ0 hc1 hrel (by rw [hE]; rfl)
      rw [hE] at hO
      rcases hO with hZ | ⟨-, hkan, -⟩
      · obtain ⟨st1, ho, hc2, hwi⟩ := hZ
        dsimp only at hnf ⊢
        by_cases hens : wahr? (eval (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
            (P.ensures f) (σ'.lese (vertragVon D f).ende (P.ensures f).orte)
            (ergEnv (D.erg f) v ρG)) = false
        · rw [if_pos hens] at hnf; exact Bool.noConfusion hnf
        rw [if_neg hens] at hnf ⊢
        cases hfind : D.invs.find? (fun i => schuldet f i &&
            !wahr? (eval ((D.invs.filter (schuldet f)).foldl
              (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
              (σ'.lese (vertragVon D f).ende (P.ensures f).orte)) (P.invariante i)
              ((D.invs.filter (schuldet f)).foldl
              (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
              (σ'.lese (vertragVon D f).ende (P.ensures f).orte)) .nil)) with
        | some i => rw [hfind] at hnf; exact Bool.noConfusion hnf
        | none =>
            have hc3 : corrW EL ((D.invs.filter (schuldet f)).foldl
                (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
                (σ'.lese (vertragVon D f).ende (P.ensures f).orte)) (leaveFrame st1 (n + 1)) :=
              (corrW_foldl_lese _ _ _ _).mpr ((corrW_lese _ _ _ _ _).mpr (corrW_leaveFrame _ hc2))
            refine ⟨_, some (.int 1), ⟨F, ρ0, o, hPr, hb, hx, st1, Or.inl ho, rfl⟩, hc3, rfl, ?_⟩
            exact wertIn_wertInP (st := st1) (st' := leaveFrame st1 (n + 1)) v rfl hwi
      · exact absurd hkan (by simp)
  | grund σ' r =>
      obtain ⟨o, hx, hO⟩ := hbody wp gp hsw hsg _ _ ρG ρ0 hc1 hrel (by rw [hE]; rfl)
      rw [hE] at hO
      obtain ⟨st1, ho, hc2, hm⟩ := hO
      exact ⟨_, some (.int 0), ⟨F, ρ0, o, hPr, hb, hx, st1, Or.inl ho, rfl⟩,
        corrW_leaveFrame _ hc2, rfl, hm⟩
  | leave h _ _ => exact absurd h (by decide)
  | next h _ _ => exact absurd h (by decide)
  | logik e => rw [hE] at hnf; exact Bool.noConfusion hnf
  | hardware e => rw [hE] at hnf; exact Bool.noConfusion hnf

/-- K3', A PLAIN FUNCTION WITH GHOSTS: `rufAt` against `CallAt` for a
    function without a channel whose body uses out-parameter cells (its
    address-taken locals, alive in its frame). -/
theorem cCorr_rufG (EL : EmitLay D) (orc : DevOrc) (XR : CCallR) (P : Programm D) (O : Orakel D)
    (passes n : Nat) (Pr : CProg) (f : D.Fn) (fc : Nat) (F : CFun) (hPr : Pr fc = some F)
    (Kf : CEnvLay D (D.params f)) (hKf : Kf.okB = true) (m : Nat) (gs : GList)
    (hgs : ∀ g ∈ geister gs, g ∉ Kf.vm ∧ (∀ q ∈ Kf.pp, q.1 ≠ g) ∧ (∀ q ∈ Kf.ks, q.1 ≠ g))
    (hloc : ∀ q ∈ gs, q.2.1 ∈ F.locals)
    (hbody : EndSemG ⟨EL, orc, n + 1, CallAt EL.lay orc XR Pr n, XR, O, passes, rufAt P O passes n⟩
      m true ⟨gs, none⟩ Kf (P.rumpf f) F.body) :
    FnCorr EL (rufAt P O passes (n + 1)) (CallAt EL.lay orc XR Pr (n + 1)) f fc F.params Kf := by
  intro σ st ρG vs ρ0 hc hb hr hnf
  simp only [rufAt] at hnf ⊢
  by_cases hq : wahr? (eval (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
      (P.requires f) (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρG) = false
  · rw [if_pos hq] at hnf; exact Bool.noConfusion hnf
  rw [if_neg hq] at hnf ⊢
  have hc1 : corrW EL (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
      (enterFrame st (n + 1) F.locals) := corrW_enterFrame (n + 1) F.locals hc
  have hrel : EnvRelG ⟨EL, orc, n + 1, CallAt EL.lay orc XR Pr n, XR, O, passes, rufAt P O passes n⟩
      ⟨gs, none⟩ Kf ρG ρ0 (enterFrame st (n + 1) F.locals) := by
    refine ⟨envRel_ghostify_frei hKf _ _ gs hgs hr _, trivial, ?_⟩
    intro q hq
    show (if n + 1 = n + 1 ∧ q.2.1 ∈ F.locals then true else _) = true
    rw [if_pos ⟨rfl, hloc q hq⟩]
  cases hE : execEnd (V := vertragVon D f) O passes (rufAt P O passes n) (P.rumpf f)
      (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρG with
  | zurueck σ' v =>
      rw [hE] at hnf
      obtain ⟨o, hx, hO⟩ := hbody _ _ ρG ρ0 hc1 hrel (by rw [hE]; rfl)
      rw [hE] at hO
      have hret : ∃ st1, corrW EL σ' st1 ∧ ((∃ cv, o = .ret st1 cv ∧ RetCorr EL (D.erg f) v cv) ∨
          ((vertragVon D f).erg = none ∧ ∃ ρ1, o = .norm st1 ρ1)) := by
        rcases hO with ⟨st1, cv, ho, hc2, hrc⟩ | ⟨-, -, hV, st1, ρ1, ho, hc2⟩
        · exact ⟨st1, hc2, Or.inl ⟨cv, ho, hrc⟩⟩
        · exact ⟨st1, hc2, Or.inr ⟨hV, ρ1, ho⟩⟩
      obtain ⟨st1, hc2, hret⟩ := hret
      dsimp only at hnf ⊢
      by_cases hens : wahr? (eval (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
          (P.ensures f) (σ'.lese (vertragVon D f).ende (P.ensures f).orte)
          (ergEnv (D.erg f) v ρG)) = false
      · rw [if_pos hens] at hnf; exact Bool.noConfusion hnf
      rw [if_neg hens] at hnf ⊢
      cases hfind : D.invs.find? (fun i => schuldet f i &&
          !wahr? (eval ((D.invs.filter (schuldet f)).foldl
            (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
            (σ'.lese (vertragVon D f).ende (P.ensures f).orte)) (P.invariante i)
            ((D.invs.filter (schuldet f)).foldl
            (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
            (σ'.lese (vertragVon D f).ende (P.ensures f).orte)) .nil)) with
      | some i => rw [hfind] at hnf; exact Bool.noConfusion hnf
      | none =>
          have hc3 : corrW EL ((D.invs.filter (schuldet f)).foldl
              (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
              (σ'.lese (vertragVon D f).ende (P.ensures f).orte)) (leaveFrame st1 (n + 1)) :=
            (corrW_foldl_lese _ _ _ _).mpr ((corrW_lese _ _ _ _ _).mpr (corrW_leaveFrame _ hc2))
          rcases hret with ⟨cv, ho, hrc⟩ | ⟨hV, ρ1, ho⟩
          · exact ⟨_, cv, ⟨F, ρ0, o, hPr, hb, hx, st1, Or.inl ho, rfl⟩, hc3, hrc⟩
          · exact ⟨_, none, ⟨F, ρ0, o, hPr, hb, hx, st1, Or.inr ⟨rfl, ρ1, ho⟩, rfl⟩, hc3,
              retCorr_none hV v⟩
  | grund σ' r =>
      obtain ⟨o, -, hO⟩ := hbody _ _ ρG ρ0 hc1 hrel (by rw [hE]; rfl)
      rw [hE] at hO
      exact hO.elim
  | leave h _ _ => exact absurd h (by decide)
  | next h _ _ => exact absurd h (by decide)
  | logik e => rw [hE] at hnf; exact Bool.noConfusion hnf
  | hardware e => rw [hE] at hnf; exact Bool.noConfusion hnf

/-- A statement that never completes normally, followed by C that is
    never reached (`__builtin_unreachable();` after a `switch` whose every
    arm leaves, emit.rs D005). -/
theorem gcorr_seqTot (X : TVCtx D) (m : Nat) (G : GCtx) {Γ : Ctx} (K : CEnvLay D Γ) {V : Vertrag D}
    {l : Bool} {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'} {cs : CS} (ct : CS)
    (hs : StmtCorrG X m G K s cs)
    (hne : ∀ σ ρG, (execStmt X.O X.passes X.R s σ ρG).istOk = false) :
    StmtCorrG X m G K s (.seq cs ct) := by
  intro σ st ρG ρC hc hr hnf
  obtain ⟨o, hx, hO⟩ := hs σ st ρG ρC hc hr hnf
  refine ⟨o, Exec.seqX hx ?_, hO⟩
  have hne' := hne σ ρG
  revert hO hne'
  cases execStmt X.O X.passes X.R s σ ρG with
  | ok σ' ρ' => intro _ h; exact absurd h (by simp [Ausgang.istOk])
  | zurueck σ' v => intro hO _; exact zurG_abrupt hO
  | grund σ' r => intro hO _; exact gruG_abrupt hO
  | leave hl σ' ρ' => intro hO _; obtain ⟨st', ρ'', ho, -⟩ := hO; subst ho; rfl
  | next hl σ' ρ' => intro hO _; obtain ⟨st', ρ'', ho, -⟩ := hO; subst ho; rfl
  | logik e => intro hO _; exact hO.elim
  | hardware e => intro hO _; exact hO.elim

/-- The emitted call site of `let x = f(a) else (e) { err }` (`T x;` and
    `R e;` are address-taken locals, stack cells of the frame):
    `if (!f(a, &x, &e)) { err } rest`, the call's answer in `tmp` (C's
    `if` evaluates the call as its full expression, 6.8.4.1). -/
def callElseCS (fc : Nat) (cargs : List CX) (nx ex tmp : Nat) (cerr crest : CS) : CS :=
  .seq (.call fc (cargs ++ [.addrL nx, .addrL ex]) (some (tmp, cBoolTy)))
    (.seq (.ite (.lnot (.var tmp)) cerr .skip) crest)

/-- The arguments of the call site: the C arguments (with their cell
    reads) evaluate without memory effect, and parameter passing gives
    the callee its relation and the two cells. -/
def ArgsToK (X : TVCtx D) (G : GCtx) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ) {τs : List Ty}
    (args : Args D Γ Λ τs) (cargs : List CX) (nx ex : Nat) (ps : List (Nat × CTy))
    (Kf : CEnvLay D τs) (wxf gxf : Nat) : Prop :=
  ∀ (σ : World D) (st : CSt) (ρG : Env D Γ) (ρC : CLok), corrW X.EL σ st →
    EnvRelG X G K ρG ρC st →
    ∃ vs st' ρ0, evArgs X.EL.lay X.orc X.fr (cargs ++ [.addrL nx, .addrL ex]) st ρC = some (vs, st') ∧
      SameML st st' ∧ bindParams ps vs = some ρ0 ∧ EnvRel X.EL Kf (evalArgs σ args σ ρG) ρ0 ∧
      ρ0 wxf = .ptr ⟨.stk X.fr nx, 0⟩ ∧ ρ0 gxf = .ptr ⟨.stk X.fr ex, 0⟩

/-- The ghost cells are plain stack cells of their declared type. -/
def GOk (X : TVCtx D) (G : GCtx) : Prop :=
  ∀ q ∈ G.gs, ∃ B, X.EL.lay (.stk X.fr q.2.1) = some B ∧ B.kind = .plain ∧ B.lay.cell 0 = some q.2.2

/-- What the callee must keep of the caller's frame: every other ghost
    cell, every ghost cell's lifetime, the channel's lifetimes -- the
    frame property of a call through out-parameters (an assumption about
    `CR` at `fc`; for `CallAt` it is the callee's own frame discipline). -/
def CallKeeps (X : TVCtx D) (G : GCtx) (fc : Nat) (nx ex : Nat) : Prop :=
  ∀ st vs st' rv, X.CR fc st vs st' rv →
    (∀ q ∈ G.gs, q.2.1 ≠ nx → q.2.1 ≠ ex → st'.mem (.stk X.fr q.2.1) = st.mem (.stk X.fr q.2.1)) ∧
    (∀ q ∈ G.gs, st'.live (.stk X.fr q.2.1) = st.live (.stk X.fr q.2.1)) ∧
    (∀ κ, G.kan = some κ → st'.live κ.wp.blk = st.live κ.wp.blk ∧
      st'.live κ.gp.blk = st.live κ.gp.blk)

theorem gsFind_mem' : ∀ (gs : GList) (y e : Nat) (τ : CTy), gsFind gs y = some (e, τ) →
    (y, e, τ) ∈ gs
  | [], _, _, _, h => by simp [gsFind] at h
  | (g, e', τ') :: gs, y, e, τ, h => by
      simp only [gsFind] at h
      by_cases hy : y = g
      · rw [if_pos hy] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        subst hy
        exact List.mem_cons_self ..
      · rw [if_neg hy] at h
        exact List.mem_cons_of_mem _ (gsFind_mem' gs y e τ h)

theorem accOk_zelle {L : CLayout} {fr e : Nat} {τ : CTy} {B : BlkLay} {st : CSt}
    (hB : L (.stk fr e) = some B) (hk : B.kind = .plain) (hc : B.lay.cell 0 = some τ)
    (hl : st.live (.stk fr e) = true) (md : AccMode) (hmd : md = .rd ∨ md = .wr) :
    accOk L st ⟨.stk fr e, 0⟩ τ md = true := by
  unfold accOk
  simp only [hB, hl, hk, Bool.true_and]
  rcases hmd with rfl | rfl
  · simp [BKind.permits, hc]
  · simp [BKind.permits, hc]

theorem zellWert_mem {L : CLayout} {fr e : Nat} {τ : CTy} {st : CSt}
    (ha : accOk L st ⟨.stk fr e, 0⟩ τ .rd = true) (hne : st.mem (.stk fr e) 0 ≠ .undef) :
    zellWert L fr st e τ = st.mem (.stk fr e) 0 := by
  unfold zellWert bLoad
  rw [if_pos ha]
  show (match (match st.mem (.stk fr e) 0 with | .undef => none | v => some v) with
    | some v => v | none => .undef) = _
  cases hm : st.mem (.stk fr e) 0 with
  | undef => exact absurd hm hne
  | int n => rfl
  | ptr p => rfl

/-- A relation read through positions on which two locals agree. -/
theorem envRel_congr {EL : EmitLay D} {Γ : Ctx} {K : CEnvLay D Γ} (hK : K.okB = true)
    {ρG : Env D Γ} {ρa ρb : CLok}
    (hab : ∀ y, (y ∈ K.vm ∨ (∃ q ∈ K.pp, q.1 = y) ∨ (∃ q ∈ K.ks, q.1 = y)) → ρa y = ρb y)
    (h : EnvRel EL K ρG ρa) : EnvRel EL K ρG ρb := by
  obtain ⟨hl, -, -⟩ := okB_spec hK
  refine ⟨fun τ x => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · rw [← hab _ (Or.inl (loc_mem hl x))]; exact h.1 τ x
  · rw [← hab _ (Or.inr (Or.inl ⟨q, hq, rfl⟩))]; exact h.2.1 q hq
  · rw [← hab _ (Or.inr (Or.inr ⟨q, hq, rfl⟩))]; exact h.2.2 q hq

theorem endOutG_zu (X : TVCtx D) (m : Nat) (G : GCtx) {Γ : Ctx} {K : CEnvLay D Γ} {τ : Ty}
    {x : Nat} {V : Vertrag D} {l : Bool} (a : EndAusgang V l (τ :: Γ)) (o : COut)
    (h : EndOutG X m false G (K.push τ x) a o) :
    StOutG X m G K a.schrumpf.zuAusgang o ∧ o.abrupt = true := by
  cases a with
  | zurueck σ v =>
      rcases h with hZ | ⟨hf, -⟩
      · exact ⟨hZ, zurG_abrupt hZ⟩
      · exact absurd hf (by decide)
  | grund σ r => exact ⟨h, gruG_abrupt h⟩
  | leave hl σ ρ =>
      obtain ⟨st', ρC', ho, hc, hr⟩ := h
      subst ho
      exact ⟨⟨st', ρC', rfl, hc, envRelG_pop hr⟩, rfl⟩
  | next hl σ ρ =>
      obtain ⟨st', ρC', ho, hc, hr⟩ := h
      subst ho
      exact ⟨⟨st', ρC', rfl, hc, envRelG_pop hr⟩, rfl⟩
  | logik e => exact h.elim
  | hardware e => exact h.elim

/-- K4, THE CALL SITE: `let x = f(a) else (e) { err } rest` against
    `if (!f(a, &x, &e)) { err } rest`. After the call, `x`'s cell holds
    the answer (the rest runs with `x` as a ghost of that cell) or `e`'s
    cell holds the reason (the error block runs with `e` as a ghost).
    The reason's constant is its index here (`hcode`, the ordinal
    convention of the header). -/
theorem bsemG_bindCallElse (X : TVCtx D) (m : Nat) (G : GCtx) {Γ : Ctx} (K : CEnvLay D Γ)
    {V : Vertrag D} {l : Bool} {Λ Λ' : List (Res D)} {τ : Ty} (f : D.Fn)
    (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ) (hp : RufPasst D V (D.signatur f) Λ)
    (hr0 : 0 < D.gruende f) (err : Endblock D V l (.grund (D.gruende f) :: Γ) (nach D f Λ))
    (rest : Block D V l (τ :: Γ) (nach D f Λ) Λ') {fc : Nat} {ps : List (Nat × CTy)}
    {Kf : CEnvLay D (D.params f)} {wxf gxf : Nat} {τw τg : CTy} {code : Nat → Int} {fcf : Nat}
    (hF : FnCorrK X.EL X.R X.CR f fc ps Kf wxf gxf τw τg code fcf) (hfr : X.fr ≠ fcf)
    {cargs : List CX} {nx ex tmp gN gE : Nat} {cerr crest : CS}
    (hA : ArgsToK X G K args cargs nx ex ps Kf wxf gxf)
    (hgN : gsFind G.gs gN = some (nx, τw)) (hgE : gsFind G.gs gE = some (ex, τg))
    (hGok : GOk X G) (hcode : ∀ r : Fin (D.gruende f), code r = (r : Nat))
    (hK : K.okB = true) (hfN : K.freshB gN = true) (hfE : K.freshB gE = true)
    (htmp : K.freshB tmp = true)
    (htk : ∀ κ, G.kan = some κ → tmp ≠ κ.wx ∧ tmp ≠ κ.gx)
    (hkeep : CallKeeps X G fc nx ex)
    (hinj : ∀ g e τ', gsFind G.gs g = some (e, τ') → (e = nx → g = gN) ∧ (e = ex → g = gE))
    (herr : EndSemG X m false G (K.push (.grund (D.gruende f)) gE) err cerr)
    (hrest : BlockSemG X m G (K.push τ gN) rest crest) :
    BlockSemG X m G K (Block.bindCallElse f args he hp hr0 err rest)
      (callElseCS fc cargs nx ex tmp cerr crest) := by
  intro σ st ρG ρC hc hrel hnf
  have hex : execBlock X.O X.passes X.R (Block.bindCallElse f args he hp hr0 err rest) σ ρG =
      match X.R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρG) with
      | .ok σ' v => (execBlock X.O X.passes X.R rest σ' (.cons (ergWert he v) ρG)).schrumpf
      | .grund σ' r => (execEnd X.O X.passes X.R err σ' (.cons r ρG)).schrumpf.zuAusgang
      | .logik e => .logik e
      | .hardware e => .hardware e := rfl
  rw [hex] at hnf ⊢
  have hc' : corrW X.EL (σ.lese Λ args.orte) st := (corrW_lese _ _ _ _ _).mpr hc
  obtain ⟨vs, st1, ρ0, hev, hs1, hb, hr0', hw0, hg0⟩ := hA _ st ρG ρC hc' hrel
  have hc1 := corrW_same hc' hs1
  have hrel1 := envRelG_same hs1 hrel
  obtain ⟨BN, hBN, hkN, hcN⟩ := hGok _ (gsFind_mem' _ _ _ _ hgN)
  obtain ⟨BE, hBE, hkE, hcE⟩ := hGok _ (gsFind_mem' _ _ _ _ hgE)
  have hlN := hrel1.2.2 _ (gsFind_mem' _ _ _ _ hgN)
  have hlE := hrel1.2.2 _ (gsFind_mem' _ _ _ _ hgE)
  have hstkN : ∃ f' x', (⟨.stk X.fr nx, 0⟩ : CPtr).blk = .stk f' x' := ⟨_, _, rfl⟩
  have hstkE : ∃ f' x', (⟨.stk X.fr ex, 0⟩ : CPtr).blk = .stk f' x' := ⟨_, _, rfl⟩
  have hdN : ∀ x, (⟨.stk X.fr nx, 0⟩ : CPtr).blk ≠ .stk fcf x := fun x h => hfr (by cases h; rfl)
  have hdE : ∀ x, (⟨.stk X.fr ex, 0⟩ : CPtr).blk ≠ .stk fcf x := fun x h => hfr (by cases h; rfl)
  -- the relation after the call, at the positions of `K`
  have hpos : ∀ (ρ' : CLok) (st2 : CSt), (∀ y, y ≠ tmp → ρ' y = ρC y) →
      (∀ q ∈ G.gs, q.2.1 ≠ nx → q.2.1 ≠ ex → st2.mem (.stk X.fr q.2.1) = st1.mem (.stk X.fr q.2.1)) →
      (∀ q ∈ G.gs, st2.live (.stk X.fr q.2.1) = st1.live (.stk X.fr q.2.1)) →
      EnvRel X.EL K ρG (ghostify X.EL.lay X.fr G.gs ρ' st2) := by
    intro ρ' st2 hρ hm hl
    refine envRel_congr hK (fun y hy => ?_) hrel1.1
    obtain ⟨hyN, hyE, hyT⟩ : y ≠ gN ∧ y ≠ gE ∧ y ≠ tmp := by
      obtain ⟨hN1, hN2, hN3⟩ := freshB_spec hfN
      obtain ⟨hE1, hE2, hE3⟩ := freshB_spec hfE
      obtain ⟨hT1, hT2, hT3⟩ := freshB_spec htmp
      rcases hy with hy | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · exact ⟨fun e => hN1 (e ▸ hy), fun e => hE1 (e ▸ hy), fun e => hT1 (e ▸ hy)⟩
      · exact ⟨hN2 q hq, hE2 q hq, hT2 q hq⟩
      · exact ⟨hN3 q hq, hE3 q hq, hT3 q hq⟩
    rw [ghostify_at, ghostify_at]
    cases hf : gsFind G.gs y with
    | none => exact (hρ y hyT).symm
    | some p =>
        obtain ⟨e', τ'⟩ := p
        obtain ⟨hi1, hi2⟩ := hinj y e' τ' hf
        have hmem := gsFind_mem' _ _ _ _ hf
        have he1 : e' ≠ nx := fun h => hyN (hi1 h)
        have he2 : e' ≠ ex := fun h => hyE (hi2 h)
        exact (zellWert_keep τ' (hm _ hmem he1 he2) (hl _ hmem)).symm
  -- the channel and the lifetimes after the call
  have hkan2 : ∀ (ρ' : CLok) (st2 : CSt), (∀ y, y ≠ tmp → ρ' y = ρC y) →
      (∀ κ, G.kan = some κ → st2.live κ.wp.blk = st1.live κ.wp.blk ∧
        st2.live κ.gp.blk = st1.live κ.gp.blk) →
      KanalOk X.EL.lay G.kan st2 ρ' := by
    intro ρ' st2 hρ hl
    have hk := hrel1.2.1
    revert hk hl htk
    cases G.kan with
    | none => intro _ _ _; trivial
    | some κ =>
        intro htk hl hk
        obtain ⟨t1, t2⟩ := htk κ rfl
        obtain ⟨l1, l2⟩ := hl κ rfl
        obtain ⟨k1, k2, k3, k4⟩ := hk
        exact ⟨by rw [hρ _ (Ne.symm t1), k1], by rw [hρ _ (Ne.symm t2), k2],
          by rw [accOk_live l1]; exact k3, by rw [accOk_live l2]; exact k4⟩
  cases hR : X.R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρG) with
  | ok σ' v =>
      rw [hR] at hnf
      obtain ⟨st2, rv, hcr, hro⟩ := hF _ st1 _ vs ρ0 _ _ hc1 hb hr0' hw0 hg0
        (accOk_zelle hBN hkN hcN hlN .wr (Or.inr rfl)) (accOk_zelle hBE hkE hcE hlE .wr (Or.inr rfl))
        hdN hdE hstkN hstkE (by rw [hR]; rfl)
      rw [hR] at hro
      obtain ⟨hc2, hrv, hwi⟩ := hro
      subst hrv
      obtain ⟨hkm, hkl, hkk⟩ := hkeep _ _ _ _ hcr
      have hx1 : Exec X.EL.lay X.orc X.fr X.CR X.XR
          (.call fc (cargs ++ [.addrL nx, .addrL ex]) (some (tmp, cBoolTy))) st ρC
          (.norm st2 (lokUpd ρC tmp (.int 1))) := Exec.call hev hcr rfl
      have hρ : ∀ y, y ≠ tmp → lokUpd ρC tmp (.int 1) y = ρC y := fun y hy => by
        simp only [lokUpd, if_neg hy]
      have hval := wertInP_ergWert he v st2 hwi
      have hlN2 : st2.live (.stk X.fr nx) = true := by
        rw [hkl _ (gsFind_mem' _ _ _ _ hgN)]; exact hlN
      have hz : zellWert X.EL.lay X.fr st2 nx τw = st2.mem (.stk X.fr nx) 0 :=
        zellWert_mem (accOk_zelle hBN hkN hcN hlN2 .rd (Or.inl rfl)) (ValCorr.ne_undef' hval)
      have hrel2 : EnvRelG X G (K.push τ gN) (.cons (ergWert he v) ρG) (lokUpd ρC tmp (.int 1)) st2 := by
        refine ⟨?_, hkan2 _ _ hρ hkk, fun q hq => by rw [hkl q hq]; exact hrel1.2.2 q hq⟩
        refine envRel_push_same hK hfN (hpos _ _ hρ hkm hkl) (ergWert he v) ?_
        rw [ghostify_at, hgN]
        show ValCorr X.EL τ (ergWert he v) (zellWert X.EL.lay X.fr st2 nx τw)
        rw [hz]
        exact hval
      rw [istFehler_schrumpf] at hnf
      obtain ⟨o, hx2, hO⟩ := hrest _ st2 _ _ hc2 hrel2 hnf
      have hite : Exec X.EL.lay X.orc X.fr X.CR X.XR (.ite (.lnot (.var tmp)) cerr .skip) st2
          (lokUpd ρC tmp (.int 1)) (.norm st2 (lokUpd ρC tmp (.int 1))) :=
        Exec.iteF (ev_lnot (ev_var (v := 1) (by simp [lokUpd])) rfl) rfl Exec.skip
      exact ⟨o, Exec.seqN hx1 (Exec.seqN hite hx2), stOutG_schrumpf X m G _ o hO⟩
  | grund σ' r =>
      obtain ⟨st2, rv, hcr, hro⟩ := hF _ st1 _ vs ρ0 _ _ hc1 hb hr0' hw0 hg0
        (accOk_zelle hBN hkN hcN hlN .wr (Or.inr rfl)) (accOk_zelle hBE hkE hcE hlE .wr (Or.inr rfl))
        hdN hdE hstkN hstkE (by rw [hR]; rfl)
      rw [hR] at hro
      obtain ⟨hc2, hrv, hm⟩ := hro
      subst hrv
      obtain ⟨hkm, hkl, hkk⟩ := hkeep _ _ _ _ hcr
      have hx1 : Exec X.EL.lay X.orc X.fr X.CR X.XR
          (.call fc (cargs ++ [.addrL nx, .addrL ex]) (some (tmp, cBoolTy))) st ρC
          (.norm st2 (lokUpd ρC tmp (.int 0))) := Exec.call hev hcr rfl
      have hρ : ∀ y, y ≠ tmp → lokUpd ρC tmp (.int 0) y = ρC y := fun y hy => by
        simp only [lokUpd, if_neg hy]
      have hlE2 : st2.live (.stk X.fr ex) = true := by
        rw [hkl _ (gsFind_mem' _ _ _ _ hgE)]; exact hlE
      have hz : zellWert X.EL.lay X.fr st2 ex τg = .int (code r) := by
        rw [zellWert_mem (accOk_zelle hBE hkE hcE hlE2 .rd (Or.inl rfl)) (by
          show st2.mem (CPtr.blk ⟨.stk X.fr ex, 0⟩) (CPtr.off ⟨.stk X.fr ex, 0⟩).toNat ≠ _
          rw [hm]; simp)]
        exact hm
      have hrel2 : EnvRelG X G (K.push (.grund (D.gruende f)) gE) (.cons r ρG)
          (lokUpd ρC tmp (.int 0)) st2 := by
        refine ⟨?_, hkan2 _ _ hρ hkk, fun q hq => by rw [hkl q hq]; exact hrel1.2.2 q hq⟩
        refine envRel_push_same hK hfE (hpos _ _ hρ hkm hkl) (show Wert D (.grund _) from r) ?_
        rw [ghostify_at, hgE]
        show ValCorr X.EL (.grund _) r (zellWert X.EL.lay X.fr st2 ex τg)
        rw [hz]
        show CVal.int (code r) = CVal.int ((r : Nat) : Int)
        rw [hcode r]
      have hnf' : (execEnd X.O X.passes X.R err σ' (.cons r ρG)).istFehler = false := by
        rw [hR] at hnf
        have e1 : ∀ (a : EndAusgang V l (.grund (D.gruende f) :: Γ)),
            a.schrumpf.zuAusgang.istFehler = a.istFehler := fun a => by cases a <;> rfl
        rw [e1] at hnf
        exact hnf
      obtain ⟨o, hx2, hO⟩ := herr _ st2 _ _ hc2 hrel2 hnf'
      obtain ⟨hO', hab⟩ := endOutG_zu X m G _ o hO
      have hite : Exec X.EL.lay X.orc X.fr X.CR X.XR (.ite (.lnot (.var tmp)) cerr .skip) st2
          (lokUpd ρC tmp (.int 0)) o :=
        Exec.iteT (ev_lnot (ev_var (v := 0) (by simp [lokUpd])) rfl) rfl hx2
      exact ⟨o, Exec.seqN hx1 (Exec.seqX hite hab), hO'⟩
  | logik e => rw [hR] at hnf; exact Bool.noConfusion hnf
  | hardware e => rw [hR] at hnf; exact Bool.noConfusion hnf

/-! ## 8. `match` on a reason, forwarding a reason, `narrow`, the check -/

/-- Arm `i` of a reason match. -/
def GrundArms.get {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    {n : Nat} → GrundArms D V l Γ Λ Λ' n → Fin n → Block D V l Γ Λ Λ'
  | _, .cons b _, ⟨0, _⟩ => b
  | _, .cons _ rest, ⟨i + 1, h⟩ => rest.get ⟨i, Nat.lt_of_succ_lt_succ h⟩

theorem execGrund_get (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (i : Fin n) (σ : World D) (ρ : Env D Γ),
      execGrund O passes R arms i σ ρ = execBlock O passes R (arms.get i) σ ρ
  | _, .cons _ _, ⟨0, _⟩, _, _ => rfl
  | _, .cons _ rest, ⟨i + 1, h⟩, σ, ρ => execGrund_get O passes R rest ⟨i, Nat.lt_of_succ_lt_succ h⟩ σ ρ

theorem endOutG_zu0 (X : TVCtx D) (m : Nat) (G : GCtx) {Γ : Ctx} {K : CEnvLay D Γ} {V : Vertrag D}
    {l : Bool} (a : EndAusgang V l Γ) (o : COut) (h : EndOutG X m false G K a o) :
    StOutG X m G K a.zuAusgang o ∧ o.abrupt = true := by
  cases a with
  | zurueck σ v =>
      rcases h with hZ | ⟨hf, -⟩
      · exact ⟨hZ, zurG_abrupt hZ⟩
      · exact absurd hf (by decide)
  | grund σ r => exact ⟨h, gruG_abrupt h⟩
  | leave hl σ ρ =>
      obtain ⟨st', ρC', ho, hc, hr⟩ := h
      subst ho
      exact ⟨⟨st', ρC', rfl, hc, hr⟩, rfl⟩
  | next hl σ ρ =>
      obtain ⟨st', ρC', ho, hc, hr⟩ := h
      subst ho
      exact ⟨⟨st', ρC', rfl, hc, hr⟩, rfl⟩
  | logik e => exact h.elim
  | hardware e => exact h.elim

theorem endIstFehler_zu {V : Vertrag D} {l : Bool} {Γ : Ctx} (a : EndAusgang V l Γ) :
    a.zuAusgang.istFehler = a.istFehler := by
  cases a <;> rfl

section Zweige

variable (X : TVCtx D) (m : Nat) (G : GCtx) {Γ : Ctx} (K : CEnvLay D Γ) {V : Vertrag D}
  {l : Bool}

/-- The run of an emitted `switch` arm `{ … } break;`: the arm's outcome,
    with the closing `break;` consumed. -/
theorem arm_brk {L : CLayout} {orc : DevOrc} {fr : Nat} {CR XR : CCallR} {c : CS} {st : CSt}
    {ρ : CLok} {o : COut} (h : Exec L orc fr CR XR c st ρ o) (hb : ∀ s r, o ≠ .brk s r)
    (hc : ∀ s r, o ≠ .cont s r) :
    ∃ o', Exec L orc fr CR XR (.seq c .brk) st ρ o' ∧ o'.unbreak = o := by
  cases o with
  | norm s r => exact ⟨.brk s r, Exec.seqN h Exec.brk, rfl⟩
  | ret s v => exact ⟨_, Exec.seqX h rfl, rfl⟩
  | brk s r => exact absurd rfl (hb s r)
  | cont s r => exact absurd rfl (hc s r)
  | jump lb s r => exact ⟨_, Exec.seqX h rfl, rfl⟩

theorem stOutG_nichtBrk {a : Ausgang V l Γ} {o : COut}
    (h : StOutG X m G K a o) : (∀ s r, o ≠ .brk s r) ∧ (∀ s r, o ≠ .cont s r) := by
  cases a with
  | ok σ ρ =>
      obtain ⟨st', ρ', ho, -⟩ := h
      subst ho; exact ⟨fun _ _ h => COut.noConfusion h, fun _ _ h => COut.noConfusion h⟩
  | zurueck σ v =>
      have h : ZurG X G σ v o := h
      unfold ZurG at h
      split at h
      · obtain ⟨st', cv, ho, -⟩ := h
        subst ho; exact ⟨fun _ _ h => COut.noConfusion h, fun _ _ h => COut.noConfusion h⟩
      · obtain ⟨st', ho, -⟩ := h
        subst ho; exact ⟨fun _ _ h => COut.noConfusion h, fun _ _ h => COut.noConfusion h⟩
  | grund σ r =>
      have h : GruG X G σ r o := h
      unfold GruG at h
      split at h
      · exact h.elim
      · obtain ⟨st', ho, -⟩ := h
        subst ho; exact ⟨fun _ _ h => COut.noConfusion h, fun _ _ h => COut.noConfusion h⟩
  | leave hl σ ρ =>
      obtain ⟨st', ρ', ho, -⟩ := h
      subst ho; exact ⟨fun _ _ h => COut.noConfusion h, fun _ _ h => COut.noConfusion h⟩
  | next hl σ ρ =>
      obtain ⟨st', ρ', ho, -⟩ := h
      subst ho; exact ⟨fun _ _ h => COut.noConfusion h, fun _ _ h => COut.noConfusion h⟩
  | logik e => exact h.elim
  | hardware e => exact h.elim

/-- A reason constant `R::F` is its index (the ordinal convention). -/
theorem ecorr_grundLit {Λ : List (Res D)} (n : Nat) (r : Fin n) :
    ExprCorr X K (.lit ((r : Nat) : Int)) (Expr.grund (Γ := Γ) (Λ := Λ) n r) := by
  intro σ st ρG ρC _ _
  exact ⟨.int ((r : Nat) : Int), st, rfl, rfl⟩

/-- R1. `switch (e) { case 0: { … } break; case 1: … }` against `match` on a
    reason: every reason has its case, labelled with its index (the
    ordinal convention), whose arm corresponds as a block -- or no case,
    and a Gabbro arm that always fails (an index no reason has: the
    ordinal convention leaves the indices below the smallest ordinal
    unused). -/
theorem gcorr_onGrund {Λ Λ' : List (Res D)} {n : Nat} {r : Expr D Γ Λ (.grund n)}
    {arms : GrundArms D V l Γ Λ Λ' n} {cr : CX} {carms : List (Int × CS)}
    (hr : ExprCorr X K cr r)
    (harms : ∀ i : Fin n, (∃ c, carms.lookup ((i : Nat) : Int) = some (.seq c .brk) ∧
      BlockSemG X m G K (arms.get i) c) ∨
      (∀ σ ρ, (execBlock X.O X.passes X.R (arms.get i) σ ρ).istFehler = true)) :
    StmtCorrG X m G K (Stmt.onGrund r arms) (.sw (cr.zs G.gs) carms) := by
  intro σ st ρG ρC hc hrel hnf
  have hc' : corrW X.EL (σ.lese Λ r.orte) st := (corrW_lese _ _ _ _ _).mpr hc
  obtain ⟨v, st1, h1, hv, hc1⟩ := hr.run X K hc' hrel.1
  have hv' : v = .int (encW (.grund n) (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρG)) := hv
  subst hv'
  have hs1 := ev_same X.EL.lay X.orc X.fr cr st _ _ st1 h1
  have h1' : ev X.EL.lay X.orc X.fr (cr.zs G.gs) st ρC =
      some (.int (encW (.grund n) (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρG)), st1) := by
    rw [ev_zs G.gs cr st st ρC (SameML.refl _)]; exact h1
  have hex : execStmt X.O X.passes X.R (Stmt.onGrund r arms) σ ρG =
      execBlock X.O X.passes X.R (arms.get (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρG))
        (σ.lese Λ r.orte) ρG := by
    show execGrund _ _ _ _ _ _ _ = _
    exact execGrund_get _ _ _ _ _ _ _
  rw [hex] at hnf ⊢
  obtain ⟨c, hl, hb⟩ : ∃ c, carms.lookup
      (encW (.grund n) (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρG)) = some (.seq c .brk) ∧
      BlockSemG X m G K (arms.get (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρG)) c := by
    rcases harms (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρG) with h | hfe
    · exact h
    · rw [hfe] at hnf; exact absurd hnf (by simp)
  obtain ⟨o, hx, hO⟩ := hb _ st1 ρG ρC hc1 (envRelG_same hs1 hrel) hnf
  obtain ⟨hnb, hnc⟩ := stOutG_nichtBrk X m G K hO
  obtain ⟨o', hx', hu⟩ := arm_brk hx hnb hnc
  refine ⟨o, ?_, hO⟩
  rw [← hu]
  exact Exec.swHit h1' hl hx'

/-- R2. `*_grund = e; return false;` -- forwarding a reason held in `e`
    (a C local or, as a cell read, an out-parameter) -- against a `match`
    whose every arm returns a reason of the caller's channel whose
    constant is the matched reason's index. -/
theorem kcorr_weiterleiten {Λ Λ' : List (Res D)} (κ : Kanal) (hkan : G.kan = some κ) {n : Nat}
    {r : Expr D Γ Λ (.grund n)} {arms : GrundArms D V l Γ Λ Λ' n} {cr : CX}
    (hr : ExprCorr X K cr r) (φ : Fin n → Fin V.gruende)
    (hφ : ∀ (i : Fin n) (σ : World D) (ρ : Env D Γ),
      execBlock X.O X.passes X.R (arms.get i) σ ρ = .grund σ (φ i))
    (hcode : ∀ i : Fin n, κ.code (φ i) = ((i : Nat) : Int))
    (hfit : ∀ i : Fin n, valFits κ.τg (.int ((i : Nat) : Int)) = true)
    {f x : Nat} (hstk : κ.gp.blk = .stk f x) :
    StmtCorrG X m G K (Stmt.onGrund r arms)
      (.seq (.store (.var κ.gx) κ.τg (cr.zs G.gs)) (.ret (some (cBoolTy, .lit 0)))) := by
  intro σ st ρG ρC hc hrel hnf
  have hk : KanalIn X.EL.lay κ st ρC := by have := hrel.2.1; rw [hkan] at this; exact this
  obtain ⟨-, k2, -, k4⟩ := hk
  have hc' : corrW X.EL (σ.lese Λ r.orte) st := (corrW_lese _ _ _ _ _).mpr hc
  obtain ⟨v, st1, h1, hv, hc1⟩ := hr.run X K hc' hrel.1
  have hv' : v = .int (encW (.grund n) (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρG)) := hv
  subst hv'
  have hs1 := ev_same X.EL.lay X.orc X.fr cr st _ _ st1 h1
  have h1' : ev X.EL.lay X.orc X.fr (cr.zs G.gs) st ρC =
      some (.int (encW (.grund n) (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρG)), st1) := by
    rw [ev_zs G.gs cr st st ρC (SameML.refl _)]; exact h1
  have hex : execStmt X.O X.passes X.R (Stmt.onGrund r arms) σ ρG =
      .grund (σ.lese Λ r.orte) (φ (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρG)) := by
    show execGrund _ _ _ _ _ _ _ = _
    exact (execGrund_get _ _ _ _ _ _ _).trans (hφ _ _ _)
  rw [hex]
  have k4' : accOk X.EL.lay st1 κ.gp κ.τg .wr = true :=
    (accOk_live (L := X.EL.lay) (st := st) (st' := st1) (p := κ.gp) (τ := κ.τg) (md := .wr)
      (by rw [hs1.2])).trans k4
  have hs := bStore_progress X.EL.lay st1 κ.gp κ.τg
    (.int (encW (.grund n) (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρG))) k4' (hfit _)
  refine ⟨_, Exec.seqN (Exec.store (by simp only [ev, k2]) h1' (convV_of_valFits _ _ (hfit _)) hs)
    (Exec.retS rfl rfl), ?_⟩
  show GruG X G _ _ _
  simp only [GruG, hkan]
  refine ⟨_, rfl, ?_, ?_⟩
  · rw [hstk]; exact corrW_memUpd_stk hc1 _ _
  · exact (memUpd_same _ _ _ _).trans (congrArg CVal.int (hcode _)).symm

/-- The emitted `narrow` check's condition: from related states it says
    whether the value lies in the target range (`narrowCond_ge_le`
    builds it for the emitted `o >= lo && o <= hi`). -/
def NarrowCond {Λ : List (Res D)} {lo hi : Int} (cc : CX) (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) : Prop :=
  ∀ (σ : World D) (st : CSt) (ρG : Env D Γ) (ρC : CLok), corrW X.EL σ st →
    EnvRelG X G K ρG ρC st →
    ∃ st', ev X.EL.lay X.orc X.fr cc st ρC =
        some (.int (b2i (decide (lo' ≤ (eval σ e σ ρG).n ∧ (eval σ e σ ρG).n ≤ hi'))), st') ∧
      SameML st st'

/-- The emitted `o >= lo && o <= hi`, in computation type `t`. -/
theorem narrowCond_ge_le {Λ : List (Res D)} {lo hi : Int} (t : CIT) {ce : CX}
    {e : Expr D Γ Λ (.int lo hi)} (he : ExprCorr X K ce e) (lo' hi' : Int) (ht : t.holds lo hi)
    (hlo' : t.holds lo' lo') (hhi' : t.holds hi' hi') :
    NarrowCond X G K (.land (.cmp .ge t (ce.zs G.gs) (.lit lo')) (.cmp .le t (ce.zs G.gs) (.lit hi')))
      e lo' hi' := by
  intro σ st ρG ρC hc hrel
  obtain ⟨st1, h1, -⟩ := he.runI X K hc hrel.1
  have hs1 := ev_same X.EL.lay X.orc X.fr ce st _ _ st1 h1
  have r1 := (eval σ e σ ρG).lo_le
  have r2 := (eval σ e σ ρG).le_hi
  have cv : conv t (eval σ e σ ρG).n = some (eval σ e σ ρG).n :=
    conv_id ⟨by have := ht.1; omega, by have := ht.2; omega⟩
  have cl : conv t lo' = some lo' := conv_id hlo'
  have ch : conv t hi' = some hi' := conv_id hhi'
  have e1 : ev X.EL.lay X.orc X.fr (ce.zs G.gs) st ρC = some (.int (eval σ e σ ρG).n, st1) := by
    rw [ev_zs G.gs ce st st ρC (SameML.refl _)]; exact h1
  have hge := ev_cmp (op := .ge) e1 (rfl : ev X.EL.lay X.orc X.fr (.lit lo') st1 ρC = _) cv cl
  cases hlo : decide (lo' ≤ (eval σ e σ ρG).n) with
  | false =>
      have hge' : CCmp.app .ge (eval σ e σ ρG).n lo' = false := by
        simp only [CCmp.app]; exact hlo
      rw [hge'] at hge
      refine ⟨st1, ?_, hs1⟩
      rw [ev_land_F hge rfl]
      have : decide (lo' ≤ (eval σ e σ ρG).n ∧ (eval σ e σ ρG).n ≤ hi') = false := by
        apply decide_eq_false; intro hh; exact absurd (decide_eq_true hh.1) (by rw [hlo]; simp)
      rw [this]; rfl
  | true =>
      have hge' : CCmp.app .ge (eval σ e σ ρG).n lo' = true := by
        simp only [CCmp.app]; exact hlo
      rw [hge'] at hge
      obtain ⟨st2, h2, -⟩ := he.runI X K (ρC := ghostify X.EL.lay X.fr G.gs ρC st1)
        (corrW_same hc hs1) (by rw [ghostify_sameML hs1]; exact hrel.1)
      have hs12 := ev_same X.EL.lay X.orc X.fr ce st1 _ _ st2 h2
      have e2 : ev X.EL.lay X.orc X.fr (ce.zs G.gs) st1 ρC = some (.int (eval σ e σ ρG).n, st2) := by
        rw [ev_zs G.gs ce st1 st1 ρC (SameML.refl _)]; exact h2
      have hle := ev_cmp (op := .le) e2 (rfl : ev X.EL.lay X.orc X.fr (.lit hi') st2 ρC = _) cv ch
      refine ⟨st2, ?_, hs1.trans hs12⟩
      rw [ev_land_T hge rfl hle (truth_b2i _)]
      have : decide (lo' ≤ (eval σ e σ ρG).n ∧ (eval σ e σ ρG).n ≤ hi') =
          CCmp.app .le (eval σ e σ ρG).n hi' := by
        simp only [CCmp.app]
        by_cases hh : (eval σ e σ ρG).n ≤ hi'
        · rw [decide_eq_true ⟨of_decide_eq_true hlo, hh⟩, decide_eq_true hh]
        · rw [decide_eq_false (fun h' => hh h'.2), decide_eq_false hh]
      rw [this]

/-- The emitted check when the lower bound is `0` over a value that is
    never negative (emit.rs: `x >= 0` "is always true" on an unsigned
    word and is left out): `o <= hi`. -/
theorem narrowCond_le0 {Λ : List (Res D)} {lo hi : Int} (t : CIT) {ce : CX}
    {e : Expr D Γ Λ (.int lo hi)} (he : ExprCorr X K ce e) (hi' : Int) (hlo : 0 ≤ lo)
    (ht : t.holds lo hi) (hhi' : t.holds hi' hi') :
    NarrowCond X G K (.cmp .le t (ce.zs G.gs) (.lit hi')) e 0 hi' := by
  intro σ st ρG ρC hc hrel
  obtain ⟨st1, h1, -⟩ := he.runI X K hc hrel.1
  have hs1 := ev_same X.EL.lay X.orc X.fr ce st _ _ st1 h1
  have r1 := (eval σ e σ ρG).lo_le
  have r2 := (eval σ e σ ρG).le_hi
  have cv : conv t (eval σ e σ ρG).n = some (eval σ e σ ρG).n :=
    conv_id ⟨by have := ht.1; omega, by have := ht.2; omega⟩
  have e1 : ev X.EL.lay X.orc X.fr (ce.zs G.gs) st ρC = some (.int (eval σ e σ ρG).n, st1) := by
    rw [ev_zs G.gs ce st st ρC (SameML.refl _)]; exact h1
  refine ⟨st1, ?_, hs1⟩
  rw [ev_cmp e1 rfl cv (conv_id hhi')]
  congr 3
  simp only [CCmp.app]
  by_cases hh : (eval σ e σ ρG).n ≤ hi'
  · rw [decide_eq_true hh, decide_eq_true ⟨by omega, hh⟩]
  · rw [decide_eq_false hh, decide_eq_false (fun h' => hh h'.2)]

/-- The exclusive bound `0 ..< n` over a value that is never negative:
    `o < n`, the range `0 .. n - 1`. -/
theorem narrowCond_lt0 {Λ : List (Res D)} {lo hi : Int} (t : CIT) {ce : CX}
    {e : Expr D Γ Λ (.int lo hi)} (he : ExprCorr X K ce e) (n : Int) (hlo : 0 ≤ lo)
    (ht : t.holds lo hi) (hn : t.holds n n) :
    NarrowCond X G K (.cmp .lt t (ce.zs G.gs) (.lit n)) e 0 (n - 1) := by
  intro σ st ρG ρC hc hrel
  obtain ⟨st1, h1, -⟩ := he.runI X K hc hrel.1
  have hs1 := ev_same X.EL.lay X.orc X.fr ce st _ _ st1 h1
  have r1 := (eval σ e σ ρG).lo_le
  have r2 := (eval σ e σ ρG).le_hi
  have cv : conv t (eval σ e σ ρG).n = some (eval σ e σ ρG).n :=
    conv_id ⟨by have := ht.1; omega, by have := ht.2; omega⟩
  have e1 : ev X.EL.lay X.orc X.fr (ce.zs G.gs) st ρC = some (.int (eval σ e σ ρG).n, st1) := by
    rw [ev_zs G.gs ce st st ρC (SameML.refl _)]; exact h1
  refine ⟨st1, ?_, hs1⟩
  rw [ev_cmp e1 rfl cv (conv_id hn)]
  congr 3
  simp only [CCmp.app]
  by_cases hh : (eval σ e σ ρG).n < n
  · rw [decide_eq_true hh, decide_eq_true ⟨by omega, by omega⟩]
  · rw [decide_eq_false hh, decide_eq_false (fun h' => hh (by omega))]

/-- R3. `narrow e to lo' .. hi' else { sonst } rest` against
    `if (!(cond)) { sonst } rest`: the emitter binds no new name, so the
    narrowed value is related through a C position `y` of the certificate
    (`narrow_bind_var`: for a local, its own C local). -/
theorem gsem_narrow {Λ Λ' : List (Res D)} {lo hi lo' hi' : Int} {e : Expr D Γ Λ (.int lo hi)}
    {sonst : Endblock D V l Γ Λ} {rest : Block D V l (.int lo' hi' :: Γ) Λ Λ'} {cc : CX}
    {csonst crest : CS} (y : Nat) (hc : NarrowCond X G K cc e lo' hi')
    (hbind : ∀ (σ : World D) (st : CSt) (ρG : Env D Γ) (ρC : CLok) (v : Wert D (.int lo' hi')),
      corrW X.EL σ st → EnvRelG X G K ρG ρC st → v.n = (eval σ e σ ρG).n →
      EnvRelG X G (K.push (.int lo' hi') y) (.cons v ρG) ρC st)
    (hs : EndSemG X m false G K sonst csonst)
    (hr : BlockSemG X m G (K.push (.int lo' hi') y) rest crest) :
    BlockSemG X m G K (Block.narrow e lo' hi' sonst rest) (.seq (.ite (.lnot cc) csonst .skip) crest) := by
  intro σ st ρG ρC hcw hrel hnf
  have hc' : corrW X.EL (σ.lese Λ e.orte) st := (corrW_lese _ _ _ _ _).mpr hcw
  obtain ⟨st1, h1, hs1⟩ := hc _ st ρG ρC hc' hrel
  have hc1 := corrW_same hc' hs1
  have hrel1 := envRelG_same hs1 hrel
  have hex : execBlock X.O X.passes X.R (Block.narrow e lo' hi' sonst rest) σ ρG =
      if h : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG).n ∧
          (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG).n ≤ hi' then
        (execBlock X.O X.passes X.R rest (σ.lese Λ e.orte)
          (.cons ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG).n, h.1, h.2⟩ ρG)).schrumpf
      else (execEnd X.O X.passes X.R sonst (σ.lese Λ e.orte) ρG).zuAusgang := rfl
  rw [hex] at hnf ⊢
  by_cases hin : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG).n ≤ hi'
  · rw [dif_pos hin] at hnf ⊢
    rw [decide_eq_true hin] at h1
    rw [istFehler_schrumpf] at hnf
    have hr2 := hbind _ st1 ρG ρC ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG).n, hin.1, hin.2⟩
      hc1 hrel1 rfl
    obtain ⟨o, hx, hO⟩ := hr _ st1 _ ρC hc1 hr2 hnf
    exact ⟨o, Exec.seqN (Exec.iteF (ev_lnot h1 (truth_b2i _)) rfl Exec.skip) hx,
      stOutG_schrumpf X m G _ o hO⟩
  · rw [dif_neg hin] at hnf ⊢
    rw [decide_eq_false hin] at h1
    rw [endIstFehler_zu] at hnf
    obtain ⟨o, hx, hO⟩ := hs _ st1 ρG ρC hc1 hrel1 hnf
    obtain ⟨hO', hab⟩ := endOutG_zu0 X m G _ o hO
    exact ⟨o, Exec.seqX (Exec.iteT (ev_lnot h1 (truth_b2i _)) rfl hx) hab, hO'⟩

/-- `narrow x …` of a local `x`: the narrowed value sits in `x`'s own C
    local. -/
theorem narrow_bind_var {Λ : List (Res D)} {lo hi lo' hi' : Int} (x : Var Γ (.int lo hi)) :
    ∀ (σ : World D) (st : CSt) (ρG : Env D Γ) (ρC : CLok) (v : Wert D (.int lo' hi')),
      corrW X.EL σ st → EnvRelG X G K ρG ρC st →
      v.n = (eval σ (Expr.var (Λ := Λ) x) σ ρG).n →
      EnvRelG X G (K.push (.int lo' hi') (K.loc x)) (.cons v ρG) ρC st := by
  intro σ st ρG ρC v _ hrel hv
  refine ⟨⟨fun τ y => ?_, hrel.1.2.1, hrel.1.2.2⟩, hrel.2⟩
  cases y with
  | hier =>
      have h := hrel.1.1 _ x
      show ghostify X.EL.lay X.fr G.gs ρC st (K.loc x) = .int v.n
      rw [h, hv]
      rfl
  | dort y => exact hrel.1.1 _ y

/-- R4. The `where`/`requires` check: `if (!(c)) { sonst } rest` against
    `pruefung`. -/
theorem gsem_pruefung {Λ Λ' : List (Res D)} {c : Expr D Γ Λ .bool} {sonst : Endblock D V l Γ Λ}
    {rest : Block D V l Γ Λ Λ'} {cc : CX} {csonst crest : CS} (hc : ExprCorr X K cc c)
    (hs : EndSemG X m false G K sonst csonst) (hr : BlockSemG X m G K rest crest) :
    BlockSemG X m G K (Block.pruefung c sonst rest)
      (.seq (.ite (.lnot (cc.zs G.gs)) csonst .skip) crest) := by
  intro σ st ρG ρC hcw hrel hnf
  have hc' : corrW X.EL (σ.lese Λ c.orte) st := (corrW_lese _ _ _ _ _).mpr hcw
  obtain ⟨st1, h1, hc1⟩ := hc.runB X K hc' hrel.1
  have hs1 := ev_same X.EL.lay X.orc X.fr cc st _ _ st1 h1
  have h1' : ev X.EL.lay X.orc X.fr (cc.zs G.gs) st ρC =
      some (.int (b2i (wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρG))), st1) := by
    rw [ev_zs G.gs cc st st ρC (SameML.refl _)]; exact h1
  have hrel1 := envRelG_same hs1 hrel
  have hex : execBlock X.O X.passes X.R (Block.pruefung c sonst rest) σ ρG =
      if wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρG) then
        execBlock X.O X.passes X.R rest (σ.lese Λ c.orte) ρG
      else (execEnd X.O X.passes X.R sonst (σ.lese Λ c.orte) ρG).zuAusgang := rfl
  rw [hex] at hnf ⊢
  cases hb : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρG) with
  | true =>
      rw [hb] at h1'
      simp only [hb, if_true] at hnf ⊢
      obtain ⟨o, hx, hO⟩ := hr _ st1 ρG ρC hc1 hrel1 hnf
      exact ⟨o, Exec.seqN (Exec.iteF (ev_lnot h1' (truth_b2i _)) rfl Exec.skip) hx, hO⟩
  | false =>
      rw [hb] at h1'
      simp only [hb, Bool.false_eq_true, if_false] at hnf ⊢
      rw [endIstFehler_zu] at hnf
      obtain ⟨o, hx, hO⟩ := hs _ st1 ρG ρC hc1 hrel1 hnf
      obtain ⟨hO', hab⟩ := endOutG_zu0 X m G _ o hO
      exact ⟨o, Exec.seqX (Exec.iteT (ev_lnot h1' (truth_b2i _)) rfl hx) hab, hO'⟩

end Zweige

/-! ## 9. `match` on a tagged union -/

/-- The payload of a case as a number (`0` for a case without one). -/
def nutzN : (c : Option (Int × Int)) → Nutzlast c → Int
  | none, _ => 0
  | some (lo, hi), z => (show Zahl lo hi from z).n

/-- Arm `i` of a tagged-union match. -/
def Arms.get {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    {cs : List (Option (Int × Int))} → Arms D V l Γ Λ Λ' cs → (i : Fin cs.length) →
      Block D V l (ArmCtx Γ (cs.get i)) Λ Λ'
  | _ :: _, .cons b _, ⟨0, _⟩ => b
  | _ :: _, .cons _ rest, ⟨i + 1, h⟩ => rest.get ⟨i, Nat.lt_of_succ_lt_succ h⟩

theorem execArms_get (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (w : Wert D (.sum cs))
      (σ : World D) (ρ : Env D Γ),
      execArms O passes R arms w σ ρ =
        (execBlock O passes R (arms.get w.1) σ (armEnv w.2 ρ)).schrumpfArm (cs.get w.1)
  | _ :: _, .cons _ _, ⟨⟨0, _⟩, _⟩, _, _ => rfl
  | _ :: _, .cons _ rest, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ =>
      execArms_get O passes R rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩ σ ρ

section Markiert

variable (X : TVCtx D) (m : Nat) (G : GCtx) {Γ : Ctx} (K : CEnvLay D Γ) {V : Vertrag D}
  {l : Bool}

/-- WHERE THE UNION LIVES: `cp` is the address of a `struct { T_marke
    marke; union { … } last; }` (a by-value parameter's stack block, a
    slot field) holding the Gabbro value: `marke` is the case's index
    (the enum's constants are the case order), the payload of a case with
    one is at `last` (offset `offL`, C type `τs i`). The memory relation
    `corrW` cannot hold a union (`tyFits (.sum _) _ = false`), so this is
    the certificate's premise about the scrutinee. -/
def SumCorr {Λ : List (Res D)} {cs : List (Option (Int × Int))} (cp : CX) (τm : CTy) (offL : Nat)
    (τs : Fin cs.length → CTy) (v : Expr D Γ Λ (.sum cs)) : Prop :=
  ∀ (σ : World D) (st : CSt) (ρG : Env D Γ) (ρC : CLok), corrW X.EL σ st →
    EnvRelG X G K ρG ρC st →
    (∃ st', ev X.EL.lay X.orc X.fr (.ld cp τm) st ρC =
        some (.int (((eval σ v σ ρG).1 : Nat) : Int), st') ∧ SameML st st') ∧
    (∀ lo hi, cs.get (eval σ v σ ρG).1 = some (lo, hi) →
      ∃ st', ev X.EL.lay X.orc X.fr (.ld (.fld cp offL) (τs (eval σ v σ ρG).1)) st ρC =
          some (.int (nutzN _ (eval σ v σ ρG).2), st') ∧ SameML st st')

/-- An emitted arm: without a payload, the arm's block; with one,
    `T x = cp->last.F;` first, into a fresh C local. -/
def ArmPasst {Λ Λ' : List (Res D)} (cp : CX) (offL : Nat) (τ : CTy) :
    (c : Option (Int × Int)) → Block D V l (ArmCtx Γ c) Λ Λ' → CS → Prop
  | none, b, cb => BlockSemG X m G K b cb
  | some (lo, hi), b, cb => ∃ x c', cb = .seq (.set x τ (.ld (.fld cp offL) τ)) c' ∧
      K.okB = true ∧ K.freshB x = true ∧ x ∉ geister G.gs ∧
      (∀ κ, G.kan = some κ → x ≠ κ.wx ∧ x ≠ κ.gx) ∧ declOk (.int lo hi) τ = true ∧
      BlockSemG X m G (K.push (.int lo hi) x) b c'

theorem armRun {Λ Λ' : List (Res D)} (cp : CX) (offL : Nat) (τ : CTy) :
    ∀ (c : Option (Int × Int)) (b : Block D V l (ArmCtx Γ c) Λ Λ') (cb : CS) (nutz : Nutzlast c)
      (σ : World D) (st : CSt) (ρG : Env D Γ) (ρC : CLok), ArmPasst X m G K cp offL τ c b cb →
      corrW X.EL σ st → EnvRelG X G K ρG ρC st →
      (∀ lo hi, c = some (lo, hi) → ∃ st', ev X.EL.lay X.orc X.fr (.ld (.fld cp offL) τ) st ρC =
          some (.int (nutzN c nutz), st') ∧ SameML st st') →
      ((execBlock X.O X.passes X.R b σ (armEnv nutz ρG)).schrumpfArm c).istFehler = false →
      ∃ o, Exec X.EL.lay X.orc X.fr X.CR X.XR cb st ρC o ∧
        StOutG X m G K ((execBlock X.O X.passes X.R b σ (armEnv nutz ρG)).schrumpfArm c) o
  | none, b, cb, nutz, σ, st, ρG, ρC, hA, hc, hr, _, hnf => hA σ st ρG ρC hc hr hnf
  | some (lo, hi), b, cb, nutz, σ, st, ρG, ρC, hA, hc, hr, hpay, hnf => by
      obtain ⟨x, c', hcb, hK, hf, hg, hkx, hd, hb⟩ := hA
      subst hcb
      obtain ⟨st1, h1, hs1⟩ := hpay lo hi rfl
      have hv : ValCorr X.EL (.int lo hi) nutz (.int (nutzN (some (lo, hi)) nutz)) := rfl
      have hr1 := envRelG_push hK hf hg hkx (envRelG_same hs1 hr)
        (show Wert D (.int lo hi) from nutz) _ hv
      have hnf' : (execBlock X.O X.passes X.R b σ (.cons nutz ρG)).istFehler = false := by
        have e : ((execBlock X.O X.passes X.R b σ (armEnv nutz ρG)).schrumpfArm (some (lo, hi))) =
            (execBlock X.O X.passes X.R b σ (.cons nutz ρG)).schrumpf := rfl
        rw [e] at hnf
        exact (istFehler_schrumpf _).symm.trans hnf
      obtain ⟨o, hx, hO⟩ := hb σ st1 _ _ (corrW_same hc hs1) hr1 hnf'
      exact ⟨o, Exec.seqN (Exec.set h1 (convV_of_valCorr hv hd)) hx,
        stOutG_schrumpf X m G _ o hO⟩

/-- R5. `switch (cp->marke) { case K: { [T x = cp->last.K;] … } break; … }`
    against `match` on a tagged union. -/
theorem gcorr_onTag {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    {v : Expr D Γ Λ (.sum cs)} {arms : Arms D V l Γ Λ Λ' cs} {cp : CX} {τm : CTy} {offL : Nat}
    {τs : Fin cs.length → CTy} {carms : List (Int × CS)} (hv : SumCorr X G K cp τm offL τs v)
    (harms : ∀ i : Fin cs.length, ∃ cb, carms.lookup ((i : Nat) : Int) = some (.seq cb .brk) ∧
      ArmPasst X m G K cp offL (τs i) (cs.get i) (arms.get i) cb) :
    StmtCorrG X m G K (Stmt.onTag v arms) (.sw (.ld cp τm) carms) := by
  intro σ st ρG ρC hc hrel hnf
  have hc' : corrW X.EL (σ.lese Λ v.orte) st := (corrW_lese _ _ _ _ _).mpr hc
  obtain ⟨⟨st1, h1, hs1⟩, -⟩ := hv _ st ρG ρC hc' hrel
  have hex : execStmt X.O X.passes X.R (Stmt.onTag v arms) σ ρG =
      (execBlock X.O X.passes X.R (arms.get (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρG).1)
        (σ.lese Λ v.orte) (armEnv (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρG).2 ρG)).schrumpfArm
        (cs.get (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρG).1) := by
    show execArms _ _ _ _ _ _ _ = _
    exact execArms_get _ _ _ _ _ _ _
  rw [hex] at hnf ⊢
  obtain ⟨cb, hl, hA⟩ := harms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρG).1
  have hc1 := corrW_same hc' hs1
  have hrel1 := envRelG_same hs1 hrel
  obtain ⟨o, hx, hO⟩ := armRun X m G K cp offL _ _ _ cb _ _ st1 ρG ρC hA hc1 hrel1
    (fun lo hi hcs => (hv _ st1 ρG ρC hc1 hrel1).2 lo hi hcs) hnf
  obtain ⟨hnb, hnc⟩ := stOutG_nichtBrk X m G K hO
  obtain ⟨o', hx', hu⟩ := arm_brk hx hnb hnc
  refine ⟨o, ?_, hO⟩
  rw [← hu]
  exact Exec.swHit h1 hl hx'

end Markiert

/-! ### Lifetimes through a call without calls -/

mutual
/-- A statement with no call, no foreign call and no atomic or volatile
    access: it changes no lifetime. -/
def CS.einfach : CS → Bool
  | .skip => true
  | .seq a b => CS.einfach a && CS.einfach b
  | .expr _ => true
  | .set _ _ _ => true
  | .store _ _ _ => true
  | .ite _ a b => CS.einfach a && CS.einfach b
  | .sw _ arms => CS.armsEinfach arms
  | .ret _ => true
  | .brk => true
  | .cont => true
  | .goto _ => true
  | .forC _ s b _ => CS.einfach s && CS.einfach b
  | .vstore _ _ _ => false
  | .astore _ _ _ _ => false
  | .acas _ _ _ _ _ _ _ => false
  | .call _ _ _ => false
  | .ext _ _ _ => false
def CS.armsEinfach : List (Int × CS) → Bool
  | [] => true
  | (_, s) :: rest => CS.einfach s && CS.armsEinfach rest
end

theorem armsEinfach_lookup : ∀ (arms : List (Int × CS)) (k : Int) (s : CS),
    CS.armsEinfach arms = true → arms.lookup k = some s → s.einfach = true
  | [], _, _, _, h => by simp at h
  | (k', s') :: rest, k, s, hw, hl => by
      simp only [CS.armsEinfach, Bool.and_eq_true] at hw
      rw [List.lookup_cons] at hl
      cases hk : (k == k') with
      | true => rw [hk] at hl; cases hl; exact hw.1
      | false => rw [hk] at hl; exact armsEinfach_lookup rest k s hw.2 hl

theorem zst_unbreak (o : COut) : o.unbreak.zst = o.zst := by
  cases o <;> rfl

theorem zst_weiter {o : COut} {m : Nat} {s : CSt} {r : CLok} (h : o.weiter m = some (s, r)) :
    o.zst = s := by
  cases o with
  | norm s1 r1 => simp only [COut.weiter, Option.some.injEq, Prod.mk.injEq] at h; exact h.1
  | cont s1 r1 => simp only [COut.weiter, Option.some.injEq, Prod.mk.injEq] at h; exact h.1
  | jump lb s1 r1 =>
      cases lb with
      | weiter m' =>
          simp only [COut.weiter] at h
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.1
          · exact absurd h (by simp)
      | ende m' => simp [COut.weiter] at h
  | ret s1 v => simp [COut.weiter] at h
  | brk s1 r1 => simp [COut.weiter] at h

theorem zst_raus {o o' : COut} {m : Nat} (h : o.raus m = some o') : o'.zst = o.zst := by
  cases o with
  | brk s1 r1 => simp only [COut.raus, Option.some.injEq] at h; subst h; rfl
  | ret s1 v => simp only [COut.raus, Option.some.injEq] at h; subst h; rfl
  | jump lb s1 r1 =>
      cases lb with
      | ende m' =>
          simp only [COut.raus] at h
          split at h <;> (simp only [Option.some.injEq] at h; subst h; rfl)
      | weiter m' =>
          simp only [COut.raus] at h
          split at h
          · exact absurd h (by simp)
          · simp only [Option.some.injEq] at h; subst h; rfl
  | norm s1 r1 => simp [COut.raus] at h
  | cont s1 r1 => simp [COut.raus] at h

/-- A simple statement changes no lifetime. -/
theorem exec_live_einfach {L : CLayout} {orc : DevOrc} {fr : Nat} {CR XR : CCallR} {cs : CS}
    {st : CSt} {ρ : CLok} {o : COut} (h : Exec L orc fr CR XR cs st ρ o) :
    cs.einfach = true → o.zst.live = st.live := by
  induction h with
  | skip => intro _; rfl
  | seqN _ _ ih1 ih2 =>
      intro he
      simp only [CS.einfach, Bool.and_eq_true] at he
      rw [ih2 he.2]; exact ih1 he.1
  | seqX _ _ ih1 =>
      intro he
      simp only [CS.einfach, Bool.and_eq_true] at he
      exact ih1 he.1
  | expr hev => intro _; exact (ev_same _ _ _ _ _ _ _ _ hev).2
  | set hev _ => intro _; exact (ev_same _ _ _ _ _ _ _ _ hev).2
  | store hp he _ hs =>
      intro _
      simp only [COut.zst]
      rw [(bStore_frame hs).1, (ev_same _ _ _ _ _ _ _ _ he).2, (ev_same _ _ _ _ _ _ _ _ hp).2]
  | vstore => intro he; simp [CS.einfach] at he
  | astore => intro he; simp [CS.einfach] at he
  | acas => intro he; simp [CS.einfach] at he
  | iteT hc _ _ ih =>
      intro he
      simp only [CS.einfach, Bool.and_eq_true] at he
      rw [ih he.1]; exact (ev_same _ _ _ _ _ _ _ _ hc).2
  | iteF hc _ _ ih =>
      intro he
      simp only [CS.einfach, Bool.and_eq_true] at he
      rw [ih he.2]; exact (ev_same _ _ _ _ _ _ _ _ hc).2
  | @swHit e arms st ρ k st1 s o he hl _ ih =>
      intro hE
      rw [zst_unbreak, ih (armsEinfach_lookup arms k s hE hl)]
      exact (ev_same _ _ _ _ _ _ _ _ he).2
  | swMiss he _ => intro _; exact (ev_same _ _ _ _ _ _ _ _ he).2
  | retN => intro _; rfl
  | retS he _ => intro _; exact (ev_same _ _ _ _ _ _ _ _ he).2
  | brk => intro _; rfl
  | cont => intro _; rfl
  | goto => intro _; rfl
  | forDone hc _ => intro _; exact (ev_same _ _ _ _ _ _ _ _ hc).2
  | forStep hc _ _ hw _ _ ihb ihs ihr =>
      intro he
      have he' := he
      simp only [CS.einfach, Bool.and_eq_true] at he
      have h1 := ihr he'
      have h2 := ihs he.1
      have h3 := ihb he.2
      simp only [COut.zst] at h2
      rw [h1, h2, ← zst_weiter hw, h3]
      exact (ev_same _ _ _ _ _ _ _ _ hc).2
  | forExit hc _ _ hx ihb =>
      intro he
      simp only [CS.einfach, Bool.and_eq_true] at he
      rw [zst_raus hx, ihb he.2]
      exact (ev_same _ _ _ _ _ _ _ _ hc).2
  | call => intro he; simp [CS.einfach] at he
  | ext => intro he; simp [CS.einfach] at he

/-- A call into a simple body changes no lifetime outside the callee's
    frame. -/
theorem callAt_live {L : CLayout} {orc : DevOrc} {XR : CCallR} {Pr : CProg} {n f : Nat}
    {F : CFun} (hPr : Pr f = some F) (hF : F.body.einfach = true) {st : CSt} {vs : List CVal}
    {st' : CSt} {rv : Option CVal} (h : CallAt L orc XR Pr (n + 1) f st vs st' rv) (b : CBlk)
    (hb : ∀ x, b ≠ .stk (n + 1) x) : st'.live b = st.live b := by
  obtain ⟨F', ρ0, o, hP, -, hx, st1, ho, rfl⟩ := h
  rw [hPr] at hP
  cases hP
  have hl := exec_live_einfach hx hF
  have hz : o.zst = st1 := by
    rcases ho with rfl | ⟨-, ρ1, rfl⟩ <;> rfl
  rw [hz] at hl
  show (leaveFrame st1 (n + 1)).live b = _
  rw [show (leaveFrame st1 (n + 1)).live b = st1.live b from by
    cases b with
    | stk f' x =>
        show (if f' = n + 1 then false else st1.live (.stk f' x)) = _
        rw [if_neg (fun e => hb x (by rw [e]))]
    | _ => rfl]
  rw [hl, enterFrame_live_ne st (n + 1) F.locals hb]

/-! ## 10. CUTS and axioms -/

/-
CUTS: what this file does not do, by name.
- THE FRAME OF A STATEMENT IS A PREMISE (`KeepsG`, per lifted statement;
  `CallKeeps`, per call site): that a statement's stores and calls do not
  reach the out-parameter cells is proved by the certificate for its
  statement, not derived from a provenance discipline of the C model.
  `callAt_live` discharges the lifetime half for a callee without calls.
- THE ORDINAL CONVENTION (header): where a reason read from a C local or
  cell meets `ValCorr`, its constant is its index (`hcode`). With the
  emitter's 1-based enum constants the elaboration numbers reasons from 1
  and leaves index 0 to an arm that fails (`gcorr_onGrund`'s second
  disjunct). The channel itself (`kcorr_retGrund`, `cCorr_rufK`) is
  generic in the constant.
- A GABBRO `narrow` OF A PLACE THAT IS NOT A LOCAL (`narrow
  g.slots[s].zaehler to 1 .. H else …`, `beispiele/48`) binds a value
  the C never names: `gsem_narrow` needs a C position for it, and a slot
  cell is not one (a later store to the slot would change the "binding").
  Where the binding is unused, the check alone is `gsem_pruefung`.
- A TAGGED UNION IN MEMORY has no memory relation (`tyFits (.sum _) _ =
  false`, no `EmitLay` for a table with a union field); `gcorr_onTag`
  takes where the union lives as a premise (`SumCorr`). IT IS NOT
  INHABITED: `ValCorr (.sum _)` is `False`, so no related state has a
  union-typed variable, and the grammar builds a union only from a
  static constructor (`Expr.fall`) -- a FINDING about the value relation,
  which would need a state to relate a union (it lives in a struct, not
  in one cell).
- A REASON COMPARED WITH `==` (`if (e == Buchfehler_Unbelegt)`,
  `beispiele/48` `nur_unbelegte_zaehlen`) has no Gabbro expression: the
  grammar compares only integers; the form has no lemma.
- `Endblock` HAS NO BINDING CONSTRUCTORS (no `narrow`, `pruefung`,
  `bindCall`, `bindCallElse`): a function body whose top level binds
  through a check or a call is elaborated through a statement holding a
  block (`breaking`, `locks`); `EndCorrG.endet` ends the body there.
- A channel function whose body loops (`traverse`, `retry`) and returns
  from inside the loop needs the loop lemmas in the channel form; only
  the lift of a loop that does not return is covered (`liftG`).
- The call's answer is read in C's `if (!f(…))` directly; the model
  writes it into a fresh local `tmp` first (`callElseCS`): the same run
  (the call is the condition's full expression, 6.8.4.1).
-/


#print axioms ev_agree
#print axioms exec_agree
#print axioms ev_zs
#print axioms stmtCorr_G0
#print axioms endSem_G0
#print axioms liftG
#print axioms liftG_zs
#print axioms exec_zs_blatt
#print axioms cCorrG_block
#print axioms cCorrG_end
#print axioms kcorr_retGrund
#print axioms kcorr_ret
#print axioms gcorr_ite
#print axioms cCorr_rufK
#print axioms bsemG_bindCallElse
#print axioms gcorr_onGrund
#print axioms kcorr_weiterleiten
#print axioms narrowCond_ge_le
#print axioms gsem_narrow
#print axioms narrow_bind_var
#print axioms gsem_pruefung
#print axioms gcorr_onTag
#print axioms gcorr_breaking
#print axioms gcorr_extPre
#print axioms gcorr_locks
#print axioms exec_live_einfach
#print axioms callAt_live
#print axioms cCorr_rufG
#print axioms gcorr_seqTot
#print axioms narrowCond_le0
#print axioms narrowCond_lt0
#print axioms ecorr_grundLit

end Gabbro.Grammatik
