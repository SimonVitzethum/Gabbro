/-
  File:      stage0/Stage0/Senke/Bild/Mehr/Ort/Segment.lean
  Subject:   SEGMENTS (multi-thread image theorem, package MT3, first piece). A segment is the part of a thread's
             decomposed prefix between two synchronisation points: memory statements (`OrtPrem`) and bindings,
             every carrier they read or write in the segment's carriers `C`. A lock, an atomic, a call, a register
             or an outside access is not in it -- there a segment ends (the steps at the synchronisation points are
             the later packages). `Segment` is the decomposed prefix (`Zerlegung`) with these premises; forgetting
             them gives the prefix itself (`segment_zerlegung`), so the single-thread chain P0-P5 applies to a
             segment unchanged.
             THE COMMIT OF A SEGMENT (`randG_segment`): machine G's thread, standing in the CURRENT machine `N` at
             the segment's start with a world `σ'` that agrees on `C` with the world `σ` the chain ran the segment
             from, takes the whole segment by its own steps -- statement by statement (`randG_schritt` on the
             statement's run from the current world, `ort_stmt_ok`), binding by binding (`randG_bind`, the value
             is the same by `OrtGleich.wert`) -- and stands at the segment's end with the thread's own result on
             `C` and the current world everywhere else. `randG_segment_ein` starts from the view machine of the
             chain; `fadenX_segment` lifts the commit to the thread machine over GX.
-/
module
public import Stage0.Senke.Bild.Mehr.Ort.Commit
public import Stage0.Senke.Bild.Mehr.Relation
@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Gabbro.Grammatik Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildLauf

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-- **A segment**: a decomposed prefix of memory statements and bindings, every carrier in `C`. -/
inductive Segment (O : Orakel D) (passes : Nat) (R : (g : D.Fn) → World D → Env D (D.params g) → RufAusgang g)
    (Agl : D.Lock → Prop) (Cg : D.Fn → Prop) (C : D.Tab ⊕ D.Glob → Prop) {V : Vertrag D} {l : Bool} :
    {Γ : Ctx} → {Λ : List (Res D)} → Endblock D V l Γ Λ → World D → Env D Γ →
    {Γe : Ctx} → {Λe : List (Res D)} → Endblock D V l Γe Λe → World D → Env D Γe → Prop where
  | halt {Γ : Ctx} {Λ : List (Res D)} (eb : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
      Segment O passes R Agl Cg C eb σ ρ eb σ ρ
  | schritt {Γ Γe : Ctx} {mr : Bool} {Λ Λ' Λe : List (Res D)} (s : Stmt D V l Γ Λ Λ')
      (rest : Endblock D V l Γ Λ') (ebe : Endblock D V l Γe Λe) (σ σ1 σe : World D) (ρ ρ1 : Env D Γ)
      (ρe : Env D Γe) (hs : StmtR Agl Cg mr s) (hC : OrtPrem C s) (hex : execStmt O passes R s σ ρ = .ok σ1 ρ1)
      (hk : Segment O passes R Agl Cg C rest σ1 ρ1 ebe σe ρe) :
      Segment O passes R Agl Cg C (.cons s rest) σ ρ ebe σe ρe
  | bind {Γ Γe : Ctx} {Λ Λe : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) (rest : Endblock D V l (τ :: Γ) Λ)
      (ebe : Endblock D V l Γe Λe) (σ σe : World D) (ρ : Env D Γ) (ρe : Env D Γe) (hC : ∀ o ∈ e.orte, C o)
      (hk : Segment O passes R Agl Cg C rest (σ.lese Λ e.orte)
        (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) ebe σe ρe) :
      Segment O passes R Agl Cg C (.bind e rest) σ ρ ebe σe ρe

/-- **A segment is a decomposed prefix**: the single-thread chain applies to it unchanged. -/
theorem segment_zerlegung {B : BodyFrame D} {Agl : D.Lock → Prop} {Cg : D.Fn → Prop} {C : D.Tab ⊕ D.Glob → Prop}
    {l : Bool} {Γ Γe : Ctx} {Λ Λe : List (Res D)} {eb : Endblock D (vertragVon D B.f) l Γ Λ}
    {ebe : Endblock D (vertragVon D B.f) l Γe Λe} {σ σe : World D} {ρ : Env D Γ} {ρe : Env D Γe}
    (hk : Segment B.O B.passes B.R Agl Cg C eb σ ρ ebe σe ρe) : Zerlegung B Agl Cg eb σ ρ ebe σe ρe := by
  induction hk with
  | halt eb σ ρ => exact .halt eb σ ρ
  | schritt s rest ebe σ σ1 σe ρ ρ1 ρe hs _ hex _ ih => exact .schritt s rest ebe σ σ1 σe ρ ρ1 ρe hs hex ih
  | bind e rest ebe σ σe ρ ρe _ _ ih => exact .bind e rest ebe σ σe ρ ρe ih

private theorem OrtPrem.blatt {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ out : List (Res D)} {C : D.Tab ⊕ D.Glob → Prop} {s : Stmt D V l Γ Λ out}
    (admitted : OrtPrem C s) : BlattG s := by
  cases s <;> first | exact False.elim admitted | constructor

private def axiomOfEvent : Ereignis D → Option D.Ax
  | .fremd (.inl called) => some called
  | _ => none

private theorem read_trace (world : World D) (held : List (Res D)) (carriers : List (D.Tab ⊕ D.Glob)) :
    (world.lese held carriers).spur.filterMap axiomOfEvent = world.spur.filterMap axiomOfEvent := by
  simp only [World.lese, World.merke, List.filterMap_append, List.filterMap_map]
  let readEvent : D.Tab ⊕ D.Glob → Ereignis D := fun carrier => match carrier with
    | .inl table => .zugriff table false held world.haelt
    | .inr global => .gzugriff global false held world.haelt
  have silent : carriers.filterMap (axiomOfEvent ∘ readEvent) = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro carrier _
    cases carrier <;> rfl
  change carriers.filterMap (axiomOfEvent ∘ readEvent) ++ _ = _
  rw [silent, List.nil_append]

private theorem write_bytes_trace (table : D.Tab) (field : D.Feld table) (byteType : D.typ table field = .int 0 255)
    (held : List (Res D)) (data : List Byte) (world : World D) (index : Int) :
    (world.schreibBytes table field byteType held index data).spur.filterMap axiomOfEvent =
      world.spur.filterMap axiomOfEvent := by
  induction data generalizing world index with
  | nil => rfl
  | cons byte tail ih =>
    rw [World.schreibBytes, ih]
    rfl

private theorem OrtPrem.foreign_trace {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ out : List (Res D)} {C : D.Tab ⊕ D.Glob → Prop} {s : Stmt D V l Γ Λ out}
    (admitted : OrtPrem C s) (O : Orakel D) (passes : Nat)
    (R : (g : D.Fn) → World D → Env D (D.params g) → RufAusgang g)
    {before after : World D} {locals updated : Env D Γ}
    (executed : execStmt O passes R s before locals = .ok after updated) :
    after.spur.filterMap axiomOfEvent = before.spur.filterMap axiomOfEvent := by
  cases admitted.blatt with
  | transition | regWrite | publish | advances | retires => cases admitted
  | shift =>
    simp only [execStmt] at executed
    split at executed
    · simp only [Ausgang.ok.injEq] at executed
      obtain ⟨rfl, _⟩ := executed
      exact read_trace _ _ _
    · cases executed
  | putBytes =>
    simp only [execStmt, Ausgang.ok.injEq] at executed
    obtain ⟨rfl, _⟩ := executed
    rw [write_bytes_trace, read_trace]
  | assignSlot | assignThru | assignThruOwn | assignSlotRef | assignGlob | assignVar =>
    simp only [execStmt, Ausgang.ok.injEq] at executed
    obtain ⟨rfl, _⟩ := executed
    exact read_trace _ _ _

/-- The exact suffix introduced by a private source segment. -/
def PrivateSourceTrace (before after : Lauf D) : Prop :=
  ∃ suffix, after = before ++ suffix ∧
    ∀ item ∈ suffix, ∀ called : D.Ax, item.ereignis ≠ .fremd (.inl called)

private theorem PrivateSourceTrace.trans {start middle finish : Lauf D}
    (left : PrivateSourceTrace start middle) (right : PrivateSourceTrace middle finish) :
    PrivateSourceTrace start finish := by
  obtain ⟨first, before, quietFirst⟩ := left
  obtain ⟨last, after, quietLast⟩ := right
  refine ⟨first ++ last, by rw [after, before, List.append_assoc], ?_⟩
  intro item member
  rcases List.mem_append.mp member with here | there
  · exact quietFirst item here
  · exact quietLast item there

private theorem privateTrace_append (run : Lauf D) (thread : Faden) {events : List (Ereignis D)}
    (quiet : events.filterMap axiomOfEvent = []) : PrivateSourceTrace run (run ++ rufEigenG thread events) := by
  refine ⟨_, rfl, ?_⟩
  intro item member called reported
  obtain ⟨event, found, rfl⟩ := List.mem_map.mp member
  have silent := List.filterMap_eq_nil_iff.mp quiet event (List.mem_reverse.mp found)
  change event = .fremd (.inl called) at reported
  rw [reported] at silent
  cases silent

private theorem privateLeafStep {P : Programm D} {O : Orakel D} {passes : Nat}
    {M : RufMaschineG D} {thread : Faden} {head : RufFadenG D}
    (frame : M.faeden thread = head) {l : Bool} {Γ : Ctx} {Λ out : List (Res D)}
    {C : D.Tab ⊕ D.Glob → Prop} {statement : Stmt D (vertragVon D head.kopf.f) l Γ Λ out}
    {rest : Endblock D (vertragVon D head.kopf.f) l Γ out} {locals updated : Env D Γ}
    {world : World D} (admitted : OrtPrem C statement)
    (ready : head.kopf.rest = ⟨l, Γ, Λ, locals, .ende (.cons statement rest)⟩)
    (held : Gabbro.Grammatik.HeldIn Λ (offen head.spur))
    (executed : execStmt O passes keinRuf statement (M.weltVon thread) locals = .ok world updated) :
    ∃ next, RufSchrittG P O passes M thread next ∧
      ZustandG next thread head.stapel head.kopf.f head.kopf.rho head.kopf.s0 head.log updated (.ende rest) world ∧
      PrivateSourceTrace M.lauf next.lauf := by
  subst head
  have leaf := admitted.blatt
  obtain ⟨events, added, accesses⟩ := leaf.erw O passes keinRuf _ _ _ _ executed
  have trace := admitted.foreign_trace O passes keinRuf executed
  rw [added, List.filterMap_append] at trace
  have quiet : events.filterMap axiomOfEvent = [] :=
    List.append_cancel_right (trace.trans (List.nil_append _).symm)
  exact ⟨_, .blatt M thread l Γ Λ out statement rest locals leaf.istBlatt ready held world updated events
    executed added (kein_nimmt accesses), zustandG_neu rfl rfl, privateTrace_append M.lauf thread quiet⟩

private theorem privateBindStep {P : Programm D} {O : Orakel D} {passes : Nat}
    {M : RufMaschineG D} {thread : Faden} {head : RufFadenG D}
    (frame : M.faeden thread = head) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    {expr : Expr D Γ Λ τ} {rest : Endblock D (vertragVon D head.kopf.f) l (τ :: Γ) Λ} {locals : Env D Γ}
    (ready : head.kopf.rest = ⟨l, Γ, Λ, locals, .ende (.bind expr rest)⟩)
    (held : Gabbro.Grammatik.HeldIn Λ (offen head.spur)) :
    let world := (M.weltVon thread).lese Λ expr.orte
    ∃ next, RufSchrittG P O passes M thread next ∧
      ZustandG next thread head.stapel head.kopf.f head.kopf.rho head.kopf.s0 head.log
        (.cons (eval world expr world locals) locals) (.ende rest) world ∧
      PrivateSourceTrace M.lauf next.lauf := by
  intro world
  subst head
  obtain ⟨events, added, _⟩ := Erw.lese (M.weltVon thread) Λ expr.orte
  have trace := read_trace (M.weltVon thread) Λ expr.orte
  rw [added, List.filterMap_append] at trace
  have quiet : events.filterMap axiomOfEvent = [] :=
    List.append_cancel_right (trace.trans (List.nil_append _).symm)
  exact ⟨_, .endeBind M thread l Γ Λ τ expr rest locals ready world rfl events added held,
    zustandG_neu rfl rfl, privateTrace_append M.lauf thread quiet⟩

/-- Internal memory segments preserve the exact set of held locks.
    Bindings record reads and the ordinary statement theorem covers
    each admitted memory effect. -/
theorem Segment.holdings {O : Orakel D} {passes : Nat}
    {R : (g : D.Fn) → World D → Env D (D.params g) → RufAusgang g}
    {Agl : D.Lock → Prop} {Cg : D.Fn → Prop} {C : D.Tab ⊕ D.Glob → Prop} {V : Vertrag D} {l : Bool}
    {Γ Γe : Ctx} {Λ Λe : List (Res D)} {eb : Endblock D V l Γ Λ} {ebe : Endblock D V l Γe Λe}
    {σ σe : World D} {ρ : Env D Γ} {ρe : Env D Γe}
    (segment : Segment O passes R Agl Cg C eb σ ρ ebe σe ρe) :
    offen σe.spur = offen σ.spur := by
  induction segment with
  | halt => rfl
  | schritt _ _ _ _ _ _ _ _ _ _ admitted executed _ ih =>
    exact ih.trans ((OrtPrem.blatt admitted).erw O passes R _ _ _ _ executed).offen
  | bind _ _ _ _ _ _ _ _ _ ih =>
    exact ih.trans ((Erw.lese _ _ _).offen)

/-- **THE COMMIT OF A SEGMENT**, from the current machine. -/
theorem randG_segment {P : Programm D} {O : Orakel D} {passes : Nat}
    {R : (g : D.Fn) → World D → Env D (D.params g) → RufAusgang g} {Cg : D.Fn → Prop} {thr : Faden}
    {stapel : List (RufRahmenG D)} {f : D.Fn} {rho : Env D (D.params f)} {s0 : World D} {Agl : D.Lock → Prop}
    {C : D.Tab ⊕ D.Glob → Prop} {l : Bool} {Γ Γe : Ctx}
    {Λ Λe : List (Res D)} {eb : Endblock D (vertragVon D f) l Γ Λ} {ebe : Endblock D (vertragVon D f) l Γe Λe}
    {σ σe : World D} {ρ : Env D Γ} {ρe : Env D Γe} (hk : Segment O passes R Agl Cg C eb σ ρ ebe σe ρe) :
    ∀ {N : RufMaschineG D} {σ' : World D}, RandG thr stapel f rho s0 Agl eb N σ' ρ → OrtGleich C σ σ' →
      ∃ (N' : RufMaschineG D) (σe' : World D), RufLaufG P O passes thr N N' ∧
        RandG thr stapel f rho s0 Agl ebe N' σe' ρe ∧ OrtGleich C σe σe' ∧
        PrivateSourceTrace N.lauf N'.lauf ∧
        ∀ c, ¬ C c → TraegerGleich σe'.speicher σ'.speicher c := by
  induction hk with
  | halt eb σ ρ =>
    intro N σ' h hσ
    exact ⟨N, σ', .refl N, h, hσ, ⟨[], (List.append_nil _).symm, fun _ h => (List.not_mem_nil h).elim⟩,
      fun c _ => traegerGleich_refl _ c⟩
  | schritt s rest ebe σ σ1 σe ρ ρ1 ρe _ hC hex _ ih =>
    intro N σ' h hσ
    obtain ⟨σ1', hex', hσ1⟩ := ort_stmt_ok O passes R hC hσ hex
    obtain ⟨⟨log, located⟩, held, free⟩ := h
    have leaf := hC.blatt
    have actual : execStmt O passes keinRuf s (N.weltVon thr) ρ = .ok σ1' ρ1 := by
      rw [located.welt, ← leaf.exec_R O passes R]
      exact hex'
    obtain ⟨N1, stepped, atRest, quiet⟩ := privateLeafStep (P := P) located.1 (rest := rest) hC rfl held.heldIn actual
    have one := RufLaufG.einzeln stepped
    have holding := (leaf.erw O passes R _ _ _ _ hex').offen
    have hR1 : RandG thr stapel f rho s0 Agl rest N1 σ1' ρ1 := by
      refine ⟨⟨log, atRest⟩, ?_, free.lauf one⟩
      rw [holding]
      exact heldB_iff (fun lock => s.held_iff lock) held
    obtain ⟨N', σe', hl2, hR2, hσe, trace, hfr⟩ := ih hR1 hσ1
    exact ⟨N', σe', one.trans hl2, hR2, hσe, PrivateSourceTrace.trans quiet trace,
      fun c hc => traegerGleich_trans (hfr c hc) (ort_rahmen O passes R s hC hex' c hc)⟩
  | @bind _ _ Λ _ _ e rest ebe σ σe ρ ρe hC _ ih =>
    intro N σ' h hσ
    obtain ⟨⟨log, located⟩, held, free⟩ := h
    obtain ⟨N1, stepped, atRest, quiet⟩ := privateBindStep (P := P) (O := O) (passes := passes)
      located.1 (expr := e) (rest := rest) (locals := ρ) rfl held.heldIn
    have he := (hσ.lese Λ e.orte).wert e hC ρ
    rw [located.welt, ← he] at atRest
    have one := RufLaufG.einzeln stepped
    have hR1 : RandG thr stapel f rho s0 Agl rest N1 (σ'.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) :=
      ⟨⟨log, atRest⟩, heldB_lese e.orte held, free.lauf one⟩
    obtain ⟨N', σe', hl2, hR2, hσe, trace, hfr⟩ := ih hR1 (hσ.lese _ e.orte)
    exact ⟨N', σe', one.trans hl2, hR2, hσe, PrivateSourceTrace.trans quiet trace,
      fun c hc => traegerGleich_trans (hfr c hc) (traeger_lese σ' _ _ c)⟩

/-- **The commit of a segment from the chain's view machine**: the current machine holds the thread's frame, a
    world agreeing on `C`, and no other holder of a lock the body may take. -/
theorem randG_segment_ein {P : Programm D} {O : Orakel D} {passes : Nat}
    {R : (g : D.Fn) → World D → Env D (D.params g) → RufAusgang g} {Cg : D.Fn → Prop} {thr : Faden}
    {stapel : List (RufRahmenG D)} {f : D.Fn} {rho : Env D (D.params f)} {s0 : World D} {Agl : D.Lock → Prop}
    {C : D.Tab ⊕ D.Glob → Prop} {l : Bool} {Γ Γe : Ctx}
    {Λ Λe : List (Res D)} {eb : Endblock D (vertragVon D f) l Γ Λ} {ebe : Endblock D (vertragVon D f) l Γe Λe}
    {σ σe σ' : World D} {ρ : Env D Γ} {ρe : Env D Γe} {M N : RufMaschineG D}
    (hk : Segment O passes R Agl Cg C eb σ ρ ebe σe ρe) (h : RandG thr stapel f rho s0 Agl eb M σ ρ)
    (hσ : OrtGleich C σ σ') (hf : N.faeden thr = M.faeden thr) (hsp : N.speicher = σ'.speicher)
    (hA : FreiA Agl N thr) :
    ∃ (N' : RufMaschineG D) (σe' : World D), RufLaufG P O passes thr N N' ∧
      RandG thr stapel f rho s0 Agl ebe N' σe' ρe ∧ OrtGleich C σe σe' ∧
      PrivateSourceTrace N.lauf N'.lauf ∧
      ∀ c, ¬ C c → TraegerGleich σe'.speicher σ'.speicher c :=
  randG_segment (P := P) hk (randG_umsetzen h hσ.spur hf hsp hA) hσ

/-- **The commit of a segment on the thread machine over GX.** -/
theorem fadenX_segment {P : Programm D} {O : Orakel D} {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    {R : (g : D.Fn) → World D → Env D (D.params g) → RufAusgang g} {Cg : D.Fn → Prop} {thr : Faden}
    {stapel : List (RufRahmenG D)} {f : D.Fn} {rho : Env D (D.params f)} {s0 : World D} {Agl : D.Lock → Prop}
    {C : D.Tab ⊕ D.Glob → Prop} {l : Bool} {Γ Γe : Ctx}
    {Λ Λe : List (Res D)} {eb : Endblock D (vertragVon D f) l Γ Λ} {ebe : Endblock D (vertragVon D f) l Γe Λe}
    {σ σe σ' : World D} {ρ : Env D Γ} {ρe : Env D Γe} {M : RufMaschineG D} {K0 K : FadenMaschine D}
    (hk : Segment O passes R Agl Cg C eb σ ρ ebe σe ρe) (h : RandG thr stapel f rho s0 Agl eb M σ ρ)
    (hσ : OrtGleich C σ σ') (hK : FadenErreichbarX P O passes Tg K0 K) (hl : K.lebt thr = true)
    (hw : K.wartet thr = []) (hf : K.m.faeden thr = M.faeden thr) (hsp : K.m.speicher = σ'.speicher)
    (hA : FreiA Agl K.m thr) :
    ∃ (N' : RufMaschineG D) (σe' : World D),
      FadenErreichbarX P O passes Tg K0 ⟨N', K.lebt, K.wartet, K.rang, K.uhr⟩ ∧
      RandG thr stapel f rho s0 Agl ebe N' σe' ρe ∧ OrtGleich C σe σe' ∧
      (∀ j, j ≠ thr → N'.faeden j = K.m.faeden j) ∧
      PrivateSourceTrace K.m.lauf N'.lauf ∧
      ∀ c, ¬ C c → TraegerGleich σe'.speicher σ'.speicher c := by
  obtain ⟨N', σe', hl', hR, hσe, quiet, hfr⟩ := randG_segment_ein (P := P) hk h hσ hf hsp hA
  exact ⟨N', σe', fadenErreichbarX_lauf' hl' hl hw hK, hR, hσe, rufLaufG_fremd hl', quiet, hfr⟩

/-- Commit a complete private segment from a registered IR thread to
    the current GX machine. Its saved view supplies the same typed
    endpoint and values on the segment carriers. Every other source
    thread and every carrier outside the segment is preserved. -/
theorem MTRel.commit_segment [Runner.IR.Kern] {P : Programm D} {O : Orakel D}
    {passes : Nat} {layout : Lay D} {program : PCfg} {source : FadenMaschine D}
    {snapshots : Nat → Option Solo} {positions : Nat → MLage D} {committed : Runner.Mem}
    {thread : Nat} {snapshot : Solo}
    (matched : MTRel P O passes layout program source snapshots positions committed)
    (registered : snapshots thread = some snapshot)
    {shared carriers : D.Tab ⊕ D.Glob → Prop} {pc : Runner.W} {Γ : Ctx} {Λ : List (Res D)}
    {rest : Endblock D (vertragVon D (positions thread).B.f) (positions thread).l Γ Λ}
    {world : World D} {env : Env D Γ}
    (quiet : let x := positions thread
      Segment x.B.O x.B.passes x.B.R x.Agl x.Cg carriers x.eb x.σ x.ρ rest world env)
    (control : snapshot.r = .next ⟨pc, (positions thread).B.fp⟩)
    (boundary : let x := positions thread
      x.B.RandIR rest pc snapshot.m world env)
    (agree : let x := positions thread
      OrtGleich carriers x.σ (source.m.speicher.welt x.σ.spur))
    (free : FreiA (positions thread).Agl source.m (positions thread).thr) :
    let x := positions thread
    ∃ machine finalWorld,
      FadenErreichbarX P O passes shared source
        ⟨machine, source.lebt, source.wartet, source.rang, source.uhr⟩ ∧
      program.ths[thread]? = some (some (.next ⟨pc, x.B.fp⟩)) ∧
      x.B.RandIR rest pc snapshot.m world env ∧
      RandG x.thr x.stapel x.B.f x.rho x.s0 x.Agl rest machine finalWorld env ∧
      OrtGleich carriers world finalWorld ∧
      (∀ other, other ≠ x.thr → machine.faeden other = source.m.faeden other) ∧
      (∀ thread, offen (machine.faeden thread).spur = offen (source.m.faeden thread).spur) ∧
      PrivateSourceTrace source.m.lauf machine.lauf ∧
      ∀ cell, ¬ carriers cell → TraegerGleich finalWorld.speicher source.m.speicher cell := by
  intro x
  obtain ⟨_, sameOracle, samePasses, _⟩ := matched.prog thread snapshot registered
  have position := matched.lage thread snapshot registered
  have semantics : Segment O passes x.B.R x.Agl x.Cg carriers x.eb x.σ x.ρ rest world env := by
    rw [← sameOracle, ← samePasses]
    exact quiet
  have storage : source.m.speicher = (source.m.speicher.welt x.σ.spur).speicher :=
    (speicher_welt_speicher _ _).symm
  obtain ⟨alive, waiting⟩ := matched.lebtG thread snapshot registered
  obtain ⟨machine, finalWorld, reached, sourceBoundary, sameWorld, otherThreads, quietTrace, otherCarriers⟩ :=
    fadenX_segment (Tg := shared) semantics position.rand.2 agree .start alive waiting
      (matched.amRand thread snapshot registered) storage free
  refine ⟨machine, finalWorld, reached, ?_, boundary, sourceBoundary, sameWorld, otherThreads, ?_, quietTrace, ?_⟩
  · exact (matched.zustand thread snapshot registered).trans (by rw [control])
  · intro issuer
    by_cases current : issuer = x.thr
    · rw [current]
      obtain ⟨_, entered⟩ := position.rand.2.1
      obtain ⟨_, exited⟩ := sourceBoundary.1
      have sourceSpur := congrArg RufFadenG.spur (matched.amRand thread snapshot registered)
      rw [exited.spur, ← sameWorld.spur, semantics.holdings, sourceSpur, entered.spur]
    · rw [otherThreads issuer current]
  · intro cell outside
    simpa only [speicher_welt_speicher] using otherCarriers cell outside

end Gabbro.Stage0.Senke.BildMehr
