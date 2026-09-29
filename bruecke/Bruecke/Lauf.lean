import Bruecke.Nachbedingung

/-!
# S3, part 5: the run -- a body of the parser's fragment, on G and on `Gabbro.Body`

The run of a lowered body on G (`execEnd` with a contract-respecting handler `R`) and the run of
the body `zuBody` computes (`Gabbro.Body.exec` with an environment `ρB`) end in related states
with the same answer -- for every `ρB` that answers each call the run makes with the answer `R`
gave there (an ANSWER TABLE, `Treu`) and respects every declared frame.

**Why a table, and why the ghost counters.** `R` sees the G world, which carries the thread's
lock TRACE; a Body environment sees only the Body state, which does not. Two calls of one callee
from the same Body state may therefore be answered differently by `R`. For a callee that writes
nothing that is harmless (its frame fixes the world, and `.call` drops the value); for a writer
the answer at a call point bumps a GHOST counter -- the field place `.field w "#"` of the
callee's first written carrier `w`, a place no pass, no body and no promise reads, and that the
callee may write exactly because it writes `w` (`Frame`). So the Body entry states of two calls
of one writer differ, and the table is a function (`Schluessel`).
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-! ## 1. Ghost counters -/

def geistOrt (w : String) : Gabbro.Body.Place := .field w "#"

def gz (w : String) (W : Gabbro.Body.World) : Int :=
  match W (geistOrt w) with
  | .int n => n
  | _ => 0

def bump (w : String) (W : Gabbro.Body.World) : Gabbro.Body.World :=
  Gabbro.Body.store W (geistOrt w) (.int (gz w W + 1))

theorem gz_store_slot (w c : String) (k : Int) (fld : String) (W : Gabbro.Body.World)
    (v : Gabbro.Body.Value) : gz w (Gabbro.Body.store W (.slot c k fld) v) = gz w W := by
  simp [gz, geistOrt, Gabbro.Body.store]

theorem gz_enc (w : String) (σ : World (declOf u)) (W : Gabbro.Body.World) :
    gz w (enc u σ W) = gz w W := by
  simp [gz, geistOrt, enc]

theorem gz_bump_self (w : String) (W : Gabbro.Body.World) : gz w (bump w W) = gz w W + 1 := by
  simp [gz, bump, Gabbro.Body.store]

theorem gz_bump_le (w w' : String) (W : Gabbro.Body.World) : gz w' W ≤ gz w' (bump w W) := by
  by_cases h : w' = w
  · subst h; rw [gz_bump_self]; omega
  · have : geistOrt w' ≠ geistOrt w := by simp [geistOrt, h]
    simp [gz, bump, Gabbro.Body.store, this]

theorem wrel_bump {σ : World (declOf u)} {W : Gabbro.Body.World} (w : String) (h : WRel u σ W) :
    WRel u σ (bump w W) := by
  intro c k fld v hv
  have : (Gabbro.Body.Place.slot c k fld) ≠ geistOrt w := by simp [geistOrt]
  simp only [bump, Gabbro.Body.store, this, ↓reduceIte]
  exact h c k fld v hv

/-! ## 2. The answer table -/

structure Eintrag where
  name : String
  ein : Gabbro.Body.State
  aus : Gabbro.Body.State × Option Gabbro.Body.Value

/-- `ρB` answers every call of the table with the table's answer. -/
def Treu (A : List Eintrag) (ρB : Gabbro.Body.Env) : Prop := ∀ e ∈ A, ρB e.name e.ein = e.aus

/-- An entry keeps the callee's contract and its frame at the entry state. -/
def EintragGut (u : UProg) (e : Eintrag) : Prop :=
  ∀ gf, fnSuch u e.name = some gf →
    (preProp (wfU u) gf e.ein → (postU u (wfU u) gf e.ein e.aus.1 e.aus.2).getD False) ∧
    (∀ p, p.carrier ∉ gf.schreibt → e.aus.1.world p = e.ein.world p)

/-- The ghost carrier of a callee: its first written carrier. -/
def geistVon (u : UProg) (n : String) : Option String := (fnSuch u n).bind (fun gf => gf.schreibt.head?)

/-- Every entry is a writer's, at an entry state whose ghost is at least the one of `W`. -/
def Oben (u : UProg) (A : List Eintrag) (W : Gabbro.Body.World) : Prop :=
  ∀ e ∈ A, ∃ w, geistVon u e.name = some w ∧ gz w W ≤ gz w e.ein.world

/-- No two entries share a key. -/
def Schluessel (A : List Eintrag) : Prop :=
  A.Pairwise (fun a b => ¬ (a.name = b.name ∧ a.ein = b.ein))

/-- Every declared frame, at the name a call resolves (`fnSuch`, the first function of the name). -/
def RahmenAlle (u : UProg) (ρB : Gabbro.Body.Env) : Prop :=
  ∀ n gf, fnSuch u n = some gf → Gabbro.Body.Frame ρB n gf.schreibt

/-- The per-unit conditions the bridge rests on (each decided per unit, `stimmigB`). -/
structure Stimmig (u : UProg) : Prop where
  tab : TabEindeutig u
  art : ∀ c : Fin u.fns.length, ArtStimmt (fnAt u c)
  namen : ∀ c : Fin u.fns.length, NamenEindeutig (fnAt u c)
  frei : ∀ c : Fin u.fns.length, NamenFrei (fnAt u c)
  olds : ∀ c : Fin u.fns.length, OldsKurz u (fnAt u c)
  post : ∀ c : Fin u.fns.length, PostDef u (fnAt u c)
  schreibt : ∀ c : Fin u.fns.length, ∀ w ∈ (fnAt u c).schreibt, ∃ t, (tabAt u t).name = w

/-! ## 3. The entry of one call -/

theorem reqAmEintritt_wahr {P : Programm (declOf u)} (G : Gesenkt u P) (f : Fin u.fns.length)
    (σ : World (declOf u)) (ρ : Env (declOf u) ((declOf u).params f)) : ReqAmEintritt P f σ ρ := by
  unfold ReqAmEintritt; rw [G.req f]; rfl

/-- The answer a writer's call point enters into the table: the G answer's world written over
    the entry world, the ghost of `w` bumped, and the G answer. -/
def antwort (w : String) (σ' : World (declOf u)) (t : Gabbro.Body.State) (r : Option Gabbro.Body.Value) :
    Gabbro.Body.State × Option Gabbro.Body.Value :=
  (⟨bump w (enc u σ' t.world), t.local'⟩, r)

/-- **The entry of a writer's call keeps the callee's contract and frame**: the promise by the
    handler's contract respect (`post_iff`), the frame by the handler's frame respect. -/
theorem eintrag_gut {P : Programm (declOf u)} (G : Gesenkt u P) (S : Stimmig u)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (hRR : RespektiertRahmen P R) (callee : Fin u.fns.length) (σr σ' : World (declOf u))
    (envA : Env (declOf u) ((declOf u).params callee)) (v : ErgVal (declOf u) ((declOf u).erg callee))
    (hR : R callee σr envA = .ok σ' v) (t : Gabbro.Body.State) (hWt : WRel u σr t.world)
    (hLt : LRel (fnAt u callee) 0 envA t.local') (w : String) (ws : List String)
    (hw : (fnAt u callee).schreibt = w :: ws) (n : String) (hn : fnSuch u n = some (fnAt u callee)) :
    EintragGut u ⟨n, t, antwort w σ' t (ergValOf ((declOf u).erg callee) v)⟩ := by
  intro gf hgf
  rw [hn] at hgf
  cases hgf
  constructor
  · intro _
    have hens := hRR.1 callee σr envA (reqAmEintritt_wahr G callee σr envA) σ' v hR
    exact (post_iff G callee (S.art callee) S.tab (S.frei callee) (S.olds callee) (S.post callee)
      σr σ' envA v t _ hWt hLt (wrel_bump w (wrel_enc u σ' t.world))).mpr hens
  · intro p hp
    have hgp : p ≠ geistOrt w := by
      intro e; subst e; apply hp; simp [geistOrt, Gabbro.Body.Place.carrier, hw]
    simp only [antwort, bump, Gabbro.Body.store, hgp, ↓reduceIte]
    cases p with
    | slot c k fld =>
      simp only [enc]
      cases hsw : slotWert u σ' c k fld with
      | none => rfl
      | some val =>
        simp only [Option.getD_some]
        unfold slotWert at hsw
        split at hsw
        · rename_i t' ht'
          split at hsw
          · rename_i fh' hf'
            cases hsw
            rw [wrel_lies_k u hWt c t' ht' fld fh' hf' k]
            congr 1
            have hfr := (hRR.2 callee σr envA σ' v hR).1.1 t'
            have hwf : (declOf u).schreibt callee t' = false := by
              show ((declOf u).signatur callee).schreibt t' = false
              rw [sigSchreibt_eq]
              unfold writesAt
              rw [show (tabAt u t').name = c from tabIdx_name _ _ _ ht']
              simp only [Gabbro.Body.Place.carrier] at hp
              simp only [List.any_eq_false, beq_iff_eq]
              intro x hx e
              subst e
              exact hp hx
            exact hfr hwf k fh'.idx
          · cases hsw
        · cases hsw
    | field c n => rfl
    | global n => rfl

/-! ## 4. The run -/

theorem oben_mono {A : List Eintrag} {W W' : Gabbro.Body.World}
    (h : ∀ w, gz w W ≤ gz w W') (hA : Oben u A W') : Oben u A W := by
  intro e he
  obtain ⟨w, hw, hle⟩ := hA e he
  exact ⟨w, hw, Int.le_trans (h w) hle⟩

/-- **The run of a lowered body.** From related states: the G run never blames a caller's
    `requires` (the handler never does, and there is no `requires`); and where it returns, there
    is an answer table -- every entry keeping its callee's contract and frame, keyed apart -- such
    that every Body environment that follows the table and respects the frames runs the Body
    body to a related state with the same answer. -/
theorem lauf {P : Programm (declOf u)} (G : Gesenkt u P) (S : Stimmig u) (c : Fin u.fns.length)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (hRR : RespektiertRahmen P R) (r : URet) (eB : List Gabbro.Body.Stmt)
    (hr : endBody u (fnAt u c) r = some eB) :
    ∀ (ss : List UStmt) (b0 : Endblock (declOf u) (verOf u c) false (ctxOf u c) (resOf u c))
      (bs : List Gabbro.Body.Stmt),
      lowBody u c ss r = .ok b0 → stmtsBody u (fnAt u c) ss = some bs →
      ∀ (σ : World (declOf u)) (ρ : Env (declOf u) (ctxOf u c)) (s : Gabbro.Body.State),
        WRel u σ s.world → LRel (fnAt u c) 0 ρ s.local' →
        (∀ e, execEnd O passes R b0 σ ρ = .logik e →
          ∃ (g : (declOf u).Fn) (σr : World (declOf u)) (envA : Env (declOf u) ((declOf u).params g)), R g σr envA = .logik e) ∧
        (∀ σ' v, execEnd O passes R b0 σ ρ = .zurueck σ' v →
          ∃ A : List Eintrag, (∀ e ∈ A, EintragGut u e) ∧ Oben u A s.world ∧ Schluessel A ∧
            ∀ ρB, Treu A ρB → RahmenAlle u ρB →
              ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB (bs ++ eB) s) = some s' ∧
                Gabbro.Body.finalValue (Gabbro.Body.exec ρB (bs ++ eB) s) =
                  ergValOf (verOf u c).erg v ∧
                WRel u σ' s'.world)
  | [], b0, bs, hlow, hbs, σ, ρ, s, hW, hL => by
      simp only [stmtsBody, Option.some.injEq] at hbs
      subst hbs
      simp only [lowBody] at hlow
      obtain ⟨σ', v, hex, hsl, hB⟩ := lowEnd_sim c hlow hr (S.art c) S.tab O passes R σ ρ s hW hL
      refine ⟨fun e h => (by rw [hex] at h; cases h), fun σ'' v' h => ?_⟩
      rw [hex] at h
      cases h
      refine ⟨[], by simp, by simp [Oben], List.Pairwise.nil, fun ρB _ _ =>
        ⟨s, (hB ρB).1, (hB ρB).2, wrel_slots u hsl hW⟩⟩
  | st :: ss, b0, bs, hlow, hbs, σ, ρ, s, hW, hL => by
      simp only [lowBody] at hlow
      split at hlow
      · cases hlow
      · rename_i gst hgst
        split at hlow
        · cases hlow
        · rename_i rest hrest
          cases hlow
          simp only [stmtsBody] at hbs
          split at hbs
          · rename_i x xs hx hxs
            simp only [Option.some.injEq] at hbs
            subst hbs
            have IH := lauf G S c O passes R hRR r eB hr ss rest xs hrest hxs
            -- a slot write: both sides take one step to related states
            have schreib : ∀ (σ₁ : World (declOf u)) (cn : String) (k : Int) (fld : String)
                (val : Gabbro.Body.Value), execStmt O passes R gst σ ρ = .ok σ₁ ρ →
                (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB x s =
                  .running ⟨Gabbro.Body.store s.world (.slot cn k fld) val, s.local'⟩) →
                WRel u σ₁ (Gabbro.Body.store s.world (.slot cn k fld) val) →
                ((∀ e, execEnd O passes R (Endblock.cons gst rest) σ ρ = .logik e →
                  ∃ (g : (declOf u).Fn) (σr : World (declOf u)) (envA : Env (declOf u) ((declOf u).params g)), R g σr envA = .logik e) ∧
                (∀ σ' v, execEnd O passes R (Endblock.cons gst rest) σ ρ = .zurueck σ' v →
                  ∃ A : List Eintrag, (∀ e ∈ A, EintragGut u e) ∧ Oben u A s.world ∧ Schluessel A ∧
                    ∀ ρB, Treu A ρB → RahmenAlle u ρB →
                      ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB (x :: xs ++ eB) s) = some s' ∧
                        Gabbro.Body.finalValue (Gabbro.Body.exec ρB (x :: xs ++ eB) s) =
                          ergValOf (verOf u c).erg v ∧
                        WRel u σ' s'.world)) := by
              intro σ₁ cn k fld val hex hstep hW₁
              have ih := IH σ₁ ρ ⟨Gabbro.Body.store s.world (.slot cn k fld) val, s.local'⟩ hW₁ hL
              have hrun : execEnd O passes R (Endblock.cons gst rest) σ ρ =
                  execEnd O passes R rest σ₁ ρ := by
                simp only [execEnd, hex]
              rw [hrun]
              refine ⟨ih.1, fun σ' v h => ?_⟩
              obtain ⟨A, hg, ho, hk, hb⟩ := ih.2 σ' v h
              refine ⟨A, hg, oben_mono (fun w => by rw [gz_store_slot]; exact Int.le_refl _) ho, hk,
                fun ρB hT hF => ?_⟩
              obtain ⟨s', h1, h2, h3⟩ := hb ρB hT hF
              refine ⟨s', ?_, ?_, h3⟩
              · simp only [List.cons_append, Gabbro.Body.exec, hstep ρB]; exact h1
              · simp only [List.cons_append, Gabbro.Body.exec, hstep ρB]; exact h2
            cases st with
            | assign b fname ix val =>
              obtain ⟨σ₁, cn, k, fld, v', hex, hstep, hW₁, _⟩ :=
                lowAssignDurch_sim c hgst hx (S.art c) S.tab O passes R σ ρ s hW hL
              exact schreib σ₁ cn k fld v' hex hstep hW₁
            | assignTab b fname ix val =>
              obtain ⟨σ₁, cn, k, fld, v', hex, hstep, hW₁, _⟩ :=
                lowAssignTab_sim c hgst hx (S.art c) S.tab O passes R σ ρ s hW hL
              exact schreib σ₁ cn k fld v' hex hstep hW₁
            | call cname args =>
              obtain ⟨callee, σr, envA, hname, hfs, hsl, hstep, hLt, _, hcases, _⟩ :=
                lowCall_sim c hgst hx (S.art c) S.tab S.namen O passes R σ ρ s hW hL
              have hWr : WRel u σr s.world := wrel_slots u hsl hW
              rcases hcases with ⟨σ', v, hR, hex⟩ | ⟨e, hR, hex⟩ | ⟨e, hR, hex⟩
              · have hrun : execEnd O passes R (Endblock.cons gst rest) σ ρ =
                    execEnd O passes R rest σ' ρ := by
                  simp only [execEnd, hex]
                rw [hrun]
                have hfr := (hRR.2 callee σr envA σ' v hR).1.1
                cases hwc : (fnAt u callee).schreibt with
                | nil =>
                  -- a callee that writes nothing: the world stays
                  have hsl' : σ'.slots = σ.slots := by
                    funext t' k' f'
                    rw [← hsl]
                    apply hfr
                    show ((declOf u).signatur callee).schreibt t' = false
                    refine (sigSchreibt_eq u callee t').trans ?_
                    unfold writesAt
                    rw [hwc]; rfl
                  have ih := IH σ' ρ s (wrel_slots u hsl' hW) hL
                  refine ⟨ih.1, fun σ'' v' h => ?_⟩
                  obtain ⟨A, hg, ho, hk, hb⟩ := ih.2 σ'' v' h
                  refine ⟨A, hg, ho, hk, fun ρB hT hF => ?_⟩
                  have hstay : ∀ t, (ρB cname t).1.world = t.world := by
                    intro t
                    funext p
                    exact hF cname _ hfs t p (by rw [hwc]; simp)
                  have hs : Gabbro.Body.step ρB x s = .running s := by
                    rw [hstep ρB, hstay]
                  obtain ⟨s', h1, h2, h3⟩ := hb ρB hT hF
                  refine ⟨s', ?_, ?_, h3⟩
                  · simp only [List.cons_append, Gabbro.Body.exec, hs]; exact h1
                  · simp only [List.cons_append, Gabbro.Body.exec, hs]; exact h2
                | cons w ws =>
                  -- a writer: one entry, its ghost bumped
                  let t : Gabbro.Body.State := ⟨s.world, Gabbro.Body.bindAll
                    ((fnAt u callee).params.map (·.1)) (envVals envA) (fun _ => .absent)⟩
                  let e0 : Eintrag := ⟨cname, t, antwort w σ' t (ergValOf ((declOf u).erg callee) v)⟩
                  let s₁ : Gabbro.Body.State := ⟨bump w (enc u σ' s.world), s.local'⟩
                  have hW₁ : WRel u σ' s₁.world := wrel_bump w (wrel_enc u σ' s.world)
                  have ih := IH σ' ρ s₁ hW₁ hL
                  refine ⟨ih.1, fun σ'' v' h => ?_⟩
                  obtain ⟨A, hg, ho, hk, hb⟩ := ih.2 σ'' v' h
                  have hgeist : geistVon u cname = some w := by
                    simp [geistVon, hfs, hwc]
                  have hgz : ∀ w', gz w' s.world ≤ gz w' s₁.world := fun w' => by
                    have := gz_bump_le w w' (enc u σ' s.world)
                    rw [gz_enc] at this
                    exact this
                  refine ⟨e0 :: A, ?_, ?_, ?_, fun ρB hT hF => ?_⟩
                  · intro e he
                    rcases List.mem_cons.mp he with rfl | he
                    · exact eintrag_gut G S R hRR callee σr σ' envA v hR t hWr hLt w ws hwc cname hfs
                    · exact hg e he
                  · intro e he
                    rcases List.mem_cons.mp he with rfl | he
                    · exact ⟨w, hgeist, Int.le_refl _⟩
                    · exact oben_mono hgz ho e he
                  · refine List.Pairwise.cons (fun e he hkey => ?_) hk
                    obtain ⟨w', hw', hle⟩ := ho e he
                    rw [← hkey.1, hgeist] at hw'
                    cases hw'
                    have : gz w s₁.world = gz w s.world + 1 := by
                      show gz w (bump w (enc u σ' s.world)) = _
                      rw [gz_bump_self, gz_enc]
                    rw [this, ← hkey.2] at hle
                    exact absurd hle (by show ¬ (gz w s.world + 1 ≤ gz w s.world); omega)
                  · have he0 : ρB cname t = e0.aus := hT e0 (List.mem_cons_self ..)
                    have hs : Gabbro.Body.step ρB x s = .running s₁ := by
                      rw [hstep ρB, he0]; rfl
                    obtain ⟨s', h1, h2, h3⟩ := hb ρB (fun e he => hT e (List.mem_cons_of_mem _ he)) hF
                    refine ⟨s', ?_, ?_, h3⟩
                    · simp only [List.cons_append, Gabbro.Body.exec, hs]; exact h1
                    · simp only [List.cons_append, Gabbro.Body.exec, hs]; exact h2
              · have hrun : execEnd O passes R (Endblock.cons gst rest) σ ρ = .logik e := by
                  simp only [execEnd, hex]
                rw [hrun]
                exact ⟨fun e' h => ⟨callee, σr, envA, by cases h; exact hR⟩,
                  fun σ' v h => by cases h⟩
              · have hrun : execEnd O passes R (Endblock.cons gst rest) σ ρ = .hardware e := by
                  simp only [execEnd, hex]
                rw [hrun]
                exact ⟨fun e' h => (by cases h), fun σ' v h => (by cases h)⟩
          · cases hbs

end Gabbro.Bruecke
