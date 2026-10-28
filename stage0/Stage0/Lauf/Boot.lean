/-
  File:      stage0/Stage0/Lauf/Boot.lean
  Subject:   Stage 0 on the thread machine: the pipeline and the checker as in `Laufzeit.lean`, then the start machine
             `RufStartG` with `main` on thread 0 and the program's roots on threads 1, 2, .., run by the fast machine
             (`Schnell/`). `boot_ist_lauf`: every output is read from a machine REACHABLE from the start machine by
             steps of `RufSchrittG`, in which thread 0 has ended.
-/
import Stage0.Laufzeit
import Stage0.Schnell.Lauf
import Stage0.Tor.Worte
import Stage0.Lauf.Memo

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Grammatik.GabbroV
  Gabbro.Grammatik.Parser.Cover.Differenz

/-- The oracle of an empty log is the machine that is never asked. -/
theorem orakelZ_leer {D : Deklaration} (kf : (a : D.Ax) → Env D (D.aparams a) → List Int) (c : Nat) :
    orakelZ kf c [] = orakelLeer D := rfl

/-- A thread's start: its root and its arguments. -/
abbrev Anfang (u : UProg) := Σ f : (declOf u).Fn, Env (declOf u) ((declOf u).params f)

/-- The start of one root: its parameters are table pointers or none. -/
def anfangVon (u : UProg) (f : Fin u.fns.length) : Except String (Anfang u) :=
  match zeigerArgs ((declOf u).params f) with
  | some ρ => .ok ⟨f, ρ⟩
  | none => .error ("the root " ++ (u.fns[f.val]?.map (·.name)).getD "" ++ " takes a parameter that is not a table pointer")

/-- **The threads of a run**: `main` on thread 0; on threads 1, 2, .. the declared roots (`entry` dispatch roots,
    `concurrent` members) and the roots of `start { .. }`, each once. -/
def anfaengeVon (u : UProg) (o : Orte u) : Except String (Anfang u × List (Anfang u)) := do
  let m ← anfangVon u o.main
  let rs ← (uOhneDoppelte (u.roots ++ u.gestartet)).mapM (fnIdx u.fns)
  let rs ← (rs.filter (· != o.main)).mapM (anfangVon u)
  pure (m, rs)

/-- The start machine: thread `t` runs the `t`-th start, every thread behind the last one `main` (it never steps). -/
def startG {u : UProg} (P : Programm (declOf u)) (σ : World (declOf u)) (m : Anfang u) (rs : List (Anfang u)) :
    RufMaschineG (declOf u) :=
  RufStartG P σ.speicher (fun t => (m :: rs).getD t m)

theorem startG_ruhe {u : UProg} (P : Programm (declOf u)) (σ : World (declOf u)) (m : Anfang u)
    (rs : List (Anfang u)) (hl : (offen (startSpur (D := declOf u) m.1)).isEmpty = true) :
    ∀ g, rs.length + 1 ≤ g → offen ((startG P σ m rs).faeden g).spur = [] := by
  intro g hg
  have hd : (m :: rs).getD g m = m := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp only [List.length_cons]; omega)]
    rfl
  simp only [startG, RufStartG, hd]
  simpa using hl

/-- The output depends on the memory only. -/
theorem ausgabe_welt {u : UProg} (o : Orte u) (S : Speicher (declOf u)) (s s' : List (Ereignis (declOf u))) :
    ausgabe u o (S.welt s) = ausgabe u o (S.welt s') := rfl

/-- The numbers of the tables, fields and statics of a unit: their positions. -/
def kodVon (u : UProg) : Kodierung (declOf u) where
  tn := fun t => (t : Fin u.tabs.length).val
  tn_inj := fun _ _ h => Fin.ext h
  fn := fun _ f => (f : Fin _).val
  fn_inj := fun _ _ _ h => Fin.ext h
  gn := fun g => (g : Fin u.globs.length).val
  gn_inj := fun _ _ h => Fin.ext h
  felder := (List.finRange u.tabs.length).flatMap fun t =>
    (List.finRange (fieldCount u t)).map fun f => (⟨t, f⟩ : Σ t : (declOf u).Tab, (declOf u).Feld t)
  globs := List.finRange u.globs.length

/-- The array memory of the start: the declared initial memory prepared, then the writes of the start in place. -/
def startAWelt (u : UProg) (h : sp0OkB u = true) (w : List (Schreib (declOf u))) : AWelt (declOf u) :=
  (AWelt.von (kodVon u) (sp0Of u h)).schreibe (kodVon u) w

theorem startAWelt_sicht (u : UProg) (h : sp0OkB u = true) (w : List (Schreib (declOf u))) :
    (startAWelt u h w).sicht (kodVon u) = ((schreibAuf w (sp0Of u h)).welt []).speicher := by
  rw [startAWelt, sicht_schreibe, sicht_von]
  rfl

/-- **Run the threads on the fast machine** and read the output of the world thread 0 ended in. -/
def lauf (u : UProg) (P : Programm (declOf u)) (o : Orte u) (B : Budget) (σ : World (declOf u)) (m : Anfang u)
    (rs : List (Anfang u)) (A : AWelt (declOf u)) (hA : A.sicht (kodVon u) = σ.speicher) :
    Except String (List UInt8) :=
  if hl : (offen (startSpur (D := declOf u) m.1)).isEmpty = true then
    let P' := memoP u P
    let s0 := SStand.start P' (kfVon u) [] B.passes σ (startG P σ m rs) (kodVon u) (rs.length + 1) A hA
    let (s, _) := s0.laufe (startG_ruhe P σ m rs hl) B.schritte (alleN (rs.length + 1)) []
    let F := s.s.F σ (startG P σ m rs)
    if fertig F 0 then ausgabe u o (F.weltVon 0) else .error "main did not end within the step budget"
  else .error "main holds locks by signature"

/-- **STAGE 0 on the thread machine**: check, then run a program of the subset on its input bytes. -/
def boot (B : Budget) (src : String) (ein : List UInt8) : Except String (List UInt8) :=
  match lex src with
  | .error _ => .error "lex"
  | .ok toks =>
    match parseTopTief toks with
    | .error e => .error e
    | .ok items =>
      match elabU (pre108 items) with
      | .error e => .error e
      | .ok u =>
        match akzeptiertU u with
        | .error e => .error e
        | .ok false => .error "refused by the checker (AkzeptiertX)"
        | .ok true =>
          if imKernB u = false then .error "outside the stage-0 subset" else
          match orteVon u with
          | .error e => .error e
          | .ok o =>
            if h : sp0OkB u = true then
              match lowerAllg u with
              | .error e => .error e
              | .ok (P, _) =>
                match startSchreib u o ein, anfaengeVon u o with
                | .error e, _ | _, .error e => .error e
                | .ok w, .ok (m, rs) =>
                  lauf u P o B ((schreibAuf w (sp0Of u h)).welt []) m rs (startAWelt u h w) (startAWelt_sicht u h w)
            else .error "no declared initial memory (sp0)"

/-- **The run is the thread machine**: every output of `lauf` is read from a machine that `RufSchrittG` reaches from
    the start machine, in which thread 0 has ended. -/
theorem lauf_ist_lauf {u : UProg} {P : Programm (declOf u)} {o : Orte u} {B : Budget} {σ : World (declOf u)}
    {m : Anfang u} {rs : List (Anfang u)} {A : AWelt (declOf u)} {hA : A.sicht (kodVon u) = σ.speicher}
    {aus : List UInt8} (h : lauf u P o B σ m rs A hA = .ok aus) :
    ∃ M : RufMaschineG (declOf u),
      RufErreichbarG P (orakelLeer (declOf u)) B.passes (startG P σ m rs) M ∧ fertig M 0 = true ∧
        ausgabe u o (M.weltVon 0) = .ok aus := by
  unfold lauf at h
  split at h
  · simp only at h
    split at h
    · rename_i hf
      obtain ⟨M, hr, hF⟩ := SStand.steht (P := memoP u P) (SStand.laufe _ B.schritte _ _ [] |>.1)
      rw [orakelZ_leer, memoP_eq] at hr
      refine ⟨M, hr, ?_, ?_⟩
      · rw [hF, fertig_normal] at hf
        exact hf
      · rw [hF] at h
        rw [← h]
        exact ausgabe_welt o _ _ _
    · cases h
  · cases h

/-- **Stage 0 on the thread machine**: every output is read from a reachable machine of the program the Lean pipeline
    built from the source, from the declared initial memory with the input, after the checker accepted. -/
theorem boot_ist_lauf {B : Budget} {src : String} {ein aus : List UInt8} (h : boot B src ein = .ok aus) :
    ∃ (u : UProg) (P : Programm (declOf u)) (fs : List (declOf u).Fn) (o : Orte u) (hs : sp0OkB u = true)
      (σ : World (declOf u)) (m : Anfang u) (rs : List (Anfang u)) (M : RufMaschineG (declOf u)),
      uebersetzeAllg src = .ok ⟨u, P, fs⟩ ∧ akzeptiertU u = .ok true ∧ imKernB u = true ∧
      startWelt u o hs ein = .ok σ ∧ anfaengeVon u o = .ok (m, rs) ∧
      RufErreichbarG P (orakelLeer (declOf u)) B.passes (startG P σ m rs) M ∧ fertig M 0 = true ∧
      ausgabe u o (M.weltVon 0) = .ok aus := by
  unfold boot at h
  split at h
  · cases h
  rename_i toks hl
  split at h
  · cases h
  rename_i items hp
  split at h
  · cases h
  rename_i u he
  split at h
  · cases h
  · cases h
  rename_i ha
  split at h
  · cases h
  rename_i hk
  split at h
  · cases h
  rename_i o _
  split at h
  · rename_i hs
    split at h
    · cases h
    rename_i P fs hw
    split at h
    · cases h
    · cases h
    rename_i w m rs hσ hmr
    obtain ⟨M, hM, hf, ho⟩ := lauf_ist_lauf h
    refine ⟨u, P, fs, o, hs, _, m, rs, M, ?_, ha, Bool.not_eq_false _ ▸ hk, by rw [startWelt, hσ]; rfl, hmr, hM, hf, ho⟩
    unfold uebersetzeAllg
    rw [hl]
    dsimp only
    rw [hp]
    dsimp only
    rw [he]
    dsimp only
    rw [hw]
  · cases h

end Gabbro.Stage0
