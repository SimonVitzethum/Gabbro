/-
  File:      stage0/Stage0/Lauf/Boot.lean
  Subject:   Stage 0 on the thread machine: the pipeline and the checker as in `Laufzeit.lean`, then the start machine
             `RufStartG` with `main` on thread 0, run by the driver. `boot_ist_lauf`: every output is read from a
             machine REACHABLE from the start machine by steps of `RufSchrittG`, in which thread 0 has ended.
-/
import Stage0.Laufzeit
import Stage0.Lauf.Treiber

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Grammatik.GabbroV
  Gabbro.Grammatik.Parser.Cover.Differenz

/-- The machine's answers for a unit of the subset keep the trace. -/
theorem orakelLeer_treu (D : Deklaration) : OrakelSpurTreu (orakelLeer D) := fun _ _ _ => rfl

/-- The start machine: `main` with its arguments on every thread; only thread 0 runs. -/
def startG {u : UProg} (P : Programm (declOf u)) (o : Orte u) (σ : World (declOf u))
    (ρ : Env (declOf u) ((declOf u).params o.main)) : RufMaschineG (declOf u) :=
  RufStartG P σ.speicher (fun _ => ⟨o.main, ρ⟩)

/-- **Run `main` on the thread machine** and read the output of the world thread 0 ended in. -/
def lauf (u : UProg) (P : Programm (declOf u)) (o : Orte u) (B : Budget) (σ : World (declOf u)) :
    Except String (List UInt8) :=
  match zeigerArgs ((declOf u).params o.main) with
  | none => .error "main takes a parameter that is not a table pointer"
  | some ρ =>
    if hl : (offen (startSpur (D := declOf u) (show (declOf u).Fn from o.main))).isEmpty = true then
      let M0 := startG P o σ ρ
      let s0 : Stand P (orakelLeer (declOf u)) B.passes M0 [0] :=
        Stand.start M0 [0] (fun g _ => by
          show offen (startSpur (D := declOf u) (show (declOf u).Fn from o.main)) = []
          simpa using hl)
      let (s, _) := s0.laufe (orakelLeer_treu _) B.schritte [⟨0, by simp⟩] []
      if fertig s.M 0 then ausgabe u o (s.M.weltVon 0) else .error "main did not end within the step budget"
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
                match startWelt u o h ein with
                | .error e => .error e
                | .ok σ => lauf u P o B σ
            else .error "no declared initial memory (sp0)"

/-- **The run is the thread machine**: every output of `lauf` is read from a machine that `RufSchrittG` reaches from
    the start machine, in which thread 0 has ended. -/
theorem lauf_ist_lauf {u : UProg} {P : Programm (declOf u)} {o : Orte u} {B : Budget} {σ : World (declOf u)}
    {aus : List UInt8} (h : lauf u P o B σ = .ok aus) :
    ∃ (ρ : Env (declOf u) ((declOf u).params o.main)) (M : RufMaschineG (declOf u)),
      RufErreichbarG P (orakelLeer (declOf u)) B.passes (startG P o σ ρ) M ∧ fertig M 0 = true ∧
        ausgabe u o (M.weltVon 0) = .ok aus := by
  unfold lauf at h
  split at h
  · cases h
  rename_i ρ _
  split at h
  · rename_i hl
    simp only at h
    split at h
    · rename_i hf
      exact ⟨ρ, _, Stand.erreicht _, hf, h⟩
    · cases h
  · cases h

/-- **Stage 0 on the thread machine**: every output is read from a reachable machine of the program the Lean pipeline
    built from the source, from the declared initial memory with the input, after the checker accepted. -/
theorem boot_ist_lauf {B : Budget} {src : String} {ein aus : List UInt8} (h : boot B src ein = .ok aus) :
    ∃ (u : UProg) (P : Programm (declOf u)) (fs : List (declOf u).Fn) (o : Orte u) (hs : sp0OkB u = true)
      (σ : World (declOf u)) (ρ : Env (declOf u) ((declOf u).params o.main)) (M : RufMaschineG (declOf u)),
      uebersetzeAllg src = .ok ⟨u, P, fs⟩ ∧ akzeptiertU u = .ok true ∧ imKernB u = true ∧
      startWelt u o hs ein = .ok σ ∧
      RufErreichbarG P (orakelLeer (declOf u)) B.passes (startG P o σ ρ) M ∧ fertig M 0 = true ∧
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
    rename_i σ hσ
    obtain ⟨ρ, M, hM, hf, ho⟩ := lauf_ist_lauf h
    refine ⟨u, P, fs, o, hs, σ, ρ, M, ?_, ha, Bool.not_eq_false _ ▸ hk, hσ, hM, hf, ho⟩
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
