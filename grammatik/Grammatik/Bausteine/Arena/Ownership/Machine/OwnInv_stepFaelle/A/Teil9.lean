module

public import Grammatik.Bausteine.Arena.Ownership.Machine.Stack.Return
public import Grammatik.Bausteine.Arena.Ownership.Machine.OwnInv_stepFaelle.A.Teil8

@[expose] public section

namespace Gabbro.Grammatik.ArenaOwnership.Machine
open Source Body

/-! ## Consuming traversal: refused syntax, vacuous preservation.

  The ownership checker refuses `Stmt.consumeTraverse` (`Checker`: `none`),
  so no ownership judgment (`OS`) covers it. A machine step on it therefore
  starts from a head whose `OR`/`OX` content is uninhabited: `dannVerbrauch`
  inverts through `OR.stmt` to the missing `OS` case; `verbrauchWeiter`,
  `verbrauchLeer` and `verbrauchFort` invert their residue (`OR` has no
  `verbrauch` case) at once; `dannLeaveVerbrauch` and `dannNextVerbrauch`
  invert the continuation (`OR`/`OX` have no `verbrauchRest` case). -/

section Kein
variable {D : Deklaration} {A : FreiForm D} {I : Interfaces A} {V : Vertrag D} {out : Flow.Output A V.erg}

/-- A consuming residue (the loop or its continuation marker). -/
def restVerbrauchend {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : GRest D V l Γ Λ → Bool
  | .verbrauch .. => true
  | .verbrauchRest .. => true
  | _ => false

/-- A consuming traversal statement. -/
def stmtVerbrauchend {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Bool
  | .consumeTraverse .. => true
  | _ => false

theorem or_kein_verbrauch {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {k c : Context} {r : GRest D V l Γ Λ}
    (h : OR A I out k c r) : restVerbrauchend r = false := by
  cases h <;> rfl

theorem ox_kein_verbrauch {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {k : Context} {r : GRest D V l Γ Λ}
    (h : OX A I out k r) : restVerbrauchend r = false := by
  cases h <;> rfl

theorem os_kein_verbrauch {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {k c c2 : Context}
    {st : Stmt D V l Γ Λ Λ'} (h : OS A I out k c st c2) : stmtVerbrauchend st = false := by
  cases h <;> rfl

theorem cont_kein_verbrauch {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {k c : Context} {r : GRest D V l Γ Λ}
    (h : Cont A I out k c r) : restVerbrauchend r = false := by
  rcases h with h | ⟨_, h⟩
  · exact or_kein_verbrauch h
  · exact ox_kein_verbrauch h

end Kein

set_option maxHeartbeats 4000000 in
theorem ownInv_step_dannVerbrauch {D : Deklaration} {P : Programm D}
  {A : FreiForm D} {I : Interfaces A} {O : Orakel D} {passes : Nat}
  {M : RufMaschineG D} {u : Faden} (s : State)
  (hH :
    Head A I { thread := u, activation := (M.faeden u).stapel.length : Frame } s (M.weltVon u) (M.faeden u).kopf.f
      (M.faeden u).kopf.rest)
  (l : Bool) (Γ : Ctx) (Λ Λ'' : List (Res D)) (t : D.Tab)
  (member : Expr D (.index (D.count t) :: Γ) Λ Ty.bool)
  (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ Ty.bool)
  (inv : Expr D Γ Λ Ty.bool) (bound : Int)
  (mass : Expr D Γ Λ (.int 0 bound))
  (body : Block D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ Λ)
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l Γ Λ Λ'') (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ'')
  (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.consumeTraverse t member edge inv bound mass body) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)) :
  OwnInv A I
    { speicher := M.speicher,
      faeden :=
        rufUpdateG M.faeden u
          { stapel := (M.faeden u).stapel,
            kopf :=
              { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                rest :=
                  (⟨l,
                      (⟨Γ,
                          (⟨Λ, (ρ, GRest.verbrauch t member edge inv bound mass body
                            ((D.count t).toNat + bound.toNat + 1) (GRest.dann rest k))⟩ :
                            (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                        (Γ : Ctx) ×
                          (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                    (l : Bool) ×
                      (Γ : Ctx) ×
                        (Λ : List (Res D)) ×
                          Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                RufRahmenG D },
            spur := (M.faeden u).spur, log := (M.faeden u).log : RufFadenG D },
      lauf := M.lauf, start := M.start : RufMaschineG D } := by
  rw [hhead] at hH
  obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
  obtain ⟨c2, hs, hc⟩ := hr.stmt trivial
  simpa [stmtVerbrauchend] using os_kein_verbrauch hs

set_option maxHeartbeats 4000000 in
theorem ownInv_step_verbrauchWeiter {D : Deklaration} {P : Programm D}
  {A : FreiForm D} {I : Interfaces A} {O : Orakel D} {passes : Nat}
  {M : RufMaschineG D} {u : Faden} (s : State)
  (hH :
    Head A I { thread := u, activation := (M.faeden u).stapel.length : Frame } s (M.weltVon u) (M.faeden u).kopf.f
      (M.faeden u).kopf.rest)
  (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (t : D.Tab)
  (member : Expr D (.index (D.count t) :: Γ) Λ Ty.bool)
  (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ Ty.bool)
  (inv : Expr D Γ Λ Ty.bool) (bound : Int)
  (mass : Expr D Γ Λ (.int 0 bound))
  (body : Block D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ Λ)
  (rest : Nat) (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)
  (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.verbrauch t member edge inv bound mass body (rest + 1) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (v : Wert D (Ty.index (D.count t))) (m : Int) (σ₃ : World D) :
  OwnInv A I
    { speicher := M.speicher,
      faeden :=
        rufUpdateG M.faeden u
          { stapel := (M.faeden u).stapel,
            kopf :=
              { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                rest :=
                  (⟨true,
                      (⟨Ty.index (D.count t) :: Γ,
                          (⟨Λ, (Env.cons v ρ, GRest.dann body (GRest.verbrauchRest t member edge inv bound mass body
                            rest m k))⟩ :
                            (Λ : List (Res D)) ×
                              Env D (Ty.index (D.count t) :: Γ) ×
                                GRest D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ)⟩ :
                        (Γ : Ctx) ×
                          (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) true Γ Λ)⟩ :
                    (l : Bool) ×
                      (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                RufRahmenG D },
            spur := σ₃.spur, log := (M.faeden u).log : RufFadenG D },
      lauf := M.lauf, start := M.start : RufMaschineG D } := by
  rw [hhead] at hH
  obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
  simpa [restVerbrauchend] using or_kein_verbrauch hr

set_option maxHeartbeats 4000000 in
theorem ownInv_step_verbrauchLeer {D : Deklaration} {P : Programm D}
  {A : FreiForm D} {I : Interfaces A} {O : Orakel D} {passes : Nat}
  {M : RufMaschineG D} {u : Faden} (s : State)
  (hH :
    Head A I { thread := u, activation := (M.faeden u).stapel.length : Frame } s (M.weltVon u) (M.faeden u).kopf.f
      (M.faeden u).kopf.rest)
  (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (t : D.Tab)
  (member : Expr D (.index (D.count t) :: Γ) Λ Ty.bool)
  (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ Ty.bool)
  (inv : Expr D Γ Λ Ty.bool) (bound : Int)
  (mass : Expr D Γ Λ (.int 0 bound))
  (body : Block D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ Λ)
  (rest : Nat) (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)
  (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.verbrauch t member edge inv bound mass body (rest + 1) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₂ : World D) :
  OwnInv A I
    { speicher := M.speicher,
      faeden :=
        rufUpdateG M.faeden u
          { stapel := (M.faeden u).stapel,
            kopf :=
              { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                rest :=
                  (⟨l,
                      (⟨Γ,
                          (⟨Λ, (ρ, k)⟩ :
                            (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                        (Γ : Ctx) ×
                          (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                    (l : Bool) ×
                      (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                RufRahmenG D },
            spur := σ₂.spur, log := (M.faeden u).log : RufFadenG D },
      lauf := M.lauf, start := M.start : RufMaschineG D } := by
  rw [hhead] at hH
  obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
  simpa [restVerbrauchend] using or_kein_verbrauch hr

set_option maxHeartbeats 4000000 in
theorem ownInv_step_verbrauchFort {D : Deklaration} {P : Programm D}
  {A : FreiForm D} {I : Interfaces A} {O : Orakel D} {passes : Nat}
  {M : RufMaschineG D} {u : Faden} (s : State)
  (hH :
    Head A I { thread := u, activation := (M.faeden u).stapel.length : Frame } s (M.weltVon u) (M.faeden u).kopf.f
      (M.faeden u).kopf.rest)
  (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (t : D.Tab)
  (member : Expr D (.index (D.count t) :: Γ) Λ Ty.bool)
  (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ Ty.bool)
  (inv : Expr D Γ Λ Ty.bool) (bound : Int)
  (mass : Expr D Γ Λ (.int 0 bound))
  (body : Block D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ Λ)
  (rest : Nat) (vor : Int)
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)
  (i : Wert D (Ty.index (D.count t))) (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨true,
          (⟨Ty.index (D.count t) :: Γ,
              (⟨Λ, (Env.cons i ρ, GRest.verbrauchRest t member edge inv bound mass body rest vor k)⟩ :
                (Λ : List (Res D)) ×
                  Env D (Ty.index (D.count t) :: Γ) ×
                    GRest D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) true Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) :
  OwnInv A I
    { speicher := M.speicher,
      faeden :=
        rufUpdateG M.faeden u
          { stapel := (M.faeden u).stapel,
            kopf :=
              { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                rest :=
                  (⟨l,
                      (⟨Γ,
                          (⟨Λ, (ρ, GRest.verbrauch t member edge inv bound mass body rest k)⟩ :
                            (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                        (Γ : Ctx) ×
                          (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                    (l : Bool) ×
                      (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                RufRahmenG D },
            spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
      lauf := M.lauf, start := M.start : RufMaschineG D } := by
  rw [hhead] at hH
  obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
  simpa [restVerbrauchend] using or_kein_verbrauch hr

set_option maxHeartbeats 4000000 in
theorem ownInv_step_dannLeaveVerbrauch {D : Deklaration} {P : Programm D}
  {A : FreiForm D} {I : Interfaces A} {O : Orakel D} {passes : Nat}
  {M : RufMaschineG D} {u : Faden} (s : State)
  (hH :
    Head A I { thread := u, activation := (M.faeden u).stapel.length : Frame } s (M.weltVon u) (M.faeden u).kopf.f
      (M.faeden u).kopf.rest)
  (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (t : D.Tab)
  (member : Expr D (.index (D.count t) :: Γ) Λ Ty.bool)
  (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ Ty.bool)
  (inv : Expr D Γ Λ Ty.bool) (bound : Int)
  (mass : Expr D Γ Λ (.int 0 bound))
  (body : Block D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ Λ)
  (rest : Nat) (vor : Int)
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)
  {Λx : List (Res D)}
  (restb : Block D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λx Λ)
  (i : Wert D (Ty.index (D.count t))) (ρ : Env D Γ) (hleave : true = true)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨true,
          (⟨Ty.index (D.count t) :: Γ,
              (⟨Λx, (Env.cons i ρ, GRest.dann (Block.cons ((.leave hleave) : Stmt D (vertragVon D (M.faeden u).kopf.f)
                true (Ty.index (D.count t) :: Γ) Λx Λx) restb)
                (GRest.verbrauchRest t member edge inv bound mass body rest vor k))⟩ :
                (Λ : List (Res D)) ×
                  Env D (Ty.index (D.count t) :: Γ) ×
                    GRest D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) true Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) :
  OwnInv A I
    { speicher := M.speicher,
      faeden :=
        rufUpdateG M.faeden u
          { stapel := (M.faeden u).stapel,
            kopf :=
              { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                rest :=
                  (⟨l,
                      (⟨Γ,
                          (⟨Λ, (ρ, k)⟩ :
                            (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                        (Γ : Ctx) ×
                          (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                    (l : Bool) ×
                      (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                RufRahmenG D },
            spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
      lauf := M.lauf, start := M.start : RufMaschineG D } := by
  rw [hhead] at hH
  obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
  obtain ⟨_, _, hc⟩ := hr.dann_inv
  simpa [restVerbrauchend] using cont_kein_verbrauch hc

set_option maxHeartbeats 4000000 in
theorem ownInv_step_dannNextVerbrauch {D : Deklaration} {P : Programm D}
  {A : FreiForm D} {I : Interfaces A} {O : Orakel D} {passes : Nat}
  {M : RufMaschineG D} {u : Faden} (s : State)
  (hH :
    Head A I { thread := u, activation := (M.faeden u).stapel.length : Frame } s (M.weltVon u) (M.faeden u).kopf.f
      (M.faeden u).kopf.rest)
  (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (t : D.Tab)
  (member : Expr D (.index (D.count t) :: Γ) Λ Ty.bool)
  (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ Ty.bool)
  (inv : Expr D Γ Λ Ty.bool) (bound : Int)
  (mass : Expr D Γ Λ (.int 0 bound))
  (body : Block D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ Λ)
  (rest : Nat) (vor : Int)
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)
  {Λx : List (Res D)}
  (restb : Block D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λx Λ)
  (i : Wert D (Ty.index (D.count t))) (ρ : Env D Γ) (hnext : true = true)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨true,
          (⟨Ty.index (D.count t) :: Γ,
              (⟨Λx, (Env.cons i ρ, GRest.dann (Block.cons ((.next hnext) : Stmt D (vertragVon D (M.faeden u).kopf.f)
                true (Ty.index (D.count t) :: Γ) Λx Λx) restb)
                (GRest.verbrauchRest t member edge inv bound mass body rest vor k))⟩ :
                (Λ : List (Res D)) ×
                  Env D (Ty.index (D.count t) :: Γ) ×
                    GRest D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) true Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σm : World D) :
  OwnInv A I
    { speicher := M.speicher,
      faeden :=
        rufUpdateG M.faeden u
          { stapel := (M.faeden u).stapel,
            kopf :=
              { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                rest :=
                  (⟨l,
                      (⟨Γ,
                          (⟨Λ, (ρ, GRest.verbrauch t member edge inv bound mass body rest k)⟩ :
                            (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                        (Γ : Ctx) ×
                          (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                    (l : Bool) ×
                      (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                RufRahmenG D },
            spur := σm.spur, log := (M.faeden u).log : RufFadenG D },
      lauf := M.lauf, start := M.start : RufMaschineG D } := by
  rw [hhead] at hH
  obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
  obtain ⟨_, _, hc⟩ := hr.dann_inv
  simpa [restVerbrauchend] using cont_kein_verbrauch hc

end Gabbro.Grammatik.ArenaOwnership.Machine
