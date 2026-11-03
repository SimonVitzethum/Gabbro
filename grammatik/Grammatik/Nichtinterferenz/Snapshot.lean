module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- A canonical, unobserved world. The argument only proves inhabitation;
    proof irrelevance makes the result independent of every memory value. -/
noncomputable def World.ohneSnapshot (σ : World D) : World D :=
  Classical.choice (show Nonempty (World D) from ⟨σ⟩)

theorem World.ohneSnapshot_gleich (σ τ : World D) : σ.ohneSnapshot = τ.ohneSnapshot := rfl

/-- Erase only saved proof snapshots. Answers, pending releases and live
    syntax remain observable, as do the thread's actual trace and memory. -/
noncomputable def GRest.kern {V : Vertrag D} :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → GRest D V l Γ Λ
  | _, _, _, .ende e => .ende e
  | _, _, _, .dann b k => .dann b k.kern
  | _, _, _, .schrumpf k => .schrumpf k.kern
  | _, _, _, .frei L k => .frei L k.kern
  | _, _, _, .trav t inv body ks k => .trav t inv body ks k.kern
  | _, _, _, .travRest t inv body ks k => .travRest t inv body ks k.kern
  | _, _, _, .wieder n bis body ueber k => .wieder n bis body ueber k.kern
  | _, _, _, .wiederRest n bis body ueber k => .wiederRest n bis body ueber k.kern
  | _, _, _, .ewig a n inv body k => .ewig a n inv body k.kern
  | _, _, _, .ewigRest a n inv body k => .ewigRest a n inv body k.kern
  | _, _, _, .wartet rest k => .wartet rest k.kern
  | _, _, _, .wartetSonst n err rest k => .wartetSonst n err rest k.kern
  | _, _, _, .abbruch k => .abbruch k.kern
  | _, _, _, .leer => .leer
  | _, _, _, .rueckBereit scopes k => .rueckBereit scopes k.kern
  | _, _, _, .verbrauch t member edge inv bound mass body n k =>
      .verbrauch t member edge inv bound mass body n k.kern
  | _, _, _, .verbrauchRest t member edge inv bound mass body n vor k =>
      .verbrauchRest t member edge inv bound mass body n vor k.kern
  | _, _, _, .zurueckgekehrt a => .zurueckgekehrt ⟨a.1, a.2.ohneSnapshot⟩
  | _, _, _, .aufraeumen a remaining => .aufraeumen ⟨a.1, a.2.ohneSnapshot⟩ remaining

/-- Projection preserves the source-return selector; only the continuation's
    saved proof worlds are erased. -/
theorem GRest.kern_scopedWert {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {r : GRest D V l Γ Λ} {e : ErgExpr D Γ Λ V.erg} {R : RueckRessourcen D V Λ}
    (h : r.scopedWert = some (e, R)) : r.kern.scopedWert = some (e, R) := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedWert_faelle h <;> subst r <;> rfl

theorem GRest.kern_scopedGrund {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {r : GRest D V l Γ Λ} {grund : Fin V.gruende} {R : RueckRessourcen D V Λ}
    (h : r.scopedGrund = some (grund, R)) : r.kern.scopedGrund = some (grund, R) := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedGrund_faelle h <;> subst r <;> rfl

/-- The projection is stable under repeated observation. -/
theorem GRest.kern_kern {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r : GRest D V l Γ Λ) : r.kern.kern = r.kern := by
  induction r <;> simp_all only [GRest.kern] <;> rfl

end Gabbro.Grammatik
