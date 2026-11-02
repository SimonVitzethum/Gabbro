module

public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem
public import Grammatik.Bausteine.Arena.ArenaStaticReset
public import Grammatik.Kern.Syntax.Typen.Transport

@[expose] public section



namespace Gabbro.Grammatik

/-! ## 1. Types, signatures, the declaration -/

/-- Types of `D.mitRuhe`: function-pointer numbers shift by one. -/
@[reducible] def tyR : Ty → Ty := Ty.mapNumbers (fun n => n + 1) id
