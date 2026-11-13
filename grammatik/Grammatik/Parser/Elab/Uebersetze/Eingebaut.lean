module

public import Grammatik.Kern.Syntax.Profil.Speicher
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil3

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

/-- C13: the builtin of a binary operator spelling (`+%`, `-%`, `*%`, `<<%`, `+|`). -/
def uBinEin : String → Option UBi
  | "+%" => some .addW
  | "-%" => some .subW
  | "*%" => some .mulW
  | "<<%" => some .shlW
  | "+|" => some .addS
  | _ => none

/-- C13: the one-operand bit intrinsic of a call name. -/
def uBitEin : String → Option UBi
  | "clz" => some .clz
  | "ctz" => some .ctz
  | "log2_floor" => some .log2Floor
  | "popcount" => some .popcount
  | "bswap" => some .bswap
  | _ => none

/-- C13: the two-operand bit intrinsic of a call name. -/
def uRotEin : String → Option UBi
  | "rotl" => some .rotl
  | "rotr" => some .rotr
  | _ => none

/-- C13: the declared storage width of the field `f` of a table, where it is a bare unsigned word. -/
def uFeldBreite (tb : UTab) (f : String) : Option Nat :=
  (tb.breiten.find? (fun p => strEq p.1 f)).map (·.2)

/-- Resolve nominal projection bases without inferring storage from an integer interval. -/
def uStorageValueType (ctx : UCtx) : SExpr → Option Ty
  | .variable name =>
    match uParamNr ctx name with
    | .ok position => ctx.types[position]?
    | .error _ => (ctx.globs.find? (fun global => strEq global.name name)).map (fun global => global.ty.toTy)
  | .call name _ => (ctx.records.find? (fun schema => strEq schema.name name)).map (·.ty)
  | .field base field => do
    let ty ← uStorageValueType ctx base
    let schema ← ctx.records.find? (fun schema => decide (schema.ty = ty))
    (schema.fields.find? (fun entry => strEq entry.1 field)).map (·.2)
  | .index base _ =>
    match uStorageValueType ctx base with
    | some (.arr element _) => some element
    | _ => none
  | _ => none

/-- The selected record declaration supplies its field width, including through nested products. -/
def uRecordBreite (ctx : UCtx) (base : SExpr) (field : String) : Option Nat := do
  let ty ← uStorageValueType ctx base
  let schema ← ctx.records.find? (fun schema => decide (schema.ty = ty))
  (schema.breiten.find? (fun entry => strEq entry.1 field)).map (·.2)

/-- C13: the declared STORAGE width in bits of an operand, where the declaration names it:
    * a parameter or a `let` local at a bare unsigned word (`UCtx.bits`);
    * a static of a bare unsigned word (`UGlob.breite`);
    * a field of a table or arena read through a pointer parameter or by the table's name (`UTab.breiten`);
    * a conversion `T(e)` where `T` is a builtin word or an alias of one (`uSpeicherBreite`: the width of the
      declaration, never the width the range of `T` fits);
    * a wrapping builtin of such operands.
    Every other operand has no width here, and the builtin over it is refused: the width is never read off the
    interval the checker computed. -/
def uBreite (ctx : UCtx) : SExpr → Option Nat
  | .variable p =>
    match uParamNr ctx p with
    | .ok j =>
      match ctx.bits[j]? with
      | some w => if 0 < w then some w else none
      | none => none
    | .error _ =>
      match ctx.globs.find? (fun g => strEq g.name p) with
      | some g => if 0 < g.breite then some g.breite else none
      | none => none
  | .field (.index (.field (.variable b) s) _) f =>
    if !strEq s "slots" then none
    else
      match uParamNr ctx b with
      | .ok j =>
        match uArtBei ctx.kinds j with
        | .ok (.ptr ⟨_, _, .table num⟩) => (ctx.tabs[num]?).bind (fun tb => uFeldBreite tb f)
        | _ => none
      | .error _ => (ctx.tabs.find? (fun x => strEq x.name b)).bind (fun tb => uFeldBreite tb f)
  | .field base field => uRecordBreite ctx base field
  | .index (.variable b) _ =>
    match ctx.tabs.find? (fun x => strEq x.name b) with
    | some tb => if tb.arena then uFeldBreite tb "wert" else none
    | none => none
  | .call f [_] =>
    match uSpeicherBreite ctx.widths (.atom f) with
    | 0 => none
    | w + 1 => some (w + 1)
  | .bin op a b =>
    match uBinEin op with
    | some .shlW => uBreite ctx a
    | some .addW | some .subW | some .mulW => (uBreite ctx a).orElse fun _ => uBreite ctx b
    | _ => none
  | _ => none

/-- C13: the declared STORAGE type of the operand of `sizeof`: a type name (a builtin word or an alias of one), or a
    place with a declared storage width (`uBreite`: a parameter, a static, a field). A place of any other type, an
    aggregate, a pointer and everything unresolved has none, and `sizeof` of it is refused. Where the checked source
    type is at hand (a parameter, a type name) the storage must carry it (`SpTy.passt`). -/
def uSpTy (ctx : UCtx) : SExpr → Option SpTy
  | .variable t =>
    match uParamNr ctx t with
    | .ok j =>
      match uBreite ctx (.variable t), ctx.types[j]? with
      | some w, some τ => if (SpTy.wort w).passt τ then some (.wort w) else none
      | _, _ => none
    | .error _ =>
      match uBreite ctx (.variable t) with
      | some w => some (.wort w)
      | none =>
        match ctx.globs.find? (fun g => strEq g.name t) with
        | some _ => none
        | none =>
          match uSpeicherBreite ctx.widths (.atom t), uTypName ctx.alias t with
          | 0, _ => none
          | w + 1, .ok (lo, hi) => if (SpTy.wort (w + 1)).passt (.int lo hi) then some (.wort (w + 1)) else none
          | _, .error _ => none
  | e => (uBreite ctx e).map SpTy.wort

/-- C13: `sizeof(e)` in bytes: the size of the declared storage type, only for a valid resolved one. -/
def uGroesse (ctx : UCtx) (e : SExpr) : Option Nat :=
  match uSpTy ctx e with
  | some sp => if sp.gueltig then some sp.bytes else none
  | none => none

end Gabbro.Grammatik.Parser.Uebersetze
