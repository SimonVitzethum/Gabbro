module
public import Grammatik.Parser.Elab.Uebersetze.Kontext.CallLookup
@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

/-- The context after `let x [: T]`: the annotated range (when there is one) and the context in which the
    rest of the block reads `x` as a numeric parameter that shadows any earlier name. -/
def uBindKopf (ctx : UCtx) (x : String) : Option STyp → Except String (Option (Int × Int) × UCtx)
  | .none =>
    .ok (.none,
      { ctx with
        names := x :: ctx.names
        kinds := .int :: ctx.kinds
        types := .int 0 0 :: ctx.types
        bits := 0 :: ctx.bits })
  | .some ty =>
    match uErgBereich ctx.alias ty with
    | .error e => .error e
    | .ok (lo, hi) =>
      .ok (.some (lo, hi),
        { ctx with
          names := x :: ctx.names
          kinds := .int :: ctx.kinds
          types := .int lo hi :: ctx.types
          bits := uBindingBreite ctx ty :: ctx.bits })

/-- The context after a local `x` of kind `k` and type `ty`. -/
def uMitLokal (ctx : UCtx) (x : String) (k : UParamArt) (ty : Ty) (muts : List String) : UCtx :=
  { ctx with
    names := x :: ctx.names
    kinds := k :: ctx.kinds
    types := ty :: ctx.types
    bits := 0 :: ctx.bits
    muts := muts }

/-- A written call-result annotation carries storage metadata after the ordinary result/range checks.
    Unannotated calls and canonical read-back retain their original contexts. -/
def uAnnotatedBinding (before : UCtx) (annotation : Option STyp) (after : UCtx) : UCtx :=
  match annotation with
  | none => after
  | some ty =>
    if before.narrow then
      { after with bits := uBindingBreite before ty :: before.bits }
    else after

/-- Cache each binder's exact source list objects, retaining all types and diagnostics. -/
def uBindKopfFast (ctx : UCtx) (name : String) : Option STyp → Except String (Option (Int × Int) × UCtx)
  | none =>
    let after : UCtx :=
      { ctx with
        names := name :: ctx.names
        kinds := .int :: ctx.kinds
        types := .int 0 0 :: ctx.types
        bits := 0 :: ctx.bits }
    .ok (none, ctx.cacheBinding after name .int (.int 0 0) rfl rfl rfl)
  | some ty =>
    match uErgBereich ctx.alias ty with
    | .error err => .error err
    | .ok (lo, hi) =>
      let after : UCtx :=
        { ctx with
          names := name :: ctx.names
          kinds := .int :: ctx.kinds
          types := .int lo hi :: ctx.types
          bits := uBindingBreite ctx ty :: ctx.bits }
      .ok (some (lo, hi), ctx.cacheBinding after name .int (.int lo hi) rfl rfl rfl)

@[csimp] theorem uBindKopf_eq_fast : @uBindKopf = @uBindKopfFast := by
  funext ctx name ty
  cases ty with
  | none => simp only [uBindKopf, uBindKopfFast, UCtx.cacheBinding_eq]
  | some ty =>
    cases found : uErgBereich ctx.alias ty with
    | error err => simp only [uBindKopf, uBindKopfFast, found]
    | ok range =>
      rcases range with ⟨lo, hi⟩
      simp only [uBindKopf, uBindKopfFast, found, UCtx.cacheBinding_eq]

def uMitLokalFast (ctx : UCtx) (name : String) (kind : UParamArt) (ty : Ty) (muts : List String) : UCtx :=
  let after : UCtx :=
    { ctx with
      names := name :: ctx.names
      kinds := kind :: ctx.kinds
      types := ty :: ctx.types
      bits := 0 :: ctx.bits
      muts := muts }
  ctx.cacheBinding after name kind ty rfl rfl rfl

@[csimp] theorem uMitLokal_eq_fast : @uMitLokal = @uMitLokalFast := by
  funext ctx name kind ty muts
  exact (UCtx.cacheBinding_eq ctx (uMitLokal ctx name kind ty muts) name kind ty rfl rfl rfl).symm

end Gabbro.Grammatik.Parser.Uebersetze
