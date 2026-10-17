import Grammatik.Llvm.Model.Syntax

/-
  File:      Grammatik/Llvm/Model/Print.lean
  Subject:   TRACK L, PHASE L0 -- THE PRINTER from the Lean IR to `.ll` text.

  The printer is what `gabbro llvm` (the untrusted Rust producer) and the Lean lowering have in
  common: a module that the Lean function lowers prints to the text LLVM reads. A parser and a
  round-trip proof are NOT part of L0; the printer is total and structural, and the shape of its
  output is pinned by examples in `Witness.lean`.

  Cuts: float constants are printed as hexadecimal doubles (what LLVM requires; a binary32 value
  is converted exactly); the metadata nodes of `!tbaa` are a fixed table printed once at the end
  of the module (the scalar types, `gabbro-root` as root); `!range` is attached inline.
-/

namespace Gabbro.Llvm

open Gabbro.Grammatik.Gleitkomma

namespace Print

/-- A natural number in hexadecimal. -/
def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def pad16 (s : String) : String := String.ofList (List.replicate (16 - s.length) '0') ++ s

/-- The exact binary64 value of a binary32 value (every binary32 number is a binary64 number). -/
def f32AsF64 (g : F32) : F64 :=
  match wertExakt f32 g with
  | some e => rundeExakt f64 e
  | none => ⟨g.sign, if g.bexp == f32.bexpMax then f64.bexpMax else 0, g.frac * 2 ^ 29⟩

/-- `0x` and the sixteen hex digits of a double. -/
def dblHex (g : F64) : String := "0x" ++ pad16 (hex (zuBits f64 g))

end Print

namespace Ty

mutual
/-- LLVM type syntax. -/
def pr : Ty → String
  | int w => "i" ++ toString w
  | flt => "float"
  | dbl => "double"
  | ptr => "ptr"
  | void => "void"
  | arr n t => "[" ++ toString n ++ " x " ++ pr t ++ "]"
  | unit => "{}"
  | fld t r => "{ " ++ ", ".intercalate (pr t :: prRest r) ++ " }"
/-- The printed remaining fields of a struct chain. -/
def prRest : Ty → List String
  | fld t r => pr t :: prRest r
  | _ => []
end

end Ty

namespace Print

/-- The node id of the `!tbaa` tag of a scalar type (fixed table, see `moduleTail`). -/
def tagId : Ty → Nat
  | .int 8 => 10 | .int 16 => 11 | .int 32 => 12 | .int 64 => 13
  | .flt => 14 | .dbl => 15 | .ptr => 16 | _ => 17

def ann (t : Ty) : Meta → String
  | .range lo hi =>
      let w := match t with | .int w => w | _ => 0
      ", !range !{i" ++ toString w ++ " " ++ toString lo ++ ", i" ++ toString w ++ " "
        ++ toString hi ++ "}"
  | .tbaa t' => ", !tbaa !" ++ toString (tagId t')

def metas (t : Ty) (ms : List Meta) : String := String.join (ms.map (ann t))

def reg (r : Reg) : String := "%t" ++ toString r
def lbl (l : Lbl) : String := "l" ++ toString l

def order : Order → String
  | .unord => "unordered" | .mono => "monotonic" | .acq => "acquire"
  | .rel => "release" | .acrel => "acq_rel" | .seqc => "seq_cst"

def binop : BinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .udiv => "udiv" | .sdiv => "sdiv"
  | .urem => "urem" | .srem => "srem" | .shl => "shl" | .lshr => "lshr" | .ashr => "ashr"
  | .and => "and" | .or => "or" | .xor => "xor"

def fop : FOp → String
  | .add => "fadd" | .sub => "fsub" | .mul => "fmul" | .div => "fdiv"

def ipred : IPred → String
  | .eq => "eq" | .ne => "ne" | .ult => "ult" | .ule => "ule" | .ugt => "ugt" | .uge => "uge"
  | .slt => "slt" | .sle => "sle" | .sgt => "sgt" | .sge => "sge"

def fpred : FPred → String
  | .oeq => "oeq" | .one => "one" | .olt => "olt" | .ole => "ole" | .ogt => "ogt" | .oge => "oge"

def cast : Cast → String
  | .zext => "zext" | .sext => "sext" | .trunc => "trunc" | .bits => "bitcast"
  | .sitof => "sitofp" | .uitof => "uitofp"

def rmw : RmwOp → String
  | .xchg => "xchg" | .add => "add" | .sub => "sub" | .and => "and" | .or => "or" | .xor => "xor"

variable (M : Modl)

/-- An operand. -/
def opd : Opd → String
  | .reg r => reg r
  | .int _ n => toString n
  | .flt g => dblHex (f32AsF64 g)
  | .dbl g => dblHex g
  | .glob g => "@" ++ ((M.globs[g]?).map Glob.name).getD ("g" ++ toString g)
  | .null => "null"

/-- A typed operand `t v`. -/
def topd (t : Ty) (o : Opd) : String := t.pr ++ " " ++ opd M o

def align (al : Nat) : String := if al = 0 then "" else ", align " ++ toString al

/-- One instruction. -/
def instr : Instr → String
  | .bin d op w a b =>
      reg d ++ " = " ++ binop op ++ " i" ++ toString w ++ " " ++ opd M a ++ ", " ++ opd M b
  | .fbin d op t a b => reg d ++ " = " ++ fop op ++ " " ++ t.pr ++ " " ++ opd M a ++ ", " ++ opd M b
  | .icmp d p w a b =>
      reg d ++ " = icmp " ++ ipred p ++ " i" ++ toString w ++ " " ++ opd M a ++ ", " ++ opd M b
  | .fcmp d p t a b =>
      reg d ++ " = fcmp " ++ fpred p ++ " " ++ t.pr ++ " " ++ opd M a ++ ", " ++ opd M b
  | .pick d c t a b =>
      reg d ++ " = select i1 " ++ opd M c ++ ", " ++ topd M t a ++ ", " ++ topd M t b
  | .cast d k s t a => reg d ++ " = " ++ cast k ++ " " ++ topd M s a ++ " to " ++ t.pr
  | .alloc d t al => reg d ++ " = alloca " ++ t.pr ++ align al
  | .load d t p al vol ms =>
      reg d ++ " = load " ++ (if vol then "volatile " else "") ++ t.pr ++ ", ptr " ++ opd M p
        ++ align al ++ metas t ms
  | .store t v p al vol ms =>
      "store " ++ (if vol then "volatile " else "") ++ topd M t v ++ ", ptr " ++ opd M p
        ++ align al ++ metas t ms
  | .gep d t p ix inb =>
      reg d ++ " = getelementptr " ++ (if inb then "inbounds " else "") ++ t.pr ++ ", ptr "
        ++ opd M p ++ String.join (ix.map fun i => ", i64 " ++ opd M i)
  | .aload d t p o al =>
      reg d ++ " = load atomic " ++ t.pr ++ ", ptr " ++ opd M p ++ " " ++ order o ++ align al
  | .astor t v p o al =>
      "store atomic " ++ topd M t v ++ ", ptr " ++ opd M p ++ " " ++ order o ++ align al
  | .armw d op t p v o =>
      reg d ++ " = atomicrmw " ++ rmw op ++ " ptr " ++ opd M p ++ ", " ++ topd M t v ++ " "
        ++ order o
  | .cas d ok t p e n so fo =>
      reg d ++ " = cmpxchg ptr " ++ opd M p ++ ", " ++ topd M t e ++ ", " ++ topd M t n ++ " "
        ++ order so ++ " " ++ order fo ++ " ; success flag in " ++ reg ok
  | .fence o => "fence " ++ order o
  | .call d f args =>
      (match d with | some r => reg r ++ " = " | none => "") ++ "call "
        ++ ((M.funs[f]?).map fun fn => fn.ret.pr).getD "void" ++ " @"
        ++ ((M.funs[f]?).map Func.name).getD ("f" ++ toString f) ++ "("
        ++ ", ".intercalate (match M.funs[f]? with
            | some fn => (fn.params.zip args).map fun pa => pa.1.t.pr ++ " " ++ opd M pa.2
            | none => args.map (opd M)) ++ ")"
  | .asm d t _ args txt =>
      (match d with | some r => reg r ++ " = " | none => "") ++ "call " ++ t.pr ++ " asm \""
        ++ txt ++ "\"(" ++ ", ".intercalate (args.map (opd M)) ++ ")"
  | .fact c => "call void @llvm.assume(i1 " ++ opd M c ++ ")"

/-- A terminator; `rt` is the return type of the function it ends. -/
def term (rt : Ty) : Term → String
  | .jmp l => "br label %" ++ lbl l
  | .br c t e => "br i1 " ++ opd M c ++ ", label %" ++ lbl t ++ ", label %" ++ lbl e
  | .sw w v d cs =>
      "switch i" ++ toString w ++ " " ++ opd M v ++ ", label %" ++ lbl d ++ " ["
        ++ " ".intercalate (cs.map fun c => "i" ++ toString w ++ " " ++ toString c.1 ++ ", label %" ++ lbl c.2)
        ++ "]"
  | .ret none => "ret void"
  | .ret (some o) => "ret " ++ rt.pr ++ " " ++ opd M o
  | .dead => "unreachable"

def phi (p : Phi) : String :=
  reg p.d ++ " = phi " ++ p.t.pr ++ " "
    ++ ", ".intercalate (p.ins.map fun e => "[ " ++ opd M e.2 ++ ", %" ++ lbl e.1 ++ " ]")

def block (rt : Ty) (b : Block) : String :=
  lbl b.lbl ++ ":\n"
    ++ String.join (b.phis.map fun p => "  " ++ phi M p ++ "\n")
    ++ String.join (b.body.map fun i => "  " ++ instr M i ++ "\n")
    ++ "  " ++ term M rt b.term ++ "\n"

def func (f : Func) : String :=
  "define " ++ f.ret.pr ++ " @" ++ f.name ++ "("
    ++ ", ".intercalate (f.params.map fun p =>
         p.t.pr ++ (if p.noali then " noalias" else "") ++ " " ++ reg p.r) ++ ") {\n"
    ++ String.join (f.blks.map (block M f.ret)) ++ "}\n"

/-- The fixed `!tbaa` node table. -/
def moduleTail : String :=
  "declare void @llvm.assume(i1 noundef)\n!0 = !{!\"gabbro-root\"}\n"
    ++ "!1 = !{!\"omnipotent char\", !0, i64 0}\n"
    ++ String.join (([("i8", 2), ("i16", 3), ("i32", 4), ("i64", 5), ("float", 6), ("double", 7),
          ("ptr", 8)].map fun (n, i) => "!" ++ toString i ++ " = !{!\"gabbro-" ++ n ++ "\", !1, i64 0}\n"))
    ++ String.join ([(10, 2), (11, 3), (12, 4), (13, 5), (14, 6), (15, 7), (16, 8)].map fun (t, i) =>
         "!" ++ toString t ++ " = !{!" ++ toString i ++ ", !" ++ toString i ++ ", i64 0}\n")

/-- The global definitions. -/
def globals : String :=
  String.join (M.globs.map fun g => "@" ++ g.name ++ " = global " ++ g.t.pr ++ " zeroinitializer\n")

/-- A whole module. -/
def modl : String :=
  globals M ++ String.join (M.funs.map (func M)) ++ moduleTail

end Print

end Gabbro.Llvm
