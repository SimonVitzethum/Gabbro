#!/usr/bin/env python3
"""Check the LLVM coverage register against actual Lean constructors/fields.

The register is a reviewed implementation classification, not a semantic proof.
No example, test program, corpus size or successful compilation is a denominator.
New/deleted model members require an explicit register update; default is OPEN.
"""
import argparse
from collections import Counter
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
REGISTER = ROOT / "dokumente/llvm-modelldeckung.tsv"
MODELS = {
    "Kern/Syntax/Typen.lean": ["Ty"],
    "Kern/Syntax/Syntax.lean": ["Signatur", "SigPasst", "Regklasse", "Deklaration", "Res", "Vertrag", "RufPasst", "Var", "Expr", "NutzlastExpr", "Args", "ErgExpr", "GleitOp", "Stmt", "Block", "Endblock", "Arms", "GrundArms", "Programm"],
    "Bausteine/Arena/ArenaZucker.lean": ["ArenaForm"],
    "Bausteine/Arena/ArenaDyn.lean": ["DynArena", "DynForm", "FreiZustand"],
    "Logik/Ruf/Maschine/RufMaschineG.lean": ["GRest"],
}


def uncomment(text):
    # Nested Lean block comments, then line comments. Keep line boundaries.
    out, i, depth = [], 0, 0
    while i < len(text):
        pair = text[i:i + 2]
        if pair == "/-":
            depth += 1
            i += 2
        elif depth and pair == "-/":
            depth -= 1
            i += 2
        elif depth:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        elif pair == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError("unclosed Lean comment")
    return "".join(out)


def members():
    result = {}
    for relative, names in MODELS.items():
        path = ROOT / "grammatik/Grammatik" / relative
        text = path.read_text()
        teile = path.with_suffix("")   # a file split by lean-teilen.py: its parts hold the declarations
        if teile.is_dir():
            text += "\n" + "\n".join(f.read_text() for f in sorted(teile.glob("T*.lean"), key=lambda f: int(f.stem[1:])))
        text = uncomment(text)
        if relative == "Kern/Syntax/Syntax.lean":
            declared = set(re.findall(r"^(?:inductive|structure) ([\w']+)", text, re.M))
            if declared != set(names):
                raise ValueError(f"core model family register differs: new={sorted(declared - set(names))}, removed={sorted(set(names) - declared)}")
        for name in names:
            match = re.search(rf"^(inductive|structure) {name}\b[^\n]*", text, re.M)
            if not match:
                raise ValueError(f"model type disappeared: {relative}:{name}")
            rest = text[match.end():]
            end = re.search(r"^(?:inductive|structure|def|abbrev|theorem|namespace|end|instance|attribute)\b", rest, re.M)
            body = rest[:end.start()] if end else rest
            if match[1] == "inductive":
                found = []
                for line in body.splitlines():
                    if not line.startswith("  | "):
                        continue
                    constructors = re.findall(r"\|\s*([\w']+)", line)
                    if not constructors:
                        raise ValueError(f"unparsed constructor in {relative}:{name}: {line}")
                    found.extend(constructors)
            else:
                found = re.findall(r"^  (?:\[)?([\w']+)\s*[:(]", body, re.M)
            if not found:
                raise ValueError(f"no members discovered: {relative}:{name}")
            for member in found:
                key = f"{name}.{member}"
                if key in result:
                    raise ValueError(f"duplicate model member: {key}")
                result[key] = f"grammatik/Grammatik/{relative}"
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", action="store_true", help="print the Lean inventory without classification")
    args = parser.parse_args()
    model = members()
    if args.inventory:
        for key, path in model.items():
            print(f"{key}\t{path}")
        return 0
    rows, errors = {}, []
    for nr, line in enumerate(REGISTER.read_text().splitlines(), 1):
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != 4:
            errors.append(f"line {nr}: expected member, status, implementation anchor, limitation")
            continue
        key, status, anchor, note = fields
        if key in rows:
            errors.append(f"line {nr}: duplicate {key}")
        if status not in {"LOWERED", "PARTIAL", "REFUSED", "ERASED", "MODEL_ONLY", "OPEN"}:
            errors.append(f"line {nr}: unknown status {status}")
        if not note:
            errors.append(f"line {nr}: missing boundary for {key}")
        if anchor != "-":
            file, _, symbol = anchor.partition("::")
            source = ROOT / file
            if not source.is_file() or (symbol and not re.search(rf"\bfn {re.escape(symbol)}\b", source.read_text())):
                errors.append(f"line {nr}: missing implementation anchor {anchor}")
        rows[key] = (status, note)
    errors += [f"unclassified Lean member: {k}" for k in sorted(model.keys() - rows.keys())]
    errors += [f"stale register member: {k}" for k in sorted(rows.keys() - model.keys())]
    for error in errors:
        print(f"ERROR: {error}", file=sys.stderr)
    if errors:
        return 1
    print(f"LLVM coverage denominator: {len(model)} actual Lean constructors/declaration fields")
    families = sorted({key.split('.')[0] for key in model})
    for family in families:
        counts = Counter(rows[key][0] for key in model if key.startswith(family + '.'))
        print(f"  {family}: " + ", ".join(f"{s}={n}" for s, n in sorted(counts.items())))
    print("Implementation classification only; no claim of compiler/binary refinement.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
