//! Recursion elimination over the emitter's typed, unoptimised instruction stream.
//!
//! Cyclic call components use heap frames and a single dispatch loop. Every SSA
//! value crossing a suspension lives in its frame; address-taken locals stay at
//! stable addresses. Direct and indirect internal calls use the same mechanism.
//! Pure tail cycles have already been lowered to jumps by the source emitter.
//! This is a producer transformation, not a translation-validation certificate.

use super::Ziel;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

const HEADER: &str = "ptr, ptr, i32, i32, ptr, ptr, i64";
const RESERVE: &str = "@\"$gabbro.stack.reserve\"";
const PUSH: &str = "@\"$gabbro.stack.push\"";
const POP: &str = "@\"$gabbro.stack.pop\"";
const RUN: &str = "@\"$gabbro.stack.run\"";
const FINISH: &str = "@\"$gabbro.stack.finish\"";

/// Split at top-level commas, respecting LLVM aggregates and quoted symbols.
fn parts(s: &str) -> Vec<&str> {
    let mut result = Vec::new();
    let (mut start, mut depth, mut quoted) = (0, 0i32, false);
    for (i, c) in s.char_indices() {
        if c == '"' {
            quoted = !quoted;
        }
        if quoted {
            continue;
        }
        match c {
            '(' | '[' | '{' | '<' => depth += 1,
            ')' | ']' | '}' | '>' => depth -= 1,
            ',' if depth == 0 => {
                result.push(s[start..i].trim());
                start = i + 1;
            }
            _ => {}
        }
    }
    result.push(s[start..].trim());
    result
}

fn ty(s: &str) -> Result<(&str, &str), String> {
    let s = s.trim_start();
    if s.is_empty() {
        return Err("missing instruction type".into());
    }
    let mut depth = 0i32;
    for (i, c) in s.char_indices() {
        match c {
            '[' | '{' | '<' => depth += 1,
            ']' | '}' | '>' => depth -= 1,
            _ => {}
        }
        if depth == 0 && (c.is_whitespace() || c == ',') {
            return Ok((&s[..i], s[i..].trim_start()));
        }
        if depth == 0 && matches!(c, ']' | '}' | '>') {
            return Ok((&s[..i + 1], s[i + 1..].trim_start()));
        }
    }
    Ok((s, ""))
}

fn typed(s: &str) -> Result<(String, String), String> {
    let (t, value) = ty(s)?;
    // ABI attributes precede the operand, including dereferenceable(N).
    let value = value.split_whitespace().last().unwrap_or(value);
    Ok((t.into(), value.into()))
}

/// LP64 allocation size/alignment from the ACTUAL emitted LLVM type bodies,
/// including aggregate padding and packed formats. Shared by arena accounting.
pub(super) fn layout(typ: &str, definitions: &[(String, String)]) -> Option<(u64, u64)> {
    fn go(typ: &str, defs: &[(String, String)], seen: &mut BTreeSet<String>) -> Option<(u64, u64)> {
        let typ = typ.trim();
        let round = |n: u64, a: u64| n.checked_add(a - 1).map(|n| n / a * a);
        if let Some(name) = typ.strip_prefix('%') {
            if !seen.insert(name.into()) {
                return None;
            }
            let (_, body) = defs.iter().find(|(n, _)| n == name)?;
            let result = go(body, defs, seen);
            seen.remove(name);
            return result;
        }
        if let Some(inner) = typ.strip_prefix('[').and_then(|s| s.strip_suffix(']')) {
            let (n, elem) = inner.split_once(" x ")?;
            let (size, align) = go(elem, defs, seen)?;
            return Some((
                round(size, align)?.checked_mul(n.trim().parse().ok()?)?,
                align,
            ));
        }
        let packed = typ.starts_with("<{");
        let body = if packed {
            typ.strip_prefix("<{")?.strip_suffix("}>")
        } else {
            typ.strip_prefix('{').and_then(|s| s.strip_suffix('}'))
        };
        if let Some(body) = body {
            let (mut size, mut align) = (0, 1);
            for field in parts(body).into_iter().filter(|s| !s.is_empty()) {
                let (bytes, natural) = go(field, defs, seen)?;
                let a = if packed { 1 } else { natural };
                size = round(size, a)?.checked_add(bytes)?;
                align = align.max(a);
            }
            return Some((round(size, align)?, align));
        }
        match typ {
            "ptr" | "double" => Some((8, 8)),
            "float" => Some((4, 4)),
            "void" => Some((0, 1)),
            _ => {
                let bits: u32 = typ.strip_prefix('i')?.parse().ok()?;
                let size = u64::from(bits.div_ceil(8));
                Some((size, size.checked_next_power_of_two()?.min(8)))
            }
        }
    }
    go(typ, definitions, &mut BTreeSet::new())
}

#[derive(Clone)]
struct Call {
    ret: String,
    callee: String,
    args: Vec<(String, String)>,
}

fn call(rhs: &str) -> Result<Option<Call>, String> {
    let Some(s) = rhs.strip_prefix("call ") else {
        return Ok(None);
    };
    let (ret, rest) = ty(s)?;
    if rest.starts_with("asm ") {
        return Ok(None);
    }
    let Some(open) = rest.find('(') else {
        return Err(format!("invalid call: {rhs}"));
    };
    let Some(close) = rest.rfind(')') else {
        return Err(format!("invalid call: {rhs}"));
    };
    let args = if close == open + 1 {
        Vec::new()
    } else {
        parts(&rest[open + 1..close])
            .into_iter()
            .map(typed)
            .collect::<Result<_, _>>()?
    };
    Ok(Some(Call {
        ret: ret.into(),
        callee: rest[..open].trim().into(),
        args,
    }))
}

#[derive(Clone)]
struct Slot {
    typ: String,
    object: bool,
    field: usize,
}
#[derive(Clone)]
struct Function {
    header: String,
    symbol: String,
    ret: String,
    params: Vec<(String, String)>,
    lines: Vec<String>,
    slots: BTreeMap<String, Slot>,
    number: usize,
}

fn definition(line: &str) -> (&str, &str) {
    match line.split_once(" = ") {
        Some((lhs, rhs)) => (lhs.trim(), rhs),
        None => ("", line),
    }
}

fn result_type(rhs: &str) -> Result<String, String> {
    let (op, rest) = rhs
        .split_once(' ')
        .ok_or_else(|| format!("untyped instruction: {rhs}"))?;
    let first = |s: &str| ty(s).map(|(t, _)| t.to_string());
    match op {
        "alloca" | "getelementptr" => Ok("ptr".into()),
        "icmp" | "fcmp" => Ok("i1".into()),
        "load" => first(
            rest.trim_start_matches("atomic ")
                .trim_start_matches("volatile "),
        ),
        "trunc" | "zext" | "sext" | "fptrunc" | "fpext" | "fptoui" | "fptosi" | "uitofp"
        | "sitofp" | "ptrtoint" | "inttoptr" | "bitcast" => first(
            rhs.rsplit_once(" to ")
                .ok_or_else(|| format!("invalid cast: {rhs}"))?
                .1,
        ),
        "select" => first(parts(rest).get(1).ok_or("invalid select")?),
        "atomicrmw" => first(parts(rest).get(1).ok_or("invalid atomicrmw")?),
        "cmpxchg" => Ok(format!(
            "{{ {}, i1 }}",
            first(parts(rest).get(1).ok_or("invalid cmpxchg")?)?
        )),
        "extractvalue" => {
            let operands = parts(rest);
            let (aggregate, _) = ty(operands[0])?;
            let fields = parts(
                aggregate
                    .trim_start_matches('{')
                    .trim_end_matches('}')
                    .trim(),
            );
            let index: usize = operands
                .get(1)
                .ok_or("invalid extractvalue")?
                .parse()
                .map_err(|_| "invalid aggregate index")?;
            Ok(fields
                .get(index)
                .ok_or("aggregate index outside type")?
                .to_string())
        }
        "phi" | "insertvalue" | "fneg" | "call" => first(rest),
        "add" | "sub" | "mul" | "udiv" | "sdiv" | "urem" | "srem" | "and" | "or" | "xor"
        | "shl" | "lshr" | "ashr" | "fadd" | "fsub" | "fmul" | "fdiv" | "frem" => {
            let mut rest = rest;
            while let Some((flag, next)) = rest.split_once(' ') {
                if matches!(flag, "nsw" | "nuw" | "exact" | "fast") {
                    rest = next;
                } else {
                    break;
                }
            }
            first(rest)
        }
        _ => Err(format!(
            "unsupported emitter instruction in continuation frame: {rhs}"
        )),
    }
}

impl Function {
    fn parse(header: &str, lines: Vec<String>, number: usize) -> Result<Self, String> {
        let (ret, rest) = ty(header.strip_prefix("define ").ok_or("missing define")?)?;
        let open = rest.find('(').ok_or("missing parameters")?;
        let close = rest.rfind(')').ok_or("missing parameter end")?;
        let symbol = rest[..open].trim().to_string();
        let params = if close == open + 1 {
            vec![]
        } else {
            parts(&rest[open + 1..close])
                .into_iter()
                .map(typed)
                .collect::<Result<Vec<_>, _>>()?
        };
        let mut slots = BTreeMap::new();
        for (typ, name) in &params {
            let field = slots.len() + 7;
            slots.insert(
                name.clone(),
                Slot {
                    typ: typ.clone(),
                    object: false,
                    field,
                },
            );
        }
        for line in &lines {
            let (name, rhs) = definition(line.trim());
            if name.is_empty() {
                continue;
            }
            let object = rhs.starts_with("alloca ");
            let typ = if object {
                ty(&rhs[7..])?.0.into()
            } else {
                result_type(rhs)?
            };
            let field = slots.len() + 7;
            slots.insert(name.into(), Slot { typ, object, field });
        }
        Ok(Self {
            header: header.into(),
            symbol,
            ret: ret.into(),
            params,
            lines,
            slots,
            number,
        })
    }
    fn frame(&self) -> String {
        format!("%\"$gabbro.frame.{}\"", self.number)
    }
    fn step(&self) -> String {
        format!("@\"$gabbro.step.{}\"", self.number)
    }
    fn size(&self) -> String {
        format!(
            "ptrtoint (ptr getelementptr ({}, ptr null, i32 1) to i64)",
            self.frame()
        )
    }
    fn compatible(&self, c: &Call) -> bool {
        self.ret == c.ret
            && self.params.len() == c.args.len()
            && self
                .params
                .iter()
                .zip(&c.args)
                .all(|((a, _), (b, _))| a == b)
    }
}

/// Only cycles need continuations. Indirect edges conservatively include every
/// compatible internal definition, so an indirect or mutual cycle cannot escape.
pub(super) fn lower(
    text: &str,
    ziel: &Ziel,
    definitions: &[(String, String)],
) -> Result<String, String> {
    let lines: Vec<_> = text.lines().collect();
    let (mut functions, mut other) = (Vec::new(), String::new());
    let mut i = 0;
    while i < lines.len() {
        if lines[i].starts_with("define ") {
            let header = lines[i];
            i += 1;
            let mut body = Vec::new();
            while i < lines.len() && lines[i] != "}" {
                body.push(lines[i].to_string());
                i += 1;
            }
            functions.push(Function::parse(header, body, functions.len())?);
        } else {
            writeln!(other, "{}", lines[i]).unwrap();
        }
        i += 1;
    }
    let mut graph: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for f in &functions {
        let mut edges = BTreeSet::new();
        for line in &f.lines {
            if let Some(c) = call(definition(line.trim()).1)? {
                for g in &functions {
                    if c.callee == g.symbol || (c.callee.starts_with('%') && g.compatible(&c)) {
                        edges.insert(g.symbol.clone());
                    }
                }
            }
        }
        graph.insert(f.symbol.clone(), edges);
    }
    let components = super::tarjan(&graph);
    let cyclic: BTreeSet<_> = components
        .into_iter()
        .filter(|c| c.len() > 1 || graph[&c[0]].contains(&c[0]))
        .flatten()
        .collect();
    if cyclic.is_empty() {
        return Ok(text.into());
    }
    let selected: BTreeMap<_, _> = functions
        .iter()
        .filter(|f| cyclic.contains(&f.symbol))
        .map(|f| (f.symbol.clone(), f.clone()))
        .collect();
    let mut out = other;
    for f in selected.values() {
        let mut fields: Vec<_> = f.slots.values().collect();
        fields.sort_by_key(|s| s.field);
        for field in &fields {
            if layout(&field.typ, definitions).is_none() {
                return Err(format!(
                    "unrepresentable continuation field type {} for {}",
                    field.typ, f.symbol
                ));
            }
        }
        let extra = fields
            .iter()
            .map(|s| format!(", {{ {}, i64 }}", s.typ))
            .collect::<String>();
        let body = format!("{{ {HEADER}{extra} }}");
        let (size, _) = layout(&body, definitions)
            .ok_or_else(|| format!("unrepresentable continuation layout for {}", f.symbol))?;
        if size > i64::MAX as u64 - 1048576 {
            return Err(format!(
                "continuation frame exceeds the addressable extent for {}",
                f.symbol
            ));
        }
        writeln!(out, "{} = type {{ {HEADER}{extra} }}", f.frame()).unwrap();
    }
    for f in &functions {
        if selected.contains_key(&f.symbol) {
            out.push_str(&emit(f, &selected)?);
        } else {
            writeln!(out, "{}\n{}\n}}", f.header, f.lines.join("\n")).unwrap();
        }
    }
    out.push_str(&runtime(ziel));
    Ok(out)
}

struct Writer<'a> {
    f: &'a Function,
    out: String,
    serial: usize,
}
impl Writer<'_> {
    fn tmp(&mut self) -> String {
        let n = self.serial;
        self.serial += 1;
        format!("%sl{n}")
    }
    fn line(&mut self, s: impl AsRef<str>) {
        writeln!(self.out, "  {}", s.as_ref()).unwrap();
    }
    fn addr(&mut self, frame: &str, field: usize, typ: &str) -> String {
        let p = self.tmp();
        self.line(format!(
            "{p} = getelementptr {typ}, ptr {frame}, i32 0, i32 {field}"
        ));
        p
    }
    fn slot(&mut self, name: &str) -> String {
        self.addr("%frame", self.f.slots[name].field, &self.f.frame())
    }
    fn value(&mut self, name: &str) -> String {
        let slot = &self.f.slots[name];
        let (typ, object) = (slot.typ.clone(), slot.object);
        let p = self.slot(name);
        if object {
            p
        } else {
            let v = self.tmp();
            self.line(format!("{v} = load {typ}, ptr {p}, align 8"));
            v
        }
    }
    fn replace(&mut self, s: &str) -> String {
        let mut out = String::new();
        let bytes = s.as_bytes();
        let mut i = 0;
        let mut quoted = false;
        while i < bytes.len() {
            if bytes[i] == b'"' {
                quoted = !quoted;
            }
            if !quoted && bytes[i] == b'%' {
                let start = i;
                i += 1;
                while i < bytes.len()
                    && (bytes[i].is_ascii_alphanumeric() || matches!(bytes[i], b'_' | b'.' | b'$'))
                {
                    i += 1;
                }
                let name = &s[start..i];
                if self.f.slots.contains_key(name) {
                    out.push_str(&self.value(name));
                } else {
                    out.push_str(name);
                }
            } else {
                let ch = s[i..].chars().next().expect("valid UTF-8 instruction");
                out.push(ch);
                i += ch.len_utf8();
            }
        }
        out
    }
    fn save(&mut self, name: &str, value: &str) {
        let p = self.slot(name);
        self.line(format!(
            "store {} {value}, ptr {p}, align 8",
            self.f.slots[name].typ
        ));
    }
    fn push(&mut self, target: &Function, c: &Call, result: &str, pc: usize) {
        let pcptr = self.addr("%frame", 2, &self.f.frame());
        self.line(format!("store i32 {pc}, ptr {pcptr}, align 4"));
        let dest = if result.is_empty() {
            "null".into()
        } else {
            self.slot(result)
        };
        // Read all arguments BEFORE reserving a frame (ancestor addresses remain stable).
        let args: Vec<_> = c
            .args
            .iter()
            .map(|(t, v)| (t.clone(), self.replace(v)))
            .collect();
        let child = self.tmp();
        self.line(format!(
            "{child} = call ptr {PUSH}(ptr %ctx, i64 {}, ptr {}, ptr {dest})",
            target.size(),
            target.step()
        ));
        for ((_, name), (typ, value)) in target.params.iter().zip(args) {
            let p = self.addr(&child, target.slots[name].field, &target.frame());
            self.line(format!("store {typ} {value}, ptr {p}, align 8"));
        }
        self.line("ret void");
    }
}

fn emit(f: &Function, selected: &BTreeMap<String, Function>) -> Result<String, String> {
    let mut w = Writer {
        f,
        out: String::new(),
        serial: 0,
    };
    let mut cases = Vec::new();
    let mut current_label = String::new();
    let mut phis: BTreeMap<String, Vec<(String, String, Vec<(String, String)>)>> = BTreeMap::new();
    for line in &f.lines {
        let line = line.trim();
        if let Some(label) = line.strip_suffix(':') {
            current_label = label.into();
        }
        let (name, rhs) = definition(line);
        if let Some(rest) = rhs.strip_prefix("phi ") {
            let (typ, incoming) = ty(rest)?;
            let mut pairs = Vec::new();
            for pair in parts(incoming) {
                let p = parts(
                    pair.trim()
                        .trim_start_matches('[')
                        .trim_end_matches(']')
                        .trim(),
                );
                if p.len() != 2 {
                    return Err("invalid phi input".into());
                }
                pairs.push((p[0].into(), p[1].trim_start_matches('%').into()));
            }
            phis.entry(current_label.clone())
                .or_default()
                .push((name.into(), typ.into(), pairs));
        }
    }
    let entry = f
        .lines
        .iter()
        .find_map(|l| l.trim().strip_suffix(':'))
        .ok_or("missing entry block")?;
    cases.push(entry.to_string());
    current_label.clear();
    for line in &f.lines {
        let line = line.trim();
        if let Some(label) = line.strip_suffix(':') {
            current_label = label.into();
            writeln!(w.out, "{line}").unwrap();
            continue;
        }
        let (name, rhs) = definition(line);
        if rhs.starts_with("alloca ") || rhs.starts_with("phi ") {
            continue;
        }
        if let Some(c) = call(rhs)? {
            if let Some(target) = selected.get(&c.callee) {
                let pc = cases.len();
                let resume = format!("sl_resume_{pc}");
                cases.push(resume.clone());
                w.push(target, &c, name, pc);
                writeln!(w.out, "{resume}:").unwrap();
                continue;
            }
            if c.callee.starts_with('%') {
                let targets: Vec<_> = selected.values().filter(|t| t.compatible(&c)).collect();
                if !targets.is_empty() {
                    let pc = cases.len();
                    let resume = format!("sl_resume_{pc}");
                    cases.push(resume.clone());
                    let fp = w.replace(&c.callee);
                    for (i, target) in targets.iter().enumerate() {
                        let matches = w.tmp();
                        w.line(format!("{matches} = icmp eq ptr {fp}, {}", target.symbol));
                        w.line(format!(
                            "br i1 {matches}, label %sl_call_{pc}_{i}, label %sl_next_{pc}_{i}"
                        ));
                        writeln!(w.out, "sl_call_{pc}_{i}:").unwrap();
                        w.push(target, &c, name, pc);
                        writeln!(w.out, "sl_next_{pc}_{i}:").unwrap();
                    }
                    // A foreign/acyclic function pointer keeps its ABI; every internal
                    // target that can close a cycle was dispatched above.
                    let instruction = w.replace(rhs);
                    if name.is_empty() {
                        w.line(instruction);
                    } else {
                        let v = w.tmp();
                        w.line(format!("{v} = {instruction}"));
                        w.save(name, &v);
                    }
                    w.line(format!("br label %{resume}"));
                    writeln!(w.out, "{resume}:").unwrap();
                    continue;
                }
            }
        }
        if let Some(rest) = rhs.strip_prefix("ret ") {
            if rest != "void" {
                let (typ, value) = ty(rest)?;
                let v = w.replace(value);
                let p = w.addr("%frame", 1, &f.frame());
                let dest = w.tmp();
                w.line(format!("{dest} = load ptr, ptr {p}, align 8"));
                w.line(format!("store {typ} {v}, ptr {dest}, align 8"));
            }
            w.line(format!("call void {POP}(ptr %ctx, ptr %frame)"));
            w.line("ret void");
            continue;
        }
        // Parallel phi copies on predecessor edges, before changing any phi cell.
        if rhs.starts_with("br ") || rhs.starts_with("switch ") {
            let mut copies = Vec::new();
            for list in phis.values() {
                for (name, _, incoming) in list {
                    if let Some((value, _)) =
                        incoming.iter().find(|(_, pred)| pred == &current_label)
                    {
                        copies.push((name.clone(), w.replace(value)));
                    }
                }
            }
            for (name, value) in copies {
                w.save(&name, &value);
            }
        }
        let instruction = w.replace(rhs);
        if name.is_empty() {
            w.line(instruction);
        } else {
            let v = w.tmp();
            w.line(format!("{v} = {instruction}"));
            w.save(name, &v);
        }
    }
    let mut out = format!(
        "define void {}(ptr %frame, ptr %ctx) {{\nsl_dispatch:\n  %pcp = getelementptr {}, ptr %frame, i32 0, i32 2\n  %pc = load i32, ptr %pcp, align 4\n  switch i32 %pc, label %sl_invalid [\n",
        f.step(),
        f.frame()
    );
    for (pc, label) in cases.iter().enumerate() {
        writeln!(out, "    i32 {pc}, label %{label}").unwrap();
    }
    out.push_str("  ]\nsl_invalid:\n  call void @llvm.trap()\n  unreachable\n");
    out.push_str(&w.out);
    out.push_str("}\n");
    // Public ABI wrapper: only this outer entry owns a dispatcher context.
    writeln!(out, "{}\nsl_entry:", f.header).unwrap();
    writeln!(out, "  %ctx = alloca {{ ptr, ptr, i64 }}, align 8\n  store {{ ptr, ptr, i64 }} zeroinitializer, ptr %ctx, align 8").unwrap();
    if f.ret != "void" {
        writeln!(out, "  %result = call ptr {RESERVE}(ptr %ctx, i64 ptrtoint (ptr getelementptr ({}, ptr null, i32 1) to i64))", f.ret).unwrap();
    }
    writeln!(
        out,
        "  %frame = call ptr {PUSH}(ptr %ctx, i64 {}, ptr {}, ptr {})",
        f.size(),
        f.step(),
        if f.ret == "void" { "null" } else { "%result" }
    )
    .unwrap();
    for (i, (typ, name)) in f.params.iter().enumerate() {
        writeln!(out, "  %arg{i} = getelementptr {}, ptr %frame, i32 0, i32 {}\n  store {typ} {name}, ptr %arg{i}, align 8", f.frame(), f.slots[name].field).unwrap();
    }
    writeln!(out, "  call void {RUN}(ptr %ctx)").unwrap();
    if f.ret != "void" {
        writeln!(out, "  %answer = load {}, ptr %result, align 8", f.ret).unwrap();
    }
    writeln!(
        out,
        "  call void {FINISH}(ptr %ctx)\n  ret {}\n}}",
        if f.ret == "void" {
            "void".into()
        } else {
            format!("{} %answer", f.ret)
        }
    )
    .unwrap();
    Ok(out)
}

fn runtime(ziel: &Ziel) -> String {
    let (map, unmap, asm, constraints, args) = if ziel.name == "x86_64" {
        (
            9,
            11,
            "syscall",
            "={rax},{rax},{rdi},{rsi},{rdx},{r10},{r8},{r9},~{rcx},~{r11},~{memory}",
            "i64 0, i64 %bytes, i64 3, i64 34, i64 -1, i64 0",
        )
    } else {
        (
            222,
            215,
            "svc #0",
            "={x0},{x8},{x0},{x1},{x2},{x3},{x4},{x5},~{memory}",
            "i64 0, i64 %bytes, i64 3, i64 34, i64 -1, i64 0",
        )
    };
    let free_constraint = if ziel.name == "x86_64" {
        "={rax},{rax},{rdi},{rsi},~{rcx},~{r11},~{memory}"
    } else {
        "={x0},{x8},{x0},{x1},~{memory}"
    };
    format!(
        r#"
declare void @llvm.trap()
; Chunk header: previous chunk, previous offset, mapping length. Data is 16-aligned.
define internal ptr {RESERVE}(ptr %ctx, i64 %size) {{
entry:
  %cp = getelementptr {{ ptr, ptr, i64 }}, ptr %ctx, i32 0, i32 1
  %up = getelementptr {{ ptr, ptr, i64 }}, ptr %ctx, i32 0, i32 2
  %chunk = load ptr, ptr %cp, align 8
  %used = load i64, ptr %up, align 8
  %safe = icmp ule i64 %size, 9223372036853727232
  br i1 %safe, label %round, label %failure
round:
  %plus = add i64 %size, 15
  %aligned = and i64 %plus, -16
  %end = add i64 %used, %aligned
  %have = icmp ne ptr %chunk, null
  br i1 %have, label %check, label %new
check:
  %lenp = getelementptr i64, ptr %chunk, i64 2
  %len = load i64, ptr %lenp, align 8
  %fits = icmp ule i64 %end, %len
  br i1 %fits, label %old, label %new
old:
  %p = getelementptr i8, ptr %chunk, i64 %used
  store i64 %end, ptr %up, align 8
  ret ptr %p
new:
  %need = add i64 %aligned, 32
  %large = icmp ugt i64 %need, 1048576
  %bytes = select i1 %large, i64 %need, i64 1048576
  %raw = call i64 asm sideeffect "{asm}", "{constraints}"(i64 {map}, {args})
  %bad = icmp uge i64 %raw, -4095
  br i1 %bad, label %failure, label %mapped
mapped:
  %base = inttoptr i64 %raw to ptr
  store ptr %chunk, ptr %base, align 8
  %savep = getelementptr i64, ptr %base, i64 1
  store i64 %used, ptr %savep, align 8
  %sizep = getelementptr i64, ptr %base, i64 2
  store i64 %bytes, ptr %sizep, align 8
  store ptr %base, ptr %cp, align 8
  %next = add i64 %aligned, 32
  store i64 %next, ptr %up, align 8
  %data = getelementptr i8, ptr %base, i64 32
  ret ptr %data
failure:
  call void @llvm.trap()
  unreachable
}}
define internal void @"$gabbro.stack.unmap"(ptr %chunk) {{
entry:
  %raw = ptrtoint ptr %chunk to i64
  %lenp = getelementptr i64, ptr %chunk, i64 2
  %len = load i64, ptr %lenp, align 8
  %rc = call i64 asm sideeffect "{asm}", "{free_constraint}"(i64 {unmap}, i64 %raw, i64 %len)
  %ok = icmp eq i64 %rc, 0
  br i1 %ok, label %done, label %failure
failure:
  call void @llvm.trap()
  unreachable
done:
  ret void
}}
define internal ptr {PUSH}(ptr %ctx, i64 %size, ptr %step, ptr %dest) {{
entry:
  %cp = getelementptr {{ ptr, ptr, i64 }}, ptr %ctx, i32 0, i32 1
  %up = getelementptr {{ ptr, ptr, i64 }}, ptr %ctx, i32 0, i32 2
  %oldchunk = load ptr, ptr %cp, align 8
  %oldused = load i64, ptr %up, align 8
  %parent = load ptr, ptr %ctx, align 8
  %frame = call ptr {RESERVE}(ptr %ctx, i64 %size)
  store ptr %parent, ptr %frame, align 8
  %dp = getelementptr {{ {HEADER} }}, ptr %frame, i32 0, i32 1
  store ptr %dest, ptr %dp, align 8
  %pcp = getelementptr {{ {HEADER} }}, ptr %frame, i32 0, i32 2
  store i32 0, ptr %pcp, align 4
  %sp = getelementptr {{ {HEADER} }}, ptr %frame, i32 0, i32 4
  store ptr %step, ptr %sp, align 8
  %scp = getelementptr {{ {HEADER} }}, ptr %frame, i32 0, i32 5
  store ptr %oldchunk, ptr %scp, align 8
  %sup = getelementptr {{ {HEADER} }}, ptr %frame, i32 0, i32 6
  store i64 %oldused, ptr %sup, align 8
  store ptr %frame, ptr %ctx, align 8
  ret ptr %frame
}}
define internal void {POP}(ptr %ctx, ptr %frame) {{
entry:
  %parent = load ptr, ptr %frame, align 8
  %cp = getelementptr {{ ptr, ptr, i64 }}, ptr %ctx, i32 0, i32 1
  %up = getelementptr {{ ptr, ptr, i64 }}, ptr %ctx, i32 0, i32 2
  %scp = getelementptr {{ {HEADER} }}, ptr %frame, i32 0, i32 5
  %saved = load ptr, ptr %scp, align 8
  %sup = getelementptr {{ {HEADER} }}, ptr %frame, i32 0, i32 6
  %used = load i64, ptr %sup, align 8
  %chunk = load ptr, ptr %cp, align 8
  %same = icmp eq ptr %chunk, %saved
  br i1 %same, label %done, label %release
release:
  call void @"$gabbro.stack.unmap"(ptr %chunk)
  br label %done
done:
  store ptr %saved, ptr %cp, align 8
  store i64 %used, ptr %up, align 8
  store ptr %parent, ptr %ctx, align 8
  ret void
}}
define internal void {RUN}(ptr %ctx) {{
entry:
  br label %loop
loop:
  %frame = load ptr, ptr %ctx, align 8
  %empty = icmp eq ptr %frame, null
  br i1 %empty, label %done, label %dispatch
dispatch:
  %sp = getelementptr {{ {HEADER} }}, ptr %frame, i32 0, i32 4
  %step = load ptr, ptr %sp, align 8
  call void %step(ptr %frame, ptr %ctx)
  br label %loop
done:
  ret void
}}
define internal void {FINISH}(ptr %ctx) {{
entry:
  %cp = getelementptr {{ ptr, ptr, i64 }}, ptr %ctx, i32 0, i32 1
  br label %loop
loop:
  %chunk = load ptr, ptr %cp, align 8
  %empty = icmp eq ptr %chunk, null
  br i1 %empty, label %done, label %release
release:
  %previous = load ptr, ptr %chunk, align 8
  call void @"$gabbro.stack.unmap"(ptr %chunk)
  store ptr %previous, ptr %cp, align 8
  br label %loop
done:
  ret void
}}
"#
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn allocation_layout_includes_padding_and_packed_strides() {
        let definitions = vec![
            ("Record".into(), "{ i8, i64 }".into()),
            ("Packed".into(), "<{ i8, i64 }>".into()),
            ("Option".into(), "{ i32, [8 x i8] }".into()),
        ];
        assert_eq!(layout("%Record", &definitions), Some((16, 8)));
        assert_eq!(layout("[3 x %Record]", &definitions), Some((48, 8)));
        assert_eq!(layout("[3 x %Packed]", &definitions), Some((27, 1)));
        assert_eq!(layout("[3 x %Option]", &definitions), Some((36, 4)));
        assert_eq!(layout("[18446744073709551615 x i64]", &definitions), None);
    }
    fn execute(name: &str, body: &str, expected: i32) {
        for target in [&super::super::ZIEL_X86_64, &super::super::ZIEL_AARCH64] {
            let transformed = lower(body, target, &[]).unwrap();
            assert!(transformed.contains("$gabbro.stack.run"));
            let exit = if target.name == "x86_64" {
                "call void asm sideeffect \"syscall\", \"{rax},{rdi},~{rcx},~{r11},~{memory}\"(i64 231, i64 %code)"
            } else {
                "call void asm sideeffect \"svc #0\", \"{x8},{x0},~{memory}\"(i64 94, i64 %code)"
            };
            let ir = format!(
                "target triple = \"{}\"\ntarget datalayout = \"{}\"\n{transformed}\ndefine void @_start() {{\nentry:\n  %answer = call i32 @\"entry\"()\n  %code = zext i32 %answer to i64\n  {exit}\n  unreachable\n}}\n",
                target.triple, target.datalayout
            );
            super::super::test_tools::run(name, target, &ir, expected);
        }
    }

    #[test]
    fn non_tail_recursion_keeps_values_and_locals_on_a_tiny_native_stack() {
        execute(
            "non-tail",
            r#"
define i32 @"depth"(i32 %p0) {
entry:
  %a = alloca [64 x i64], align 8
  %ptr = getelementptr [64 x i64], ptr %a, i32 0, i32 33
  store i64 19, ptr %ptr, align 8
  %done = icmp eq i32 %p0, 0
  br i1 %done, label %base, label %recurse
base:
  ret i32 0
recurse:
  %n = sub i32 %p0, 1
  %child = call i32 @"depth"(i32 %n)
  %second = call i32 @"depth"(i32 0)
  %both = add i32 %child, %second
  %saved = load i64, ptr %ptr, align 8
  %value = trunc i64 %saved to i32
  %result = add i32 %both, %value
  ret i32 %result
}
define i32 @"entry"() {
entry:
  %r = call i32 @"depth"(i32 200000)
  %ok = icmp eq i32 %r, 3800000
  %code = select i1 %ok, i32 73, i32 99
  ret i32 %code
}
"#,
            73,
        );
    }

    #[test]
    fn indirect_mutual_recursion_preserves_phi_and_aggregate_returns() {
        execute(
            "indirect-mutual",
            r#"
define { i32, i1 } @"a"(i32 %p0) {
entry:
  %done = icmp eq i32 %p0, 0
  br i1 %done, label %base, label %recurse
base:
  ret { i32, i1 } { i32 7, i1 true }
recurse:
  %n = sub i32 %p0, 1
  %fp = alloca ptr, align 8
  store ptr @"b", ptr %fp, align 8
  %f = load ptr, ptr %fp, align 8
  %pair = call { i32, i1 } %f(i32 %n)
  %value = extractvalue { i32, i1 } %pair, 0
  %sum = add i32 %value, 1
  %out = insertvalue { i32, i1 } %pair, i32 %sum, 0
  ret { i32, i1 } %out
}
define { i32, i1 } @"b"(i32 %p0) {
entry:
  %small = icmp eq i32 %p0, 0
  br i1 %small, label %left, label %right
left:
  br label %merge
right:
  %n = sub i32 %p0, 1
  %v = call { i32, i1 } @"a"(i32 %n)
  br label %merge
merge:
  %answer = phi { i32, i1 } [ { i32 7, i1 true }, %left ], [ %v, %right ]
  ret { i32, i1 } %answer
}
define i32 @"entry"() {
entry:
  %pair = call { i32, i1 } @"a"(i32 200000)
  %value = extractvalue { i32, i1 } %pair, 0
  %ok = icmp eq i32 %value, 100007
  %code = select i1 %ok, i32 71, i32 99
  ret i32 %code
}
"#,
            71,
        );
    }
}
