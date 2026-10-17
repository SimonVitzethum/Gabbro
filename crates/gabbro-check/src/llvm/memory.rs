//! Page reclamation beneath the unchanged ArenaDyn free-slot semantics.
//! Links live outside payloads, so a fully dead chunk can be discarded without
//! losing reusable indices or requiring a minimum element size.
use super::*;

pub(super) fn chunk_slots(a: &ArenaInfo) -> u64 {
    (1048576 / arena_breite(a)).max(1)
}
pub(super) fn metadata_size(a: &ArenaInfo) -> Option<u64> {
    a.max
        .checked_add(a.max.div_ceil(chunk_slots(a)))?
        .checked_mul(8)
}

pub(super) fn meta_cell(k: &mut Koerper, name: &str, index: &str, count: bool) -> String {
    let a = k.s.arenen[name].clone();
    let raw = k.tmp();
    k.zeile(&format!(
        "{raw} = load i64, ptr {}, align 8",
        gteil(name, "meta")
    ));
    let base = k.tmp();
    k.zeile(&format!("{base} = inttoptr i64 {raw} to ptr"));
    let offset = if count {
        let chunk = k.tmp();
        k.zeile(&format!("{chunk} = udiv i64 {index}, {}", chunk_slots(&a)));
        let offset = k.tmp();
        k.zeile(&format!("{offset} = add i64 {chunk}, {}", a.max));
        offset
    } else {
        index.into()
    };
    let p = k.tmp();
    k.zeile(&format!(
        "{p} = getelementptr i64, ptr {base}, i64 {offset}"
    ));
    p
}

pub(super) fn live_change(k: &mut Koerper, name: &str, index: &str, allocate: bool, span: Span) {
    let a = k.s.arenen[name].clone();
    let p = meta_cell(k, name, index, true);
    let old = k.tmp();
    let new = k.tmp();
    k.zeile(&format!("{old} = load i64, ptr {p}, align 8"));
    k.zeile(&format!(
        "{new} = {} i64 {old}, 1",
        if allocate { "add" } else { "sub" }
    ));
    k.zeile(&format!("store i64 {new}, ptr {p}, align 8"));
    if allocate {
        return;
    }
    let empty = k.tmp();
    k.zeile(&format!("{empty} = icmp eq i64 {new}, 0"));
    let reclaim = k.block("arena_reclaim");
    let done = k.block("arena_reclaimed");
    k.zeile(&format!("br i1 {empty}, label %{reclaim}, label %{done}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{reclaim}:");
    k.beendet = false;
    let chunk = k.tmp();
    k.zeile(&format!("{chunk} = udiv i64 {index}, {}", chunk_slots(&a)));
    let first = k.tmp();
    k.zeile(&format!("{first} = mul i64 {chunk}, {}", chunk_slots(&a)));
    let remaining = k.tmp();
    k.zeile(&format!("{remaining} = sub i64 {}, {first}", a.max));
    let full = k.tmp();
    k.zeile(&format!(
        "{full} = icmp ugt i64 {remaining}, {}",
        chunk_slots(&a)
    ));
    let slots = k.tmp();
    k.zeile(&format!(
        "{slots} = select i1 {full}, i64 {}, i64 {remaining}",
        chunk_slots(&a)
    ));
    let bytes = k.tmp();
    k.zeile(&format!("{bytes} = mul i64 {slots}, {}", arena_breite(&a)));
    let Some(addr) = arena_zelle(k, name, &first) else {
        return;
    };
    discard(k, &addr, &bytes, span);
    k.zeile(&format!("br label %{done}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{done}:");
    k.beendet = false;
}

fn binding(k: &Koerper, name: &str) -> Option<(String, FnSig)> {
    let candidates: BTreeMap<_, _> =
        k.s.plaene
            .keys()
            .filter(|full| full.rsplit("::").next() == Some(name))
            .filter_map(|full| Some((k.s.emitnamen.get(full)?.clone(), k.s.fns.get(full)?.clone())))
            .collect();
    if candidates.len() == 1 {
        candidates.into_iter().next()
    } else {
        None
    }
}

fn return_static_pages(k: &mut Koerper, address: &str, bytes: &str, span: Span) {
    let (Some((page_fn, page_sig)), Some((give_fn, give_sig))) = (
        binding(k, "gabbro_os_seitengroesse"),
        binding(k, "gabbro_os_seiten_zurueck"),
    ) else {
        return;
    };
    if !page_sig.params.is_empty()
        || page_sig.ret.as_ref().map(|x| &x.0) != Some(&LlTyp::Int(64))
        || give_sig.params.iter().map(|x| &x.0).collect::<Vec<_>>()
            != vec![&LlTyp::Ptr, &LlTyp::Int(64)]
        || give_sig.ret.as_ref().map(|x| &x.0) != Some(&LlTyp::Int(32))
    {
        weigere(
            k.s,
            "Y103",
            span,
            "page-return binding has an incompatible ABI".into(),
        );
        return;
    }
    let page = k.tmp();
    k.zeile(&format!("{page} = call i64 {}()", gname(&page_fn)));
    let nonzero = k.tmp();
    let bounded = k.tmp();
    let page_ok = k.tmp();
    k.zeile(&format!("{nonzero} = icmp ne i64 {page}, 0"));
    k.zeile(&format!("{bounded} = icmp ule i64 {page}, 4294967296"));
    k.zeile(&format!("{page_ok} = and i1 {nonzero}, {bounded}"));
    let check = k.block("range_page_check");
    let done = k.block("range_page_done");
    k.zeile(&format!("br i1 {page_ok}, label %{check}, label %{done}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{check}:");
    k.beendet = false;
    let raw = k.tmp();
    k.zeile(&format!("{raw} = ptrtoint ptr {address} to i64"));
    let limit0 = k.tmp();
    let limit = k.tmp();
    let safe = k.tmp();
    k.zeile(&format!("{limit0} = sub i64 -1, {bytes}"));
    k.zeile(&format!("{limit} = sub i64 {limit0}, {page}"));
    k.zeile(&format!("{safe} = icmp ule i64 {raw}, {limit}"));
    let round = k.block("range_page_round");
    k.zeile(&format!("br i1 {safe}, label %{round}, label %{done}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{round}:");
    k.beendet = false;
    let plus = k.tmp();
    let before = k.tmp();
    let low_units = k.tmp();
    let lo = k.tmp();
    k.zeile(&format!("{plus} = add i64 {raw}, {page}"));
    k.zeile(&format!("{before} = sub i64 {plus}, 1"));
    k.zeile(&format!("{low_units} = udiv i64 {before}, {page}"));
    k.zeile(&format!("{lo} = mul i64 {low_units}, {page}"));
    let end = k.tmp();
    let high_units = k.tmp();
    let hi = k.tmp();
    let whole = k.tmp();
    k.zeile(&format!("{end} = add i64 {raw}, {bytes}"));
    k.zeile(&format!("{high_units} = udiv i64 {end}, {page}"));
    k.zeile(&format!("{hi} = mul i64 {high_units}, {page}"));
    k.zeile(&format!("{whole} = icmp ult i64 {lo}, {hi}"));
    let give = k.block("range_page_return");
    k.zeile(&format!("br i1 {whole}, label %{give}, label %{done}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{give}:");
    k.beendet = false;
    let length = k.tmp();
    let ptr = k.tmp();
    let rc = k.tmp();
    k.zeile(&format!("{length} = sub i64 {hi}, {lo}"));
    k.zeile(&format!("{ptr} = inttoptr i64 {lo} to ptr"));
    k.zeile(&format!(
        "{rc} = call i32 {}(ptr {ptr}, i64 {length})",
        gname(&give_fn)
    ));
    k.zeile(&format!("br label %{done}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{done}:");
    k.beendet = false;
}

/// Discard only whole 64 KiB-aligned interior pages of an anonymous mapping.
/// This granule is compatible with the supported Linux 4/16/64 KiB pages.
/// Failure preserves the payload and therefore needs no logical rollback.
pub(super) fn discard(k: &mut Koerper, addr: &str, bytes: &str, span: Span) {
    let raw = k.tmp();
    k.zeile(&format!("{raw} = ptrtoint ptr {addr} to i64"));
    let limit = k.tmp();
    let safe = k.tmp();
    k.zeile(&format!("{limit} = sub i64 -65536, {bytes}"));
    k.zeile(&format!("{safe} = icmp ule i64 {raw}, {limit}"));
    let round = k.block("memory_discard_round");
    let done = k.block("memory_discarded");
    k.zeile(&format!("br i1 {safe}, label %{round}, label %{done}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{round}:");
    k.beendet = false;
    let rounded = k.tmp();
    k.zeile(&format!("{rounded} = add i64 {raw}, 65535"));
    let lo = k.tmp();
    k.zeile(&format!("{lo} = and i64 {rounded}, -65536"));
    let end = k.tmp();
    k.zeile(&format!("{end} = add i64 {raw}, {bytes}"));
    let hi = k.tmp();
    k.zeile(&format!("{hi} = and i64 {end}, -65536"));
    let pages = k.tmp();
    k.zeile(&format!("{pages} = icmp ult i64 {lo}, {hi}"));
    let yes = k.block("memory_discard");
    k.zeile(&format!("br i1 {pages}, label %{yes}, label %{done}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{yes}:");
    k.beendet = false;
    let len = k.tmp();
    k.zeile(&format!("{len} = sub i64 {hi}, {lo}"));
    let args = runtime_args(k.s.ziel, &[lo, len, "4".into()]);
    let _ = laufzeit_ruf(k, "madvise", &args, span);
    k.zeile(&format!("br label %{done}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{done}:");
    k.beendet = false;
}

pub(super) fn reset(k: &mut Koerper, name: &str, span: Span) {
    let a = k.s.arenen[name].clone();
    let used = k.tmp();
    k.zeile(&format!(
        "{used} = load i64, ptr {}, align 8",
        gteil(name, "belegt")
    ));
    let idx = k.alloca("i64");
    k.zeile(&format!("store i64 0, ptr {idx}, align 8"));
    let count = k.tmp();
    k.zeile(&format!(
        "{count} = add i64 {used}, {}",
        chunk_slots(&a) - 1
    ));
    let chunks = k.tmp();
    k.zeile(&format!("{chunks} = udiv i64 {count}, {}", chunk_slots(&a)));
    let head = k.block("arena_reset_counts");
    let body = k.block("arena_reset_count");
    let done = k.block("arena_reset_done");
    k.zeile(&format!("br label %{head}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{head}:");
    k.beendet = false;
    let i = k.tmp();
    k.zeile(&format!("{i} = load i64, ptr {idx}, align 8"));
    let more = k.tmp();
    k.zeile(&format!("{more} = icmp ult i64 {i}, {chunks}"));
    k.zeile(&format!("br i1 {more}, label %{body}, label %{done}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{body}:");
    k.beendet = false;
    let slot = k.tmp();
    k.zeile(&format!("{slot} = mul i64 {i}, {}", chunk_slots(&a)));
    let p = meta_cell(k, name, &slot, true);
    k.zeile(&format!("store i64 0, ptr {p}, align 8"));
    let next = k.tmp();
    k.zeile(&format!("{next} = add i64 {i}, 1"));
    k.zeile(&format!("store i64 {next}, ptr {idx}, align 8"));
    k.zeile(&format!("br label %{head}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{done}:");
    k.beendet = false;
    // No allocation means no mapping; zero-length discard must not touch it.
    let bytes = k.tmp();
    k.zeile(&format!("{bytes} = mul i64 {used}, {}", arena_breite(&a)));
    if let Some(addr) = arena_zelle(k, name, "0") {
        discard(k, &addr, &bytes, span);
    }
    k.zeile(&format!(
        "store i64 0, ptr {}, align 8",
        gteil(name, "belegt")
    ));
    k.zeile(&format!(
        "store i64 -1, ptr {}, align 8",
        gteil(name, "frei")
    ));
}

/// Static range reset follows the model's zeroing rule. Page return is an
/// optional program binding, never an assumption about file-backed statics.
pub(super) fn reset_range(k: &mut Koerper, r: &ResetSlotStmt, span: Span) {
    let Some(g) = k.s.globale.get(&r.tisch.text).cloned() else {
        weigere(
            k.s,
            "Y103",
            span,
            "range reset without a static array".into(),
        );
        return;
    };
    let LlTyp::Feld(elem, len) = &g.typ else {
        weigere(k.s, "Y103", span, "range reset of a non-array".into());
        return;
    };
    let Some(width) = groesse_von_ll(k.s, elem) else {
        weigere(
            k.s,
            "Y103",
            span,
            "range reset with unknown element layout".into(),
        );
        return;
    };
    if len
        .checked_mul(width)
        .is_none_or(|bytes| bytes > i64::MAX as u64)
    {
        weigere(
            k.s,
            "Y103",
            span,
            "range reset exceeds the addressable extent".into(),
        );
        return;
    }
    let Some(index) =
        senke_expr(k, &r.index).and_then(|v| angleiche(k, v, &LlTyp::Int(64), Zeichen::U))
    else {
        return;
    };
    let Some(count) =
        senke_expr(k, &r.menge).and_then(|v| angleiche(k, v, &LlTyp::Int(64), Zeichen::U))
    else {
        return;
    };
    let within = k.tmp();
    let room = k.tmp();
    let fits = k.tmp();
    let valid = k.tmp();
    k.zeile(&format!("{within} = icmp ule i64 {}, {len}", count.text));
    k.zeile(&format!("{room} = sub i64 {len}, {}", count.text));
    k.zeile(&format!("{fits} = icmp ule i64 {}, {room}", index.text));
    k.zeile(&format!("{valid} = and i1 {within}, {fits}"));
    let ok = k.block("range_valid");
    let fail = k.block("range_invalid");
    k.zeile(&format!("br i1 {valid}, label %{ok}, label %{fail}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{fail}:");
    k.beendet = false;
    falle(k);
    let _ = writeln!(k.text, "{ok}:");
    k.beendet = false;
    let address = k.tmp();
    k.zeile(&format!(
        "{address} = getelementptr {}, ptr {}, i32 0, i64 {}",
        g.typ.text(),
        gname(&r.tisch.text),
        index.text
    ));
    let bytes = k.tmp();
    k.zeile(&format!("{bytes} = mul i64 {}, {width}", count.text));
    let cursor = k.alloca("i64");
    k.zeile(&format!("store i64 0, ptr {cursor}, align 8"));
    let head = k.block("range_zero");
    let body = k.block("range_byte");
    let done = k.block("range_done");
    k.zeile(&format!("br label %{head}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{head}:");
    k.beendet = false;
    let i = k.tmp();
    k.zeile(&format!("{i} = load i64, ptr {cursor}, align 8"));
    let more = k.tmp();
    k.zeile(&format!("{more} = icmp ult i64 {i}, {bytes}"));
    k.zeile(&format!("br i1 {more}, label %{body}, label %{done}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{body}:");
    k.beendet = false;
    let p = k.tmp();
    k.zeile(&format!("{p} = getelementptr i8, ptr {address}, i64 {i}"));
    // Volatile prevents introducing an unresolved libc memset in a no-libc binary.
    k.zeile(&format!("store volatile i8 0, ptr {p}, align 1"));
    let next = k.tmp();
    k.zeile(&format!("{next} = add i64 {i}, 1"));
    k.zeile(&format!("store i64 {next}, ptr {cursor}, align 8"));
    k.zeile(&format!("br label %{head}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{done}:");
    k.beendet = false;
    return_static_pages(k, &address, &bytes, span);
}

#[cfg(test)]
mod tests {
    use super::super::test_tools::source;

    #[test]
    fn whole_thread_groups_run_before_join_and_repeat_with_fresh_storage() {
        let program = r#"module threads {
pub static mut Z : u32 = 0;
pub table T count 128 { slot { tick : bool, } }
pub lock L protects { Z } rank 0 held <= 8 ops;
extern fn rendezvous() effects { pure } costs <= 4 ops;
impl fn worker() effects { reads Z, writes Z, locks L } costs <= 64 ops {
    rendezvous();
    locks L { Z = Z +% 1; }
}
impl fn other() effects { reads Z, writes Z, locks L } costs <= 128 ops { worker(); }
impl fn group() effects { reads Z, writes Z, locks L } costs <= 512 ops {
    start { worker, other };
}
pub fn main() -> u32 effects { reads Z, writes Z, locks L, reads T, reads T.slots } costs <= 131072 ops {
    traverse i over slots of T by unvisited
        touches reads T, reads T.slots, reads Z, writes Z, locks L
    { group(); }
    locks L {
        if Z == 256 { return 73; }
        return 99;
    }
}
}"#;
        super::super::test_tools::source_with("thread-groups", program, 73, |ir, _| {
            let ir = ir.replace("declare void @\"rendezvous\"()", "");
            // A barrier makes sequential spawn/join deadlock. The next pair
            // advances to the next even ticket, testing repeated groups too.
            format!(
                r#"{ir}
@test_barrier = global i32 0, align 4
define void @"rendezvous"() {{
entry:
  %old = atomicrmw add ptr @test_barrier, i32 1 seq_cst, align 4
  %pair = udiv i32 %old, 2
  %next = add i32 %pair, 1
  %threshold = mul i32 %next, 2
  br label %wait
wait:
  %value = load atomic i32, ptr @test_barrier seq_cst, align 4
  %ready = icmp uge i32 %value, %threshold
  br i1 %ready, label %done, label %wait
done:
  ret void
}}
"#
            )
        });
    }

    #[test]
    fn empty_payload_pages_are_discarded_without_losing_free_links() {
        let source = r#"module reclaim {
pub arena A capacity 0 .. 131072 of u64;
extern fn touch() effects { writes A } costs <= 4 ops;
extern fn probe() -> u32 effects { reads A } costs <= 4 ops;
pub fn main() -> u64 effects { reads A, writes A } costs <= 512 ops {
    let a = alloc A (7) else { return 1; };
    touch();
    if probe() != 91 { return 2; }
    free A[a];
    if probe() != 0 { return 3; }
    let b = alloc A (100) else { return 4; };
    return A[b];
}
}"#;
        for target in [&super::super::ZIEL_X86_64, &super::super::ZIEL_AARCH64] {
            let (ast, mut diagnostics) = gabbro_syntax::lies("reclaim", source);
            crate::pruefe(&ast, &mut diagnostics);
            let ir = super::super::emittiere_llvm(
                &ast,
                &mut diagnostics,
                crate::gatter::Bau::Auslieferung,
                target,
            );
            assert_eq!(
                diagnostics.fehler_zahl(),
                0,
                "{}",
                diagnostics.zeige(source)
            );
            // Foreign test instrumentation observes an otherwise dead payload
            // page. It is deliberately outside the source-language API.
            let ir = ir
                .replace("declare void @\"touch\"()", "")
                .replace("declare i32 @\"probe\"()", "");
            let instrumented = format!(
                r#"{ir}
define void @"touch"() {{
entry:
  %raw = load i64, ptr @"A.basis", align 8
  %address = add i64 %raw, 131072
  %ptr = inttoptr i64 %address to ptr
  store volatile i8 91, ptr %ptr, align 1
  ret void
}}
define i32 @"probe"() {{
entry:
  %raw = load i64, ptr @"A.basis", align 8
  %address = add i64 %raw, 131072
  %ptr = inttoptr i64 %address to ptr
  %byte = load volatile i8, ptr %ptr, align 1
  %value = zext i8 %byte to i32
  ret i32 %value
}}
"#
            );
            super::super::test_tools::run("reclaim-pages", target, &instrumented, 100);
        }
    }

    #[test]
    fn compiled_non_tail_source_uses_continuations() {
        source(
            "source-recursion",
            r#"module recursion {
impl fn count(n : u32 in 0 .. 200000) -> u32 costs <= 64 ops decreases n {
    if n == 0 { return 0; }
    let child : u32 = count(n - 1);
    return child +% 1;
}
pub fn main() -> u32 costs <= 128 ops {
    let value = count(200000);
    if value == 200000 { return 73; }
    return 99;
}
}"#,
            73,
        );
    }

    #[test]
    fn recursive_error_channels_unwind_without_native_calls() {
        source(
            "recursive-channel",
            r#"module channel {
reason R { Stop = 1 "stopped" exhaustive }
impl fn descend(n : u32 in 0 .. 200000) -> u32 or R
    costs <= 64 ops decreases n
{
    if n == 0 { return R::Stop; }
    let child = descend(n - 1) else (e) { return e; }
    return child;
}
pub fn main() -> u32 costs <= 128 ops {
    let value = descend(200000) else (e) { return 77; }
    return 99;
}
}"#,
            77,
        );
    }

    #[test]
    fn one_byte_slots_reuse_the_same_index_without_corrupting_neighbours() {
        source(
            "small-slot-reuse",
            r#"module slots {
pub arena A capacity 0 .. 4 of u8;
pub fn main() -> u32 effects { reads A, writes A } costs <= 512 ops {
    let a = alloc A (7) else { return 1; };
    let b = alloc A (35) else { return 2; };
    free A[a];
    let c = alloc A (100) else { return 3; };
    let x : u32 = A[c];
    let y : u32 = A[b];
    reset A;
    let d = alloc A (17) else { return 4; };
    let z : u32 = A[d];
    return x + y + z;
}
}"#,
            152,
        );
    }

    #[test]
    fn static_range_zeroing_preserves_both_neighbours_and_nonzero_initial_data() {
        source(
            "range-reset",
            r#"module range {
pub static mut B : [u8; 8192] = 0 aligned 4096;
pub fn main() -> u32 effects { reads B, writes B } costs <= 10000 ops {
    B[0] = 7;
    B[8191] = 13;
    B[5000] = 19;
    B[199] = 9;
    reset B at 4096 count 4095;
    reset B at 200 count 100;
    let a : u32 = B[0];
    let b : u32 = B[8191];
    let c : u32 = B[5000];
    let d : u32 = B[200];
    let e : u32 = B[199];
    return a + b + c + d + e;
}
}"#,
            29,
        );
    }
}
