//! Machine-applicable repairs (lane 187, lever 4 of `dokumente/PLAN-EINFACHHEIT.md`).
//!
//! A diagnostic may carry a `Fix` (`gabbro_syntax::diag::Fix`): a span in the checked
//! source plus its replacement text, rendered as a `fix:` line with the span and the
//! replacement. This module holds what every fix site shares: the constructors for the recurring
//! shapes (append to a comma list, comma-aware delete) and the applier (`apply_fixes`)
//! that `gabbro pruefe --fix` and the tests drive.
//!
//! What a fix may be is decided at each refusing rule, never here: this module invents
//! no edit, it only applies the ones the diagnostics carry. A fix that weakens a
//! contract, deletes a check, or silences a refusal does not belong in a diagnostic in
//! the first place -- no applier can repair that. And no pass reads a fix back: the
//! verdicts are unchanged with or without them, so the pass register is untouched.

use gabbro_syntax::ast::{Wirkung, Wirkungen, WirkungArt};
use gabbro_syntax::diag::{Absagen, Fix};
use gabbro_syntax::span::Span;

/// Append `entry` to a brace-enclosed comma list (`effects { reads a, writes b }`).
///
/// The edit lands before the closing brace. The one exception is a lone `pure`: it is
/// contradicted by the very entry the caller names (a body that writes is not pure),
/// so the entry takes its place instead of standing beside it as a second refusal.
pub fn append_effect(list: &Wirkungen, entry: String) -> Fix {
    if list.liste.len() == 1 && matches!(list.liste[0].art, WirkungArt::Rein) {
        Fix::new(list.liste[0].span, entry)
    } else {
        Fix::insert(list.span.bis.saturating_sub(1), format!(", {entry} "))
    }
}

/// Append `item` to a bare comma list (a `requires` line, a `touches` line, a `clobbers`
/// line): `, item` at `end`, where `end` is the end offset of the last entry.
pub fn append_item(end: u32, item: String) -> Fix {
    Fix::insert(end, format!(", {item}"))
}

/// Delete entry `i` out of a comma-separated list whose entry spans are `spans`
/// (`spans.len() >= 2`). The span covers the entry plus one adjacent comma, so no stray
/// comma is left behind: the first entry takes the comma after it, any other the one
/// before it.
pub fn delete_entry(spans: &[Span], i: usize) -> Fix {
    if i == 0 {
        Fix::delete(Span::neu(spans[0].von, spans[1].von))
    } else {
        Fix::delete(Span::neu(spans[i - 1].bis, spans[i].bis))
    }
}

/// Entry spans of an effect list, in order -- the input `delete_entry` reads.
pub fn entry_spans(list: &Wirkungen) -> Vec<Span> {
    list.liste.iter().map(|e: &Wirkung| e.span).collect()
}

/// One applied edit, for the `--fix` report line.
pub struct AppliedFix {
    pub code: String,
    pub von: u32,
    pub bis: u32,
    pub replacement: String,
}

/// Apply every fix carried by `refusals` to `source`, rear to front so earlier offsets
/// stay valid. Fixes with out-of-range spans are skipped, never trusted: a span that
/// does not lie in this source belongs to another one. A span that splits a character
/// is corrupt for the same reason. Overlapping fixes keep the first in descending
/// order and skip the rest; the next `--fix` round re-reads what is left.
pub fn apply_fixes(source: &str, refusals: &Absagen) -> (String, Vec<AppliedFix>) {
    let len = source.len() as u32;
    let mut fixes: Vec<(usize, &'static str, &Fix)> = refusals
        .absagen
        .iter()
        .enumerate()
        .filter_map(|(i, a)| a.fix.as_ref().map(|f| (i, a.code, f)))
        .collect();
    // Descending by span, stable by emission order for ties: deterministic.
    fixes.sort_by(|a, b| (b.2.span.von, b.2.span.bis, a.0).cmp(&(a.2.span.von, a.2.span.bis, b.0)));
    let mut out = source.to_string();
    let mut taken: Vec<(u32, u32)> = Vec::new();
    let mut applied = Vec::new();
    for (_, code, f) in fixes {
        let (von, bis) = (f.span.von as usize, f.span.bis as usize);
        if f.span.von > f.span.bis || f.span.bis > len {
            continue;
        }
        if taken.iter().any(|(a, b)| {
            let (a, b) = (*a as usize, *b as usize);
            // A shared interior point, or the same non-empty range twice (the first
            // fix wins there). Two insertions at one offset are NOT in each other's
            // way -- both land, one after the other.
            von.max(a) < bis.min(b) || (von == a && bis == b && von != bis)
        }) {
            continue;
        }
        if !out.is_char_boundary(von) || !out.is_char_boundary(bis) {
            continue;
        }
        out.replace_range(von..bis, &f.replacement);
        taken.push((f.span.von, f.span.bis));
        applied.push(AppliedFix {
            code: code.to_string(),
            von: f.span.von,
            bis: f.span.bis,
            replacement: f.replacement.clone(),
        });
    }
    // Report order is source order.
    applied.sort_by_key(|a| (a.von, a.bis));
    (out, applied)
}

/// Run the checker over `source` and apply its fixes, up to `rounds` rounds. Returns
/// the fixed source, the refusals of the last round, and the total applied count.
/// Stops early when a round applies nothing: what is left has no fix, and re-running
/// would only re-print it.
pub fn fix_to_stable(name: &str, source: &str, rounds: usize) -> (String, Absagen, usize) {
    let mut text = source.to_string();
    let mut total = 0usize;
    for _ in 0..rounds {
        let (baum, mut absagen) = gabbro_syntax::lies(name, &text);
        crate::pruefe(&baum, &mut absagen);
        let (next, applied) = apply_fixes(&text, &absagen);
        if applied.is_empty() {
            break;
        }
        total += applied.len();
        text = next;
    }
    // The refusals returned always describe the source returned: one final check over
    // the fixed text, so a test reads what holds NOW, not what held a round ago.
    let (baum, mut absagen) = gabbro_syntax::lies(name, &text);
    crate::pruefe(&baum, &mut absagen);
    (text, absagen, total)
}
