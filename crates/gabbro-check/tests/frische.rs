//! Freshness across aliased table handles (task 5d): carriers key by
//! TABLE, so a write through any handle expires every taint of that
//! table -- and nothing of another table.

use gabbro_syntax::diag::Stufe;

fn fehler(quelle: &str) -> Vec<String> {
    let (baum, mut absagen) = gabbro_syntax::lies("frische", quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect()
}

fn sauber(quelle: &str) {
    let f = fehler(quelle);
    assert!(f.is_empty(), "expected 0 errors, got {f:?} for:\n{quelle}");
}

fn faellt(quelle: &str, code: &str) {
    let f = fehler(quelle);
    assert!(
        f.iter().any(|c| c == code),
        "expected {code}, got {f:?} for:\n{quelle}"
    );
}

fn tabelle() -> &'static str {
    "table T count 4 {
    slot {
        x : u32,
    }
}
"
}

#[test]
fn zweiter_griff_gleicher_tabelle_faellt() {
    faellt(
        &format!(
            "module frisch {{
{tabelle}impl fn f(t : ptr<normal, rw> T, u : ptr<normal, rw> T, i : index into T) -> u32
    effects {{ reads t.slots, writes u.slots }}
    costs <= 64 ops
{{
    let v : u32 = t.slots[i].x;
    u.slots[i].x = 1;
    if v == 0 {{ return 1; }}
    return 0;
}}
}}",
            tabelle = tabelle()
        ),
        "M147",
    );
}

#[test]
fn schreiben_durch_zweiten_griff_faellt() {
    faellt(
        &format!(
            "module frisch {{
{tabelle}impl fn schreibe(u : ptr<normal, rw> T, i : index into T)
    effects {{ writes u.slots }}
    costs <= 16 ops
{{
    u.slots[i].x = 1;
}}
impl fn f(t : ptr<normal, rw> T, u : ptr<normal, rw> T, i : index into T) -> u32
    effects {{ reads t.slots, writes u.slots }}
    costs <= 64 ops
{{
    let v : u32 = t.slots[i].x;
    schreibe(u, i);
    if v == 0 {{ return 1; }}
    return 0;
}}
}}",
            tabelle = tabelle()
        ),
        "M147",
    );
}

#[test]
fn andere_tabelle_bleibt_frisch() {
    sauber(
        "module frisch {
table A count 4 {
    slot {
        x : u32,
    }
}
table B count 4 {
    slot {
        x : u32,
    }
}
impl fn f(t : ptr<normal, rw> A, u : ptr<normal, rw> B, i : index into A, j : index into B) -> u32
    effects { reads t.slots, writes u.slots }
    costs <= 64 ops
{
    let v : u32 = t.slots[i].x;
    u.slots[j].x = 1;
    if v == 0 { return 1; }
    return 0;
}
}",
    );
}

#[test]
fn neulesung_nach_schreiben_bleibt_frisch() {
    sauber(
        "module frisch {
table A count 4 {
    slot {
        x : u32,
    }
}
impl fn f(t : ptr<normal, rw> A, i : index into A) -> u32
    effects { reads t.slots, writes t.slots }
    costs <= 64 ops
{
    let v : u32 = t.slots[i].x;
    t.slots[i].x = v;
    let w : u32 = t.slots[i].x;
    if w == 0 { return 1; }
    return w;
}
}",
    );
}
