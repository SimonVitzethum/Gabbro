//! Bounded-string length discipline (lane 256): specified, not wired.
//!
//! A bounded string carries its declared maximum the way `u32` carries
//! `in 0 .. N`. Lengths are tracked like M101-family bounds: a literal
//! has a known length, `concat` adds lengths and refuses past the
//! target max, indexing is in-range or refused. Unbounded strings stay
//! refused by name (no constructor here takes no max).
//!
//! These are pure functions over lengths, mirroring
//! `grammatik/Grammatik/ZeichenfolgeGebunden.lean`
//! (`BString`, `bliteral`, `bconcat`, `bindex`). No parser, checker
//! pass, or emitter calls them yet; wiring them to syntax is open work
//! (see MUSE-REPORT-256.md). What this module pins down is the
//! arithmetic the future rule must implement, with both directions
//! tested below.

/// A literal fits exactly when its known length fits the declared max.
pub fn literal_passt(max: usize, len: usize) -> bool {
    len <= max
}

/// `concat` fits exactly when the length sum fits the target max.
/// `None` is the refusal (overflow of the sum, or past the max).
pub fn concat_passt(ziel_max: usize, a_len: usize, b_len: usize) -> Option<usize> {
    let summe = a_len.checked_add(b_len)?;
    if summe <= ziel_max {
        Some(summe)
    } else {
        None
    }
}

/// Bounded indexing: in-range or refused.
pub fn index_passt(len: usize, i: usize) -> bool {
    i < len
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn literal_in_max_wird_angenommen() {
        assert!(literal_passt(8, 2));
        assert!(literal_passt(8, 8));
    }

    #[test]
    fn literal_ueber_max_wird_verweigert() {
        assert!(!literal_passt(8, 9));
    }

    #[test]
    fn concat_in_max_meldet_summe() {
        assert_eq!(concat_passt(8, 2, 1), Some(3));
        assert_eq!(concat_passt(8, 4, 4), Some(8));
    }

    #[test]
    fn concat_ueber_max_wird_verweigert() {
        assert_eq!(concat_passt(8, 5, 4), None);
        assert_eq!(concat_passt(2, 2, 1), None);
    }

    #[test]
    fn concat_summenueberlauf_wird_verweigert() {
        assert_eq!(concat_passt(usize::MAX, usize::MAX, 1), None);
    }

    #[test]
    fn index_innen_wird_angenommen_aussen_verweigert() {
        assert!(index_passt(3, 0));
        assert!(index_passt(3, 2));
        assert!(!index_passt(3, 3));
        assert!(!index_passt(0, 0));
    }
}
