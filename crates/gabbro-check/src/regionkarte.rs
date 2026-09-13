//! **The span map from payload positions back into the region**
//! (`PLAN-ERWEITUNG.md` §6, lane E7).
//!
//! A library call `@lib#f ( args ) { region }` carries its region as raw
//! tokens with spans (lane E1: `RawToken { text, span }`). When the region is
//! one day compiled into a payload -- and later into expanded core terms --
//! a checker refusal about element `i` of that output must point at the line
//! the user wrote, not at the call. This map is that routing: payload (or
//! expansion) position in, region token span out. It travels with the call --
//! every diagnostic about region content reports through it, never at the
//! whole-call span.

use gabbro_syntax::ast::{LibraryCall, RawToken};
use gabbro_syntax::span::Span;

/// The region tokens of one library call, as a map from payload positions.
#[derive(Debug, Clone, Copy)]
pub struct RegionKarte<'a> {
    token: &'a [RawToken],
}

impl<'a> RegionKarte<'a> {
    /// The map over this call's region.
    pub fn neu(region: &'a [RawToken]) -> RegionKarte<'a> {
        RegionKarte { token: region }
    }

    /// The map over this call's region, taken from the call itself.
    pub fn vom_ruf(ruf: &'a LibraryCall) -> RegionKarte<'a> {
        RegionKarte::neu(&ruf.region)
    }

    /// The site of the first region token -- where a diagnostic about the
    /// region as a whole points (`N069` names it in its note).
    pub fn erste(&self) -> Option<Span> {
        self.token.first().map(|t| t.span)
    }

    /// Payload (or expansion) element `i` back to its region token.
    ///
    /// Positions run in token order, so element `i` belongs to token `i`;
    /// an index past the end clamps to the last token instead of falling
    /// off the region -- a wrong index is still a statement about the
    /// region, never about the call around it. An empty region maps
    /// nothing: there is no user line to point at.
    pub fn fuer(&self, nutzlast_index: usize) -> Option<Span> {
        if self.token.is_empty() {
            return None;
        }
        self.token.get(nutzlast_index.min(self.token.len() - 1)).map(|t| t.span)
    }

    /// The reporting span for a diagnostic about this call's region: the
    /// first region token where there is one, the whole-call span where
    /// the region is empty (an empty region has no line of its own).
    pub fn ruf_span(&self, ruf: &LibraryCall) -> Span {
        self.erste().unwrap_or(ruf.span)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn token(text: &str, von: u32, bis: u32) -> RawToken {
        RawToken {
            text: text.to_string(),
            span: Span::neu(von, bis),
        }
    }

    #[test]
    fn payload_index_maps_to_its_token_in_order() {
        let region = vec![token("dispatch", 10, 18), token("0", 19, 20)];
        let karte = RegionKarte::neu(&region);
        assert_eq!(karte.fuer(0), Some(Span::neu(10, 18)));
        assert_eq!(karte.fuer(1), Some(Span::neu(19, 20)));
    }

    #[test]
    fn payload_index_past_the_end_clamps_to_the_last_token() {
        // A wrong index is still a statement about the region, never about
        // the call around it: it stays on the last token.
        let region = vec![token("dispatch", 10, 18), token("0", 19, 20)];
        let karte = RegionKarte::neu(&region);
        assert_eq!(karte.fuer(7), Some(Span::neu(19, 20)));
    }

    #[test]
    fn empty_region_maps_nothing() {
        let region: Vec<RawToken> = Vec::new();
        let karte = RegionKarte::neu(&region);
        assert_eq!(karte.erste(), None);
        assert_eq!(karte.fuer(0), None);
    }
}
