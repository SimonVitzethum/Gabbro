
### Flat record embedding

A record body may contain `..Name`, for example
`type Body = { ..Pos, mass: f64, };`. Embedded fields precede the record's
own fields, preserving embedding order and each embedded record's field order.
Their types and field metadata are retained. Literals and field access use the
resulting flat field names; embedding introduces no conversion or subtyping.
Duplicate field names, non-record targets and recursive embeddings are refused
with named `record embedding` errors. Existing restrictions on field metadata
remain enforced by the record exporter after expansion.
