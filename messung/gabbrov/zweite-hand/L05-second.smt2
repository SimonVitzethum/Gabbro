(set-option :produce-models true)
(set-option :timeout 60000)

; ===========================================================================
;  L05 -- "the CDT stays well-formed"
;
;  VC:  cdt_wohlgeformt(pre)  AND  unlink's body ran  ==>  cdt_wohlgeformt(post)
;
;  CONVENTION: premises + body + NEGATED post-goal are asserted.
;    unsat   => L05 HOLDS (passed)
;    sat     => L05 REFUTED, model = counterexample
;    unknown => undecided
;
;  PREMISES USED (and nothing else -- the fragment DECLARES each of these):
;    P1  cdt_wohlgeformt(c) in the pre-state       (`maintains cdt_wohlgeformt`)
;    P2  c.slots[s].used                           (`requires ... c.slots[s].used`)
;    P3  the plumbing range fact: an `option index into CapSpace` that is
;        Some(k) satisfies 0 <= k < N; and s : SlotIdx is in range too.
;  DELIBERATELY NOT ASSUMED (the source comments say the language could not
;  state them -- «B14» mutual sibling chain, «B13» refcount, and there is no
;  acyclicity declaration anywhere):
;    -- no acyclicity of `parent`
;    -- no `slots[s.next_sibling].prev_sibling == s` mutual sibling chain
;    -- no relation between `used` and any option field
; ===========================================================================

; ------------------------------ prelude ------------------------------------
(declare-datatype Value
  ((vint (ival Int)) (vbool (bval Bool)) (vabsent) (vpresent (pidx Int))))
(declare-datatype Fld
  ((F_used) (F_gen) (F_object) (F_rights) (F_badge)
   (F_parent) (F_first_child) (F_next_sibling) (F_prev_sibling)))
(declare-datatype Place ((mkslot (sidx Int) (sfld Fld))))
(define-sort World () (Array Place Value))
(define-fun par ((w World) (i Int)) Value (select w (mkslot i F_parent)))

; reachesIn, unrolled.  BOUND = 6.
(define-fun rch0 ((w World) (s Int) (t Int)) Bool (= s t))
(define-fun rch1 ((w World) (s Int) (t Int)) Bool
  (ite (= s t) true (let ((v (par w s))) (and ((_ is vpresent) v) (rch0 w (pidx v) t)))))
(define-fun rch2 ((w World) (s Int) (t Int)) Bool
  (ite (= s t) true (let ((v (par w s))) (and ((_ is vpresent) v) (rch1 w (pidx v) t)))))
(define-fun rch3 ((w World) (s Int) (t Int)) Bool
  (ite (= s t) true (let ((v (par w s))) (and ((_ is vpresent) v) (rch2 w (pidx v) t)))))
(define-fun rch4 ((w World) (s Int) (t Int)) Bool
  (ite (= s t) true (let ((v (par w s))) (and ((_ is vpresent) v) (rch3 w (pidx v) t)))))
(define-fun rch5 ((w World) (s Int) (t Int)) Bool
  (ite (= s t) true (let ((v (par w s))) (and ((_ is vpresent) v) (rch4 w (pidx v) t)))))
(define-fun rch6 ((w World) (s Int) (t Int)) Bool
  (ite (= s t) true (let ((v (par w s))) (and ((_ is vpresent) v) (rch5 w (pidx v) t)))))

(define-fun ROOT () Int 0)   ; `const WURZEL : u32 = 0;`

; --------------------------- the table domain ------------------------------
; `forall s in slots of c` -- the WHOLE table, every declared slot index.  The
; source writes no `used` guard, and N is `table ... count N`.  N is pinned to
; 4 so the whole VC stays quantifier-free and therefore DECIDABLE; 4 is the
; smallest N that is not degenerate (a 1-slot table has only the root in it).
(define-fun N () Int 4)
(define-fun cdtWf ((w World)) Bool
  (and (rch6 w 0 ROOT) (rch6 w 1 ROOT) (rch6 w 2 ROOT) (rch6 w 3 ROOT)))

; P3 -- the plumbing range fact, on every option field of every slot, PLUS the
; plumbing well-typedness of an `option index into CapSpace` (it is absent or
; present and nothing else).  Both are pure plumbing; asserting them only makes
; the premise set STRONGER, so a `sat` here is a stronger refutation.
(define-fun rangeok ((w World) (i Int) (f Fld)) Bool
  (let ((v (select w (mkslot i f))))
    (or ((_ is vabsent) v)
        (and ((_ is vpresent) v) (<= 0 (pidx v)) (< (pidx v) N)))))

; ------------------------------- the states --------------------------------
(declare-const w0 World)   ; the pre-state world
(declare-const x  Int)     ; the argument `s : SlotIdx` of `unlink`

(assert (and (<= 0 x) (< x N)))                       ; P3, for the argument
(assert (and (rangeok w0 0 F_parent) (rangeok w0 0 F_first_child)
             (rangeok w0 0 F_next_sibling) (rangeok w0 0 F_prev_sibling)
             (rangeok w0 1 F_parent) (rangeok w0 1 F_first_child)
             (rangeok w0 1 F_next_sibling) (rangeok w0 1 F_prev_sibling)
             (rangeok w0 2 F_parent) (rangeok w0 2 F_first_child)
             (rangeok w0 2 F_next_sibling) (rangeok w0 2 F_prev_sibling)
             (rangeok w0 3 F_parent) (rangeok w0 3 F_first_child)
             (rangeok w0 3 F_next_sibling) (rangeok w0 3 F_prev_sibling)))

(assert (= (select w0 (mkslot x F_used)) (vbool true)))   ; P2 `requires`
(assert (cdtWf w0))                                       ; P1 `maintains`, pre

; ------------------------- the body of `unlink` ----------------------------
;   match c.slots[s].prev_sibling {
;     Some(p) => { c.slots[p].next_sibling = c.slots[s].next_sibling; }
;     None    => { match c.slots[s].parent {
;                    Some(par) => { c.slots[par].first_child = c.slots[s].next_sibling; }
;                    None      => { } } }
;   }
(define-fun ps0 () Value (select w0 (mkslot x F_prev_sibling)))
(define-fun pa0 () Value (select w0 (mkslot x F_parent)))
(define-fun ns0 () Value (select w0 (mkslot x F_next_sibling)))
(define-fun w1 () World
  (ite ((_ is vpresent) ps0)
       (store w0 (mkslot (pidx ps0) F_next_sibling) ns0)
       (ite ((_ is vpresent) pa0)
            (store w0 (mkslot (pidx pa0) F_first_child) ns0)
            w0)))

;   match c.slots[s].next_sibling {
;     Some(n) => { c.slots[n].prev_sibling = c.slots[s].prev_sibling; }
;     None    => { } }
;   (both reads are of the CURRENT state, i.e. of w1 -- the first match may
;    have written into slot x itself when p == x.)
(define-fun ns1 () Value (select w1 (mkslot x F_next_sibling)))
(define-fun ps1 () Value (select w1 (mkslot x F_prev_sibling)))
(define-fun w2 () World
  (ite ((_ is vpresent) ns1)
       (store w1 (mkslot (pidx ns1) F_prev_sibling) ps1)
       w1))

;   c.slots[s].parent       = None;
;   c.slots[s].first_child  = None;
;   c.slots[s].next_sibling = None;
;   c.slots[s].prev_sibling = None;
(define-fun w3 () World (store w2 (mkslot x F_parent)       vabsent))
(define-fun w4 () World (store w3 (mkslot x F_first_child)  vabsent))
(define-fun w5 () World (store w4 (mkslot x F_next_sibling) vabsent))
(define-fun w6 () World (store w5 (mkslot x F_prev_sibling) vabsent))

; ------------------------ the NEGATED post-goal ----------------------------
(assert (not (cdtWf w6)))

(check-sat)
(get-model)
(echo "--- witness readout ---")
(get-value (x))
(get-value ((par w0 0) (par w0 1) (par w0 2) (par w0 3)))
(get-value ((par w6 0) (par w6 1) (par w6 2) (par w6 3)))
(get-value ((rch6 w0 0 ROOT) (rch6 w0 1 ROOT) (rch6 w0 2 ROOT) (rch6 w0 3 ROOT)))
(get-value ((rch6 w6 0 ROOT) (rch6 w6 1 ROOT) (rch6 w6 2 ROOT) (rch6 w6 3 ROOT)))
