#!/bin/bash
# gen-scale.sh KIND N [OUT] — print a Gabbro source with N functions of shape KIND.
# Kinds: independent plain guard calls tables44 mixed longb longc.
# Only constructs from stage0/proben-ir/*.gab and stage0/proben-compiler/*.gab.
# Shell only (bash/awk/printf). Method doc: stage0/proben-compiler/SCALE.txt.
kind=$1; n=$2; out=${3:-/dev/stdout}
case $kind in independent|plain|guard|calls|tables44|mixed|longb|longc) ;; *)
  echo "gen-scale.sh: unknown kind $kind" >&2; exit 2;; esac
awk -v kind="$kind" -v n="$n" '
function pg(i, tail) {
  printf "impl fn g%d(p : u32 in 0 .. 100) -> u32 in 0 .. 100\n", i
  print "    effects { reads T.slots, writes T.slots }\n{\n    let mut c : u32 in 0 .. 20 = 0;"
  print "    if p < 10 {\n        T.slots[p].v = p + 20;\n        if c < 20 { c = c + 1; }\n    } else {"
  print "        if c < 19 { c = c + 2; }\n    }\n    if p == 0 { return c; }\n    let d = p - 1;"
  print "    if d < 10 {\n        return T.slots[d].v;\n    }\n    " tail "\n}"
}
function pm(i, tail) {
  printf "impl fn m%d(x : u32 in 0 .. 60, acc : u32 in 0 .. 200, fuel : u32 in 0 .. 128) -> MOut\n", i
  print "    decreases fuel\n{\n    narrow fuel to 1 .. 128 else { return MOut(v: 0, ok: false); }"
  print "    if x == 0 {\n        if acc < 200 { return MOut(v: acc + 1, ok: true); }"
  print "        return MOut(v: 0, ok: false);\n    }\n    " tail "\n}"
}
function cl(   c, i) {
  c = ""
  for (i = 0; i < 4; i++) c = c "reads T" i ".slots, writes T" i ".slots, "
  for (i = 0; i < 4; i++) c = c "reads s" i ", writes s" i ", "
  sub(/, $/, "", c); return c
}
BEGIN {
  if (kind == "independent") {
    print "module scale {"
    for (i = 0; i < n; i++)
      printf "impl fn p%d(x : u32 in 0 .. 50) -> u32 in 0 .. 100 { return x + x; }\n", i
    print "impl fn main() -> u32 in 0 .. 10 { return 7; }\n}"
  } else if (kind == "plain") {
    print "module scale {"
    print "impl fn p0(x : u32 in 0 .. 50) -> u32 in 0 .. 100 {\n    return x + x;\n}"
    for (i = 1; i < n; i++) {
      printf "impl fn p%d(x : u32 in 0 .. 50) -> u32 in 0 .. %d {\n    let a = p%d(x);\n", i, 100 + i, i - 1
      print "    return a + 1;\n}" }
    print "impl fn main() -> u32 in 0 .. 10 {"
    printf "    let v = p%d(5);\n    if v == %d { return 7; }\n    return 0;\n}\n}", n - 1, n + 9
  } else if (kind == "guard") {
    print "module scale {\ntable T count 10 { slot { v : u32 in 0 .. 100, } }"
    pg(0, "return 3;")
    for (i = 1; i < n; i++) pg(i, sprintf("let q = g%d(p);\n    return q;", i - 1))
    print "impl fn main() -> u32 in 0 .. 10\n    effects { reads T.slots, writes T.slots }\n{"
    printf "    let r = g%d(50);\n    if r == 3 { return 7; }\n    return 0;\n}\n}", n - 1
  } else if (kind == "calls") {
    print "module scale {"
    print "impl fn addsmall(a : u32 in 0 .. 40, b : u32 in 0 .. 40) -> u32 in 0 .. 80 {\n    return a + b;\n}"
    print "impl fn h0(x : u32 in 0 .. 10) -> u32 in 0 .. 40 {\n    let t = x + x;\n    return t + x;\n}"
    for (i = 1; i < n; i++) {
      printf "impl fn h%d(x : u32 in 0 .. 10) -> u32 in 0 .. 40 {\n    let a = h%d(x);\n", i, i - 1
      print "    if x == 5 { return a; }"
      printf "    let b = h%d(3);\n    if x == 6 { return b; }\n    let c = addsmall(a, b);\n", i - 1
      printf "    let d = addsmall(h%d(1), h%d(2));\n", i - 1, i - 1
      print "    narrow c to 0 .. 40 else { return a; }\n    narrow d to 0 .. 40 else { return b; }"
      print "    if x == 7 { return d; }\n    return c;\n}" }
    print "impl fn main() -> u32 in 0 .. 20 {"
    printf "    let r = h%d(5);\n    if r == 15 { return 7; }\n    return 0;\n}\n}", n - 1
  } else if (kind == "tables44") {
    c = cl()
    print "module scale {"
    for (i = 0; i < 4; i++) printf "table T%d count 8 { slot { v : u32 in 0 .. 100, w : u32 in 0 .. 200, } }\n", i
    for (i = 0; i < 4; i++) printf "static mut s%d : u32 in 0 .. 100 = 0;\n", i
    for (i = 0; i < n; i++) {
      printf "impl fn t%d(x : u32 in 0 .. 50) -> u32 in 0 .. 100\n    effects { %s }\n{\n", i, c
      printf "    s%d = x;\n    if x < 8 {\n        T%d.slots[x].v = x + 1;\n", i % 4, i % 4
      printf "        T%d.slots[x].w = s%d;\n    }\n", i % 4, i % 4
      if (i == 0) printf "    return s%d;\n}\n", i % 4
      else printf "    let q = t%d(x);\n    return q;\n}\n", i - 1 }
    print "impl fn main() -> u32 in 0 .. 10\n    effects { " c " }\n{"
    printf "    let r = t%d(5);\n    if r == 5 { return 7; }\n    return 0;\n}\n}", n - 1
  } else if (kind == "mixed") {
    print "module scale {\ntype MOut = { v : u32 in 0 .. 255, ok : bool, };"
    pm(0, "return MOut(v: x, ok: true);")
    for (i = 1; i < n; i++)
      pm(i, sprintf("let r = m%d(x - 1, acc, fuel - 1);\n    if !r.ok { return MOut(v: 0, ok: false); }\n    let w = r.v;\n    if w == 0 { return MOut(v: x, ok: true); }\n    return r;", i - 1))
    exv = (n < 9) ? 8 - n : 1
    print "impl fn main() -> u32 in 0 .. 10 {"
    printf "    let r = m%d(7, 0, 100);\n    if r.ok {\n        if r.v == %d { return 7; }\n", n - 1, exv
    print "        return 1;\n    }\n    return 0;\n}\n}"
  } else if (kind == "longb") {
    print "module scale {\ntable T count 10 { slot { v : u32 in 0 .. 100, } }"
    print "impl fn main() -> u32 in 0 .. 10\n    effects { reads T.slots, writes T.slots }\n{"
    printf "    let mut c : u32 in 0 .. %d = 0;\n", n
    for (i = 0; i < n; i++) printf "    if c < %d { c = c + 1; }\n", n
    print "    let p : u32 in 0 .. 100 = 4;"
    for (i = 0; i < n; i++) print "    if p < 10 { T.slots[p].v = p + 20; }"
    print "    if p == 0 { return 0; }\n    let d = p - 1;\n    if d < 10 {"
    print "        let w = T.slots[d].v;\n        if w == 24 { return 1; }\n    }"
    printf "    if c == %d { return 7; }\n    return 0;\n}\n}", n
  } else if (kind == "longc") {
    print "module scale {"
    print "impl fn id40(x : u32 in 0 .. 40) -> u32 in 0 .. 40 { return x; }"
    print "impl fn addsmall(a : u32 in 0 .. 40, b : u32 in 0 .. 40) -> u32 in 0 .. 80 {\n    return a + b;\n}"
    print "impl fn main() -> u32 in 0 .. 10 {\n    let v0 : u32 in 0 .. 40 = 8;\n    let u0 : u32 in 0 .. 40 = 0;"
    prev = "v0"; j = 0
    for (i = 0; i < n; i++) {
      j++
      printf "    let a%d = id40(%s);\n", j, prev
      if (j % 4 == 0) printf "    let s%d = addsmall(id40(a%d), u0);\n", j, j
      else printf "    let s%d = addsmall(a%d, u0);\n", j, j
      printf "    narrow s%d to 0 .. 40 else { return 0; }\n", j
      prev = sprintf("s%d", j) }
    printf "    if %s == 8 { return 7; }\n    return 0;\n}\n}", prev
  }
}' > "$out"
[ -n "$(tail -c 1 "$out")" ] && printf '\n' >> "$out"
wc -l "$out"
