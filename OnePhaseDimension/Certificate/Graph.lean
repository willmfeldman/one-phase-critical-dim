/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Nat.Digits.Defs

/-!
# Graph keys for scalar tensor monomials

A *graph key* describes a tensor monomial in a symmetric matrix `A`, vectors `p, ℓ`, a cubic
tensor `X` and scalars `g, w, z` on `ℝ⁵`:

  `g^h w^a z^b ∏ tr(A^{k_i}) · ∑_{internal indices} ∏_{edges} (A^k)_{uv} · (vector and X entries)`.

An edge carries a matrix power `A^k` (with `A^0 = δ`) between two endpoints. An endpoint is a
free slot, a copy of `p`, a copy of `ℓ`, or an incidence at one of the copies of `X`. Copies of
`p` and `ℓ` are degree-one vertices; each copy of `X` has three incidences.

This file contains only the combinatorial side, designed so that everything reduces in the
Lean kernel:

* `Endpoint`, `Edge`, `Key` and their numeric codes;
* `Key.pack : Key → ℕ`, an injective (on bounded keys) packing into a single natural number in
  base `256`, used as the sort key of polynomials; `Key.unpack` is its inverse;
* `Key.normalize` (sorting) and `Key.reduce` (trace and `X`-trace reductions), combined in
  `Key.canon`;
* `Key.mul` (disjoint union) and `Key.contract` (contraction of two free slots);
* `Poly`, sorted association lists from packed keys to integer coefficients, with a
  structurally recursive merge;
* `decodeWord`, the decimal digit-word encoding of the tables.

The semantics is in `OnePhaseDimension.Certificate.Eval`.

## Encoding

The decimal encoding of the tables (the 2026-09-24 version, Section "Tensor monomials") uses
labels `0, …, r-1` for free slots, `5` for `p`, `6` for `ℓ`, `7, 8` for the first and second
copy of `X`. Internally we use the numeric endpoint codes

  `X_1 ↦ 0`, `X_0 ↦ 1`, `ℓ ↦ 2`, `p ↦ 3`, `slot i ↦ 4 + 2i`, and `X_c ↦ 2c + 1` for `c ≥ 2`,

so that the code is injective for any number of slots and of `X` copies. On keys with at most
two copies of `X` (the only ones that occur) this is the order of the 2026-09-24 version, which
replaces the labels `5, 6, 7, 8` by `-1, -2, -3, -4`: our canonical form is then exactly the
paper's (sorted endpoints, sorted edges, sorted traces, and the lexicographically larger edge
list under the exchange of the two copies of `X`).

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

@[expose] public section

namespace OnePhaseDimension.Certificate

/-- The base of the packed key encoding. -/
abbrev packBase : ℕ := 256

/-! ### Endpoints and edges -/

/-- An endpoint of an edge of a graph key. -/
inductive Endpoint where
  /-- A copy of the vector `p`. -/
  | p
  /-- A copy of the vector `ℓ`. -/
  | ell
  /-- An incidence at the `c`-th copy of the cubic tensor `X`. -/
  | x (c : ℕ)
  /-- The `i`-th free slot. -/
  | slot (i : ℕ)
  deriving DecidableEq, Repr, Inhabited

namespace Endpoint

/-- The numeric code of an endpoint: `X_1 ↦ 0`, `X_0 ↦ 1`, `ℓ ↦ 2`, `p ↦ 3`,
`slot i ↦ 4 + 2i`, and `X_c ↦ 2c + 1` for `c ≥ 2`. -/
def code : Endpoint → ℕ
  | x c => if c = 0 then 1 else if c = 1 then 0 else 2 * c + 1
  | ell => 2
  | p => 3
  | slot i => 4 + 2 * i

/-- Inverse of `Endpoint.code`. -/
def ofCode (n : ℕ) : Endpoint :=
  if n = 0 then x 1 else if n = 1 then x 0 else if n = 2 then ell else if n = 3 then p
  else if n % 2 = 0 then slot ((n - 4) / 2) else x ((n - 1) / 2)

@[simp] theorem ofCode_code (e : Endpoint) : ofCode e.code = e := by
  match e with
  | x 0 => rfl
  | x 1 => rfl
  | x (c + 2) =>
    change ofCode (2 * (c + 2) + 1) = x (c + 2)
    unfold ofCode; split_ifs <;> first | omega | (congr 1; omega) | contradiction
  | ell => rfl
  | p => rfl
  | slot i =>
    change ofCode (4 + 2 * i) = slot i
    unfold ofCode; split_ifs <;> first | omega | (congr 1; omega)

theorem code_injective : Function.Injective code := fun a b h => by
  rw [← ofCode_code a, ← ofCode_code b, h]

/-- Shift free slots by `s` and `X` copies by `t`; `p` and `ℓ` are unchanged. -/
def shift (s t : ℕ) : Endpoint → Endpoint
  | x c => x (c + t)
  | slot i => slot (i + s)
  | e => e

/-- Exchange the first two copies of `X`. -/
def swapX : Endpoint → Endpoint
  | x 0 => x 1
  | x 1 => x 0
  | e => e

/-- Whether the endpoint is an incidence at a copy of `X`. -/
def isX : Endpoint → Bool
  | x _ => true
  | _ => false

/-- Whether the endpoint is the free slot `i`. -/
def isSlot (i : ℕ) : Endpoint → Bool
  | slot j => j == i
  | _ => false

/-- Renumber free slots after deleting slots `i < j`: slots above `j` move down by two, slots
strictly between `i` and `j` by one. Slots `i, j` themselves are not expected to occur. -/
def dropSlots (i j : ℕ) : Endpoint → Endpoint
  | slot k => slot (if k < i then k else if k < j then k - 1 else k - 2)
  | e => e

/-- Rename free slot `i` to `σ[i]` (slots beyond the length of `σ` are unchanged). -/
def permSlot (σ : List ℕ) : Endpoint → Endpoint
  | slot i => slot (σ.getD i i)
  | e => e

/-- The decimal digit label of the tables: `0–4` free slots, `5 = p`, `6 = ℓ`, `7, 8` the two
copies of `X`. Other digits are read as free slots. -/
def ofDigit (d : ℕ) : Endpoint :=
  if d = 5 then p else if d = 6 then ell else if d = 7 then x 0 else if d = 8 then x 1
  else slot d

end Endpoint

/-- An unoriented edge carrying the matrix `A ^ pow` between endpoints `u` and `v`. -/
structure Edge where
  /-- First endpoint. -/
  u : Endpoint
  /-- Second endpoint. -/
  v : Endpoint
  /-- The power of `A` carried by the edge. -/
  pow : ℕ
  deriving DecidableEq, Repr, Inhabited

namespace Edge

/-- The code of an edge, ordered lexicographically by `(u.code, v.code, pow)` for bounded
codes. -/
def code (e : Edge) : ℕ := (e.u.code * packBase + e.v.code) * packBase + e.pow

/-- Put the endpoint with smaller code first. -/
def orient (e : Edge) : Edge :=
  if e.v.code < e.u.code then ⟨e.v, e.u, e.pow⟩ else e

/-- Apply a map to both endpoints. -/
def mapEnds (f : Endpoint → Endpoint) (e : Edge) : Edge := ⟨f e.u, f e.v, e.pow⟩

/-- The digits of an edge in the packed encoding. -/
def digits (e : Edge) : List ℕ := [e.u.code, e.v.code, e.pow]

/-- Whether the edge has an endpoint at a copy of `X`. -/
def hasX (e : Edge) : Bool := e.u.isX || e.v.isX

end Edge

/-! ### Keys -/

/-- A graph key: the rank, the powers of `g, w, z`, the list of powers `k` of trace factors
`tr A^k`, and the list of edges. -/
structure Key where
  /-- Number of free slots. -/
  rank : ℕ
  /-- Power of `g`. -/
  gPow : ℕ
  /-- Power of `w`. -/
  wPow : ℕ
  /-- Power of `z`. -/
  zPow : ℕ
  /-- Powers `k` of the trace factors `tr A^k`. -/
  traces : List ℕ
  /-- The edges. -/
  edges : List Edge
  deriving DecidableEq, Repr, Inhabited

namespace Key

/-- The digit list of a key: `rank, gPow, wPow, zPow, #traces, traces…, #edges, edges…`, each
edge contributing `u.code, v.code, pow`. -/
def digits (k : Key) : List ℕ :=
  [k.rank, k.gPow, k.wPow, k.zPow, k.traces.length] ++ k.traces ++
    k.edges.length :: k.edges.flatMap Edge.digits

/-- All digits are below the packing base. -/
def Bounded (k : Key) : Prop := ∀ d ∈ k.digits, d < packBase

instance (k : Key) : Decidable k.Bounded := inferInstanceAs (Decidable (∀ d ∈ _, _))

/-- Pack a digit list (most significant first) behind a leading sentinel digit `1`. -/
def packDigits (ds : List ℕ) : ℕ := ds.foldl (fun acc d => acc * packBase + d) 1

/-- The packed form of a key, a single natural number. Key comparison is one `Nat`
comparison. -/
def pack (k : Key) : ℕ := packDigits k.digits

/-- Base-`256` digits, least significant first, with explicit fuel (structural recursion). -/
def digitsLE : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, n => if n = 0 then [] else n % packBase :: digitsLE fuel (n / packBase)

/-- Parse `count` edges from a digit list. -/
def parseEdges : ℕ → List ℕ → List Edge
  | 0, _ => []
  | n + 1, u :: v :: k :: rest => ⟨.ofCode u, .ofCode v, k⟩ :: parseEdges n rest
  | _ + 1, _ => []

/-- Parse a digit list produced by `Key.digits`. -/
def ofDigits : List ℕ → Key
  | r :: h :: a :: b :: nt :: rest =>
    match rest.drop nt with
    | ne :: rest' => ⟨r, h, a, b, rest.take nt, parseEdges ne rest'⟩
    | [] => ⟨r, h, a, b, rest.take nt, []⟩
  | _ => ⟨0, 0, 0, 0, [], []⟩

/-- Inverse of `Key.pack` on bounded keys. -/
def unpack (n : ℕ) : Key := ofDigits ((digitsLE (n + 1) n).reverse.drop 1)

/-! ### Packing is invertible on bounded keys -/

theorem foldl_pack_eq (ds : List ℕ) (a : ℕ) :
    ds.foldl (fun acc d => acc * packBase + d) a =
      Nat.ofDigits packBase ds.reverse + packBase ^ ds.length * a := by
  induction ds generalizing a with
  | nil => simp
  | cons d ds ih =>
    rw [List.foldl_cons, ih, List.reverse_cons, Nat.ofDigits_append, List.length_reverse,
      List.length_cons, pow_succ]
    simp only [Nat.ofDigits_singleton]
    ring

theorem packDigits_eq (ds : List ℕ) :
    packDigits ds = Nat.ofDigits packBase (ds.reverse ++ [1]) := by
  rw [packDigits, foldl_pack_eq, Nat.ofDigits_append, List.length_reverse,
    Nat.ofDigits_singleton]

theorem digitsLE_eq_digits : ∀ fuel n, n < fuel → digitsLE fuel n = Nat.digits packBase n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, n, h => by
    rw [digitsLE]
    split_ifs with hn
    · simp [hn]
    · rw [Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hn),
        digitsLE_eq_digits fuel (n / packBase) (by simp only [packBase]; omega)]

theorem parseEdges_flatMap (es : List Edge) (rest : List ℕ) :
    parseEdges es.length (es.flatMap Edge.digits ++ rest) = es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.length_cons, List.flatMap_cons, Edge.digits, List.cons_append,
      List.nil_append, parseEdges, Endpoint.ofCode_code, ih]

theorem ofDigits_digits (k : Key) : ofDigits k.digits = k := by
  have h := parseEdges_flatMap k.edges []
  rw [List.append_nil] at h
  simp [digits, ofDigits, h]

/-- Packing is inverted by `Key.unpack` on keys whose digits are below the base. -/
theorem unpack_pack {k : Key} (hk : k.Bounded) : unpack (pack k) = k := by
  have hlt : pack k < pack k + 1 := Nat.lt_succ_self _
  rw [unpack, digitsLE_eq_digits _ _ hlt, pack, packDigits_eq, Nat.digits_ofDigits _ (by norm_num)]
  · simp [ofDigits_digits]
  · intro l hl
    simp only [List.mem_append, List.mem_reverse, List.mem_singleton] at hl
    rcases hl with hl | rfl
    · exact hk l hl
    · norm_num
  · intro _
    simp

theorem pack_injective {k k' : Key} (hk : k.Bounded) (hk' : k'.Bounded) (h : k.pack = k'.pack) :
    k = k' := by
  rw [← unpack_pack hk, h, unpack_pack hk']

/-! ### Simple operations -/

/-- Whether some edge has an endpoint at a copy of `X`. -/
def hasX (k : Key) : Bool := k.edges.any Edge.hasX

/-- One more than the largest `X` copy index occurring in the key (zero if there is none). -/
def xBound (k : Key) : ℕ :=
  k.edges.foldr (fun e acc => max acc (max (bound e.u) (bound e.v))) 0
where
  /-- One more than the copy index of an `X` endpoint, zero otherwise. -/
  bound : Endpoint → ℕ
    | .x c => c + 1
    | _ => 0

/-- Tensor product: disjoint union, with the free slots of `t` shifted after those of `s` and
the copies of `X` of `t` after those of `s`. -/
def mul (s t : Key) : Key where
  rank := s.rank + t.rank
  gPow := s.gPow + t.gPow
  wPow := s.wPow + t.wPow
  zPow := s.zPow + t.zPow
  traces := s.traces ++ t.traces
  edges := s.edges ++ t.edges.map (Edge.mapEnds (Endpoint.shift s.rank s.xBound))

/-- Contract the edges at free slots `i` and `j` (`i < j`), assuming each occurs exactly once.
If both lie on the same edge it becomes a trace factor; otherwise the two edges are joined and
their powers add. Remaining slots are renumbered. -/
def contract (i j : ℕ) (k : Key) : Key :=
  let atI := fun e : Edge => e.u.isSlot i || e.v.isSlot i
  let atJ := fun e : Edge => e.u.isSlot j || e.v.isSlot j
  let rest := (k.edges.filter fun e => !(atI e || atJ e)).map
    (Edge.mapEnds (Endpoint.dropSlots i j))
  let other := fun (e : Edge) (m : ℕ) => if e.u.isSlot m then e.v else e.u
  match k.edges.find? atI, k.edges.find? atJ with
  | some e, some f =>
    if atJ e then
      { k with rank := k.rank - 2, traces := e.pow :: k.traces, edges := rest }
    else
      { k with rank := k.rank - 2,
               edges := (Edge.mapEnds (Endpoint.dropSlots i j)
                 ⟨other e i, other f j, e.pow + f.pow⟩) :: rest }
  | _, _ => { k with rank := k.rank - 2, edges := rest }

/-- Rename the free slots by `σ`: slot `i` becomes slot `σ[i]`. -/
def permSlots (σ : List ℕ) (k : Key) : Key :=
  { k with edges := k.edges.map (Edge.mapEnds (Endpoint.permSlot σ)) }

/-- Contract slot `0` with slot `n`, then `0` with `n - 1`, …, `0` with `1`: for a product
`s ⊗ t` of two rank-`n` keys this is the full contraction `⟨s, t⟩` (slot `i` with slot `i`). -/
def contractPairs : ℕ → Key → Key
  | 0, k => k
  | n + 1, k => contractPairs n (k.contract 0 (n + 1))

/-! ### Canonical form -/

/-- Insert `a` before the first element `b` with `le a b`. -/
def insertBy {α : Type*} (le : α → α → Bool) (a : α) : List α → List α
  | [] => [a]
  | b :: l => if le a b then a :: b :: l else b :: insertBy le a l

/-- Insertion sort with a Boolean comparison (structurally recursive, kernel-reducible). -/
def sortBy {α : Type*} (le : α → α → Bool) : List α → List α
  | [] => []
  | a :: l => insertBy le a (sortBy le l)

theorem perm_insertBy {α : Type*} (le : α → α → Bool) (a : α) :
    ∀ l : List α, (insertBy le a l).Perm (a :: l)
  | [] => .refl _
  | b :: l => by
    unfold insertBy
    split_ifs
    · exact .refl _
    · exact ((perm_insertBy le a l).cons b).trans (.swap a b l)

theorem perm_sortBy {α : Type*} (le : α → α → Bool) : ∀ l : List α, (sortBy le l).Perm l
  | [] => .refl _
  | a :: l => (perm_insertBy le a _).trans ((perm_sortBy le l).cons a)

/-- Sort the endpoints of every edge, the edge list and the trace list. -/
def sortAll (k : Key) : Key :=
  { k with
    traces := sortBy Nat.ble k.traces
    edges := sortBy (fun e f => Nat.ble e.code f.code) (k.edges.map Edge.orient) }

/-- Exchange the first two copies of `X`. -/
def swapX (k : Key) : Key := { k with edges := k.edges.map (Edge.mapEnds Endpoint.swapX) }

/-- The normal form of a key under the relabellings that preserve its value: sorting, and the
exchange of the two copies of `X` (the sorted form with the larger packed code is kept). -/
def normalize (k : Key) : Key :=
  let k₁ := sortAll k
  if k.hasX then
    let k₂ := sortAll k.swapX
    if k₁.pack < k₂.pack then k₂ else k₁
  else k₁

/-- Reduce the trace factors: `tr A^0 = 5`, `tr A = 0`, `tr A^2 = 1`. Returns the scalar factor
and the remaining powers. These reductions hold for symmetric trace-free `A` with `|A| = 1`. -/
def reduceTraces : List ℕ → ℤ × List ℕ
  | [] => (1, [])
  | t :: ts =>
    let r := reduceTraces ts
    if t = 0 then (5 * r.1, r.2) else if t = 1 then (0, r.2)
    else if t = 2 then r else (r.1, t :: r.2)

/-- Whether some edge is a power-zero loop at one copy of `X` (a trace of `X`). -/
def hasXTrace (k : Key) : Bool :=
  k.edges.any fun e => e.pow == 0 && e.u.isX && e.u == e.v

/-- Apply the trace reductions and the vanishing of `X`-traces. Returns a scalar factor and a
key; the factor is `0` when the monomial vanishes. -/
def reduce (k : Key) : ℤ × Key :=
  if k.hasXTrace then (0, k) else
    let r := reduceTraces k.traces
    (r.1, { k with traces := r.2 })

/-- Canonical form: a scalar factor and a normalized key. On admissible data,
`eval k = c * eval k'` where `(c, k') = canon k`. -/
def canon (k : Key) : ℤ × Key :=
  let r := k.reduce
  (r.1, normalize r.2)

/-- The packed canonical form, with the scalar factor. -/
def canonPack (k : Key) : ℤ × ℕ :=
  let r := k.canon
  (r.1, r.2.pack)

end Key

/-! ### Decoding the decimal tables -/

/-- Read a digit list in consecutive triples. -/
def triples : List ℕ → List (ℕ × ℕ × ℕ)
  | a :: b :: c :: rest => (a, b, c) :: triples rest
  | _ => []

/-- The key of a rank-`r` tensor monomial encoded by a decimal digit word: the first triple
`h b j` gives `g^h (tr A^3)^b w^[j=1] z^[j=2]`, and each later triple `u v k` an edge carrying
`A^k` between the endpoints labelled `u` and `v`. -/
def decodeWord (r : ℕ) (word : List ℕ) : Key :=
  match triples word with
  | [] => ⟨r, 0, 0, 0, [], []⟩
  | (h, b, j) :: es =>
    { rank := r, gPow := h
      wPow := if j = 1 then 1 else 0
      zPow := if j = 2 then 1 else 0
      traces := List.replicate b 3
      edges := es.map fun e => ⟨.ofDigit e.1, .ofDigit e.2.1, e.2.2⟩ }

/-- The `len` decimal digits of `n`, most significant first, with leading zeros. Written with
the recursor `Nat.rec` and an accumulator, which the kernel reduces faster than a compiled
pattern match. -/
def wordDigits (len n : ℕ) : List ℕ :=
  (Nat.rec (motive := fun _ => ℕ → List ℕ → List ℕ) (fun _ acc => acc)
    (fun _ ih m acc => ih (m / 10) ((m % 10) :: acc)) len) n []

/-! ### Polynomials -/

/-- A polynomial in graph keys: an association list from packed keys to integer coefficients,
kept sorted by increasing key with no zero coefficients. -/
abbrev Poly := List (ℕ × ℤ)

namespace Poly

/-- Insert-merge one term into a sorted polynomial, given the merge of the tail. Structural in
the second list. -/
def mergeAux (a : ℕ) (c : ℤ) (p : Poly) (mp : Poly → Poly) : Poly → Poly
  | [] => (a, c) :: p
  | (b, d) :: q =>
    if a < b then (a, c) :: mp ((b, d) :: q)
    else if b < a then (b, d) :: mergeAux a c p mp q
    else if c + d = 0 then mp q else (a, c + d) :: mp q

/-- Merge (add) two sorted polynomials, cancelling zero coefficients. Structurally recursive. -/
def merge : Poly → Poly → Poly
  | [], q => q
  | (a, c) :: p, q => mergeAux a c p (merge p) q

/-- Sum of two polynomials. -/
abbrev add (p q : Poly) : Poly := merge p q

/-- Multiply all coefficients by an integer. -/
def smul (c : ℤ) (p : Poly) : Poly :=
  if c = 0 then [] else p.map fun t => (t.1, c * t.2)

/-- Collect a list of terms into a sorted polynomial. -/
def ofList (l : List (ℕ × ℤ)) : Poly :=
  l.foldr (fun t acc => if t.2 = 0 then acc else merge [t] acc) []

end Poly

namespace Poly

/-- One round of pairwise merging. -/
def mergePairs : List Poly → List Poly
  | a :: b :: rest => merge a b :: mergePairs rest
  | l => l

/-- Sum of a list of polynomials by a balanced merge tree (`fuel` rounds; `l.length` rounds
always suffice). -/
def mergeAllAux : ℕ → List Poly → List Poly
  | 0, l => l
  | n + 1, l => mergeAllAux n (mergePairs l)

/-- Sum of a list of polynomials by a balanced merge tree. -/
def mergeAll (l : List Poly) : Poly :=
  ((mergeAllAux l.length l).headD [])

end Poly

namespace Key

/-- Whether all digits of the key are below the packing base (Boolean form of `Key.Bounded`). -/
def boundedB (k : Key) : Bool := k.digits.all fun d => Nat.blt d packBase

/-- The packed key `0` is not the packing of any key; it marks an overflow of the packing. -/
def overflowTerm : Poly := [(0, 1)]

/-- The single-term polynomial `c · k`, after canonicalization. If the reduced key has a digit
that does not fit the packing base, the result is the marker `overflowTerm` instead; since its
coefficient is positive, a marker can never cancel in a sum, so a final result without the key
`0` certifies that every packed key was bounded. -/
def term (c : ℤ) (k : Key) : Poly :=
  let r := k.reduce
  if r.1 * c = 0 then [] else
    if r.2.boundedB then [((normalize r.2).pack, r.1 * c)] else overflowTerm

end Key

/-! ### Text dump in the reference format

`r<r>g<g>w<w>z<z>|t<k1>,<k2>,…|<U><V><k>,…`, where an endpoint is printed as `Y X L P` for the
second copy of `X`, the first copy of `X`, `ℓ`, `p`, and as its index for a free slot. These
functions are for `#eval` dumps only and are not used in kernel computations. -/

/-- The one-character label of an endpoint in the text dump. -/
def Endpoint.toRefString : Endpoint → String
  | .x 0 => "X"
  | .x 1 => "Y"
  | .x c => s!"X{c}"
  | .ell => "L"
  | .p => "P"
  | .slot i => toString i

/-- The text form of a key. -/
def Key.toRefString (k : Key) : String :=
  s!"r{k.rank}g{k.gPow}w{k.wPow}z{k.zPow}|t" ++ ",".intercalate (k.traces.map toString) ++
    "|" ++ ",".intercalate (k.edges.map fun e =>
      e.u.toRefString ++ e.v.toRefString ++ toString e.pow)

/-- The lines `<key> <coefficient>` of a polynomial, sorted as strings. -/
def Poly.dumpLines (P : Poly) : List String :=
  (P.map fun t => s!"{(Key.unpack t.1).toRefString} {t.2}").mergeSort
    (fun a b => decide (a ≤ b))

/-- An integer literal in constructor form, `.ofNat n` or `.negSucc n` (cheap to elaborate). -/
def intCtorString : ℤ → String
  | .ofNat n => s!".ofNat {n}"
  | .negSucc n => s!".negSucc {n}"

/-- A Lean definition `def name : List (ℕ × ℤ) := [...]` with the terms of a polynomial, one
per line (used to generate expected outputs of chunks). -/
def Poly.toLeanDef (name : String) (P : Poly) : String :=
  s!"def {name} : List (ℕ × ℤ) := [\n" ++
    ",\n".intercalate (P.map fun t => s!"  ({t.1}, {intCtorString t.2})") ++ "]\n"

end OnePhaseDimension.Certificate
