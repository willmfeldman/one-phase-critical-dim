/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Graph

/-!
# Kernel-reducible versions of the graph-key operations

The definitions of `OnePhaseDimension.Certificate.Graph` are written for readability. Here each
operation on the hot path of a block expansion has a twin with suffix `_k`, written only with
the recursors `List.rec`, `Nat.rec`, `Bool.rec`, `Option.rec`, `Endpoint.rec`, the
`Nat`-literal operations accelerated in the kernel (`Nat.add`, `Nat.mul`, `Nat.ble`, `Nat.blt`,
`Nat.beq`, …) and `Int.beq'`; no `Decidable` instances, `if` or compiled pattern matching occur.
This follows the kernel-reduction pattern of `Lean.Grind.CommRing`. Every twin comes with a
lemma `*_k_eq` identifying it with the readable definition, so that a kernel computation with
the twins proves the corresponding statement about the readable definitions.

The twins are `noncomputable` (the compiler does not support recursors); they are only meant
for `decide +kernel`.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate

/-! ### Generic list functions -/

/-- `List.map` by the recursor. -/
noncomputable def lmap_k {α β : Type} (f : α → β) (l : List α) : List β :=
  List.rec [] (fun a _ ih => f a :: ih) l

/-- `List.append` by the recursor. -/
noncomputable def lappend_k {α : Type} (l m : List α) : List α :=
  List.rec m (fun a _ ih => a :: ih) l

/-- `List.flatMap` by the recursor. -/
noncomputable def lflatMap_k {α β : Type} (f : α → List β) (l : List α) : List β :=
  List.rec [] (fun a _ ih => lappend_k (f a) ih) l

/-- `List.length` by the recursor. -/
noncomputable def length_k {α : Type} (l : List α) : ℕ :=
  List.rec 0 (fun _ _ ih => Nat.succ ih) l

/-- `List.filter` by the recursor. -/
noncomputable def lfilter_k {α : Type} (p : α → Bool) (l : List α) : List α :=
  List.rec [] (fun a _ ih => Bool.rec ih (a :: ih) (p a)) l

/-- `List.find?` by the recursor. -/
noncomputable def lfind_k {α : Type} (p : α → Bool) (l : List α) : Option α :=
  List.rec none (fun a _ ih => Bool.rec ih (some a) (p a)) l

/-- `List.getD l i d` by the recursor. -/
noncomputable def lgetD_k (l : List ℕ) (i d : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => d)
    (fun a _ ih n => Nat.rec (motive := fun _ => ℕ) a (fun m _ => ih m) n) l i

/-- `max` on `ℕ` by `Nat.ble`. -/
noncomputable def max_k (a b : ℕ) : ℕ := Bool.rec a b (Nat.ble a b)

/-- Insert into a sorted list of naturals. -/
noncomputable def insertNat_k (a : ℕ) (l : List ℕ) : List ℕ :=
  List.rec [a] (fun b l ih => Bool.rec (b :: ih) (a :: b :: l) (Nat.ble a b)) l

/-- Insertion sort of a list of naturals. -/
noncomputable def sortNat_k (l : List ℕ) : List ℕ :=
  List.rec [] (fun a _ ih => insertNat_k a ih) l

/-! ### Endpoints and edges -/

namespace Endpoint

/-- `Endpoint.code` by the recursor. -/
noncomputable def code_k (e : Endpoint) : ℕ :=
  Endpoint.rec (motive := fun _ => ℕ) 3 2
    (fun c => Bool.rec (Bool.rec (Nat.add (Nat.mul 2 c) 1) 0 (Nat.beq c 1)) 1 (Nat.beq c 0))
    (fun i => Nat.add 4 (Nat.mul 2 i)) e

/-- `Endpoint.isSlot` by the recursor. -/
noncomputable def isSlot_k (i : ℕ) (e : Endpoint) : Bool :=
  Endpoint.rec (motive := fun _ => Bool) false false (fun _ => false) (fun j => Nat.beq j i) e

/-- `Endpoint.isX` by the recursor. -/
noncomputable def isX_k (e : Endpoint) : Bool :=
  Endpoint.rec (motive := fun _ => Bool) false false (fun _ => true) (fun _ => false) e

/-- `Endpoint.shift` by the recursor. -/
noncomputable def shift_k (s t : ℕ) (e : Endpoint) : Endpoint :=
  Endpoint.rec (motive := fun _ => Endpoint) p ell (fun c => x (Nat.add c t))
    (fun i => slot (Nat.add i s)) e

/-- `Endpoint.dropSlots` by the recursor. -/
noncomputable def dropSlots_k (i j : ℕ) (e : Endpoint) : Endpoint :=
  Endpoint.rec (motive := fun _ => Endpoint) p ell x
    (fun k => slot (Bool.rec (Bool.rec (Nat.sub k 2) (Nat.sub k 1) (Nat.blt k j)) k
      (Nat.blt k i))) e

/-- `Endpoint.swapX` by the recursor. -/
noncomputable def swapX_k (e : Endpoint) : Endpoint :=
  Endpoint.rec (motive := fun _ => Endpoint) p ell
    (fun c => Bool.rec (Bool.rec (x c) (x 0) (Nat.beq c 1)) (x 1) (Nat.beq c 0)) slot e

/-- `Endpoint.permSlot` by the recursor. -/
noncomputable def permSlot_k (σ : List ℕ) (e : Endpoint) : Endpoint :=
  Endpoint.rec (motive := fun _ => Endpoint) p ell x (fun i => slot (lgetD_k σ i i)) e

/-- `Key.xBound.bound` by the recursor. -/
noncomputable def xBound_k (e : Endpoint) : ℕ :=
  Endpoint.rec (motive := fun _ => ℕ) 0 0 (fun c => Nat.succ c) (fun _ => 0) e

end Endpoint

namespace Edge

/-- `Edge.mapEnds`, with explicit projections. -/
def mapEnds_k (f : Endpoint → Endpoint) (e : Edge) : Edge := ⟨f e.u, f e.v, e.pow⟩

/-- The code of an edge with endpoint codes `a, b` and power `k`. -/
def codeOf (a b k : ℕ) : ℕ := Nat.add (Nat.mul (Nat.add (Nat.mul a 256) b) 256) k

/-- `Edge.code` by the recursor. -/
noncomputable def code_k (e : Edge) : ℕ := codeOf e.u.code_k e.v.code_k e.pow

/-- The code of the oriented edge, `e.orient.code`. -/
noncomputable def orientCode_k (e : Edge) : ℕ :=
  Bool.rec (codeOf e.u.code_k e.v.code_k e.pow) (codeOf e.v.code_k e.u.code_k e.pow)
    (Nat.blt e.v.code_k e.u.code_k)

/-- Whether the edge has an endpoint at a copy of `X`. -/
noncomputable def hasX_k (e : Edge) : Bool := Bool.or e.u.isX_k e.v.isX_k

/-- Whether the edge is a power-zero loop at one copy of `X`. -/
noncomputable def isXTrace_k (e : Edge) : Bool :=
  Bool.and (Bool.and (Nat.beq e.pow 0) e.u.isX_k) (Nat.beq e.u.code_k e.v.code_k)

end Edge

/-! ### Keys -/

namespace Key

/-- Fold digits into a packed number (base `256`). -/
noncomputable def foldDigits_k (acc : ℕ) (ds : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun a => a)
    (fun d _ ih a => ih (Nat.add (Nat.mul a 256) d)) ds acc

/-- Fold edge codes into a packed number (three base-`256` digits per edge). -/
noncomputable def foldCodes_k (acc : ℕ) (cs : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun a => a)
    (fun c _ ih a => ih (Nat.add (Nat.mul a 16777216) c)) cs acc

/-- The packed number of a key with the given traces and edge codes. -/
noncomputable def packWith_k (k : Key) (traces codes : List ℕ) : ℕ :=
  foldCodes_k (Nat.add (Nat.mul (foldDigits_k
    (foldDigits_k 1 [k.rank, k.gPow, k.wPow, k.zPow, length_k traces]) traces) 256)
    (length_k codes)) codes

/-- `Key.pack` by recursors. -/
noncomputable def pack_k (k : Key) : ℕ := packWith_k k k.traces (lmap_k Edge.code_k k.edges)

/-- `Key.hasX` by the recursor. -/
noncomputable def hasX_k (k : Key) : Bool :=
  List.rec false (fun e _ ih => Bool.or e.hasX_k ih) k.edges

/-- `Key.hasXTrace` by the recursor. -/
noncomputable def hasXTrace_k (k : Key) : Bool :=
  List.rec false (fun e _ ih => Bool.or e.isXTrace_k ih) k.edges

/-- `Key.xBound` by the recursor. -/
noncomputable def xBound_k (k : Key) : ℕ :=
  List.rec 0 (fun e _ ih => max_k ih (max_k e.u.xBound_k e.v.xBound_k)) k.edges

/-- `Key.mul` by recursors. -/
noncomputable def mul_k (s t : Key) : Key :=
  ⟨Nat.add s.rank t.rank, Nat.add s.gPow t.gPow, Nat.add s.wPow t.wPow, Nat.add s.zPow t.zPow,
    lappend_k s.traces t.traces,
    lappend_k s.edges (lmap_k (Edge.mapEnds_k (Endpoint.shift_k s.rank s.xBound_k)) t.edges)⟩

/-- Whether an edge is incident to free slot `i`. -/
noncomputable def atSlot_k (i : ℕ) (e : Edge) : Bool := Bool.or (e.u.isSlot_k i) (e.v.isSlot_k i)

/-- The endpoint of `e` other than free slot `m`. -/
noncomputable def other_k (e : Edge) (m : ℕ) : Endpoint := Bool.rec e.u e.v (e.u.isSlot_k m)

/-- `Key.contract` by recursors. -/
noncomputable def contract_k (i j : ℕ) (k : Key) : Key :=
  Option.rec
    (⟨Nat.sub k.rank 2, k.gPow, k.wPow, k.zPow, k.traces,
      lmap_k (Edge.mapEnds_k (Endpoint.dropSlots_k i j))
        (lfilter_k (fun e => Bool.not (Bool.or (atSlot_k i e) (atSlot_k j e))) k.edges)⟩)
    (fun e => Option.rec
      (⟨Nat.sub k.rank 2, k.gPow, k.wPow, k.zPow, k.traces,
        lmap_k (Edge.mapEnds_k (Endpoint.dropSlots_k i j))
          (lfilter_k (fun e => Bool.not (Bool.or (atSlot_k i e) (atSlot_k j e))) k.edges)⟩)
      (fun f => Bool.rec
        (⟨Nat.sub k.rank 2, k.gPow, k.wPow, k.zPow, k.traces,
          Edge.mapEnds_k (Endpoint.dropSlots_k i j)
            ⟨other_k e i, other_k f j, Nat.add e.pow f.pow⟩ ::
          lmap_k (Edge.mapEnds_k (Endpoint.dropSlots_k i j))
            (lfilter_k (fun e => Bool.not (Bool.or (atSlot_k i e) (atSlot_k j e))) k.edges)⟩)
        (⟨Nat.sub k.rank 2, k.gPow, k.wPow, k.zPow, e.pow :: k.traces,
          lmap_k (Edge.mapEnds_k (Endpoint.dropSlots_k i j))
            (lfilter_k (fun e => Bool.not (Bool.or (atSlot_k i e) (atSlot_k j e))) k.edges)⟩)
        (atSlot_k j e))
      (lfind_k (atSlot_k j) k.edges))
    (lfind_k (atSlot_k i) k.edges)

/-- `Key.permSlots` by recursors. -/
noncomputable def permSlots_k (σ : List ℕ) (k : Key) : Key :=
  ⟨k.rank, k.gPow, k.wPow, k.zPow, k.traces,
    lmap_k (Edge.mapEnds_k (Endpoint.permSlot_k σ)) k.edges⟩

/-- `Key.contractPairs` by recursors. -/
noncomputable def contractPairs_k (n : ℕ) (k : Key) : Key :=
  Nat.rec (motive := fun _ => Key → Key) (fun k => k)
    (fun n ih k => ih (contract_k 0 (Nat.succ n) k)) n k

/-- `Key.reduceTraces` by recursors. -/
noncomputable def reduceTraces_k (ts : List ℕ) : ℤ × List ℕ :=
  List.rec (1, []) (fun t _ ih =>
    Bool.rec
      (Bool.rec
        (Bool.rec (ih.1, t :: ih.2) ih (Nat.beq t 2))
        (0, ih.2) (Nat.beq t 1))
      (Int.mul 5 ih.1, ih.2) (Nat.beq t 0)) ts

/-- The packed code of the sorted form of `k` (`(Key.sortAll k).pack`). -/
noncomputable def sortedPack_k (k : Key) : ℕ :=
  packWith_k k (sortNat_k k.traces) (sortNat_k (lmap_k Edge.orientCode_k k.edges))

/-- `(Key.normalize k).pack` by recursors. -/
noncomputable def normalizePack_k (k : Key) : ℕ :=
  Bool.rec (sortedPack_k k)
    (Bool.rec (sortedPack_k k)
      (sortedPack_k ⟨k.rank, k.gPow, k.wPow, k.zPow, k.traces,
        lmap_k (Edge.mapEnds_k Endpoint.swapX_k) k.edges⟩)
      (Nat.blt (sortedPack_k k) (sortedPack_k ⟨k.rank, k.gPow, k.wPow, k.zPow, k.traces,
        lmap_k (Edge.mapEnds_k Endpoint.swapX_k) k.edges⟩)))
    (hasX_k k)

/-- `Key.canonPack` by recursors. -/
noncomputable def canonPack_k (k : Key) : ℤ × ℕ :=
  Bool.rec
    ((reduceTraces_k k.traces).1,
      normalizePack_k ⟨k.rank, k.gPow, k.wPow, k.zPow, (reduceTraces_k k.traces).2, k.edges⟩)
    (0, normalizePack_k k)
    (hasXTrace_k k)

/-- All entries of a list are below `256`. -/
noncomputable def allLt_k (l : List ℕ) : Bool :=
  List.rec true (fun d _ ih => Bool.and (Nat.blt d 256) ih) l

/-- `Key.boundedB` by recursors. -/
noncomputable def boundedB_k (k : Key) : Bool :=
  Bool.and (allLt_k [k.rank, k.gPow, k.wPow, k.zPow, length_k k.traces])
    (Bool.and (allLt_k k.traces) (Bool.and (Nat.blt (length_k k.edges) 256)
      (List.rec true (fun e _ ih => Bool.and (allLt_k [e.u.code_k, e.v.code_k, e.pow]) ih)
        k.edges)))

/-- `Key.reduce` by recursors. -/
noncomputable def reduce_k (k : Key) : ℤ × Key :=
  Bool.rec ((reduceTraces_k k.traces).1,
      ⟨k.rank, k.gPow, k.wPow, k.zPow, (reduceTraces_k k.traces).2, k.edges⟩)
    (0, k) (hasXTrace_k k)

/-- `Key.term` by recursors. -/
noncomputable def term_k (c : ℤ) (k : Key) : Poly :=
  Bool.rec
    (Bool.rec overflowTerm [(normalizePack_k (reduce_k k).2, Int.mul (reduce_k k).1 c)]
      (boundedB_k (reduce_k k).2))
    [] (Int.beq' (Int.mul (reduce_k k).1 c) 0)

end Key

/-! ### Polynomials -/

namespace Poly

/-- `Poly.merge` by recursors (outer recursion on the first list, inner on the second). -/
noncomputable def merge_k (p : Poly) : Poly → Poly :=
  List.rec (motive := fun _ => Poly → Poly) (fun q => q)
    (fun ac p' ihp q =>
      List.rec (motive := fun _ => Poly) (ac :: p')
        (fun bd q' ihq =>
          Bool.rec
            (Bool.rec
              (Bool.rec ((ac.1, Int.add ac.2 bd.2) :: ihp q') (ihp q')
                (Int.beq' (Int.add ac.2 bd.2) 0))
              (bd :: ihq) (Nat.blt bd.1 ac.1))
            (ac :: ihp (bd :: q')) (Nat.blt ac.1 bd.1))
        q)
    p

/-- `Poly.mergePairs` by the recursor, carrying a pending polynomial. -/
noncomputable def mergePairsAux_k (l : List Poly) : Option Poly → List Poly :=
  List.rec (motive := fun _ => Option Poly → List Poly)
    (fun o => Option.rec [] (fun a => [a]) o)
    (fun x _ ih o => Option.rec (ih (some x)) (fun a => merge_k a x :: ih none) o) l

/-- `Poly.mergeAll` by recursors. -/
noncomputable def mergeAll_k (l : List Poly) : Poly :=
  List.rec [] (fun a _ _ => a)
    (Nat.rec (motive := fun _ => List Poly → List Poly) (fun l => l)
      (fun _ ih l => ih (mergePairsAux_k l none)) (length_k l) l)

end Poly

/-! ### Agreement with the readable definitions -/

section Agreement

variable {α β : Type}

theorem brec_eq_ite {γ : Sort*} (x y : γ) (b : Bool) :
    Bool.rec (motive := fun _ => γ) x y b = if b = true then y else x := by
  cases b <;> rfl

theorem orec_eq {γ : Sort*} {δ : Type} (x : γ) (f : δ → γ) (o : Option δ) :
    Option.rec (motive := fun _ => γ) x f o = match o with | none => x | some d => f d := by
  cases o <;> rfl

theorem lmap_k_eq (f : α → β) (l : List α) : lmap_k f l = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg (f a :: ·) ih

theorem lappend_k_eq (l m : List α) : lappend_k l m = l ++ m := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg (a :: ·) ih

theorem lflatMap_k_eq (f : α → List β) (l : List α) : lflatMap_k f l = l.flatMap f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change lappend_k (f a) (lflatMap_k f l) = _
    rw [lappend_k_eq, ih, List.flatMap_cons]

theorem length_k_eq (l : List α) : length_k l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg Nat.succ ih

theorem lfilter_k_eq (p : α → Bool) (l : List α) : lfilter_k p l = l.filter p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change Bool.rec (motive := fun _ => List α) (lfilter_k p l) (a :: lfilter_k p l) (p a) = _
    rw [List.filter_cons, ih]
    cases p a <;> rfl

theorem lfind_k_eq (p : α → Bool) (l : List α) : lfind_k p l = l.find? p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change Bool.rec (motive := fun _ => Option α) (lfind_k p l) (some a) (p a) = _
    rw [List.find?_cons, ih]
    cases p a <;> rfl

theorem lgetD_k_eq (l : List ℕ) (i d : ℕ) : lgetD_k l i d = l.getD i d := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ m => exact ih m

theorem max_k_eq (a b : ℕ) : max_k a b = max a b := by
  simp only [max_k, brec_eq_ite, Nat.ble_eq]
  split_ifs with h <;> omega

theorem insertNat_k_eq (a : ℕ) (l : List ℕ) : insertNat_k a l = Key.insertBy Nat.ble a l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    change Bool.rec (motive := fun _ => List ℕ) (b :: insertNat_k a l) (a :: b :: l)
      (Nat.ble a b) = _
    rw [ih, Key.insertBy]
    cases Nat.ble a b <;> rfl

theorem sortNat_k_eq (l : List ℕ) : sortNat_k l = Key.sortBy Nat.ble l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change insertNat_k a (sortNat_k l) = _
    rw [insertNat_k_eq, ih, Key.sortBy]

theorem map_insertBy {γ : Type} (f : γ → ℕ) (a : γ) (l : List γ) :
    (Key.insertBy (fun x y => Nat.ble (f x) (f y)) a l).map f =
      Key.insertBy Nat.ble (f a) (l.map f) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [Key.insertBy, List.map_cons]
    split_ifs <;> simp [ih]

theorem map_sortBy {γ : Type} (f : γ → ℕ) (l : List γ) :
    (Key.sortBy (fun x y => Nat.ble (f x) (f y)) l).map f = Key.sortBy Nat.ble (l.map f) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [Key.sortBy, List.map_cons, map_insertBy, ih]

namespace Endpoint

theorem code_k_eq (e : Endpoint) : e.code_k = e.code := by
  cases e with
  | p => rfl
  | ell => rfl
  | slot i => rfl
  | x c =>
    change Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (2 * c + 1) 0
      (Nat.beq c 1)) 1 (Nat.beq c 0) = _
    simp only [brec_eq_ite, Nat.beq_eq, code]

theorem isSlot_k_eq (i : ℕ) (e : Endpoint) : e.isSlot_k i = e.isSlot i := by
  cases e <;> rfl

theorem isX_k_eq (e : Endpoint) : e.isX_k = e.isX := by
  cases e <;> rfl

theorem shift_k_eq (s t : ℕ) (e : Endpoint) : e.shift_k s t = e.shift s t := by
  cases e <;> rfl

theorem dropSlots_k_eq (i j : ℕ) (e : Endpoint) : e.dropSlots_k i j = e.dropSlots i j := by
  cases e with
  | slot k =>
    change slot (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (k - 2) (k - 1)
      (Nat.blt k j)) k (Nat.blt k i)) = _
    simp only [brec_eq_ite, Nat.blt_eq, dropSlots]
  | _ => rfl

theorem swapX_k_eq (e : Endpoint) : e.swapX_k = e.swapX := by
  cases e with
  | x c =>
    change Bool.rec (motive := fun _ => Endpoint) (Bool.rec (motive := fun _ => Endpoint) (x c)
      (x 0) (Nat.beq c 1)) (x 1) (Nat.beq c 0) = _
    rcases c with _ | _ | c <;> rfl
  | _ => rfl

theorem permSlot_k_eq (σ : List ℕ) (e : Endpoint) : e.permSlot_k σ = e.permSlot σ := by
  cases e with
  | slot i => exact congrArg slot (lgetD_k_eq σ i i)
  | _ => rfl

theorem xBound_k_eq (e : Endpoint) : e.xBound_k = Key.xBound.bound e := by
  cases e <;> rfl

end Endpoint

namespace Edge

theorem code_k_eq (e : Edge) : e.code_k = e.code := by
  simp only [code_k, codeOf, Endpoint.code_k_eq, code]
  rfl

theorem orientCode_k_eq (e : Edge) : e.orientCode_k = e.orient.code := by
  simp only [orientCode_k, codeOf, Endpoint.code_k_eq, brec_eq_ite, Nat.blt_eq, orient]
  split_ifs <;> rfl

theorem hasX_k_eq (e : Edge) : e.hasX_k = e.hasX := by
  simp only [hasX_k, Endpoint.isX_k_eq, hasX]

theorem mapEnds_k_eq (f : Endpoint → Endpoint) (e : Edge) : e.mapEnds_k f = e.mapEnds f := rfl

end Edge

namespace Key

theorem foldDigits_k_eq (acc : ℕ) (ds : List ℕ) :
    foldDigits_k acc ds = ds.foldl (fun acc d => acc * packBase + d) acc := by
  induction ds generalizing acc with
  | nil => rfl
  | cons d ds ih => exact ih _

theorem foldCodes_k_cons (acc c : ℕ) (cs : List ℕ) :
    foldCodes_k acc (c :: cs) = foldCodes_k (Nat.add (Nat.mul acc 16777216) c) cs := rfl

theorem foldCodes_k_eq (acc : ℕ) (es : List Edge) :
    foldCodes_k acc (es.map Edge.code) =
      (es.flatMap Edge.digits).foldl (fun acc d => acc * packBase + d) acc := by
  induction es generalizing acc with
  | nil => rfl
  | cons e es ih =>
    have h : Nat.add (Nat.mul acc 16777216) e.code =
        e.digits.foldl (fun acc d => acc * packBase + d) acc := by
      simp only [Edge.digits, Edge.code, List.foldl_cons, List.foldl_nil, packBase, Nat.add_eq,
        Nat.mul_eq]
      ring
    rw [List.flatMap_cons, List.foldl_append, ← ih, List.map_cons, foldCodes_k_cons, h]

theorem packWith_k_eq (k : Key) (ts : List ℕ) (es : List Edge) :
    packWith_k k ts (es.map Edge.code) = ({ k with traces := ts, edges := es } : Key).pack := by
  simp only [packWith_k, foldCodes_k_eq, foldDigits_k_eq, length_k_eq, List.length_map, pack,
    packDigits, digits, List.foldl_append, List.foldl_cons, List.cons_append, List.nil_append]
  rfl

theorem pack_k_eq (k : Key) : k.pack_k = k.pack := by
  have h : (Edge.code_k : Edge → ℕ) = Edge.code := funext Edge.code_k_eq
  rw [pack_k, lmap_k_eq, h, packWith_k_eq]

theorem sortedPack_k_eq (k : Key) : k.sortedPack_k = k.sortAll.pack := by
  have h : sortNat_k (lmap_k Edge.orientCode_k k.edges) =
      (sortBy (fun e f => Nat.ble e.code f.code) (k.edges.map Edge.orient)).map Edge.code := by
    rw [sortNat_k_eq, map_sortBy, List.map_map, lmap_k_eq]
    congr 1
    exact List.map_congr_left fun e _ => Edge.orientCode_k_eq e
  rw [sortedPack_k, h, packWith_k_eq, sortNat_k_eq]
  rfl

theorem hasX_k_eq (k : Key) : k.hasX_k = k.hasX := by
  simp only [hasX_k, hasX]
  induction k.edges with
  | nil => rfl
  | cons e es ih =>
    change (e.hasX_k || _) = _
    rw [ih, Edge.hasX_k_eq, List.any_cons]

theorem isXTrace_k_eq (e : Edge) :
    e.isXTrace_k = (e.pow == 0 && e.u.isX && e.u == e.v) := by
  have h1 : Nat.beq e.pow 0 = (e.pow == 0) := by
    rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]
  have h2 : Nat.beq e.u.code e.v.code = (e.u == e.v) := by
    rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq, Endpoint.code_injective.eq_iff]
  simp only [Edge.isXTrace_k, Endpoint.isX_k_eq, Endpoint.code_k_eq, h1, h2]

theorem hasXTrace_k_eq (k : Key) : k.hasXTrace_k = k.hasXTrace := by
  simp only [hasXTrace_k, hasXTrace]
  induction k.edges with
  | nil => rfl
  | cons e es ih =>
    change (e.isXTrace_k || _) = _
    rw [ih, isXTrace_k_eq, List.any_cons]

theorem xBound_k_eq (k : Key) : k.xBound_k = k.xBound := by
  simp only [xBound_k, xBound]
  induction k.edges with
  | nil => rfl
  | cons e es ih =>
    change max_k _ (max_k e.u.xBound_k e.v.xBound_k) = _
    rw [ih, max_k_eq, max_k_eq, Endpoint.xBound_k_eq, Endpoint.xBound_k_eq, List.foldr_cons]

theorem mul_k_eq (s t : Key) : s.mul_k t = s.mul t := by
  have h : Edge.mapEnds_k (Endpoint.shift_k s.rank s.xBound_k) =
      Edge.mapEnds (Endpoint.shift s.rank s.xBound) := by
    funext e
    simp only [Edge.mapEnds_k, Edge.mapEnds, Endpoint.shift_k_eq, xBound_k_eq]
  simp only [mul_k, mul, lappend_k_eq, lmap_k_eq, h]
  rfl

theorem permSlots_k_eq (σ : List ℕ) (k : Key) : k.permSlots_k σ = k.permSlots σ := by
  have h : Edge.mapEnds_k (Endpoint.permSlot_k σ) = Edge.mapEnds (Endpoint.permSlot σ) := by
    funext e
    simp only [Edge.mapEnds_k, Edge.mapEnds, Endpoint.permSlot_k_eq]
  simp only [permSlots_k, permSlots, lmap_k_eq, h]

theorem contract_k_eq (i j : ℕ) (k : Key) : k.contract_k i j = k.contract i j := by
  have hI : ∀ m, atSlot_k m = fun e : Edge => e.u.isSlot m || e.v.isSlot m := by
    intro m; funext e; simp only [atSlot_k, Endpoint.isSlot_k_eq]
  have hD : Edge.mapEnds_k (Endpoint.dropSlots_k i j) = Edge.mapEnds (Endpoint.dropSlots i j) := by
    funext e
    simp only [Edge.mapEnds_k, Edge.mapEnds, Endpoint.dropSlots_k_eq]
  have hO : ∀ (e : Edge) m, other_k e m = if e.u.isSlot m then e.v else e.u := by
    intro e m
    simp only [other_k, brec_eq_ite, Endpoint.isSlot_k_eq]
  simp only [contract_k, contract, lfind_k_eq, lfilter_k_eq, lmap_k_eq, hI, hD, hO, orec_eq,
    brec_eq_ite, Nat.sub_eq, Nat.add_eq]
  generalize List.find? (fun e => Endpoint.isSlot i e.u || Endpoint.isSlot i e.v) k.edges = oi
  generalize List.find? (fun e => Endpoint.isSlot j e.u || Endpoint.isSlot j e.v) k.edges = oj
  cases oi <;> cases oj <;> rfl

theorem contractPairs_k_eq (n : ℕ) (k : Key) : k.contractPairs_k n = k.contractPairs n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    change contractPairs_k n (contract_k 0 (n + 1) k) = _
    rw [ih, contract_k_eq, contractPairs]

theorem reduceTraces_k_eq (ts : List ℕ) : reduceTraces_k ts = reduceTraces ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    change Bool.rec (motive := fun _ => ℤ × List ℕ) (Bool.rec (motive := fun _ => ℤ × List ℕ)
      (Bool.rec (motive := fun _ => ℤ × List ℕ) ((reduceTraces_k ts).1, t :: (reduceTraces_k ts).2)
        (reduceTraces_k ts) (Nat.beq t 2)) (0, (reduceTraces_k ts).2) (Nat.beq t 1))
      (Int.mul 5 (reduceTraces_k ts).1, (reduceTraces_k ts).2) (Nat.beq t 0) = _
    simp only [brec_eq_ite, Nat.beq_eq, ih, reduceTraces]
    rfl

theorem normalizePack_k_eq (k : Key) : k.normalizePack_k = k.normalize.pack := by
  have hs : sortedPack_k ⟨k.rank, k.gPow, k.wPow, k.zPow, k.traces,
      lmap_k (Edge.mapEnds_k Endpoint.swapX_k) k.edges⟩ = k.swapX.sortAll.pack := by
    rw [sortedPack_k_eq]
    congr 2
    simp only [swapX, lmap_k_eq]
    congr 1
    exact List.map_congr_left fun e _ => by
      simp only [Edge.mapEnds_k, Edge.mapEnds, Endpoint.swapX_k_eq]
  simp only [normalizePack_k, brec_eq_ite, Nat.blt_eq, hs, sortedPack_k_eq, hasX_k_eq, normalize]
  split_ifs <;> rfl

theorem canonPack_k_eq (k : Key) : k.canonPack_k = k.canonPack := by
  simp only [canonPack_k, brec_eq_ite, hasXTrace_k_eq, canonPack, canon, reduce,
    reduceTraces_k_eq]
  split_ifs <;> simp only [normalizePack_k_eq]

theorem allLt_k_eq (l : List ℕ) : allLt_k l = l.all fun d => Nat.blt d packBase := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    change (Nat.blt d 256 && allLt_k l) = _
    rw [ih, List.all_cons]

theorem boundedB_k_eq (k : Key) : k.boundedB_k = k.boundedB := by
  have he : ∀ es : List Edge, List.rec (motive := fun _ => Bool) true
      (fun e _ ih => Bool.and (allLt_k [e.u.code_k, e.v.code_k, e.pow]) ih) es =
      (es.flatMap Edge.digits).all fun d => Nat.blt d packBase := by
    intro es
    induction es with
    | nil => rfl
    | cons e es ih =>
      change (allLt_k [e.u.code_k, e.v.code_k, e.pow] && _) = _
      rw [ih, allLt_k_eq, List.flatMap_cons, List.all_append, Endpoint.code_k_eq,
        Endpoint.code_k_eq]
      rfl
  rw [boundedB_k, he]
  simp only [allLt_k_eq, length_k_eq, boundedB, digits, List.all_append,
    List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc]

theorem reduce_k_eq (k : Key) : k.reduce_k = k.reduce := by
  simp only [reduce_k, brec_eq_ite, hasXTrace_k_eq, reduceTraces_k_eq, reduce]

theorem term_k_eq (c : ℤ) (k : Key) : term_k c k = term c k := by
  simp only [term_k, brec_eq_ite, Int.beq'_eq, reduce_k_eq, normalizePack_k_eq, boundedB_k_eq,
    term, Int.mul_def]

end Key

namespace Poly

theorem merge_k_eq (p q : Poly) : merge_k p q = merge p q := by
  induction p generalizing q with
  | nil => rfl
  | cons ac p ih =>
    obtain ⟨a, c⟩ := ac
    have hp : (fun q => merge_k p q) = merge p := funext ih
    induction q with
    | nil => rfl
    | cons bd q ihq =>
      obtain ⟨b, d⟩ := bd
      change Bool.rec (motive := fun _ => Poly) (Bool.rec (motive := fun _ => Poly)
        (Bool.rec (motive := fun _ => Poly) ((a, Int.add c d) :: merge_k p q) (merge_k p q)
          (Int.beq' (Int.add c d) 0)) ((b, d) :: merge_k ((a, c) :: p) q) (Nat.blt b a))
        ((a, c) :: merge_k p ((b, d) :: q)) (Nat.blt a b) = _
      simp only [ihq, brec_eq_ite, Nat.blt_eq, Int.beq'_eq, ih, merge, mergeAux, Int.add_def]

theorem mergePairsAux_k_eq (l : List Poly) :
    ∀ o, mergePairsAux_k l o =
      match o with | none => mergePairs l | some a => mergePairs (a :: l) := by
  induction l with
  | nil => intro o; cases o <;> rfl
  | cons x l ih =>
    intro o
    cases o with
    | none => exact (ih (some x))
    | some a =>
      change merge_k a x :: mergePairsAux_k l none = _
      rw [ih none, merge_k_eq]
      rfl

theorem mergeAll_k_eq (l : List Poly) : mergeAll_k l = mergeAll l := by
  have h : ∀ n (l : List Poly), Nat.rec (motive := fun _ => List Poly → List Poly) (fun l => l)
      (fun _ ih l => ih (mergePairsAux_k l none)) n l = mergeAllAux n l := by
    intro n
    induction n with
    | zero => intro l; rfl
    | succ n ih =>
      intro l
      change Nat.rec (motive := fun _ => List Poly → List Poly) (fun l => l)
        (fun _ ih l => ih (mergePairsAux_k l none)) n (mergePairsAux_k l none) = _
      rw [ih, mergePairsAux_k_eq]
      rfl
  simp only [mergeAll_k, mergeAll, h, length_k_eq]
  cases mergeAllAux l.length l <;> rfl

end Poly

end Agreement

end OnePhaseDimension.Certificate
