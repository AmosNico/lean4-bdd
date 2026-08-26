module

public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Sum.Order
public import Bdd.Basic

import Bdd.Collect

open Pointer (Reachable)
open Bdd
open RawBdd
open RawPointer

namespace Reduce

inductive RawPointer.LE : RawPointer → RawPointer → Prop where
  | terminal b b' : b ≤ b' → LE (terminal b) (terminal b')
  | node n n' : n ≤ n' → LE (node n) (node n')
  | mixed b n : LE (terminal b) (node n)

@[no_expose]
public instance : LE RawPointer where
  le := RawPointer.LE

@[simp]
public lemma RawPointer.terminal_le_terminal {b b'} : terminal b ≤ terminal b' ↔ b ≤ b' :=
  ⟨by rintro ⟨_, _, h⟩; exact h, fun h ↦ .terminal b b' h⟩

@[simp]
public lemma RawPointer.terminal_le_node {b n} : terminal b ≤ node n :=
  LE.mixed b n

@[simp]
public lemma RawPointer.node_le_node {n n'} : node n ≤ node n' ↔ n ≤ n' :=
  ⟨by rintro ⟨⟩; assumption, fun h ↦ .node n n' h⟩

@[simp]
public lemma RawPointer.not_node_le_terminal {n b} : ¬ node n ≤ terminal b := by
  rintro ⟨⟩

public lemma RawPointer.le_trans (p q r : RawPointer) (h1 : p ≤ q) (h2 : q ≤ r) : p ≤ r := by
  cases h1 <;> cases h2
  case terminal.terminal b1 b2 h1 b3 h2 => exact .terminal b1 b3 (.trans h1 h2)
  case terminal.mixed b1 b2 h1 n3 => exact .mixed b1 n3
  case node.node n1 n2 h1 n3 h2 => exact .node n1 n3 (.trans h1 h2)
  case mixed.node b1 n2 n3 h2 => exact .mixed b1 n3

public lemma RawPointer.le_refl : ∀ (p : RawPointer), p ≤ p
  | .terminal b => .terminal b b (Bool.le_refl b)
  | .node n => .node n n (Nat.le_refl n)

public lemma RawPointer.le_total : ∀ (p q : RawPointer), p ≤ q ∨ q ≤ p
  | .terminal b, .terminal b' =>
    match Bool.le_total b b' with
    | .inl h => .inl (.terminal b b' h)
    | .inr h => .inr (.terminal b' b h)
  | .terminal b, .node n' => .inl (.mixed b n')
  | .node n, .node n' =>
    match Nat.le_total n n' with
    | .inl h => .inl (.node n n' h)
    | .inr h => .inr (.node n' n h)
  | .node n, .terminal b' => .inr (.mixed b' n)

public lemma RawPointer.le_antisymm (p q : RawPointer) (h1 : p ≤ q) (h2 : q ≤ p) : p = q := by
    cases h1 <;> cases h2 <;> grind only

public instance : LinearOrder RawPointer where
  le_trans := RawPointer.le_trans
  le_refl := RawPointer.le_refl
  le_total := RawPointer.le_total
  le_antisymm := RawPointer.le_antisymm
  toDecidableLE
    | .terminal b, .terminal b' => decidable_of_iff' _ RawPointer.terminal_le_terminal
    | .terminal b, .node n' => Decidable.isTrue RawPointer.terminal_le_node
    | .node n, .terminal b' => Decidable.isFalse RawPointer.not_node_le_terminal
    | .node n, .node n' => decidable_of_iff' _ RawPointer.node_le_node

public abbrev KeyPair := Lex (RawPointer × RawPointer)

public structure State (n) (m) where
  size : Nat
  heap : Vector (RawNode n) size
  ids  : Vector (Option RawPointer) m

public structure ProvedState (n m : Nat) where
  state : State n m
  hh    : ∀ k : Fin state.size, state.heap[k].Bounded k

def initial (n m : Nat) : State n m :=
  ⟨0, Vector.emptyWithCapacity 0, Vector.replicate m none⟩

public def provedStateInitial (n m : Nat) : ProvedState n m where
  state := ⟨0, Vector.emptyWithCapacity 0, Vector.replicate m none⟩
  hh := fun k => k.elim0

@[expose]
public def get_id {n m : Nat} (ps : ProvedState n m) (p : Pointer m)
    (h : ∀ j, p = .node j → (ps.state.ids[j]).isSome) : RawPointer :=
  match p with
  | .terminal b => .terminal b
  | .node j     => (ps.state.ids[j]).get (h j rfl)

/-- Record that input node `j` maps to output pointer `p`. -/
@[expose]
public def set_id {n m : Nat} (ps : ProvedState n m) (j : Fin m) (p : RawPointer) : ProvedState n m :=
  { state := { size := ps.state.size, heap := ps.state.heap, ids := ps.state.ids.set j (some p) },
    hh    := ps.hh }

public lemma set_id_self {n m : Nat} (ps : ProvedState n m) (j : Fin m) (p : RawPointer) :
    (set_id ps j p).state.ids[j] = some p := by
  show (ps.state.ids.set j (some p))[j] = some p
  simp [Vector.getElem_set_self]

public lemma set_id_ne {n m : Nat} (ps : ProvedState n m) (j k : Fin m) (p : RawPointer)
    (h : k ≠ j) : (set_id ps j p).state.ids[k] = ps.state.ids[k] := by
  show (ps.state.ids.set j (some p))[k] = ps.state.ids[k]
  exact Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne h.symm)

@[expose]
public def push_node {n m : Nat} (ps : ProvedState n m) (N : RawNode n)
    (hN : N.Bounded ps.state.size) : ProvedState n m × RawPointer :=
  let hh' : ∀ k : Fin (ps.state.size + 1), (ps.state.heap.push N)[k].Bounded k := fun k => by
    by_cases hlt : k.1 < ps.state.size
    · simp only [Fin.getElem_fin, Vector.getElem_push_lt hlt]
      exact ps.hh ⟨k.1, hlt⟩
    · have hk : k.1 = ps.state.size := by omega
      simp only [Fin.getElem_fin, show k.1 = ps.state.size from hk,
                 Vector.getElem_push_eq]
      exact hN
  ⟨⟨{ size := ps.state.size + 1, heap := ps.state.heap.push N, ids := ps.state.ids }, hh'⟩,
   .node ps.state.size⟩

/-- Injectivity of `toTree` for sub-BDDs sharing the same heap, given heap index-injectivity. -/
lemma structural_canonical_key {n s : Nat} {M : Vector (Node n s) s}
    (node_inj : ∀ (kp kq : Fin s),
        M[kp].var = M[kq].var → M[kp].low = M[kq].low → M[kp].high = M[kq].high → kp = kq) :
    ∀ (P Q : OBdd n s), P.1.heap = M → Q.1.heap = M →
      OBdd.toTree P = OBdd.toTree Q → P.1.root = Q.1.root := by
  intro P
  induction P using OBdd.init_inductionOn with
  | base b O h1 h2 =>
    intro Q hP_heap hQ_heap htree_eq
    rw [OBdd.toTree_terminal h2] at htree_eq
    cases hQ : Q.1.root with
    | terminal bq =>
      rw [OBdd.toTree_terminal hQ] at htree_eq
      grind only
    | node jq =>
      rw [OBdd.toTree_node hQ] at htree_eq
      exact absurd htree_eq (by simp)
  | step P' jp h1 hP' ih_low ih_high =>
    intro Q hP_heap hQ_heap htree_eq
    cases hQ : Q.1.root with
    | terminal bq =>
      rw [← OBdd.toTree_eq_leaf_iff_terminal] at hQ
      grind only [OBdd.toTree_node hP']
    | node jq =>
      have hQ_ord : Bdd.Ordered ⟨Q.1.heap, Pointer.node jq⟩ := by
        rcases Q with ⟨⟨qheap, qroot⟩, qord⟩; simp only at hQ; subst hQ; exact qord
      rw [OBdd.toTree_node hP', OBdd.toTree_node hQ] at htree_eq
      injection htree_eq with hvar hlo_tree hhi_tree
      specialize ih_low (Q.low hQ) (by simp [hP_heap]) (by simp [hQ_heap]) hlo_tree
      specialize ih_high (Q.high hQ) (by simp [hP_heap]) (by simp [hQ_heap]) hhi_tree
      simp [OBdd.low_root_eq_low] at ih_low
      simp [OBdd.high_root_eq_high] at ih_high
      rw [hP_heap, hQ_heap] at ih_high ih_low hvar
      specialize node_inj jp jq hvar ih_low ih_high
      rw [hP', node_inj]

/-- In a structurally canonical heap (no two positions have the same raw node),
    any ordered BDD is reduced. -/
public lemma structural_canonical_reduced {n s : Nat}
    {v : Vector (RawNode n) s} {hh : ∀ k : Fin s, v[k].Bounded k}
    (hsc : ∀ k1 k2 : Fin s, v[k1] = v[k2] → k1 = k2)
    {root : Pointer s}
    (hord : Bdd.Ordered ⟨cook_heap v hh, root⟩)
    (hnored : Bdd.NoRedundancy ⟨cook_heap v hh, root⟩) :
    OBdd.Reduced ⟨⟨cook_heap v hh, root⟩, hord⟩ := by
  let O : OBdd n s := ⟨⟨cook_heap v hh, root⟩, hord⟩
  -- Helper: cook_heap nodes relate back to raw nodes
  have cook_heap_eq : ∀ k : Fin s, (cook_heap v hh)[k] = v[k].cook (RawNode.bounded_of_le (hh k) (by omega)) := by
    intro k
    simp [cook_heap_eq, Fin.getElem_fin, Vector.getElem_ofFn]
  -- Helper: if cooked nodes at kp and kq are equal, then kp = kq
  have node_inj : ∀ (kp kq : Fin s),
      (cook_heap v hh)[kp].var  = (cook_heap v hh)[kq].var →
      (cook_heap v hh)[kp].low  = (cook_heap v hh)[kq].low →
      (cook_heap v hh)[kp].high = (cook_heap v hh)[kq].high →
      kp = kq := by
    intro kp kq hvar hlow hhigh
    apply hsc
    rw [cook_heap_eq kp, cook_heap_eq kq] at hvar hlow hhigh
    simp only [RawNode.cook_eq] at hvar hlow hhigh
    rw [cook_inj] at hlow hhigh
    rcases hkp : v[kp] with ⟨vap, lop, hip⟩
    rcases hkq : v[kq] with ⟨vaq, loq, hiq⟩
    simp only [hkp] at hvar hlow hhigh
    simp only [hkq] at hvar hlow hhigh
    subst hvar hlow hhigh
    rfl
  let M := cook_heap v hh
  have key : ∀ (P Q : OBdd n s), P.1.heap = M → Q.1.heap = M →
      OBdd.toTree P = OBdd.toTree Q → P.1.root = Q.1.root :=
    structural_canonical_key node_inj
  -- Now prove Reduced
  constructor
  · exact hnored
  · intro ⟨p, hp_reach⟩ ⟨q, hq_reach⟩ hsim
    -- hsim : SimilarRP O ⟨p, hp_reach⟩ ⟨q, hq_reach⟩
    -- = toTree of sub-BDD at p = toTree of sub-BDD at q
    show p = q
    have hop : Bdd.Ordered ⟨M, p⟩ :=
      O.ordered_of_reachable hp_reach
    have hoq : Bdd.Ordered ⟨M, q⟩ :=
      O.ordered_of_reachable hq_reach
    simp only [OBdd.similarRP_iff, OBdd.subBdd_eq] at hsim
    exact key ⟨⟨M, p⟩, hop⟩ ⟨⟨M, q⟩, hoq⟩ rfl rfl hsim

@[expose]
public def Invariant {n m : Nat} (O : OBdd n m) (ps : ProvedState n m) (i : Nat) : Prop :=
  -- Completeness
  (∀ (j : Fin m),
      i < O.1.heap[j].var.1 →
      Reachable O.1.heap O.1.root (.node j) →
      (ps.state.ids[j]).isSome) ∧
  -- Correctness
  ∀ (j : Fin m) (ptr : RawPointer),
      ps.state.ids[j] = some ptr →
      ∃ hj   : Bdd.Ordered ⟨O.1.heap, .node j⟩,
        ∃ hptr : ptr.Bounded ps.state.size,
          ∃ ho : Bdd.Ordered ⟨cook_heap ps.state.heap ps.hh, ptr.cook hptr⟩,
            OBdd.Reduced ⟨⟨cook_heap ps.state.heap ps.hh, ptr.cook hptr⟩, ho⟩ ∧
            ∀ I,
              OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, ptr.cook hptr⟩, ho⟩ I =
              OBdd.evaluate ⟨⟨O.1.heap, .node j⟩, hj⟩ I

public lemma inv_initial {n m : Nat} {O : OBdd n m} {i : Nat}
    (hi : ∀ j : Fin m, O.1.heap[j].var.1 ≤ i) :
    Invariant O (provedStateInitial n m) i :=
  ⟨fun j h _ => absurd h (Nat.not_lt.mpr (hi j)),
   fun j ptr h => by simp [provedStateInitial] at h⟩

public lemma Invariant.ids_isSome {n m : Nat} {O : OBdd n m} {ps : ProvedState n m}
    {i : Nat} (inv : Invariant O ps i)
    {j : Fin m}
    (hvar  : i < O.1.heap[j].var.1)
    (hreach : Reachable O.1.heap O.1.root (.node j)) :
    (ps.state.ids[j]).isSome :=
  inv.1 j hvar hreach

/-- When ids[j] = some (.inr k), the output node's var ≥ the input node's var. -/
@[expose]
public def VarInvariant {n m : Nat} (O : OBdd n m) (ps : ProvedState n m) : Prop :=
  ∀ (j : Fin m) (k : Fin ps.state.size),
    ps.state.ids[j] = some (node k.1) →
    O.1.heap[j].var.1 ≤ ps.state.heap[k].va.1

@[expose]
public def AllAbove {n m : Nat} (ps : ProvedState n m) (i : Nat) : Prop :=
  ∀ k : Fin ps.state.size, i < ps.state.heap[k].va.1

/-- The heap is injective: no two positions have the same raw node. -/
@[expose]
public def HeapInjective {n : Nat} (ps : ProvedState n m) : Prop :=
  ∀ k1 k2 : Fin ps.state.size, ps.state.heap[k1] = ps.state.heap[k2] → k1 = k2

public lemma varInvariant_initial {n m : Nat} {O : OBdd n m} :
    VarInvariant O (provedStateInitial n m) := by
  intro j k
  exact absurd k.isLt (by simp [provedStateInitial])

public lemma allAbove_initial {n m : Nat} {i : Nat} :
    AllAbove (provedStateInitial n m) i := by
  intro k
  exact absurd k.isLt (by simp [provedStateInitial])

public lemma heapInjective_initial {n m : Nat} :
    HeapInjective (provedStateInitial n m) := by
  intro k1
  exact absurd k1.isLt (by simp [provedStateInitial])

@[expose]
public def EntryCorrect {n m : Nat} (O : OBdd n m) (ps : ProvedState n m) (i : Nat)
    (entry : (RawPointer × RawPointer) × Fin m) : Prop :=
  Reachable O.1.heap O.1.root (.node entry.2) ∧
  O.1.heap[entry.2].var.1 = i ∧
  (∀ l, O.1.heap[entry.2].low = .node l → ps.state.ids[l] = some entry.1.1) ∧
  (∀ l, O.1.heap[entry.2].high = .node l → ps.state.ids[l] = some entry.1.2) ∧
  (∀ b, O.1.heap[entry.2].low = .terminal b → entry.1.1 = terminal b) ∧
  (∀ b, O.1.heap[entry.2].high = .terminal b → entry.1.2 = terminal b)

/-- The BDD obtained by pushing a fresh node for `entry` is ordered, reduced, and
    evaluates like the original sub-BDD at `entry.2`. -/
public abbrev NodePushedCorrectly {n m : Nat} (O : OBdd n m) (ps : ProvedState n m)
    (entry : (RawPointer × RawPointer) × Fin m)
    (hbound : entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size) : Prop :=
  let N    : RawNode n := ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩
  let hN   : N.Bounded ps.state.size := ⟨hbound.1, hbound.2⟩
  let ps₁  := (push_node ps N hN).1
  let ptr  := (push_node ps N hN).2
  let ps₂  := set_id ps₁ entry.2 ptr
  ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
  ∃ hp : ptr.Bounded ps₂.state.size,
  ∃ ho : Bdd.Ordered ⟨cook_heap ps₂.state.heap ps₂.hh, ptr.cook hp⟩,
    OBdd.Reduced ⟨⟨cook_heap ps₂.state.heap ps₂.hh, ptr.cook hp⟩, ho⟩ ∧
    ∀ I, OBdd.evaluate ⟨⟨cook_heap ps₂.state.heap ps₂.hh, ptr.cook hp⟩, ho⟩ I =
         OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I

/-- The current pointer `curptr` correctly represents the sub-BDD at `entry.2`. -/
public abbrev CurptrSemantic {n m : Nat} (O : OBdd n m) (ps : ProvedState n m)
    (curptr : RawPointer) (entry : (RawPointer × RawPointer) × Fin m) : Prop :=
  ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
  ∃ hp : curptr.Bounded ps.state.size,
  ∃ ho : Bdd.Ordered ⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩,
    OBdd.Reduced ⟨⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩, ho⟩ ∧
    ∀ I, OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩, ho⟩ I =
         OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I

end Reduce
