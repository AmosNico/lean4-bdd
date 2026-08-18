module

public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.DeriveFintype
import Init.Data.ToString.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Std.Data.HashSet.Lemmas
public import Bdd.Nary
public import Bdd.DecisionTree

public section

instance {α : Type u} [ToString α] : ToString (Vector α k) := ⟨fun v ↦ v.toList.toString⟩

/-- Pointer to a BDD node or terminal -/
inductive Pointer m where
  | terminal : Bool → Pointer _
  | node : Fin m → Pointer m
deriving Fintype, DecidableEq, Repr, Hashable

instance Pointer.instToString : ToString (Pointer m) := ⟨fun p =>
  match p with
  | .terminal true => "⊤"
  | .terminal false => "⊥"
  | .node j => "→" ++ toString j⟩

inductive Pointer.le : Pointer m → Pointer m → Prop where
  | terminal_le_terminal : b ≤ c → le (terminal b) (terminal c)
  | terminal_le_node : le (terminal b) (node j)
  | node_le_node : j ≤ i → le (node j) (node i)

instance Pointer.instLE : LE (Pointer m) := {le := Pointer.le}

instance Pointer.instDecidableLe : DecidableLE (Pointer m) :=
  fun p q ↦ match p with
  | terminal b => match q with
    | terminal c => match Bool.instDecidableLe b c with
      | isTrue ht => isTrue  (.terminal_le_terminal ht)
      | isFalse hf => isFalse (by intro contra; cases contra; contradiction)
    | node i => isTrue (.terminal_le_node)
  | node j => match q with
    | terminal c => isFalse (by intro contra; contradiction)
    | node i => match Fin.decLe j i with
      | isTrue ht => isTrue (.node_le_node ht)
      | isFalse hf => isFalse (by intro contra; cases contra; contradiction)

open Pointer

/-- BDD node -/
structure Node (n) (m) where
  var  : Fin n
  low  : Pointer m
  high : Pointer m
deriving DecidableEq, Repr

instance Node.instToString {n m} : ToString (Node n m) :=
  ⟨fun N => "⟨" ++ toString N.var ++ ", " ++ toString N.low ++ ", " ++ toString N.high ++ "⟩"⟩

/-- Raw BDD -/
structure Bdd n m where
  heap : Vector (Node n m) m
  root : Pointer m
deriving DecidableEq

instance Bdd.instToString {n m} : ToString (Bdd n m) :=
  ⟨fun B => "⟨" ++ toString B.heap ++ ", " ++ toString B.root  ++ "⟩"⟩

def Bdd.low {n m} (B : Bdd n m) {j} : B.root = node j → Bdd n m
  | _ => {heap := B.heap, root := B.heap[j].low}

lemma Bdd.low_eq {n m} {B : Bdd n m} {j} {h : B.root = node j} :
    B.low h = {heap := B.heap, root := B.heap[j].low} := (rfl)

def Bdd.high {n m} (B : Bdd n m) {j} : B.root = node j → Bdd n m
  | _ => {heap := B.heap, root := B.heap[j].high}

lemma Bdd.high_eq {n m} {B : Bdd n m} {j} {h : B.root = node j} :
    B.high h = {heap := B.heap, root := B.heap[j].high} := (rfl)

open Bdd
-- example : Bdd n 0 := ⟨Vector.emptyWithCapacity 0, .terminal true⟩

-- example : Bdd 1 1 := ⟨Vector.singleton ⟨0, .node 0, .node 0⟩, .node 0⟩

inductive Edge (M : Vector (Node n m) m) : Pointer m → Pointer m → Prop where
  | low {j}  : Edge M (node j) M[j].low
  | high {j} : Edge M (node j) M[j].high

lemma edge_iff {n m} {M : Vector (Node n m) m} {p q} :
    Edge M p q ↔ ∃ j, p = node j ∧ (q = M[j].low ∨ q = M[j].high) := by
  grind only [Edge]

/-- Terminals have no outgoing edges. -/
lemma not_terminal_edge {q} : ¬ Edge w (terminal b) q := by
  intro contra
  contradiction

lemma Bdd.edge_low {n m} (B : Bdd n m) {j} (h : B.root = node j) :
    Edge B.heap B.root (B.low h).root := by
  simp only [low, h]
  exact Edge.low

lemma Bdd.edge_high {n m} (B : Bdd n m) {j} (h : B.root = node j) :
    Edge B.heap B.root (B.high h).root := by
  simp only [high, h]
  exact Edge.high

--FIXME: Maybe use WithTop (Fin n) instead of Fin n.succ
def Pointer.toVar (M : Vector (Node n m) m) : Pointer m → Fin n.succ
  | terminal _ => Fin.last n
  | node j     => ⟨M[j].var.1, .trans M[j].var.2 (Nat.lt_add_one n)⟩

@[simp]
lemma Pointer.toVar_terminal {n m} (w : Vector (Node n m) m) : toVar w (terminal b) = ⟨n, Nat.lt_add_one n⟩ := (rfl)

@[simp]
lemma Pointer.toVar_node {n m} (w : Vector (Node n m) m) {j} : (toVar w (node j)).1 = w[j].var.1 := (rfl)

lemma Pointer.toVar_heap_set {i j : Fin n} : i ≠ j → (toVar (M.set i N) (node j)).1 = (toVar M (node j)).1 := by
  intro neq
  simp only [Nat.succ_eq_add_one, toVar_node]
  congr 2
  apply Vector.getElem_set_ne
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  simp_all

lemma Pointer.toVar_heap_set' {i j : Fin n} : i ≠ j → (toVar (M.set i N) (node j)) = (toVar M (node j)) := by
  intro neq
  simp only [Nat.succ_eq_add_one]
  apply Fin.eq_of_val_eq
  exact toVar_heap_set neq

@[simp]
def Pointer.MayPrecede (M : Vector (Node n m) m) (p q : Pointer m) := toVar M p < toVar M q

/-- Terminals must not precede other pointers. -/
@[simp, grind .]
lemma Pointer.not_terminal_mayPrecede : ¬ MayPrecede M (terminal b) p := by
  cases p with
  | terminal _ => simp [MayPrecede]
  | node     j => exact not_lt.mpr (Fin.le_last _)

/-- Non-terminals may precede terminals. -/
lemma Pointer.MayPrecede_node_terminal {n m} (w : Vector (Node n m) m) {j} : MayPrecede w (node j) (terminal b) := by
  simp only [MayPrecede, Nat.succ_eq_add_one, toVar, Fin.getElem_fin]
  refine Fin.mk_lt_of_lt_val ?_
  simp only [Fin.val_last, Fin.is_lt]

def Pointer.Reachable {n m} (v : Vector (Node n m) m) := Relation.ReflTransGen (Edge v)

namespace Pointer.Reachable

variable {n m} {v : Vector (Node n m) m}

lemma refl {p} : Reachable v p p :=
  Relation.ReflTransGen.refl

@[trans]
lemma trans {p q r} : Reachable v p q → Reachable v q r → Reachable v p r :=
  Relation.ReflTransGen.trans

lemma ofEdge {p q} : Edge v p q → Reachable v p q :=
  Relation.ReflTransGen.single

lemma cons {p q r} : Edge v p q → Reachable v q r → Reachable v p r :=
  fun e r => trans (ofEdge e ) r

lemma snoc {p q r} : Reachable v p q → Edge v q r → Reachable v p r :=
  Relation.ReflTransGen.tail

lemma eq_of_eq_edge {n} {v : Vector (Node n m) m} {n'} {v' : Vector (Node n' m) m} :
    Edge v = Edge v' → Reachable v = Reachable v' := by
  grind only [Reachable]

@[elab_as_elim]
lemma cases_snoc {p} {motive : (q : _) → Reachable v p q → Prop} {q} (h1 : Reachable v p q)
    (refl : motive p .refl)
    (snoc : ∀ {q r} (h1 : Reachable v p q) (h2 : Edge v q r), motive r (.snoc h1 h2)) :
    motive q h1 :=
  Relation.ReflTransGen.casesOn h1 refl snoc

@[cases_eliminator]
lemma cases_cons {q} {motive : (p : _) → Reachable v p q → Prop} {p} (h1 : Reachable v p q)
    (refl : motive q .refl)
    (cons : ∀ {p r} (h1 : Edge v r p) (h2 : Reachable v p q), motive r (.cons h1 h2)) :
    motive p h1 := by
  apply Relation.ReflTransGen.cases_head at h1
  rcases h1 with (rfl | ⟨r, e, r⟩)
  · exact refl
  · exact cons e r

@[induction_eliminator]
lemma recOn {p} {motive : (q : _) → Reachable v p q → Prop} {q} (h1 : Reachable v p q)
    (refl : motive p .refl)
    (snoc : ∀ {q r} (h1 : Reachable v p q) (h2 : Edge v q r),
      motive q h1 → motive r (.snoc h1 h2)) :
    motive q h1 :=
  Relation.ReflTransGen.recOn h1 refl snoc

@[elab_as_elim]
lemma recOn' {q} {motive : (p : _) → Reachable v p q → Prop} {p} (h1 : Reachable v p q)
    (refl : motive q .refl)
    (cons : ∀ {p r} (h1 : Edge v r p) (h2 : Reachable v p q),
      motive p h2 → motive r (.cons h1 h2)) :
    motive p h1 :=
  Relation.ReflTransGen.head_induction_on h1 refl cons

@[simp]
lemma terminal_iff {b} {q : Pointer m} : Reachable v (terminal b) q ↔ q = terminal b := by
  constructor
  · intro hr
    induction hr with
    | refl => rfl
    | snoc => grind only [not_terminal_edge]
  · grind only [refl]

end Pointer.Reachable

@[simp]
lemma Bdd.reachable_low {n m} {B : Bdd n m} {j} (h : B.root = node j) :
    Reachable B.heap B.root B.heap[j].low :=
  Reachable.ofEdge (B.edge_low h)

@[simp]
lemma Bdd.reachable_high {n m} {B : Bdd n m} {j} (h : B.root = node j) :
    Reachable B.heap B.root B.heap[j].high :=
  Reachable.ofEdge (B.edge_high h)

/-- `B.RelevantPointer` is the subtype of pointers reachable from `B.root`. -/
abbrev Bdd.RelevantPointer {n m} (B : Bdd n m) := { q // Reachable B.heap B.root q}

def Bdd.Relevant {n m} (B : Bdd n m) (p : Pointer m) :=
  Reachable B.heap B.root p

lemma Bdd.relevant_iff_reachable {n m} {B : Bdd n m} {p : Pointer m} :
    B.Relevant p ↔ Reachable B.heap B.root p := by rfl

lemma Bdd.relevant_root {n m} (B : Bdd n m) : B.Relevant B.root := by
  simp only [relevant_iff_reachable, Reachable.refl]

private instance Bdd.instDecidableEqRelevantPointer : DecidableEq (Bdd.RelevantPointer B) :=
  fun _ _ ↦ decidable_of_iff _ (symm Subtype.ext_iff)

private def Bdd.toRelevantPointer {n m} (B : Bdd n m) : B.RelevantPointer :=
  ⟨B.root, Relation.ReflTransGen.refl⟩

/-- The `Edge` relation lifted to `RelevantPointer`s. -/
@[simp]
private abbrev Bdd.RelevantEdge (B : Bdd n m) (p q : B.RelevantPointer) := Edge B.heap p.1 q.1

private lemma Bdd.relevantEdge_of_edge_of_reachable  {B : Bdd n m}
    (e : Edge B.heap p q) (hp : Reachable B.heap B.root p) :
  RelevantEdge B ⟨p, hp⟩ ⟨q, .snoc hp e⟩ := e

def Bdd.MayPrecede (B : Bdd n m) (p q : Pointer m) :=
  toVar B.heap p < toVar B.heap q

lemma Bdd.mayPrecede_iff {n m} {B : Bdd n m} {p q} :
    B.MayPrecede p q ↔ ∃ j, p = node j ∧ ∀ j', q = node j' → B.heap[j].var < B.heap[j'].var := by
  simp only [MayPrecede, toVar]
  split
  all_goals split
  all_goals grind only [= Lean.Grind.toInt_fin, usr Fin.val_last]

lemma Bdd.mayPrecede_eq_of_heap_eq {n m} {B1 B2 : Bdd n m} :
    B1.heap = B2.heap → B1.MayPrecede = B2.MayPrecede := by
  grind only [MayPrecede]

@[simp]
lemma Bdd.mayPrecede_node {n m} {B : Bdd n m} {j j'} :
    B.MayPrecede (node j) (node j') ↔ B.heap[j].var < B.heap[j'].var := by
  grind only [mayPrecede_iff]

/-- A BDD is `Ordered` if all edges relevant from the root respect the variable ordering. -/
def Bdd.Ordered {n m} (B : Bdd n m) :=
  ∀ p q, Reachable B.heap B.root p → Edge B.heap p q → B.MayPrecede p q

lemma Bdd.ordered_iff {n m} {B : Bdd n m} : B.Ordered ↔
    ∀ p q, Reachable B.heap B.root p → Edge B.heap p q → B.MayPrecede p q := by rfl

lemma Bdd.ordered_iff' {n m} {B : Bdd n m} : B.Ordered ↔
    ∀ p q, Reachable B.heap B.root p → Edge B.heap p q → toVar B.heap p < toVar B.heap q := by
  simp only [ordered_iff, MayPrecede]

lemma Bdd.no_self_edge_of_ordered {n m} {B : Bdd n m} {p : Pointer m} :
    B.Ordered → B.Relevant p → ¬ Edge B.heap p p := by
  grind only [ordered_iff', relevant_iff_reachable]

/-- Terminals induce `Ordered` BDDs. -/
lemma Bdd.ordered_of_terminal {B : Bdd n m} : B.root = .terminal b → B.Ordered := by
  grind only [ordered_iff, Reachable.terminal_iff, not_terminal_edge]

structure OBdd (n m : ℕ) where
  bdd : Bdd n m
  ordered : bdd.Ordered

@[simp]
lemma OBdd.mk_eq_self {n m} {O : OBdd n m} {h} : OBdd.mk ⟨O.bdd.heap, O.bdd.root⟩ h = O := (rfl)

@[simp]
lemma OBdd.eq_iff_bdd_eq {n m : ℕ} {O U : OBdd n m} :
    O = U ↔ O.bdd.heap = U.bdd.heap ∧ O.bdd.root = U.bdd.root  := by
  grind only [OBdd, Bdd]

@[expose]
def OEdge (O U : OBdd n m) := O.1.heap = U.1.heap ∧ Edge O.1.heap O.1.root U.1.root

def Bdd.var {n m} (B : Bdd n m) : Fin n.succ := B.root.toVar B.heap

lemma Bdd.var_eq {n m} (B : Bdd n m) : B.var = B.root.toVar B.heap := by
  simp only [var]

lemma Bdd.var_node {n m} {B : Bdd n m} {j} (h : B.root = node j) :
    B.var = B.heap[j].var.castSucc := by
  simp only [var_eq, h, Fin.ext_iff, toVar_node, Fin.val_castSucc]

def OBdd.var {n m} (O : OBdd n m) : ℕ := O.1.var

lemma OBdd.var_eq_bdd_var {n m} (O : OBdd n m) : O.var = O.bdd.var := by
  simp only [var]

lemma OBdd.var_eq {n m} (O : OBdd n m) : O.var = O.bdd.root.toVar O.bdd.heap := by
  simp only [var_eq_bdd_var, Bdd.var_eq]

lemma OBdd.var_node {n m} {O : OBdd n m} {j} (h : O.bdd.root = node j) :
    O.var = O.bdd.heap[j].var := by
  grind only [var_eq, !toVar_node]

lemma OBdd.var_le {n m} (O : OBdd n m) : O.var ≤ n := by
  grind only [var]

@[simp]
def OBdd.rav {n m} (B : OBdd n m) : Nat := n - B.var

/-- The `OEdge` relation between Ordered BDDs is well-founded. -/
theorem OEdge.wellFounded {n m} : @WellFounded (OBdd n m) OEdge := by
  suffices s : Subrelation (@OEdge n m) (InvImage Nat.lt (OBdd.var ·)) from
    Subrelation.wf s (InvImage.wf _ (Nat.lt_wfRel.wf))
  rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨h1, h2⟩
  simp_all only
  simp only [InvImage, OBdd.var, Nat.lt_eq, Fin.val_fin_lt, var]
  simp only [ordered_iff'] at hx
  rw [← h1] at h2 ⊢
  exact hx x.root y.root .refl h2

/-- The `OEdge` relation between Ordered BDDs is converse well-founded. -/
theorem OEdge.flip_wellFounded {n m} : @WellFounded (OBdd n m) (flip OEdge) := by
  refine Subrelation.wf ?_ (InvImage.wf OBdd.rav (Nat.lt_wfRel.wf))
  rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨h1, h2⟩
  simp_all only
  simp only [InvImage, OBdd.rav, OBdd.var, var,  WellFoundedRelation.rel]
  simp only [ordered_iff'] at hy
  rw [← h1] at h2
  specialize hy y.root x.root .refl h2
  grind only [= Lean.Grind.toInt_fin]

instance OEdge.instWellFoundedRelation {n m} : WellFoundedRelation (OBdd n m) where
  rel := flip OEdge
  wf  := flip_wellFounded

lemma Bdd.ordered_of_reachable {O : OBdd n m} :
    Reachable O.bdd.heap O.bdd.root p → Ordered ⟨O.bdd.heap, p⟩ := by
  have h : (Bdd.mk O.bdd.heap p).MayPrecede = O.bdd.MayPrecede := Bdd.mayPrecede_eq_of_heap_eq rfl
  have := O.ordered
  simp only [ordered_iff, h]
  grind only [Reachable.trans, ordered_iff]


/-- All BDDs in the graph of an `Ordered` BDD are `Ordered`. -/
lemma Bdd.ordered_of_relevant (O : OBdd n m) (S : O.1.RelevantPointer) :
    Ordered {heap := O.1.heap, root := S.1} := ordered_of_reachable S.2

lemma Bdd.ordered_of_edge {n m} {B : Bdd n m} {p} :
    B.Ordered → Edge B.heap B.root p → Bdd.Ordered ⟨B.heap, p⟩ :=
  fun o e ↦ ordered_of_reachable (O := ⟨B, o⟩) (Reachable.ofEdge e)

lemma Bdd.high_ordered {B : Bdd n m} (h : B.root = node j) : B.Ordered → (B.high h).Ordered := by
  intro o
  apply Bdd.ordered_of_edge o
  rw [h]
  right

lemma Bdd.low_ordered {B : Bdd n m} (h : B.root = node j) : B.Ordered → (B.low h).Ordered := by
  intro o
  apply Bdd.ordered_of_edge o
  rw [h]
  left

lemma Bdd.low_heap_eq_heap {B : Bdd n m} {h : B.root = node j} : (B.low h).heap = B.heap := (rfl)
lemma Bdd.low_root_eq_low {B : Bdd n m} {h : B.root = node j} : (B.low h).root = B.heap[j].low := (rfl)

lemma Bdd.high_heap_eq_heap {B : Bdd n m} {h : B.root = node j} : (B.high h).heap = B.heap := (rfl)
lemma Bdd.high_root_eq_high {B : Bdd n m} {h : B.root = node j} : (B.high h).root = B.heap[j].high := (rfl)

def OBdd.high {n m} (O : OBdd n m) {j} : O.1.root = node j → OBdd n m
  | h => ⟨O.1.high h, Bdd.high_ordered h O.2⟩

def OBdd.low (O : OBdd n m) : O.1.root = node j → OBdd n m
  | h => ⟨O.1.low h, Bdd.low_ordered h O.2⟩

@[simp]
lemma OBdd.mk_eq_high {n m} {O : OBdd n m} {j : Fin m} {ho : Ordered _} (h : O.1.root = node j) :
    OBdd.mk ⟨O.bdd.heap, O.bdd.heap[j].high⟩ ho = O.high h := (rfl)

@[simp]
lemma OBdd.mk_eq_low {n m} {O : OBdd n m} {j : Fin m} {ho : Ordered _} (h : O.1.root = node j) :
    OBdd.mk ⟨O.bdd.heap, O.bdd.heap[j].low⟩ ho = O.low h := (rfl)

-- TODO :  check if needed
lemma OBdd.high_eq {n m} (O : OBdd n m) {j} {h : O.1.root = node j} :
    O.high h = ⟨O.1.high h, Bdd.high_ordered h O.2⟩ := (rfl)

-- TODO :  check if needed
lemma OBdd.low_eq {n m} (O : OBdd n m) {j} {h : O.1.root = node j} :
    O.low h = ⟨O.1.low h, Bdd.low_ordered h O.2⟩ := (rfl)

lemma OBdd.bdd_high {n m} (O : OBdd n m) {j} {h : O.1.root = node j} :
    (O.high h).bdd = O.bdd.high h := (rfl)

lemma OBdd.bdd_low {n m} (O : OBdd n m) {j} {h : O.1.root = node j} :
    (O.low h).bdd = O.bdd.low h := (rfl)

@[simp]
lemma OBdd.low_heap_eq_heap {n m} {O : OBdd n m} {j} (h : O.1.root = node j) :
    (O.low h).1.heap = O.1.heap := (rfl)

@[simp]
lemma OBdd.low_root_eq_low {n m} {O : OBdd n m} {j} (h : O.1.root = node j) :
    (O.low h).1.root = O.1.heap[j].low := (rfl)

@[simp]
lemma OBdd.high_heap_eq_heap {n m} {O : OBdd n m} {j} (h : O.1.root = node j) :
    (O.high h).1.heap = O.1.heap := (rfl)

@[simp]
lemma OBdd.high_root_eq_high {n m} {O : OBdd n m} {j} (h : O.1.root = node j) :
    (O.high h).1.root = O.1.heap[j].high := (rfl)

lemma oedge_of_low  {h : O.1.root = node j} : OEdge O (O.low h)  := ⟨rfl, edge_low  (h := h)⟩
lemma oedge_of_high {h : O.1.root = node j} : OEdge O (O.high h) := ⟨rfl, edge_high (h := h)⟩

macro_rules | `(tactic| decreasing_trivial) => `(tactic| exact oedge_of_low)
macro_rules | `(tactic| decreasing_trivial) => `(tactic| exact oedge_of_high)

def OBdd.toTree {n m} (O : OBdd n m) : DecisionTree n :=
  match h : O.1.root with
  | terminal b => .leaf b
  | node j     => .branch O.1.heap[j].var (toTree (O.low h)) (toTree (O.high h))
termination_by O

lemma OBdd.toTree_terminal {n m : ℕ} {O : OBdd n m} {b} (h : O.bdd.root = terminal b) :
    O.toTree = DecisionTree.leaf b := by
  grind only [toTree]

lemma OBdd.toTree_eq_leaf_iff_terminal {n m : ℕ} {O : OBdd n m} {b} :
    O.toTree = DecisionTree.leaf b ↔ O.bdd.root = terminal b := by
  grind only [toTree]

lemma OBdd.toTree_node {n m : ℕ} {O : OBdd n m} {j} (h : O.bdd.root = node j) :
    O.toTree = DecisionTree.branch O.bdd.heap[j].var (O.low h).toTree (O.high h).toTree := by
  grind only [toTree]

def OBdd.evaluate {n m} : OBdd n m → Vector Bool n → Bool := DecisionTree.evaluate ∘ OBdd.toTree

lemma OBdd.evaluate_def {n m} {O : OBdd n m} : O.evaluate = O.toTree.evaluate := (rfl)

lemma OBdd.evaluate_cast {n m n' I} {O : OBdd n m} (h : n = n') : (h ▸ O).evaluate I = O.evaluate (h ▸ I) := by
  subst h
  rfl

@[expose]
def OBdd.HSimilar (O : OBdd n m) (U : OBdd n m') := O.toTree = U.toTree

def OBdd.Similar : OBdd n m → OBdd n m → Prop := HSimilar

/-- Similarity of `Ordered` BDDs is decidable. -/
instance OBdd.instDecidableSimilar {n m} : DecidableRel (β := OBdd n m) OBdd.Similar :=
  fun O U ↦ decidable_of_decidable_of_iff (show O.toTree = U.toTree ↔ _ by simp [Similar, HSimilar])

-- FIXME: Use the instance from Sim.lean instead.
instance OBdd.instDecidableHSimilar (O : OBdd n m) (U : OBdd n m') : Decidable (OBdd.HSimilar O U) :=
  decidable_of_decidable_of_iff (show O.toTree = U.toTree ↔ _ by simp [HSimilar])

def OBdd.SimilarRP (O : OBdd n m) (p q : O.1.RelevantPointer) :=
  Similar ⟨{heap := O.1.heap, root := p.1}, ordered_of_reachable p.2⟩
          ⟨{heap := O.1.heap, root := q.1}, ordered_of_reachable q.2⟩

@[no_expose]
instance OBdd.instDecidableSimilarRP : Decidable (OBdd.SimilarRP O l r) := by
  simp only [OBdd.SimilarRP]; infer_instance

lemma OBdd.similarRP_iff {n m} {O : OBdd n m} {p q : O.1.RelevantPointer} : O.SimilarRP p q ↔
    (OBdd.mk ⟨O.bdd.heap, p⟩ (ordered_of_reachable p.2)).toTree =
    (OBdd.mk ⟨O.bdd.heap, q⟩ (ordered_of_reachable q.2)).toTree := by rfl

/-- Isomorphism of `Ordered` BDDs is an equivalence relation. -/
lemma OBdd.Similar.instEquivalence {n m} : Equivalence (α := OBdd n m) OBdd.Similar := by
  apply InvImage.equivalence
  constructor <;> simp_all [HSimilar]

-- instance OBdd.Similar.instReflexive : Reflexive (α := OBdd n m) OBdd.Similar := instEquivalence.refl

-- instance OBdd.Similar.instSymmetric : Symmetric (α := OBdd n m) OBdd.Similar := fun _ _ ↦ instEquivalence.symm

-- instance OBdd.Similar.instTransitive : Transitive (α := OBdd n m) OBdd.Similar := fun _ _ _ ↦ instEquivalence.trans

/-- A pointer is redundant if it point to node `N` with `N.low = N.high`. -/
inductive Pointer.Redundant (M : Vector (Node n m) m) : Pointer m → Prop where
  | red : M[j].low = M[j].high → Redundant M (node j)

instance Pointer.Redundant.instDecidable {n m} (w : Vector (Node n m) m) : DecidablePred (Redundant w) := by
  intro p
  cases p
  case terminal => apply isFalse; intro; contradiction
  case node j =>
    cases decEq w[j].low w[j].high
    case isFalse => apply isFalse; intro contra; cases contra; contradiction
    case isTrue h => exact isTrue ⟨h⟩

@[expose]
def Bdd.NoRedundancy (B : Bdd n m) := ∀ (p : B.RelevantPointer), ¬ Redundant B.heap p.1

/-- A BDD is `Reduced` if its graph does not contain redundant nodes or distinct similar subgraphs. -/
@[expose]
def OBdd.Reduced {n m} (O : OBdd n m) : Prop
  -- No redundant pointers.
  := NoRedundancy O.1
  -- Similarity implies pointer-equality.
   ∧ Subrelation (SimilarRP O) (InvImage Eq Subtype.val)

@[simp]
private def RelevantPointer.var {n m} {B : Bdd n m} (p : B.RelevantPointer) : Nat := p.1.toVar B.heap

@[simp]
private def RelevantPointer.gap {n m} {B : Bdd n m} (p : B.RelevantPointer) : Nat := n - (RelevantPointer.var p)

private theorem RelevantEdge.flip_wellFounded (o : Ordered B) : WellFounded (flip (RelevantEdge B)) := by
  have : Subrelation (flip (RelevantEdge B)) (InvImage Nat.lt RelevantPointer.gap) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ e
    simp_all only [InvImage, flip, RelevantPointer.gap]
    apply Nat.sub_lt_sub_left
    cases e <;> simp
    simp [B.ordered_iff'.1 o y x hy e]
  exact Subrelation.wf this (InvImage.wf _ (Nat.lt_wfRel.wf))

private instance RelevantEdge.instWellFoundedRelation {n m} (O : OBdd n m) : WellFoundedRelation O.1.RelevantPointer where
  rel := flip O.1.RelevantEdge
  wf  := (RelevantEdge.flip_wellFounded O.2)

@[no_expose, implicit_reducible]
private instance OBdd.instDecidableReflTransGen {n m} (O : OBdd n m) (p : O.1.RelevantPointer) (q) :
    Decidable (Relation.ReflTransGen (Edge O.1.heap) p.1 q) := by
  convert decidable_of_iff _ (symm Relation.reflTransGen_iff_eq_or_transGen)
  convert instDecidableOr
  · exact decEq q p.1
  · convert decidable_of_iff _ (symm Relation.TransGen.head'_iff)
    rcases h : p.1
    case terminal =>
      apply isFalse
      rintro ⟨x, contra1, contra2⟩
      contradiction
    case node j =>
      let low := O.1.heap[j].low
      have hlow : Relation.ReflTransGen (Edge O.1.heap) O.1.root low :=
        Relation.ReflTransGen.tail p.2 (by rw [h]; exact Edge.low)
      cases OBdd.instDecidableReflTransGen O ⟨low, hlow⟩ q
      case isFalse hfl =>
        let high := O.1.heap[j].high
        have hhigh : Relation.ReflTransGen (Edge O.1.heap) O.1.root high :=
          Relation.ReflTransGen.tail p.2 (by rw [h]; exact Edge.high)
        cases OBdd.instDecidableReflTransGen O ⟨high, hhigh⟩ q
        case isFalse hfh =>
          apply isFalse
          rintro ⟨c, contra1, contra2⟩
          simp_all only
          cases contra1
          case low =>
            apply hfl
            apply Relation.reflTransGen_swap.mp
            apply Relation.ReflTransGen.tail
            apply Relation.reflTransGen_swap.mpr
            exact contra2
            simp_all only [not_true_eq_false, low]
          case high =>
            apply hfh
            apply Relation.reflTransGen_swap.mp
            apply Relation.ReflTransGen.tail
            apply Relation.reflTransGen_swap.mpr
            exact contra2
            simp_all only [not_true_eq_false, low, high]
        case isTrue hth =>
          apply isTrue
          use high
          constructor
          · simp only [high, Edge.high]
          · apply hth
      case isTrue hth =>
        apply isTrue
        use low
        constructor
        · simp only [low, Edge.low]
        · apply hth
termination_by p
decreasing_by
  all_goals simp_all only [flip, RelevantEdge, Fin.getElem_fin]
  · exact Edge.low
  · exact Edge.high

@[no_expose]
instance Pointer.instDecidableReachable {n m} (O : OBdd n m) :
    DecidablePred (Reachable O.1.heap O.1.root) :=
  OBdd.instDecidableReflTransGen O ⟨O.1.root, .refl⟩

@[expose]
def OBdd.size {n m} (O : OBdd n m) := Fintype.card { j // Reachable O.1.heap O.1.root (.node j) }

private instance OBdd.instFintypeRelevantPointer {n m} (O : OBdd n m) : Fintype (O.1.RelevantPointer) := by
  convert Subtype.fintype _ <;> infer_instance

@[implicit_reducible]
def Pointer.decidableEitherReachable {n m} (O U : OBdd n m) (h : O.1.heap = U.1.heap) :
    DecidablePred (fun q ↦ (Reachable O.1.heap O.1.root q) ∨ (Reachable O.1.heap U.1.root q)) := by
  intro p
  simp
  cases instDecidableReachable O p with
  | isFalse hf =>
    cases instDecidableReachable U p with
    | isFalse hhf =>
      apply isFalse
      simp_all [or_self, not_false_eq_true]
    | isTrue  hht =>
      apply isTrue
      simp_all only [or_true]
  | isTrue  ht =>
    apply isTrue
    simp_all only [true_or]

@[implicit_reducible]
def OBdd.fintypeEitherRelevantPointer (O U : OBdd n m) (h : O.1.heap = U.1.heap) :
    Fintype { q // Reachable O.1.heap O.1.root q ∨ Reachable O.1.heap U.1.root q } := by
  convert Subtype.fintype _
  · exact decidableEitherReachable O U h
  · infer_instance

/-- The inverse image of a decidable relation is decidable. -/
private instance my_decidableRel_of_invImage2 {r : β → β → Prop} [DecidableRel r] {f : α → β} :
    DecidableRel (InvImage r f) :=
  fun a b ↦ decidable_of_decidable_of_iff (show (r (f a) (f b)) ↔ _ by simp [InvImage])

/-- `Reduced` is decidable. -/
@[no_expose]
instance OBdd.instReducedDecidable {n m} : DecidablePred (α := OBdd n m) Reduced :=
  fun _ ↦ (instDecidableAnd (dp := Fintype.decidableForallFintype) (dq := Fintype.decidableForallFintype))

/-- The output of equal constant functions with inhabited domain is equal. -/
lemma eq_of_constant_eq {α β} {c c' : β} [Inhabited α] :
    Function.const α c = Function.const α c' → c = c' :=
  fun h ↦ (show (Function.const α c) default = (Function.const α c') default by rw [h])

lemma Bdd.terminal_or_node {n m} (B : Bdd n m) :
    (∃ b, (B.root = terminal b ∧ B = {heap := B.heap, root := terminal b}))
  ∨ (∃ j, (B.root = node j ∧ B = {heap := B.heap, root := node j})) := by
  cases h : B.root
  case terminal b => left;  use b; simp [← h]
  case node j => right; use j; simp [← h]

theorem OBdd.init_inductionOn {n m} t {motive : OBdd n m → Prop}
    (base : (b : Bool) → (B : OBdd n m) → B.1.heap = t.1.heap → B.1.root = terminal b  → motive B)
    (step : (B : OBdd n m) → (j : Fin m) → B.1.heap = t.1.heap → (h : B.1.root = node j) →
      motive (B.low h) → motive (B.high h) → motive B)
    : motive t := by
  rcases (terminal_or_node t.1) with ⟨b, h1, h2⟩ | ⟨j, h1, h2⟩
  case inl => exact base b t rfl h1
  case inr =>
    apply step t j rfl h1
    · exact OBdd.init_inductionOn (t.low h1) base step
    · exact OBdd.init_inductionOn (t.high h1) base step
termination_by t

@[expose]
def OBdd.isTerminal {n m} (O : OBdd n m) := ∃ b, O.1.root = terminal b

lemma not_OEdge_of_isTerminal {O : OBdd n m}: O.isTerminal → ¬ OEdge O U := by
  rintro ⟨b, h⟩ ⟨_, contra⟩
  rw [h] at contra
  exact not_terminal_edge contra

/-- The graph induced by a terminal BDD consists of a sole terminal pointer. -/
private lemma Bdd.terminal_relevant_iff {n m} {B : Bdd n m} (h : B.root = terminal b) (S : B.RelevantPointer) {motive : Pointer m → Prop} :
    motive S.1 ↔ motive (terminal b) := by
  rw [← h]
  rcases S with ⟨s, hs⟩
  cases hs with
  | refl => simp
  | cons e r => simp only [h, not_terminal_edge] at e

lemma Bdd.eq_terminal_of_relevant {n m} {B : Bdd n m} {b}
    (h : B.root = terminal b) (S : B.RelevantPointer) : S.1 = terminal b :=
  (terminal_relevant_iff (by simp [h]) S).mp rfl

/-- Terminal BDDs are reduced. -/
lemma OBdd.reduced_of_terminal {n m} {O : OBdd n m} : O.isTerminal → O.Reduced := by
  rintro ⟨b, h⟩
  constructor
  · intro p R
    have contra : Redundant O.1.heap (terminal b) := by apply (terminal_relevant_iff h p).mp R
    contradiction
  · intro p q _
    calc p.1
      _ = terminal b :=         (eq_terminal_of_relevant (by rw [← h]) p)
      _ = q.1        := Eq.symm (eq_terminal_of_relevant (by rw [← h]) q)

lemma Bdd.reduced_of_terminal : OBdd.Reduced ⟨⟨M, terminal b⟩, o⟩ := OBdd.reduced_of_terminal ⟨b, rfl⟩

/-- Sub-BDDs of a reduced BDD are reduced. -/
private lemma OBdd.reduced_of_relevant {O : OBdd n m} (S : O.1.RelevantPointer):
    O.Reduced → OBdd.Reduced ⟨{heap := O.1.heap, root := S.1}, ordered_of_relevant O S⟩ := by
  intro R
  induction O using OBdd.init_inductionOn
  case base b U h1 h2 =>
    apply OBdd.reduced_of_terminal
    simp_rw [isTerminal, Bdd.eq_terminal_of_relevant h2 S]
    use b
  case step O' _ _ _ _ _ =>
    constructor
    · intro p; apply R.1 ⟨p.1, Reachable.trans S.2 p.2⟩
    · intro q p _
      have : O'.SimilarRP ⟨q.1, Reachable.trans S.2 q.2⟩ ⟨p.1, Reachable.trans S.2 p.2⟩ := by
        simp_all only [SimilarRP, Similar]
      apply R.2 this

lemma OBdd.ordered_of_edge {O : OBdd n m} {h : O.1.heap = v} {r : O.1.root = q} (p) :
    Edge v q p → Bdd.Ordered {heap := v, root := p} := by
  rw [← h, ← r]
  intro e
  exact ordered_of_relevant O ⟨p, Reachable.ofEdge e⟩

lemma OBdd.ordered_of_low_edge {j : Fin n} :
    Bdd.Ordered {heap := v, root := node j} → Bdd.Ordered {heap := v, root := v[j].low} := by
  intro o x y h
  apply ordered_of_relevant ⟨{ heap := v, root := node j }, o⟩ ⟨v[j].low, (Reachable.ofEdge Edge.low)⟩
  simpa

lemma OBdd.ordered_of_high_edge {j : Fin n} :
    Bdd.Ordered {heap := v, root := node j} → Bdd.Ordered {heap := v, root := v[j].high} := by
  intro o x y h
  apply ordered_of_relevant ⟨{ heap := v, root := node j }, o⟩ ⟨v[j].high, (Reachable.ofEdge Edge.high)⟩
  simpa

/-- Spell out `OBdd.evaluate` for terminals. -/
@[simp, grind →]
lemma OBdd.evaluate_terminal {n m} {O : OBdd m n} {b} :
    O.bdd.root = terminal b → O.evaluate = fun _ ↦ b := by
  intro h
  ext I
  simp [evaluate_def, OBdd.toTree_terminal h, DecisionTree.evaluate_leaf]

/-- Spell out `OBdd.evaluate` for non-terminals. -/
@[simp, grind =>]
lemma OBdd.evaluate_node {n m} {O : OBdd n m} {I : Vector Bool n} {j : Fin m}
    (h : O.bdd.root = node j) : O.evaluate I =
    if I[O.bdd.heap[j].var] then OBdd.evaluate (O.high h) I else OBdd.evaluate (O.low h) I := by
  simp only [evaluate_def, OBdd.toTree_node h, DecisionTree.evaluate_branch]

lemma OBdd.evaluate_node' {n m} {O : OBdd n m} {j : Fin m} (h : O.1.root = node j) :
    O.evaluate = fun I ↦
      if I[O.1.heap[j].var] then (O.high h).evaluate I else (O.low h).evaluate I := by
  ext I
  exact OBdd.evaluate_node h

lemma OBdd.HSimilar_of_terminal {n m m' : Nat} {b : Bool} {O : OBdd n m} {U : OBdd n m'} :
    O.1.root = terminal b → U.1.root = terminal b → O.HSimilar U := by
  intro h1 h2
  simp [HSimilar]
  rw [toTree_terminal h1, toTree_terminal h2]

private lemma aux {O : OBdd n m} {i : Fin m} :
    O.1.heap[i.1].var = Fin.castPred (toVar O.1.heap (node i)) (Fin.exists_castSucc_eq.mp ⟨O.1.heap[i.1].var, by simp [toVar]; rfl⟩) :=
  by simp [toVar]

lemma OBdd.var_lt_high_var {n m} {O : OBdd n m} {j} {h : O.1.root = node j} :
    O.var < (O.high h).var := by
  simp only [var_eq, Nat.succ_eq_add_one, high_heap_eq_heap, Fin.val_fin_lt]
  exact ordered_iff'.1 O.ordered _ _ .refl (O.bdd.edge_high h)

lemma OBdd.var_lt_low_var {n m} {O : OBdd n m} {j} {h : O.1.root = node j} :
    O.var < (O.low h).var := by
  simp only [var_eq, Nat.succ_eq_add_one, low_heap_eq_heap, Fin.val_fin_lt]
  exact ordered_iff'.1 O.ordered _ _ .refl (O.bdd.edge_low h)

lemma OBdd.not_dependsOn_lt_root {n m} {O : OBdd n m} {I J}
    (h : ∀ (i : Fin n), O.var ≤ i → I[i] = J[i]) : O.evaluate I = O.evaluate J := by
  induction O using init_inductionOn with
  | base => grind only [→ evaluate_terminal]
  | step O' j h2 h3 ih_low ih_high =>
    simp only [evaluate_node' h3]
    congr 1
    · simp only [eq_iff_iff, Bool.coe_iff_coe]
      apply h
      grind only [var_eq, = Lean.Grind.toInt_fin, !toVar_node, = Fin.val_castLE]
    · exact ih_high (by grind only [!var_lt_high_var])
    · exact ih_low (by grind only [!var_lt_low_var])

-- TODO : replace by `OBdd.not_dependsOn_lt_root`
lemma OBdd.independentOf_lt_root (O : OBdd n m) (i : Fin O.var) :
    Nary.IndependentOf (O.evaluate) (i.castLE O.var_le) := by
  cases h : O.1.root with
  | terminal _ => simp [evaluate_terminal h]
  | node j =>
    intro b I
    rw [evaluate_node' h]
    simp only
    rcases i with ⟨i, hi⟩
    congr 1
    · simp only [eq_iff_iff, Bool.coe_iff_coe]
      symm
      apply Vector.getElem_set_ne _ _ (Nat.ne_of_lt (by grind [O.var_node]))
    · exact (independentOf_lt_root (O.high h) ⟨i, .trans hi var_lt_high_var⟩) b I
    · exact (independentOf_lt_root (O.low  h) ⟨i, .trans hi var_lt_low_var⟩) b I
termination_by O

def OBdd.size' {n m} : OBdd n m → Nat := DecisionTree.size ∘ OBdd.toTree

lemma OBdd.size_zero_of_terminal : OBdd.isTerminal O → O.size' = 0 := by
  rintro ⟨b, h⟩
  rcases O with ⟨⟨heap, root⟩, o⟩
  subst h
  simp only [size', Function.comp_apply]
  unfold toTree
  rfl

lemma OBdd.high_reduced {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} : O.Reduced → (O.high h).Reduced := by
  intro o
  apply reduced_of_relevant ⟨O.1.heap[j].high, ?_⟩ o
  exact O.bdd.reachable_high h

lemma OBdd.low_reduced {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} : O.Reduced → (O.low h).Reduced := by
  intro o
  apply reduced_of_relevant ⟨O.1.heap[j].low, ?_⟩ o
  exact O.bdd.reachable_low h

lemma OBdd.size_node {n m} {O : OBdd n m} {j : Fin m} (h : O.1.root = node j) : O.size' = 1 + (O.low h).size' + (O.high h).size' := by
  simp only [size', Function.comp_apply, toTree_node h]
  rfl

lemma OBdd.evaluate_high_eq_evaluate_low_of_independentOf_root {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} :
    Nary.IndependentOf O.evaluate O.1.heap[j].var → (O.high h).evaluate = (O.low h).evaluate := by
  intro i
  ext I
  trans O.evaluate I
  · rw [i true I]
    rw [evaluate_node' h]
    simp only [Fin.getElem_fin, Vector.getElem_set_self, ↓reduceIte]
    exact (independentOf_lt_root (O.high h) ⟨O.1.heap[j].var, (by convert var_lt_high_var (O := O); rw [O.var_node h])⟩) true I
  · rw [i false I]
    rw [evaluate_node' h]
    simp only [Fin.getElem_fin, Vector.getElem_set_self]
    symm
    exact (independentOf_lt_root (O := O.low h) ⟨O.1.heap[j].var, (by convert var_lt_low_var  (O := O); rw [O.var_node h])⟩) false I

lemma OBdd.evaluate_high_eq_evaluate_set_true {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} :
    (O.high h).evaluate = O.evaluate ∘ fun I ↦ I.set O.1.heap[j].var true := by
  ext I
  simp only [Function.comp_apply]
  rw [evaluate_node' h (j := j)]
  beta_reduce
  simp only [Fin.getElem_fin, Vector.getElem_set_self, ↓reduceIte]
  have := var_lt_high_var (h := h)
  simp only [var_eq, h, toVar_node, high_heap_eq_heap, high_root_eq_high] at this
  apply independentOf_lt_root (O.high h) ⟨O.1.heap[j].var, (by convert var_lt_high_var (O := O); rw [O.var_node h])⟩

lemma OBdd.evaluate_low_eq_evaluate_set_false {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} :
    (O.low h).evaluate = O.evaluate ∘ fun I ↦ I.set O.1.heap[j].var false := by
  ext I
  simp only [Function.comp_apply]
  rw [evaluate_node' h (j := j)]
  beta_reduce
  simp only [Fin.getElem_fin, Vector.getElem_set_self]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have := var_lt_high_var (h := h)
  simp only [var_eq, h, toVar_node, high_heap_eq_heap, high_root_eq_high] at this
  apply independentOf_lt_root (O.low h) ⟨O.1.heap[j].var, (by convert var_lt_low_var (O := O); rw [O.var_node h])⟩

lemma OBdd.evaluate_high_eq_of_evaluate_eq_and_var_eq' {n m m' : Nat} {O : OBdd n m} {U : OBdd n m'} {j : Fin m} {i : Fin m'} {ho : O.1.root = node j} {hu : U.1.root = node i} :
    O.evaluate = U.evaluate → O.1.heap[j].var = U.1.heap[i].var → (O.high ho).evaluate = (U.high hu).evaluate := by
  grind only [!evaluate_high_eq_evaluate_set_true]

lemma OBdd.evaluate_high_eq_of_evaluate_eq_and_var_eq {n m} {O U : OBdd n m} {j i : Fin m} {ho : O.1.root = node j} {hu : U.1.root = node i} :
    O.evaluate = U.evaluate → O.1.heap[j].var = U.1.heap[i].var → (O.high ho).evaluate = (U.high hu).evaluate := evaluate_high_eq_of_evaluate_eq_and_var_eq'

lemma OBdd.evaluate_low_eq_of_evaluate_eq_and_var_eq' {n m m' : Nat} {O : OBdd n m} {U : OBdd n m'} {j : Fin m} {i : Fin m'} {ho : O.1.root = node j} {hu : U.1.root = node i} :
  O.evaluate = U.evaluate → O.1.heap[j].var = U.1.heap[i].var → (O.low ho).evaluate = (U.low hu).evaluate := by
  grind only [evaluate_low_eq_evaluate_set_false, ← evaluate_low_eq_evaluate_set_false]

lemma OBdd.evaluate_low_eq_of_evaluate_eq_and_var_eq {n m} {O U : OBdd n m} {j i : Fin m} {ho : O.1.root = node j} {hu : U.1.root = node i} :
  O.evaluate = U.evaluate → O.1.heap[j].var = U.1.heap[i].var → (O.low ho).evaluate = (U.low hu).evaluate := evaluate_low_eq_of_evaluate_eq_and_var_eq'

lemma OBdd.not_reduced_of_sim_high_low {n m} {O : OBdd n m} {j : Fin m} (h : O.1.root = node j) :
    Similar (O.high h) (O.low h) → ¬ O.Reduced := by
  intro iso R
  apply R.1 O.1.toRelevantPointer
  simp [toRelevantPointer]
  rw [h]
  constructor
  have giso : SimilarRP O ⟨(O.high h).1.root, O.bdd.reachable_high h⟩
                                ⟨(O.low  h).1.root, O.bdd.reachable_low h⟩ := iso
  exact (symm (R.2 giso))

/-- Reduced OBDDs are canonical.  -/
theorem OBdd.Canonicity {O : OBdd n m} {U : OBdd n m'} (ho : O.Reduced) (hu : U.Reduced) :
    O.evaluate = U.evaluate → O.HSimilar U := by
  intro h
  cases O_root_def : O.1.root with
  | terminal b =>
    cases U_root_def : U.1.root with
    | terminal c =>
      simp only [HSimilar]
      simp [evaluate_terminal O_root_def, evaluate_terminal U_root_def] at h
      rw [toTree_terminal O_root_def]
      grind [evaluate_def, toTree_terminal]
    | node i =>
      rw [evaluate_terminal O_root_def] at h
      have : (U.high U_root_def).evaluate = (U.low U_root_def).evaluate := by
        ext I
        trans b
        · rw [evaluate_high_eq_evaluate_set_true]
          rw [← h]
          simp
        · rw [evaluate_low_eq_evaluate_set_false]
          rw [← h]
          simp
      absurd hu
      apply not_reduced_of_sim_high_low U_root_def
      apply OBdd.Canonicity (high_reduced hu) (low_reduced hu) this
  | node j =>
    cases U_root_def : U.1.root with
    | terminal c =>
      rw [evaluate_terminal U_root_def] at h
      have : (O.high O_root_def).evaluate = (O.low O_root_def).evaluate := by
        ext I
        trans c
        · rw [evaluate_high_eq_evaluate_set_true]
          rw [h]
          simp
        · rw [evaluate_low_eq_evaluate_set_false]
          rw [h]
          simp
      absurd ho
      apply not_reduced_of_sim_high_low O_root_def
      apply OBdd.Canonicity (high_reduced ho) (low_reduced ho) this
    | node i =>
      simp only [HSimilar]
      rw [toTree_node O_root_def, toTree_node U_root_def]
      simp only [DecisionTree.branch.injEq]
      have same_var : O.1.heap[j].var = U.1.heap[i].var := by
        apply eq_iff_le_not_lt.mpr
        constructor
        · apply le_of_not_gt
          intro contra
          have := independentOf_lt_root O ⟨U.1.heap[i].var.1, by simp only [Fin.getElem_fin, var, Nat.succ_eq_add_one, Bdd.var]; rw [O_root_def]; simpa⟩
          rw [h] at this
          apply hu.1 U.1.toRelevantPointer
          simp only [toRelevantPointer, U_root_def]
          simp only [Nary.IndependentOf] at this
          have that : OBdd.Similar (U.high U_root_def) (U.low U_root_def) :=
            OBdd.Canonicity (high_reduced hu) (low_reduced hu) (evaluate_high_eq_evaluate_low_of_independentOf_root this)
          constructor
          have iso : SimilarRP U ⟨(U.high U_root_def).1.root, U.1.reachable_high U_root_def⟩
                                  ⟨(U.low  U_root_def).1.root, U.1.reachable_low U_root_def⟩ := that
          exact (symm (hu.2 iso))
        · intro contra
          have := independentOf_lt_root U ⟨O.1.heap[j].var.1, by simp only [Fin.getElem_fin, var, Nat.succ_eq_add_one, Bdd.var]; rw [U_root_def]; simpa⟩
          rw [← h] at this
          simp only [Nary.IndependentOf] at this
          have that : OBdd.Similar (O.high O_root_def) (O.low O_root_def) :=
            OBdd.Canonicity (high_reduced ho) (low_reduced ho) (evaluate_high_eq_evaluate_low_of_independentOf_root this)
          apply ho.1 O.1.toRelevantPointer
          simp [toRelevantPointer]
          rw [O_root_def]
          constructor
          have iso : SimilarRP O ⟨(O.high O_root_def).1.root, O.1.reachable_high O_root_def⟩
                                  ⟨(O.low  O_root_def).1.root, O.1.reachable_low O_root_def⟩ := that
          exact (symm (ho.2 iso))
      constructor
      · exact same_var
      · constructor
        · apply OBdd.Canonicity (low_reduced  ho) (low_reduced  hu) (evaluate_low_eq_of_evaluate_eq_and_var_eq'  h same_var)
        · apply OBdd.Canonicity (high_reduced ho) (high_reduced hu) (evaluate_high_eq_of_evaluate_eq_and_var_eq' h same_var)
termination_by O.size' + U.size'
decreasing_by
  simp [size_node U_root_def]; omega
  simp [size_node O_root_def]; omega
  all_goals
    simp [size_node O_root_def, size_node U_root_def]; omega

/-- The only reduced BDD that denotes a constant function is the terminal BDD. -/
theorem OBdd.terminal_of_constant (O : OBdd n m) :
    O.Reduced → O.evaluate = (fun _ ↦ b) → O.1.root = terminal b := by
  intro R h
  cases O_root_def : O.1.root
  case terminal b' =>
    grind only [OBdd.evaluate_terminal O_root_def]
  case node j =>
    exfalso
    refine not_reduced_of_sim_high_low O_root_def ?_ R
    have : (O.high O_root_def).evaluate = (O.low O_root_def).evaluate := by
      ext I
      trans b
      · simp [evaluate_high_eq_evaluate_set_true, h]
      · simp [evaluate_low_eq_evaluate_set_false, h]
    exact OBdd.Canonicity (high_reduced R) (low_reduced R) this

theorem OBdd.Canonicity_reverse {O : OBdd n m} {U : OBdd n m'}:
    O.HSimilar U → O.evaluate = U.evaluate := by
  simp_all [evaluate, Function.comp_apply, HSimilar]

/-- An acyclicity lemma: an edge from `O` to `U` implies that `O` is not reachable from `U`.  -/
lemma OBdd.not_oedge_reachable {n m} {O U : OBdd n m}: OEdge O U → ¬ Reachable O.1.heap U.1.root O.1.root := by
  rintro ⟨same_heap, e⟩ contra
  apply Relation.reflTransGen_iff_eq_or_transGen.mp at contra
  cases contra with
  | inl h =>
    rw [← h] at e
    exact Bdd.no_self_edge_of_ordered O.ordered O.bdd.relevant_root e
  | inr h =>
    apply Relation.TransGen.head'_iff.mp at h
    rcases h with ⟨c, h1, h2⟩
    rw [same_heap] at h1
    let V : OBdd n m := ⟨{heap := U.1.heap, root := c}, ordered_of_edge (r := rfl) (h := rfl) c h1⟩
    have : c = V.1.root := rfl
    rw [this] at h1 h2
    apply not_oedge_reachable ⟨by rfl, h1⟩
    trans O.1.root
    rw [same_heap] at h2; exact h2
    rw [← same_heap]; exact Reachable.ofEdge e
termination_by O

lemma OBdd.not_reachable_low_root {n m} {O : OBdd n m} {j} (h : O.bdd.root = node j) :
    ¬Reachable O.bdd.heap O.bdd.heap[j].low O.bdd.root := by
  intro r
  exact OBdd.not_oedge_reachable oedge_of_low (U := O.low h) (by simp; exact r)

lemma OBdd.not_reachable_high_root {n m} {O : OBdd n m} {j} (h : O.bdd.root = node j) :
    ¬Reachable O.bdd.heap O.bdd.heap[j].high O.bdd.root := by
  intro r
  exact OBdd.not_oedge_reachable oedge_of_high (U := O.high h) (by simp; exact r)


lemma Pointer.Reachable_iff {M : Vector (Node n m) m } :
  Pointer.Reachable M r p ↔ (r = p ∨ (∃ j, r = .node j ∧ (Pointer.Reachable M M[j].low p ∨ Pointer.Reachable M M[j].high p))) := by
  constructor
  · intro h
    cases h with
    | refl =>
      left
      rfl
    | cons e r =>
      right
      obtain ⟨j, rfl, rfl | rfl⟩ := edge_iff.1 e
      · exact ⟨j, rfl, .inl r⟩
      · exact ⟨j, rfl, .inr r⟩
  · intro h
    cases h with
    | inl h => rw [h]; left
    | inr h =>
      rcases h with ⟨j, rfl, h⟩
      cases h with
      | inl h => exact .trans (.ofEdge Edge.low) h
      | inr h => exact .trans (.ofEdge Edge.high) h

lemma OBdd.reachable_or_eq_low_high {O : OBdd n m} :
    Reachable O.1.heap O.1.root p → (O.1.root = p ∨ (∃ j, ∃ (h : O.1.root = node j), (Reachable O.1.heap (O.low h).1.root p ∨ Reachable O.1.heap (O.high h).1.root p))) := by
  intro hr
  cases Reachable_iff.mp hr with
  | inl => left; assumption
  | inr h =>
    right
    rcases h with ⟨j, O_root_def, hj⟩
    use j, O_root_def
    cases hj with
    | inl hl => left;  simpa [low, Bdd.low]
    | inr hh => right; simpa [high, Bdd.high]

lemma not_isTerminal_of_root_eq_node {n m} {j} {O : OBdd n m} (h : O.1.root = node j) : ¬ O.isTerminal := by
  rintro ⟨b, hb⟩
  rw [h] at hb
  contradiction

def OBdd.OReachable {n m} := Relation.ReflTransGen (@OEdge n m)

lemma OBdd.low_oreachable {n m} {j} {O U : OBdd n m} {U_root_def : U.1.root = node j}: O.OReachable U → O.OReachable (U.low U_root_def) := fun h ↦
  Relation.ReflTransGen.tail h oedge_of_low

lemma OBdd.high_oreachable {n m} {j} {O U : OBdd n m} {U_root_def : U.1.root = node j} : O.OReachable U → O.OReachable (U.high U_root_def) := fun h ↦
  Relation.ReflTransGen.tail h oedge_of_high

lemma OBdd.reachable_node_iff {O : OBdd n m} (h : O.1.root = node j) :
  Reachable O.1.heap O.1.root = fun q ↦
    (Reachable O.1.heap O.1.root q ∧ ¬ Reachable O.1.heap (O.low h).1.root q ∧ ¬ Reachable O.1.heap (O.high h).1.root q) ∨
    (Reachable O.1.heap (O.low  h).1.root q ∧ ¬ Reachable O.1.heap (O.high h).1.root q) ∨
    (Reachable O.1.heap (O.high h).1.root q ∧ ¬ Reachable O.1.heap (O.low  h).1.root q) ∨
    (Reachable O.1.heap (O.low  h).1.root q ∧   Reachable O.1.heap (O.high h).1.root q) := by
  ext p
  constructor
  · intro r
    cases instDecidableReachable (O.low h) p with
    | isFalse hf =>
      cases instDecidableReachable (O.high h) p with
      | isFalse hhf =>
        left
        exact ⟨r, hf, hhf⟩
      | isTrue hht =>
        right
        right
        left
        exact ⟨hht, hf⟩
    | isTrue ht =>
      cases instDecidableReachable (O.high h) p with
      | isFalse hhf =>
        right
        left
        exact ⟨ht, hhf⟩
      | isTrue hht =>
        right
        right
        right
        exact ⟨ht, hht⟩
  · intro r
    cases r with
    | inl r => exact r.1
    | inr r =>
      cases r with
      | inl r =>
        trans (O.low h).1.root
        · exact O.bdd.reachable_low h
        · exact r.1
      | inr r =>
        cases r with
        | inl r =>
          trans (O.high h).1.root
          · exact O.bdd.reachable_high h
          · exact r.1
        | inr r =>
          trans (O.high h).1.root
          · exact O.bdd.reachable_high h
          · exact r.2

@[no_expose]
instance OBdd.instFintypeReachableFromNode (O : OBdd n m) (h : O.1.root = node j) : Fintype {q // (q = O.1.root ∨ (Reachable O.1.heap (O.low  h).1.root q ∨ Reachable O.1.heap (O.high h).1.root q))} := by
  convert Subtype.fintype _
  · intro p
    simp only
    cases decEq p O.1.root with
    | isFalse hf =>
      cases instDecidableReachable (O.low h) p with
      | isFalse hhf =>
        cases instDecidableReachable (O.high h) p with
        | isFalse hhhf =>
          apply isFalse
          simp
          exact ⟨hf, hhf, hhhf⟩
        | isTrue hhht =>
          apply isTrue
          right
          right
          assumption
      | isTrue hht =>
        apply isTrue
        right
        left
        assumption
    | isTrue h =>
      apply isTrue
      left
      assumption
  · infer_instance

lemma OBdd.reachable_from_node_iff' {O : OBdd n m} (h : O.1.root = node j) :
    Reachable O.1.heap O.1.root p ↔ p = O.1.root ∨ (Reachable O.1.heap (O.low h).1.root p ∨ Reachable O.1.heap (O.high h).1.root p) := by
  constructor
  · intro r
    cases r with
    | refl => left; rfl
    | cons e r =>
      rename_i q
      right
      rw [h] at e
      cases e with
      | low =>
        left
        rw [low_root_eq_low]
        exact r
      | high =>
        right
        rw [high_root_eq_high]
        exact r
  · intro r
    cases r with
    | inl r =>
      rw [r]
      left
    | inr r =>
      simp only [low_root_eq_low, high_root_eq_high] at r
      cases r with
      | inl r => exact .trans (O.bdd.reachable_low h) r
      | inr r => exact .trans (O.bdd.reachable_high h) r

lemma OBdd.card_reachable_node' {O : OBdd n m} (h : O.1.root = node j) :
  Fintype.card {p // Reachable O.1.heap O.1.root p} =
  Fintype.card {p // p = O.1.root ∨ (Reachable O.1.heap (O.low  h).1.root p ∨ Reachable O.1.heap (O.high h).1.root p)} := by
  apply Fintype.card_congr'
  conv =>
    lhs
    arg 1
    ext
    rw [reachable_from_node_iff' h]

lemma OBdd.eq_root_disjoint_reachable_low_or_high {O : OBdd n m} (h : O.1.root = node j) :
    Disjoint
      (· = O.1.root)
      (fun p ↦ (Reachable O.1.heap (O.low  h).1.root p ∨ Reachable O.1.heap (O.high h).1.root p)) := by
  intro P h1 h2 p hp
  specialize h1 p hp
  specialize h2 p hp
  simp_all only
  cases h2 with
  | inl l =>
    rw [← h] at l
    apply OBdd.not_oedge_reachable oedge_of_low l
  | inr l =>
    rw [← h] at l
    apply OBdd.not_oedge_reachable oedge_of_high l

lemma OBdd.card_reachable_node {O : OBdd n m} (h : O.1.root = node j) :
  Fintype.card { q // Reachable O.1.heap O.1.root q } =
  1 + Fintype.card { q // Reachable (O.low h).1.heap (O.low h).1.root q ∨ Reachable (O.high h).1.heap (O.high h).1.root q } := by
  rw [card_reachable_node' h]
  rw [@Fintype.card_subtype_or_disjoint _ _ _ (eq_root_disjoint_reachable_low_or_high h) ..]
  · simp only [Fintype.card_unique, low_heap_eq_heap, add_right_inj]
    apply @Fintype.card_congr' ..
    · apply fintypeEitherRelevantPointer (O.low h) (O.high h); simp
    · simp
  · exact Fintype.subtypeEq O.1.root

lemma Bdd.ordered_of_low_high_ordered {n m} {B : Bdd n m} {j} (h : B.root = node j):
    (B.low h).Ordered → B.var < (B.low h).var →
    (B.high h).Ordered → B.var < (B.high h).var →
    Ordered B := by
  simp only [ordered_iff', var]
  intro hl1 hl2 hh1 hh2 p q hr e
  simp only [low_heap_eq_heap, low_root_eq_low, h] at hl1 hl2
  simp only [high_heap_eq_heap, high_root_eq_high, h] at hh1 hh2
  cases hr
  case refl => grind only [edge_iff]
  case cons q' r e' =>
    rw [h] at e'
    cases e' with
    | low => exact hl1 p q r e
    | high => exact hh1 p q r e

lemma Bdd.ordered_of_ordered_heap_not_reachable_set (O : OBdd n m) :
    ∀ i N, ¬ Reachable O.1.heap O.1.root (node i) → Ordered ⟨O.1.heap.set i N, O.1.root⟩ := by
  intro i N unr
  induction O using OBdd.init_inductionOn with
  | base b O' h1 h2 => exact ordered_of_terminal h2
  | step O' j h1 h2 ih_low ih_high =>
    have h3 : i ≠ j := by
      intro contra
      rw [contra] at unr
      rw [h2] at unr
      apply unr
      left
    apply ordered_of_low_high_ordered (by rw [h2])
    · simp only [low, Fin.getElem_fin]
      rw [Vector.getElem_set_ne i.2 j.2 (Fin.val_ne_of_ne h3)]
      apply ih_low
      intro h4
      apply unr
      trans O'.1.heap[j].low
      · exact O'.bdd.reachable_low h2
      · exact h4
    · simp only [var_eq, low, Fin.getElem_fin]
      rw [Vector.getElem_set_ne i.2 j.2 (Fin.val_ne_of_ne h3)]
      rw [h2, toVar_heap_set' h3]
      have h4 : toVar O'.1.heap (node j) < toVar O'.1.heap O'.1.heap[j].low :=
        ordered_iff'.1 O'.ordered (node j) O'.1.heap[j].low (h2 ▸ .refl) Edge.low
      convert h4 using 1
      cases low_def : O.1.heap[j].low with
      | terminal bl =>
        simp_all only [Fin.getElem_fin, toVar_terminal]
      | node jl =>
        simp only [← h1, Fin.getElem_fin] at low_def
        simp only [low_def, Fin.getElem_fin]
        simp only [Fin.ext_iff, toVar_node, Fin.getElem_fin]
        rw [Vector.getElem_set_ne i.2 jl.2]
        simp only [ne_eq, Fin.val_inj]
        intro rfl
        apply unr
        rw [← low_def]
        exact O'.bdd.reachable_low h2
    · simp only [high, Fin.getElem_fin]
      rw [Vector.getElem_set_ne i.2 j.2 (Fin.val_ne_of_ne h3)]
      apply ih_high
      intro h4
      apply unr
      trans O'.1.heap[j].high
      · exact O'.bdd.reachable_high h2
      · exact h4
    · simp only [var_eq, high, Fin.getElem_fin]
      rw [Vector.getElem_set_ne i.2 j.2 (Fin.val_ne_of_ne h3)]
      rw [h2, toVar_heap_set' h3]
      have h4 : toVar O'.1.heap (node j) < toVar O'.1.heap O'.1.heap[j].high :=
        ordered_iff'.1 O'.ordered (node j) O'.1.heap[j].high (h2 ▸ .refl) Edge.high
      convert h4 using 1
      cases high_def : O.1.heap[j].high with
      | terminal bl =>
        simp_all only [Fin.getElem_fin, toVar_terminal]
      | node jl =>
        simp only [← h1, Fin.getElem_fin] at high_def
        simp only [high_def, Fin.getElem_fin]
        simp only [Fin.ext_iff, toVar_node, Fin.getElem_fin]
        rw [Vector.getElem_set_ne i.2 jl.2]
        simp only [ne_eq, Fin.val_inj]
        intro rfl
        apply unr
        rw [← high_def]
        exact O'.bdd.reachable_high h2

lemma Pointer.mayPrecede_of_reachable {B : Bdd n m} :
    B.Ordered → Reachable B.heap B.root p → Pointer.toVar B.heap B.root ≤ Pointer.toVar B.heap p := by
  intro ho hp
  induction hp with
  | refl => simp
  | @snoc b c r e ih =>
    trans toVar B.heap b
    · exact ih
    · have : toVar B.heap b < toVar B.heap c :=
        ordered_iff'.1 ho b c r e
      omega

lemma OBdd.reduced_var_dependent {O : OBdd n m} {p : Fin n} :
    O.Reduced → (∀ i : Fin p, Nary.IndependentOf (O.evaluate) ⟨i.1, by omega⟩) → p.1 ≤ O.1.var.1 := by
  intro hr hp
  cases O_root_def : O.1.root with
  | terminal _ =>
    simp only [Nat.succ_eq_add_one, Bdd.var, O_root_def, Pointer.toVar_terminal]
    exact Fin.le_last p.castSucc
  | node j =>
    by_contra c
    simp only [not_le] at c
    have := hp ⟨O.1.var, by aesop⟩
    simp only [Nat.succ_eq_add_one] at this
    suffices s : (O.high O_root_def).evaluate = (O.low O_root_def).evaluate by
      absurd hr
      apply not_reduced_of_sim_high_low O_root_def
      apply OBdd.Canonicity (OBdd.high_reduced hr) (OBdd.low_reduced hr) s
    ext I
    trans O.evaluate I
    · simp only [Bdd.var, O_root_def, Pointer.toVar_node, Fin.eta] at this
      have := this true I
      rw [this]
      rw [OBdd.evaluate_node' O_root_def]
      simp only [Fin.getElem_fin, Vector.getElem_set_self]
      simp only [↓reduceIte]
      suffices s : Nary.IndependentOf (O.high O_root_def).evaluate O.1.heap[j.1].var by rw [← s true I]
      refine independentOf_lt_root (O.high O_root_def) ⟨O.1.heap[j.1].var.1, ?_⟩
      convert OBdd.var_lt_high_var
      simp only [O.var_node O_root_def, Fin.getElem_fin]
    · symm
      simp only [Bdd.var, O_root_def, Pointer.toVar_node, Fin.eta] at this
      have := this false I
      rw [this]
      rw [OBdd.evaluate_node' O_root_def]
      simp only [Fin.getElem_fin, Vector.getElem_set_self]
      simp only [Bool.false_eq_true, ↓reduceIte]
      suffices s : Nary.IndependentOf (O.low O_root_def).evaluate O.1.heap[j.1].var by rw [s false I]
      refine independentOf_lt_root (O.low O_root_def) ⟨O.1.heap[j.1].var.1, ?_⟩
      convert OBdd.var_lt_low_var
      simp only [O.var_node O_root_def, Fin.getElem_fin]

@[expose]
def Bdd.usesVar (B : Bdd n m) (i : Fin n) := ∃ j, Reachable B.heap B.root (node j) ∧ B.heap[j].var = i

lemma Bdd.usesVar_of_high_usesVar {B : Bdd n m} {h : B.root = node j} :
    (B.high h).usesVar i → B.usesVar i := by
  rintro ⟨j, h1, h2⟩
  use j
  constructor
  · trans (B.high h).root
    · exact B.reachable_high h
    · exact h1
  · simp_all [high_heap_eq_heap]

lemma Bdd.usesVar_of_low_usesVar {B : Bdd n m} {h : B.root = node j} :
    (B.low h).usesVar i → B.usesVar i := by
  rintro ⟨j, h1, h2⟩
  use j
  constructor
  · trans (B.low h).root
    · exact B.reachable_low h
    · exact h1
  · simp_all [low_heap_eq_heap]

lemma OBdd.usesVar_of_high_usesVar {O : OBdd n m} {h : O.1.root = node j} :
    (O.high h).1.usesVar i → O.1.usesVar i := by
  rintro ⟨j, h1, h2⟩
  use j
  constructor
  · trans (O.high h).1.root
    · exact O.bdd.reachable_high h
    · exact h1
  · simp_all

lemma OBdd.usesVar_of_low_usesVar {O : OBdd n m} {h : O.1.root = node j} :
    (O.low h).1.usesVar i → O.1.usesVar i := by
  rintro ⟨j, h1, h2⟩
  use j
  constructor
  · trans (O.low h).1.root
    · exact O.bdd.reachable_low h
    · exact h1
  · simp_all

lemma OBdd.dependsOn_of_usesVar_of_reduced {O : OBdd n m} :
    O.Reduced → Reachable O.1.heap O.1.root (node j) → O.1.heap[j].var = i →
    ∃ v1 v2, (∀ i' ≠ i, v1[i'] = v2[i']) ∧ O.evaluate v1 ≠ O.evaluate v2 := by
  intro hr hj rfl
  generalize heq : node j = p at hj
  symm at heq
  cases hj with
  | refl =>
    rw [evaluate_node' heq]
    by_contra contra
    apply not_reduced_of_sim_high_low (O := O) heq
    · apply OBdd.Canonicity
      · exact high_reduced hr
      · exact low_reduced hr
      · ext x
        simp only [ne_eq, not_exists, not_and, Decidable.not_not] at contra
        specialize contra
          (x.set O.1.heap[j].var false)
          (x.set O.1.heap[j].var true)
          (by grind only [= Fin.getElem_fin, = Vector.getElem_set])
        simp at contra
        calc _
          _ = (O.high heq).evaluate (x.set O.1.heap[j].var true) := by
            have hj : O.1.heap[j].var.1 < (O.high heq).var := by
              grind only [= Lean.Grind.toInt_fin, !var_lt_high_var, var_node]
            exact not_dependsOn_lt_root (by grind)
          _ = (O.low heq).evaluate (x.set O.1.heap[j].var false) := by symm; assumption
          _ = _ := by
            symm
            have hhi : O.1.heap[j].var.1 < (O.low heq).var := by
              grind only [= Lean.Grind.toInt_fin, !var_lt_low_var, var_node]
            exact not_dependsOn_lt_root (by grind)
    · exact hr
  | cons e r =>
    rename_i p
    rw [edge_iff] at e
    rcases e with ⟨jr, h_root, (rfl | rfl)⟩
    · have h1 := OBdd.dependsOn_of_usesVar_of_reduced
        (low_reduced (h := h_root) hr)
        (by rw [low_heap_eq_heap, low_root_eq_low, ← heq]; exact r)
        rfl
      rcases h1 with ⟨v1, v2, h1, h2⟩
      use v1.set (O.bdd.heap[jr].var) false, v2.set (O.bdd.heap[jr].var) false
      constructor
      · intro i hi
        simp only [Fin.getElem_fin, Vector.getElem_set]
        split
        · rfl
        · exact h1 i (by grind only [low_heap_eq_heap])
      contrapose h2
      calc _
        _ = O.evaluate (v1.set (O.bdd.heap[jr].var) false) := by
          rw [evaluate_low_eq_evaluate_set_false]
          rfl
        _ = O.evaluate (v2.set (O.bdd.heap[jr].var) false) := h2
        _ = (O.low h_root).evaluate v2 := by
          rw [evaluate_low_eq_evaluate_set_false]
          rfl
    · have h1 := OBdd.dependsOn_of_usesVar_of_reduced
        (high_reduced (h := h_root) hr)
        (by rw [high_heap_eq_heap, high_root_eq_high, ← heq]; exact r)
        rfl
      rcases h1 with ⟨v1, v2, h1, h2⟩
      use v1.set O.bdd.heap[jr].var true, v2.set O.bdd.heap[jr].var true
      constructor
      · intro i hi
        simp only [Fin.getElem_fin, Vector.getElem_set]
        split
        · rfl
        · exact h1 i (by grind only [high_heap_eq_heap])
      contrapose h2
      calc _
        _ = O.evaluate (v1.set (O.bdd.heap[jr].var) true) := by
          rw [evaluate_high_eq_evaluate_set_true]
          rfl
        _ = O.evaluate (v2.set (O.bdd.heap[jr].var) true) := h2
        _ = (O.high h_root).evaluate v2 := by
          rw [evaluate_high_eq_evaluate_set_true]
          rfl
termination_by O
decreasing_by
  · simp [flip, oedge_of_low]
  · simp [flip, oedge_of_high]

lemma OBdd.usesVar_of_dependsOn {O : OBdd n m} {i : Fin n} :
    O.evaluate v ≠ O.evaluate (v.set i b) → O.1.usesVar i := by
  intro h
  cases O_root_def : O.1.root with
  | terminal _ =>
    simp [evaluate_terminal O_root_def] at h
  | node j =>
    cases decEq O.1.heap[j].var i with
    | isFalse hf =>
      cases lt_or_gt_of_ne hf with
      | inl hl =>
        rw [evaluate_node' O_root_def] at h
        simp only at h
        split at h
        next hh =>
          simp only [Fin.getElem_fin] at h hh hf
          simp_rw [Vector.getElem_set_ne (xs := v) (i := i.1) (j := O.1.heap[j.1].var) (by omega) (by omega) (by omega)] at h
          rw [hh] at h
          simp only [↓reduceIte] at h
          exact usesVar_of_high_usesVar (usesVar_of_dependsOn h)
        next hh =>
          simp only [Bool.not_eq_true] at hh
          simp only [Fin.getElem_fin] at h hh hf
          simp_rw [Vector.getElem_set_ne (xs := v) (i := i.1) (j := O.1.heap[j.1].var) (by omega) (by omega) (by omega)] at h
          rw [hh] at h
          simp only [Bool.false_eq_true, ↓reduceIte, ne_eq] at h
          exact usesVar_of_low_usesVar (usesVar_of_dependsOn h)
      | inr hr =>
        have := (independentOf_lt_root O ⟨i.1, by simp [var, Bdd.var, O_root_def]; omega⟩) b v
        contradiction
    | isTrue ht =>
      use j
      constructor
      · rw [O_root_def]; left
      · exact ht
termination_by O

lemma OBdd.usesVar_iff_dependsOn_of_reduced {O : OBdd n m} :
    O.Reduced → (O.1.usesVar i ↔ Nary.DependsOn O.evaluate i) := by
  intro hr
  constructor
  · rintro ⟨j, hj, hi⟩
    rw [Nary.dependsOn_iff]
    exact OBdd.dependsOn_of_usesVar_of_reduced hr hj hi
  · intro nind
    simp only [Nary.DependsOn, Nary.IndependentOf, not_forall] at nind
    rcases nind with ⟨b, v, hbv⟩
    exact usesVar_of_dependsOn hbv

lemma OBdd.usesVar_iff (i : Fin n) (O : OBdd n m) : O.1.usesVar i ↔ (∃ j, ∃ (hj : O.1.root = node j), (O.1.heap[j].var = i ∨ ((O.low hj).1.usesVar i ∨ (O.high hj).1.usesVar i))) := by
  constructor
  · rintro ⟨j, hj, hi⟩
    rcases O_def : O with ⟨⟨heap, root⟩, o⟩
    simp_all
    cases root with
    | terminal _ =>
      cases hj with
      | cons e => exact False.elim (not_terminal_edge e)
    | node j' =>
      use j', rfl
      cases hj with
      | refl => left; assumption
      | cons e r =>
        cases e with
        | low =>
          right
          left
          use j
          simp only [low, Bdd.low]
          constructor
          · exact r
          · exact hi
        | high =>
          right
          right
          use j
          simp only [high, Bdd.high]
          constructor
          · exact r
          · exact hi
  · rintro ⟨j, hj, h⟩
    cases h with
    | inl h =>
      use j
      rw [hj]
      constructor
      · left
      · exact h
    | inr h =>
      cases h with
      | inl h => exact usesVar_of_low_usesVar h
      | inr h => exact usesVar_of_high_usesVar h

lemma OBdd.toTree_usesVar {O : OBdd n m} : O.1.usesVar i ↔ O.toTree.usesVar i := by
  constructor
  · rw [OBdd.usesVar_iff]
    rw [DecisionTree.usesVar_iff]
    rintro ⟨j, hj, h⟩
    rw [toTree_node hj]
    use O.1.heap[j].var, (O.low hj).toTree, (O.high hj).toTree
    cases h with
    | inl h => simp_all
    | inr h =>
      simp only [Fin.getElem_fin, true_and]
      right
      cases h with
      | inl h =>
        left
        rw [toTree_usesVar (O := (O.low hj))] at h
        assumption
      | inr h =>
        right
        rw [toTree_usesVar (O := (O.high hj))] at h
        assumption
  · intro h
    cases O_root_def : O.1.root with
    | terminal _ =>
      rw [toTree_terminal O_root_def] at h
      contradiction
    | node j =>
      rw [DecisionTree.usesVar_iff] at h
      rcases h with ⟨i', l, h, h1, h2⟩
      rw [toTree_node O_root_def] at h1
      injection h1 with ha hl hh
      cases h2 with
      | inl h2 =>
        use j
        constructor
        · rw [O_root_def]; left
        · simp_all
      | inr h2 =>
        cases h2 with
        | inl h2 =>
          rw [← hl, ← toTree_usesVar] at h2
          exact usesVar_of_low_usesVar h2
        | inr h2 =>
          rw [← hh, ← toTree_usesVar] at h2
          exact usesVar_of_high_usesVar h2
termination_by O

lemma OBdd.evaluate_eq_of_forall_usesVar {O : OBdd n m} {I J : Vector Bool n} :
    (∀ i, O.1.usesVar i → I[i] = J[i]) → O.evaluate I = O.evaluate J := by
  intro h
  apply Nary.eq_of_forall_dependency_getElem_eq
  rintro ⟨i, hi⟩
  apply h
  simp only [Nary.DependsOn, Nary.IndependentOf, not_forall] at hi
  rcases hi with ⟨b, v, hbv⟩
  apply usesVar_of_dependsOn hbv

lemma Pointer.eq_terminal_of_reachable : Pointer.Reachable w (.terminal b) p → p = (.terminal b) := by
  intro h
  cases h with
  | refl => rfl
  | cons => contradiction

lemma Bdd.not_usesVar_of_terminal : ¬ Bdd.usesVar ⟨M, .terminal b⟩ i := by
  simp only [usesVar, not_exists]
  intro j
  simp only [Fin.getElem_fin, not_and]
  intro hr
  apply eq_terminal_of_reachable at hr
  contradiction


lemma Bdd.not_usesVar_of_var_gt {M : Vector (Node n m) m} {j : Fin m} : Bdd.Ordered ⟨M, .node j⟩ → M[j].var > i → ¬ Bdd.usesVar ⟨M, .node j⟩ i := by
  intro o h
  simp only [usesVar, not_exists]
  intro j'
  simp only [Fin.getElem_fin, not_and]
  intro hr
  have := mayPrecede_of_reachable (B := ⟨M, .node j⟩) (p := .node j') o hr
  simp_all only [Fin.getElem_fin, gt_iff_lt, Nat.succ_eq_add_one]
  simp_all only [toVar, Nat.succ_eq_add_one, Fin.getElem_fin, Fin.mk_le_mk, Fin.val_fin_le]
  omega

private def usesVar_helper
    (O : OBdd n m) (i : Fin n) (p : Pointer m) (hpr : Reachable O.1.heap O.1.root p) :
  StateM
    { s : Std.HashSet (Fin m) //
      ∀ j ∈ s, Reachable O.1.heap O.1.root (.node j) ∧ ¬ Bdd.usesVar ⟨O.1.heap, .node j⟩ i }
    (Decidable (Bdd.usesVar ⟨O.1.heap, p⟩ i)) :=
  match p with
  | .terminal b => return isFalse not_usesVar_of_terminal
  | .node j =>
    if hgt : O.1.heap[j].var > i
    then return isFalse (not_usesVar_of_var_gt (Bdd.ordered_of_reachable hpr) hgt)
    else
    if hv : O.1.heap[j].var = i
      then return isTrue ⟨j, .refl, hv⟩
      else do
        let s ← get
        if hh : j ∈ s.1
        then return isFalse (s.2 j hh).2
        else
          match ← usesVar_helper O i O.1.heap[j].low (.snoc hpr .low) with
          | isTrue ht => return isTrue (by apply usesVar_of_low_usesVar; simp only [Bdd.low]; exact ht; rfl)
          | isFalse hf =>
          -- TODO : why is the type annotation needed here? Note that only `←` does not work, for some reason `:= ←` is needed
          let h : Decidable (Bdd.usesVar ⟨O.bdd.heap, O.bdd.heap[j].high⟩ i) :=
            ← usesVar_helper O i O.1.heap[j].high (.snoc hpr .high)
          match h with
          | isTrue htt => return isTrue (by apply usesVar_of_high_usesVar; simp only [Bdd.high]; exact htt; rfl)
          | isFalse hff =>
            have : ¬ Bdd.usesVar { heap := O.1.heap, root := node j } i := by
              intro contra
              rw [OBdd.usesVar_iff (O := ⟨⟨O.1.heap, .node j⟩, Bdd.ordered_of_reachable hpr⟩)] at contra
              grind only [OBdd.low, low, OBdd.high, high]
            set ( ⟨ s.1.insert j,
                    by
                      intro j'
                      rw [Std.HashSet.mem_insert, beq_iff_eq]
                      rintro (rfl | h)
                      · exact ⟨hpr, this⟩
                      · exact (s.2 j' h)
                  ⟩ : { s : Std.HashSet (Fin m) // ∀ j, j ∈ s → Reachable O.1.heap O.1.root (.node j) ∧ ¬ Bdd.usesVar ⟨O.1.heap, .node j⟩ i }
                )
            return isFalse this
termination_by OBdd.size' (⟨⟨O.1.heap, p⟩, Bdd.ordered_of_reachable hpr⟩ : OBdd n m)
decreasing_by
  · simp [OBdd.size_node, OBdd.low, Bdd.low]; omega
  · simp [OBdd.size_node, OBdd.high, Bdd.high]

@[no_expose]
instance OBdd.instDecidableUsesVar {O : OBdd n m} : DecidablePred O.1.usesVar :=
  fun i ↦ (usesVar_helper O i O.1.root .refl ⟨Std.HashSet.emptyWithCapacity, by simp⟩).1

lemma Bdd.terminal_of_zero_vars {B : Bdd n m} : n = 0 → ∃ b, B.root = .terminal b := by
  intro h
  subst h
  cases hr : B.root with
  | terminal b => exact ⟨b, rfl⟩
  | node j => exact False.elim (Nat.not_lt_zero _ B.heap[j].var.2)

lemma Bdd.terminal_of_zero_heap {B : Bdd n m} : m = 0 → ∃ b, B.root = .terminal b := by
  intro h
  subst h
  cases hr : B.root with
  | terminal b => exact ⟨b, rfl⟩
  | node j => exact False.elim (Nat.not_lt_zero _ j.2)

@[expose]
def Pointer.equiv (p : Pointer m) (p' : Pointer m') :=
  (∀ b, p = .terminal b → p' = .terminal b) ∧ (∀ j, p = .node j → ∃ (j' : Fin m'), p' = .node j' ∧ j.1 = j'.1)

lemma Pointer.equiv_refl (p : Pointer m) : p.equiv p := by
  simp only [Pointer.equiv]
  constructor
  · intro b hb
    exact hb
  · intro j hj
    use j

lemma Pointer.equiv_symm {p : Pointer m} : p.equiv q → q.equiv p := by
  simp only [Pointer.equiv]
  simp_all only [Bool.forall_bool, and_imp]
  intro h1 h2 h3
  constructor
  · constructor
    · intro hq
      cases p with
      | terminal b => grind only [terminal.injEq]
      | node _ =>
        rcases (h3 _ rfl) with ⟨_, hc⟩
        rw [hc.1] at hq; contradiction
    · intro hq
      cases p with
      | terminal b => grind only [terminal.injEq]
      | node _ =>
        rcases (h3 _ rfl) with ⟨_, hc⟩
        rw [hc.1] at hq; contradiction
  · intro j hj
    cases p with
    | terminal b => grind only [terminal.injEq]
    | node j' =>
      rcases h3 j' rfl with ⟨j'', hj1, hj2⟩
      rw [hj1] at hj
      injection hj with heq
      subst heq
      use j'
      simp [hj2]

@[expose]
def Node.equiv (N : Node n m) (N' : Node n' m') :=
  N.var.1 = N'.var.1 ∧ Pointer.equiv N.low N'.low ∧ Pointer.equiv N.high N'.high

lemma Node.equiv_refl (N : Node n m) : N.equiv N := by
  simp only [Node.equiv]
  simp
  constructor
  · exact Pointer.equiv_refl N.low
  · exact Pointer.equiv_refl N.high

lemma Node.equiv_symm : Node.equiv N M → Node.equiv M N := by
  simp only [Node.equiv]
  simp_all
  intro h1 h2 h3
  constructor
  · exact Pointer.equiv_symm h2
  · exact Pointer.equiv_symm h3

lemma Bdd.ordered_of_ordered_heap_all_reachable_eq (O : OBdd n m) (B : Bdd n m') :
    (∀ j : Fin m', Reachable B.heap B.root (node j) → ∃ hj : j.1 < m, Node.equiv O.1.heap[j.1] B.heap[j]) →
    (∀ j, B.root = .node j → ∃ hj, O.1.root = .node ⟨j.1, hj⟩) →
    Ordered B := by
  intro h1 h2
  cases B_root_def : B.root with
  | terminal b => exact ordered_of_terminal B_root_def
  | node j =>
    rcases h2 _ B_root_def with ⟨hj1', hj2'⟩
    apply ordered_of_low_high_ordered B_root_def
    · apply ordered_of_ordered_heap_all_reachable_eq (O.low hj2')
      · intro jj hrjj
        simp only [low_heap_eq_heap]
        apply h1
        apply Relation.reflTransGen_swap.mpr
        right
        exact Relation.reflTransGen_swap.mp hrjj
        exact B.edge_low B_root_def
      · intro jl B_low_def
        simp only [OBdd.low, Bdd.low, Fin.getElem_fin]
        rcases h1 jl (.snoc .refl (by rw [← B_low_def]; exact B.edge_low _)) with ⟨hjl1, _⟩
        rcases h1 j (by rw [← B_root_def]; left) with ⟨hj1, hj2, hj3, hj4⟩
        rcases Pointer.equiv_symm hj3 with ⟨hj31, hj32⟩
        use hjl1
        simp only [Bdd.low] at B_low_def
        rcases hj32 _ B_low_def with ⟨j', hj1', hj2'⟩
        rw [hj1']
        simp only [node.injEq]
        exact Fin.eq_mk_iff_val_eq.mpr (id (Eq.symm hj2'))
    · rcases h1 j (by rw [← B_root_def]; left) with ⟨hj1, hj2, hj3, hj4⟩
      have := OBdd.var_lt_low_var (O := O) (h := hj2')
      simp_all [OBdd.var, Bdd.var, OBdd.low, Bdd.low]
      apply Fin.lt_def.mpr
      simp only [toVar]
      have that : (toVar B.heap B.heap[j.1].low).1 = (toVar O.1.heap O.1.heap[j.1].low).1 := by
        rcases Pointer.equiv_symm hj3 with ⟨hj31, hj32⟩
        cases hl : B.heap[↑j].low with
        | terminal b =>
          simp [hj31 b hl]
        | node jl =>
          rcases hj32 jl hl with ⟨jl', hjl1', hjl2'⟩
          rw [hjl1']
          simp only [Nat.succ_eq_add_one, toVar_node, Fin.getElem_fin]
          simp_rw [← hjl2']
          rcases h1 jl (by rw [← hl]; exact Reachable.ofEdge .low) with ⟨hs1, hs2, _, _⟩
          exact symm hs2
      simp only [toVar] at that
      rw [that]
      exact this
    · apply ordered_of_ordered_heap_all_reachable_eq (O.high hj2')
      · intro jj hrjj
        simp only [high_heap_eq_heap]
        apply h1
        apply Relation.reflTransGen_swap.mpr
        right
        exact Relation.reflTransGen_swap.mp hrjj
        exact B.edge_high B_root_def
      · intro jl B_high_def
        simp only [OBdd.high, Bdd.high, Fin.getElem_fin]
        rcases h1 jl (.snoc .refl (by rw [← B_high_def]; exact B.edge_high _)) with ⟨hjl1, _⟩
        rcases h1 j (by rw [← B_root_def]; left) with ⟨hj1, hj2, hj3, hj4⟩
        rcases Pointer.equiv_symm hj4 with ⟨hj41, hj42⟩
        use hjl1
        simp only [Bdd.high] at B_high_def
        rcases hj42 _ B_high_def with ⟨j', hj1', hj2'⟩
        rw [hj1']
        simp only [node.injEq]
        exact Fin.eq_mk_iff_val_eq.mpr (id (Eq.symm hj2'))
    · rcases h1 j (by rw [← B_root_def]; left) with ⟨hj1, hj2, hj3, hj4⟩
      have := OBdd.var_lt_high_var (O := O) (h := hj2')
      simp_all [OBdd.var, Bdd.var, OBdd.high, Bdd.high]
      apply Fin.lt_def.mpr
      simp only [toVar]
      have that : (toVar B.heap B.heap[j.1].high).1 = (toVar O.1.heap O.1.heap[j.1].high).1 := by
        rcases Pointer.equiv_symm hj4 with ⟨hj41, hj42⟩
        cases hl : B.heap[↑j].high with
        | terminal b =>
          simp [hj41 b hl]
        | node jl =>
          rcases hj42 jl hl with ⟨jl', hjl1', hjl2'⟩
          rw [hjl1']
          simp only [Nat.succ_eq_add_one, toVar_node, Fin.getElem_fin]
          simp_rw [← hjl2']
          rcases h1 jl (by rw [← hl]; exact Reachable.ofEdge .high) with ⟨hs1, hs2, _, _⟩
          exact symm hs2
      simp only [toVar] at that
      rw [that]
      exact this
termination_by O

lemma OBdd.toTree_eq_toTree_of_ordered_heap_all_reachable_eq (O : OBdd n m) (U : OBdd n m') :
    (∀ j : Fin m', Reachable U.1.heap U.1.root (node j) → ∃ hj : j.1 < m, Node.equiv O.1.heap[j.1] U.1.heap[j]) →
    Pointer.equiv U.1.root O.1.root →
    O.toTree = U.toTree := by
  intro h1 h2
  cases U_root_def : U.1.root with
  | terminal b =>
    simp only [Pointer.equiv] at h2
    have := h2.1 b U_root_def
    simp_all [OBdd.toTree_terminal]
  | node j =>
    simp only [Pointer.equiv] at h2
    have := h2.2 j U_root_def
    rcases this with ⟨j', hj', hjj'⟩
    rw [OBdd.toTree_node U_root_def]
    rw [OBdd.toTree_node hj']
    have := h1 j (by simp [U_root_def]; left)
    rcases this with ⟨hj, hev, hel, heh⟩
    congr 1
    · simp_all; apply Fin.eq_of_val_eq; exact hev
    · apply toTree_eq_toTree_of_ordered_heap_all_reachable_eq
      · intro jj hrjj
        simp only [low_heap_eq_heap]
        apply h1
        apply Relation.reflTransGen_swap.mpr
        right
        exact Relation.reflTransGen_swap.mp hrjj
        exact oedge_of_low.2
      · simp_all [OBdd.low, Bdd.low]
        exact Pointer.equiv_symm hel
    · apply toTree_eq_toTree_of_ordered_heap_all_reachable_eq
      · intro jj hrjj
        simp only [high_heap_eq_heap]
        apply h1
        apply Relation.reflTransGen_swap.mpr
        right
        exact Relation.reflTransGen_swap.mp hrjj
        exact oedge_of_high.2
      · simp_all [OBdd.high, Bdd.high]
        exact Pointer.equiv_symm heh
termination_by O

lemma OBdd.evaluate_eq_evaluate_of_ordered_heap_all_reachable_eq (O : OBdd n m) (U : OBdd n m') :
    (∀ j : Fin m', Reachable U.1.heap U.1.root (node j) → ∃ hj : j.1 < m, Node.equiv O.1.heap[j.1] U.1.heap[j]) →
    Pointer.equiv U.1.root O.1.root →
    O.evaluate = U.evaluate := by
  intro h1 h2
  ext I
  simp only [OBdd.evaluate, Function.comp_apply]
  rw [toTree_eq_toTree_of_ordered_heap_all_reachable_eq O U h1 h2]


namespace RawBdd

@[expose]
def RawPointer := Bool ⊕ Nat

structure RawNode (n) where
  va : Fin n
  lo : RawPointer
  hi : RawPointer

@[expose]
def RawPointer.Bounded (m : Nat) (p : RawPointer) := ∀ {i}, p = .inr i → i < m

lemma RawPointer.bounded_of_le {p : RawPointer} (hm : p.Bounded m) (h : m ≤ m') : p.Bounded m' := by
  intro i hi
  cases hp : p with
  | inl val => simp_all
  | inr val =>
    have := hm hp
    simp_all
    injection hi with heq
    subst heq
    omega

@[expose]
def RawPointer.cook (p : RawPointer) (h : p.Bounded m) : Pointer m :=
  match p with
  | .inl b => .terminal b
  | .inr i => .node ⟨i, h rfl⟩

lemma RawPointer.cook_equiv {h1 : RawPointer.Bounded m1 p} {h2 : RawPointer.Bounded m2 p} : Pointer.equiv (RawPointer.cook p h1) (RawPointer.cook p h2) := by
  simp only [Pointer.equiv]
  constructor
  · intro b hb
    cases p <;> simp_all [RawPointer.cook]
  · intro j hj
    cases p with
    | inl val => contradiction
    | inr val =>
      simp only [Bounded] at h1 h2
      simp only [cook, Pointer.node.injEq] at hj
      rw [Fin.eq_mk_iff_val_eq] at hj
      simp only at hj
      subst hj
      use ⟨j.1, h2 rfl⟩
      simp [RawPointer.cook]

/-- `cook` ignores the `Bounded` witness: the bound is a `Prop`, so two cooks of the same
raw pointer at the same heap size are equal. -/
lemma RawPointer.cook_eq {p : RawPointer} {h1 h2 : p.Bounded m} : p.cook h1 = p.cook h2 := by
  cases p with
  | inl _ => rfl
  | inr i => exact congrArg Pointer.node (Fin.ext rfl)

def RawPointer.fromPointer : Pointer m → RawPointer
  | .terminal b => .inl b
  | .node j => .inr j.1

@[expose]
def RawNode.Bounded (m : Nat) (N : RawNode n) := N.lo.Bounded m ∧ N.hi.Bounded m

lemma RawNode.bounded_of_le {N : RawNode n} (hm : N.Bounded m) (h : m ≤ m') : N.Bounded m' :=
  ⟨RawPointer.bounded_of_le hm.1 h, RawPointer.bounded_of_le hm.2 h⟩

@[expose]
def RawNode.cook (N : RawNode n) (h : N.Bounded m) : Node n m := ⟨N.va, N.lo.cook h.1, N.hi.cook h.2⟩

lemma RawNode.cook_equiv : Node.equiv (RawNode.cook N h1) (RawNode.cook N h2) := by
  simp only [Node.equiv]
  constructor
  · rfl
  · rcases h1 with ⟨h11, h12⟩
    rcases h2 with ⟨h21, h22⟩
    constructor
    · apply RawPointer.cook_equiv <;> assumption
    · apply RawPointer.cook_equiv <;> assumption

@[expose]
def cook_heap (v : Vector (RawNode n) c) (hh : ∀ i : Fin c, v[i].Bounded i) : Vector (Node n c) c :=
  Vector.ofFn (fun i ↦ v[i].cook (RawNode.bounded_of_le (hh i) (by omega)))

@[expose]
def toVar_or (M : Vector (Node n m) m) : Pointer m → Nat → Nat
  | .terminal _, i => i
  | .node j, _     => M[j].var

@[simp]
lemma toVar_or_terminal_eq {n m} (w : Vector (Node n m) m) : toVar_or w (.terminal b) i = i := (rfl)

@[simp]
lemma toVar_or_node_eq {n m} (w : Vector (Node n m) m) {j} : toVar_or w (.node j) i = w[j].var := (rfl)

lemma cook_low {rn : RawNode n} {h1} {h2} : rn.lo.cook (m := m) h1 = (rn.cook h2).low := (rfl)

lemma cook_high {rn : RawNode n} {h1} {h2} : rn.hi.cook (m := m) h1 = (rn.cook h2).high := (rfl)

lemma cook_inj {p q : RawPointer} {hp} {hq} : p.cook (m := m) hp = q.cook hq → p = q := by
  intro h
  cases p <;> cases q <;> simp_all [RawPointer.cook]

lemma cook_aux {p : RawPointer} {h1} {h2} : p.cook h1 = .node j → p.cook h2 = .node ⟨j, hj⟩ := by
  intro h
  cases p with
  | inl val => simp_all [RawPointer.cook]
  | inr val =>
    simp_all [RawPointer.cook]
    rw [Fin.eq_mk_iff_val_eq] at h
    exact h

private lemma push_ordered_aux {v : Vector (RawNode n) m} {h0} {h2} :
    Reachable (cook_heap (v.push N) h2) (RawPointer.cook p h3) q →
    ∀ j, q = .node j →
    ∃ hj : j < m, Pointer.Reachable (cook_heap v h0) (p.cook h1) (.node ⟨j.1, hj⟩) := by
  intro h
  induction h with
  | refl =>
    intro i hi
    cases p with
    | inl val => contradiction
    | inr val =>
      simp [RawPointer.cook] at hi
      subst hi
      simp only
      use h1 rfl
      simp [RawPointer.cook]
      left
  | snoc r e ih =>
    rintro j rfl
    rename_i b
    simp only [RawNode.Bounded] at h2
    obtain ⟨jb, rfl, h4⟩ := edge_iff.1 e
    specialize h2 jb
    simp_all only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn]
    have h5 : RawPointer.Bounded (m + 1) (Sum.inr j) := by
      simp [RawPointer.Bounded]
      intro i hi
      injection hi with heq
      rw [← heq]
      omega
    have h6 : j < jb := by
      rcases h4 with h4 | h4
      · apply h2.1
        rw [show Pointer.node j = RawPointer.cook (.inr j.1) h5 by rfl] at h4
        rw [← cook_low] at h4
        exact cook_inj h4.symm
        apply RawPointer.bounded_of_le h2.1
        omega
      · apply h2.2
        rw [show Pointer.node j = RawPointer.cook (.inr j.1) h5 by rfl] at h4
        rw [← cook_high] at h4
        exact cook_inj h4.symm
        apply RawPointer.bounded_of_le h2.2
        omega
    use lt_of_lt_of_le h6 (Nat.le_of_lt_succ jb.2)
    rcases (ih jb rfl) with ⟨r1, r2⟩
    trans .node ⟨jb, r1⟩
    · exact r2
    · simp_rw [Vector.getElem_push_lt r1] at h4
      right
      left
      rcases h4 with h4 | h4
      · convert Edge.low
        simp [RawNode.cook]
        rw [cook_aux h4.symm]
      · convert Edge.high
        simp [RawNode.cook]
        rw [cook_aux h4.symm]

lemma push_ordered : Bdd.Ordered ⟨cook_heap v h0, RawPointer.cook p h1⟩ → Bdd.Ordered ⟨cook_heap (v.push N) h2, RawPointer.cook p h3⟩ := by
  intro h
  apply Bdd.ordered_of_ordered_heap_all_reachable_eq ⟨⟨cook_heap v h0, RawPointer.cook p h1⟩, h⟩
  · intro j hj
    rcases (push_ordered_aux hj (h2 := h2) (h1 := h1) (h0 := h0) j rfl) with ⟨r1, r2⟩
    use r1
    simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_push_lt r1,
      RawNode.cook_equiv]
  · intro j hj
    simp_all only
    simp [RawPointer.cook] at hj
    split at hj
    next heq => contradiction
    next heq =>
      simp only [Pointer.node.injEq] at hj
      subst hj
      use h1 rfl
      simp [RawPointer.cook]

lemma push_evaluate {n m} {O : OBdd n (m + 1)} {v : Vector (RawNode n) m} {N h0 p hp h1 hp' ho}
    (h_heap : O.bdd.heap = cook_heap (v.push N) h0) (h_root : O.bdd.root = RawPointer.cook p hp) :
    O.evaluate = OBdd.evaluate ⟨⟨cook_heap v h1, RawPointer.cook p hp'⟩, ho⟩ := by
  apply OBdd.evaluate_eq_evaluate_of_ordered_heap_all_reachable_eq
  · simp only [Fin.getElem_fin]
    intro j hj
    use (by omega)
    rw [h_heap]
    simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn, Fin.is_lt, Vector.getElem_push_lt]
    exact RawNode.cook_equiv
  · simp only [h_root]
    exact RawPointer.cook_equiv (h1 := hp') (h2 := hp)

end RawBdd
