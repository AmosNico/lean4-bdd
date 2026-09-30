module

public import Bdd.Basic

public structure Bdd.Monotone {n m} (B : Bdd n m) (f : ℕ → ℕ) : Prop where
  h1 : ∀ i : Fin n, f i < f n
  h2 : ∀ i i' : Fin n, i < i' → B.usesVar i → B.usesVar i' → f i < f i'

lemma OBdd.monotone_low {n m} {O : OBdd n m} {j} {h : O.bdd.root = .node j} {f}
    (hf : O.bdd.Monotone f) : (O.low h).bdd.Monotone f where
  h1 := hf.1
  h2  i i' hii' hi hi' :=
    hf.2 i i' hii' (OBdd.usesVar_of_low_usesVar hi) (OBdd.usesVar_of_low_usesVar hi')

lemma OBdd.monotone_high {n m} {O : OBdd n m} {j} {h : O.bdd.root = .node j} {f}
    (hf : O.bdd.Monotone f) : (O.high h).bdd.Monotone f where
  h1 := hf.1
  h2  i i' hii' hi hi' :=
    hf.2 i i' hii' (OBdd.usesVar_of_high_usesVar hi) (OBdd.usesVar_of_high_usesVar hi')

lemma OBdd.monotone_subBdd {n m} {O : OBdd n m} {p hp} {f}
    (hf : O.bdd.Monotone f) : (O.subBdd ⟨p, hp⟩).bdd.Monotone f where
  h1 := hf.1
  h2  i i' hii' hi hi' :=
    hf.2 i i' hii' (OBdd.usesVar_of_subBdd_usesVar hi) (OBdd.usesVar_of_subBdd_usesVar hi')

namespace Relabel

def relabel_node {n m} {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n) : Node n m → Node (f n) m
  | ⟨var, low, high⟩ => ⟨⟨f var.1, hf _⟩, low, high⟩

def relabel_heap {n m} {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n) :
    Vector (Node n m) m → Vector (Node (f n) m) m := Vector.map (relabel_node hf)

def relabel {n m} {f : ℕ → ℕ} (hf : ∀ i : Fin n, f i < f n) : Bdd n m → Bdd (f n) m
  | ⟨heap, root⟩ => ⟨relabel_heap hf heap, root⟩

lemma relabel_root {n m} {f : ℕ → ℕ} {hf : ∀ i : Fin n, f i < f n} {B : Bdd n m} :
    (relabel hf B).root = B.root := (rfl)

lemma relabel_edge {n m} (B : Bdd n m) {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n) :
    Edge (relabel hf B).heap = Edge B.heap := by
  ext p q
  simp only [edge_iff, Fin.getElem_fin, relabel, relabel_heap, Vector.getElem_map, relabel_node]

lemma relabel_reachable_iff {n m : ℕ} {f : ℕ → ℕ} {h : ∀ (i : Fin n), f i < f n} {x} {B : Bdd n m} :
    Pointer.Reachable (relabel h B).heap (relabel h B).root x ↔
    Pointer.Reachable B.heap B.root x := by
  rw [relabel_root]
  rw [Pointer.Reachable.eq_of_eq_edge (relabel_edge B h)]

lemma relabel_MayPrecede {n m} {B : Bdd n m} {f : ℕ → ℕ} (hf : B.Monotone f) {x y : Pointer m}
    (hx : Pointer.Reachable (relabel hf.1 B).heap (relabel hf.1 B).root x)
    (hy : Pointer.Reachable (relabel hf.1 B).heap (relabel hf.1 B).root y) :
    B.MayPrecede x y → (relabel hf.1 B).MayPrecede x y := by
  simp only [Bdd.mayPrecede_iff, forall_exists_index, and_imp]
  intro j rfl h1
  use j, rfl
  intro j' rfl
  simp only [relabel, relabel_heap, Fin.lt_def]
  simp only [Fin.getElem_fin, Vector.getElem_map, relabel_node]
  apply hf.2
  · exact h1 j' rfl
  · use j
    constructor
    · exact relabel_reachable_iff.mp hx
    · rfl
  · use j'
    constructor
    · exact relabel_reachable_iff.mp hy
    · rfl

lemma relabel_ordered {n m} {B : Bdd n m} {f} (hf : B.Monotone f) :
    Bdd.Ordered B → Bdd.Ordered (relabel hf.1 B) := by
  simp only [Bdd.ordered_iff]
  intro ho p q hp e
  have h : B.MayPrecede p q := by
    rw [relabel_reachable_iff] at hp
    rw [relabel_edge] at e
    exact ho p q hp e
  exact relabel_MayPrecede hf hp (Pointer.Reachable.snoc hp e) h

public def orelabel {n m} (O : OBdd n m) {f} (hf : O.bdd.Monotone f) : OBdd (f n) m :=
    ⟨relabel hf.1 O.1, relabel_ordered hf O.2⟩

lemma orelabel_reachable_iff {n m} {O : OBdd n m} {f : ℕ → ℕ} {hf : O.bdd.Monotone f} {x} :
    Pointer.Reachable (orelabel O hf).bdd.heap (orelabel O hf).bdd.root x ↔
    Pointer.Reachable O.bdd.heap O.bdd.root x :=
  relabel_reachable_iff

lemma low_orelabel {n m} {O : OBdd n m} {j} {h : O.1.root = .node j} {f} (hf : O.bdd.Monotone f) :
    (orelabel O hf).low h = orelabel (O.low h) (OBdd.monotone_low hf) := by
  rw [OBdd.eq_iff_bdd_eq]
  simp only [orelabel, relabel, relabel_heap, OBdd.low_heap_eq_heap, OBdd.low_root_eq_low,
    Fin.getElem_fin, Vector.getElem_map, true_and]
  rfl

lemma high_orelabel {n m} {O : OBdd n m} {j} {h : O.1.root = .node j} {f} (hf : O.bdd.Monotone f) :
    (orelabel O hf).high h = orelabel (O.high h) (OBdd.monotone_high hf) := by
  rw [OBdd.eq_iff_bdd_eq]
  simp only [orelabel, relabel, relabel_heap, OBdd.high_heap_eq_heap, OBdd.high_root_eq_high,
    Fin.getElem_fin, Vector.getElem_map, true_and]
  rfl

lemma subBdd_orelabel {n m} {O : OBdd n m} {f} (hf : O.bdd.Monotone f) {p hp} :
    (orelabel O hf).subBdd ⟨p, hp⟩ =
      orelabel (O.subBdd ⟨p, by rwa [orelabel_reachable_iff] at hp⟩) (OBdd.monotone_subBdd hf) := by
  rw [OBdd.eq_iff_bdd_eq]
  simp only [orelabel, relabel, relabel_heap, OBdd.heap_subBdd, OBdd.root_subBdd, and_self]

@[simp]
public theorem orelabel_evaluate {n m} (O : OBdd n m) {f} (hf : O.bdd.Monotone f) {I} :
    OBdd.evaluate (orelabel O hf) I = O.evaluate (Vector.ofFn (fun i ↦ I[f i]'(hf.1 i))) := by
  simp only [orelabel]
  cases O_root_def : O.1.root with
  | terminal _ =>
    simp only [relabel, O_root_def]
    rw [OBdd.evaluate_terminal O_root_def]
    rw [OBdd.evaluate_terminal rfl]
  | node j =>
    rw [OBdd.evaluate_node' O_root_def]
    have h : (⟨(relabel hf.1 O.1), relabel_ordered hf O.2⟩ : OBdd _ _).1.root = Pointer.node j :=
      O_root_def
    rw [OBdd.evaluate_node' h]
    simp only
    congr 1
    · simp only [relabel, relabel_heap, Fin.getElem_fin, Vector.getElem_map, relabel_node]
      simp_all only [Vector.getElem_ofFn]
    · have := orelabel_evaluate (O.high O_root_def) (OBdd.monotone_high hf) (I := I)
      rw [← this, ← high_orelabel hf]
      rfl
    · have := orelabel_evaluate (O.low O_root_def) (OBdd.monotone_low hf) (I := I)
      rw [← this, ← low_orelabel hf]
      rfl
termination_by O

lemma relabel_toTree_relabel {n m} (O : OBdd n m) {f} (hf : O.bdd.Monotone f) :
    OBdd.toTree (orelabel O hf) = DecisionTree.relabel hf.1 (OBdd.toTree O) := by
  simp only [orelabel]
  cases O_root_def : O.1.root with
  | terminal b =>
    simp only [relabel]
    rw [OBdd.toTree_terminal O_root_def]
    simp_rw [O_root_def]
    rw [OBdd.toTree_terminal rfl]
    simp [DecisionTree.relabel]
  | node _ =>
    rw [OBdd.toTree_node O_root_def]
    rw [OBdd.toTree_node (by trans O.1.root; rfl; exact O_root_def)]
    simp only [Fin.getElem_fin]
    congr 1
    · simp only [relabel, relabel_heap, Vector.getElem_map, relabel_node]
    · have := relabel_toTree_relabel (O.low O_root_def) (OBdd.monotone_low hf)
      rw [← low_orelabel hf] at this
      exact this
    · have := relabel_toTree_relabel (O := (O.high O_root_def)) (OBdd.monotone_high hf)
      rw [← high_orelabel hf] at this
      exact this
termination_by O

lemma orelabel_preserves_similarRP_aux {n m} {O : OBdd n m} {f} (hf : O.bdd.Monotone f)
    {p q} (hb : (O.subBdd p).toTree.relabel hf.1 = (O.subBdd q).toTree.relabel hf.1) :
    (O.subBdd p).toTree = (O.subBdd q).toTree := by
  rw [DecisionTree.relabel_injective hb]
  intro ii ii' hii hii' hfi
  rw [← OBdd.toTree_usesVar] at hii hii'
  apply OBdd.usesVar_of_subBdd_usesVar at hii
  apply OBdd.usesVar_of_subBdd_usesVar at hii'
  contrapose hfi
  cases ne_iff_lt_or_gt.mp hfi
  next h => grind only [hf.2 ii ii' h hii hii']
  next h => grind only [hf.2 ii' ii h hii' hii]

lemma orelabel_preserves_similarRP {n m} {O : OBdd n m} {f} (hf : O.bdd.Monotone f)
    {p q : Pointer m}
    {hp : Pointer.Reachable (orelabel O hf).1.heap (orelabel O hf).1.root p}
    {hq : Pointer.Reachable (orelabel O hf).1.heap (orelabel O hf).1.root q} :
    (orelabel O hf).SimilarRP ⟨p, hp⟩ ⟨q, hq⟩ →
    O.SimilarRP ⟨p, orelabel_reachable_iff.mp hp⟩ ⟨q, orelabel_reachable_iff.mp hq⟩ := by
  intro sim
  simp only [OBdd.similarRP_iff] at ⊢ sim
  cases p with
  | terminal _ =>
    cases q with
    | terminal _ =>
      simp_all only [OBdd.subBdd_eq, Pointer.terminal.injEq, OBdd.toTree_terminal,
        DecisionTree.leaf.injEq]
    | node _ =>
      simp only [Pointer.terminal.injEq, OBdd.toTree_terminal, OBdd.subBdd_eq] at sim
      rw [OBdd.toTree_node rfl] at sim
      contradiction
  | node j =>
    cases q with
    | terminal _ =>
      simp only [Pointer.terminal.injEq, OBdd.toTree_terminal, OBdd.subBdd_eq] at sim
      rw [OBdd.toTree_node rfl] at sim
      contradiction
    | node i =>
      rw [OBdd.toTree_node (OBdd.root_subBdd ⟨Pointer.node j, _⟩)] at sim ⊢
      rw [OBdd.toTree_node (OBdd.root_subBdd ⟨Pointer.node i, _⟩)] at sim ⊢
      injection sim with ha hb hc
      simp only [orelabel, relabel, relabel_heap, OBdd.heap_subBdd, Fin.getElem_fin,
        Vector.getElem_map, relabel_node, Fin.mk.injEq] at ha
      simp only [OBdd.heap_subBdd, OBdd.low_subBdd, OBdd.high_subBdd, DecisionTree.branch.injEq]
      simp only [subBdd_orelabel] at hb hc
      simp only [orelabel_reachable_iff] at hp hq
      split_ands
      · contrapose ha
        simp_rw [ne_iff_lt_or_gt] at ha ⊢
        cases ha with
        | inl h => exact .inl (hf.2 O.1.heap[j].var O.1.heap[i].var h ⟨j, hp, rfl⟩ ⟨i, hq, rfl⟩)
        | inr h => exact .inr (hf.2 O.1.heap[i].var O.1.heap[j].var h ⟨i, hq, rfl⟩ ⟨j, hp, rfl⟩)
      · have h1 := low_orelabel
          (O := O.subBdd ⟨.node j, hp⟩)
          (h := OBdd.root_subBdd _)
          (OBdd.monotone_subBdd hf)
        have h2 := low_orelabel
          (O := O.subBdd ⟨.node i, hq⟩)
          (h := OBdd.root_subBdd _)
          (OBdd.monotone_subBdd hf)
        rw [h1, h2] at hb
        simp only [OBdd.low_subBdd, relabel_toTree_relabel] at hb
        exact orelabel_preserves_similarRP_aux hf hb
      · have h1 := high_orelabel
          (O := O.subBdd ⟨.node j, hp⟩)
          (h := OBdd.root_subBdd _)
          (OBdd.monotone_subBdd hf)
        have h2 := high_orelabel
          (O := O.subBdd ⟨.node i, hq⟩)
          (h := OBdd.root_subBdd _)
          (OBdd.monotone_subBdd hf)
        rw [h1, h2] at hc
        simp only [OBdd.high_subBdd, relabel_toTree_relabel] at hc
        exact orelabel_preserves_similarRP_aux hf hc

public lemma orelabel_reduced {n m} {O : OBdd n m} {f} (hf : O.bdd.Monotone f) :
    O.Reduced → (orelabel O hf).Reduced := by
  rintro ⟨r1, r2⟩
  constructor
  · rintro ⟨_, hp⟩ ⟨j, red⟩
    simp only [orelabel, relabel, relabel_heap, Fin.getElem_fin, Vector.getElem_map] at red
    simp only [relabel_node] at red
    apply r1 ⟨.node j, relabel_reachable_iff.mp hp⟩
    exact .red j red
  · rintro _ _ sim
    exact r2 (orelabel_preserves_similarRP hf sim)

@[simp]
lemma relabel_id {n m} {B : Bdd n m} : relabel (f := id) (by simp) B = B := by
  simp only [id_eq, relabel, relabel_heap]
  congr
  ext i hi
  simp only [Vector.getElem_map, relabel_node, id_eq, Fin.eta]

@[simp]
public lemma orelabel_id {n m} {O : OBdd n m} :
    orelabel O (f := id) ⟨by simp, fun _ _ _ _ _ ↦ by simpa⟩ = O := by
  simp [orelabel]

end Relabel
