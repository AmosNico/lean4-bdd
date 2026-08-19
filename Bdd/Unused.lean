module

import all Bdd.Basic
import all Bdd.Size

section not_used
open Pointer

inductive Pointer.le {m} : Pointer m → Pointer m → Prop where
  | terminal_le_terminal {b c} : b ≤ c → le (terminal b) (terminal c)
  | terminal_le_node {b j} : le (terminal b) (node j)
  | node_le_node {j i} : j ≤ i → le (node j) (node i)

instance Pointer.instLE : LE (Pointer m) := {le := Pointer.le}

instance Pointer.instDecidableLe {m} : DecidableLE (Pointer m) :=
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

@[simp]
def Pointer.MayPrecede {n m} (M : Vector (Node n m) m) (p q : Pointer m) := toVar M p < toVar M q

/-- Terminals must not precede other pointers. -/
@[simp, grind .]
lemma Pointer.not_terminal_mayPrecede : ¬ MayPrecede M (terminal b) p := by
  cases p with
  | terminal _ => simp [MayPrecede]
  | node     j => exact not_lt.mpr (Fin.le_last _)

/-- Non-terminals may precede terminals. -/
lemma Pointer.MayPrecede_node_terminal {n m} (w : Vector (Node n m) m) {j b} : MayPrecede w (node j) (terminal b) := by
  simp only [MayPrecede, Nat.succ_eq_add_one, toVar, Fin.getElem_fin]
  refine Fin.mk_lt_of_lt_val ?_
  simp only [Fin.val_last, Fin.is_lt]

def OBdd.OReachable {n m} := Relation.ReflTransGen (@OEdge n m)

lemma OBdd.low_oreachable {n m} {j} {O U : OBdd n m} {U_root_def : U.1.root = node j}:
    O.OReachable U → O.OReachable (U.low U_root_def) :=
  fun h ↦ Relation.ReflTransGen.tail h oedge_of_low

lemma OBdd.high_oreachable {n m} {j} {O U : OBdd n m} {U_root_def : U.1.root = node j} :
    O.OReachable U → O.OReachable (U.high U_root_def) :=
  fun h ↦ Relation.ReflTransGen.tail h oedge_of_high

lemma aux {O : OBdd n m} {i : Fin m} :
    O.1.heap[i.1].var = Fin.castPred (toVar O.1.heap (node i)) (Fin.exists_castSucc_eq.mp ⟨O.1.heap[i.1].var, by simp [toVar]; rfl⟩) :=
  by simp [toVar]

/-- The output of equal constant functions with inhabited domain is equal. -/
lemma eq_of_constant_eq {α β} {c c' : β} [Inhabited α] :
    Function.const α c = Function.const α c' → c = c' :=
  fun h ↦ (show (Function.const α c) default = (Function.const α c') default by rw [h])

lemma OBdd.reachable_node_iff {n m j} {O : OBdd n m} (h : O.1.root = node j) :
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

/-- Similarity of `Ordered` BDDs is decidable. -/
instance OBdd.instDecidableSimilar {n m} : DecidableRel (β := OBdd n m) OBdd.Similar :=
  fun O U ↦ decidable_of_decidable_of_iff (show O.toTree = U.toTree ↔ _ by simp [Similar, HSimilar])

-- FIXME: Use the instance from Sim.lean instead.
instance OBdd.instDecidableHSimilar {n m m'} (O : OBdd n m) (U : OBdd n m') : Decidable (OBdd.HSimilar O U) :=
  decidable_of_decidable_of_iff (show O.toTree = U.toTree ↔ _ by simp [HSimilar])

@[no_expose]
instance OBdd.instDecidableSimilarRP : Decidable (OBdd.SimilarRP O l r) := by
  simp only [OBdd.SimilarRP]; infer_instance

instance OBdd.instFintypeRelevantPointer {n m} (O : OBdd n m) : Fintype (O.1.RelevantPointer) := by
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

@[no_expose]
instance OBdd.instFintypeReachableFromNode (O : OBdd n m) (h : O.1.root = node j) :
    Fintype { q // q = O.1.root ∨ (Reachable O.1.heap (O.low  h).1.root q ∨ Reachable O.1.heap (O.high h).1.root q) } := by
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

/-- The inverse image of a decidable relation is decidable. -/
instance my_decidableRel_of_invImage2 {r : β → β → Prop} [DecidableRel r] {f : α → β} :
    DecidableRel (InvImage r f) :=
  fun a b ↦ decidable_of_decidable_of_iff (show (r (f a) (f b)) ↔ _ by simp [InvImage])

instance Bdd.instDecidableEqRelevantPointer : DecidableEq (Bdd.RelevantPointer B) :=
  fun _ _ ↦ decidable_of_iff _ (symm Subtype.ext_iff)

/-- `Reduced` is decidable. -/
@[no_expose]
instance OBdd.instReducedDecidable {n m} : DecidablePred (α := OBdd n m) Reduced :=
  fun _ ↦ (instDecidableAnd (dp := Fintype.decidableForallFintype) (dq := Fintype.decidableForallFintype))

lemma OBdd.card_reachable_node' {O : OBdd n m} (h : O.1.root = node j) :
  Fintype.card {p // Reachable O.1.heap O.1.root p} =
  Fintype.card {p // p = O.1.root ∨ (Reachable O.1.heap (O.low  h).1.root p ∨ Reachable O.1.heap (O.high h).1.root p)} := by
  apply Fintype.card_congr'
  conv =>
    lhs
    arg 1
    ext
    rw [reachable_from_node_iff' h]

lemma OBdd.card_reachable_node {n m j} {O : OBdd n m} (h : O.1.root = node j) :
  Fintype.card { q // Reachable O.1.heap O.1.root q } =
  1 + Fintype.card { q // Reachable (O.low h).1.heap (O.low h).1.root q ∨ Reachable (O.high h).1.heap (O.high h).1.root q } := by
  rw [card_reachable_node' h]
  rw [@Fintype.card_subtype_or_disjoint _ _ _ (eq_root_disjoint_reachable_low_or_high h) ..]
  · simp only [Fintype.card_unique, low_heap_eq_heap, add_right_inj]
    apply @Fintype.card_congr' ..
    · apply fintypeEitherRelevantPointer (O.low h) (O.high h); simp
    · simp
  · exact Fintype.subtypeEq O.1.root

@[no_expose, implicit_reducible]
instance OBdd.instDecidableReachable' {n m} (O : OBdd n m) (p : O.1.RelevantPointer) q :
    Decidable (Reachable O.1.heap p.val q) := by
  rcases p with ⟨p, hp⟩
  match p with
  | terminal b =>
    exact decidable_of_iff _ Reachable.terminal_iff.symm
  | node j =>
    let high := O.1.heap[j].high
    let low := O.1.heap[j].low
    suffices Decidable (q = node j ∨ Reachable O.bdd.heap high q ∨ Reachable O.bdd.heap low q) from
      decidable_of_iff _ Bdd.reachable_node_iff.symm
    refine @instDecidableOr _ _ ?_ (@instDecidableOr _ _ ?_ ?_)
    · exact decEq ..
    · have hr : Reachable O.1.heap O.1.root high :=
        Reachable.snoc hp Edge.high
      exact OBdd.instDecidableReachable' O ⟨high, hr⟩ q
    · have hr : Reachable O.1.heap O.1.root low :=
        Reachable.snoc hp Edge.low
      exact OBdd.instDecidableReachable' O ⟨low, hr⟩ q
termination_by p
decreasing_by
  all_goals simp_all only [flip, Bdd.RelevantEdge]
  · exact Edge.high
  · exact Edge.low

namespace Size

def bool_of_size_eq_zero {n m} (O : OBdd n m) (h : size O = 0) : Bool :=
  match O_root_def : O.1.root with
  | .terminal b => b
  | .node _ => False.elim (not_isTerminal_of_root_eq_node O_root_def (isTerminal_iff_size_eq_zero.mp h))

end Size
