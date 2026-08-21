module

public import Bdd.Basic
import Std.Data.HashMap.Lemmas

namespace Sim

structure State {n m m'} (O : OBdd n m) (U : OBdd n m') where
  lr : Std.HashMap (Fin m) (Fin m')
  rl : Std.HashMap (Fin m') (Fin m)
  hl : ∀ j j',
    lr[j]? = some j' → rl[j']? = some j           ∧
    ∃ hj hj', OBdd.HSimilar (O.subBdd ⟨.node j, hj⟩) (U.subBdd ⟨.node j', hj'⟩)
  hr : ∀ j j',
    rl[j']? = some j → lr[j]? = some j'            ∧
    ∃ hj hj', OBdd.HSimilar (O.subBdd ⟨.node j, hj⟩) (U.subBdd ⟨.node j', hj'⟩)

def sim_helper {n m m'}
    (O : OBdd n m) (hO : OBdd.Reduced O)
    (U : OBdd n m') (hU : OBdd.Reduced U)
    (p : Pointer m) (hpr : Pointer.Reachable O.1.heap O.1.root p)
    (q : Pointer m') (hqr : Pointer.Reachable U.1.heap U.1.root q) :
  StateM
    (State O U)
    (Decidable (OBdd.HSimilar (O.subBdd ⟨p, hpr⟩) (U.subBdd ⟨q, hqr⟩))) :=
  match hp : p with
  | .terminal b =>
    match hq : q with
    | .terminal b' =>
      if hb : b = b'
      then return isTrue (by simpa [OBdd.HSimilar, OBdd.toTree_terminal])
      else return isFalse (by simpa [OBdd.HSimilar, OBdd.toTree_terminal])
    | .node j' => return isFalse (by simp [OBdd.HSimilar, OBdd.toTree_terminal, OBdd.toTree_node])
  | .node j =>
    match hq : q with
    | .terminal b' => return isFalse (by simp [OBdd.HSimilar, OBdd.toTree_terminal, OBdd.toTree_node])
    | .node j' =>
      if hv : O.1.heap[j].var = U.1.heap[j'].var
      then do
        let s ← get
        match hl : s.lr[j]? with
        | none =>
          match hr : s.rl[j']? with
          | none =>
            let hll ← sim_helper O hO U hU
              O.1.heap[j].low (Pointer.Reachable.snoc hpr .low)
              U.1.heap[j'].low (Pointer.Reachable.snoc hqr .low)
            if h : ((O.subBdd ⟨O.bdd.heap[j].low, _⟩).HSimilar (U.subBdd ⟨U.bdd.heap[j'].low, _⟩)) then
              let hhh :=
                ← sim_helper O hO U hU
                O.1.heap[j].high (Pointer.Reachable.snoc hpr .high)
                U.1.heap[j'].high (Pointer.Reachable.snoc hqr .high)
              if h' : ((O.subBdd ⟨O.bdd.heap[j].high, _⟩).HSimilar (U.subBdd ⟨U.bdd.heap[j'].high, _⟩)) then
                set
                  (⟨s.lr.insert j j', s.rl.insert j' j,
                    fun jj jj' hjj ↦ by
                      simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at hjj
                      split at hjj
                      next heq =>
                        subst heq
                        simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
                        split
                        next heqq =>
                          subst heqq
                          simp only [true_and]
                          use hpr, hqr
                          simp only [OBdd.HSimilar] at ⊢ h h'
                          rw [OBdd.toTree_node (OBdd.root_subBdd ⟨.node j, _⟩)]
                          rw [OBdd.toTree_node (OBdd.root_subBdd ⟨.node j', _⟩)]
                          simp only [OBdd.heap_subBdd, OBdd.low_subBdd, OBdd.high_subBdd,
                            DecisionTree.branch.injEq]
                          exact ⟨hv, h, h'⟩
                        next heqq => injection hjj; contradiction
                      next heq =>
                        simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
                        split
                        next heqq =>
                          subst heqq
                          rw [(s.hl jj j' hjj).1] at hr
                          contradiction
                        next heqq =>
                          exact s.hl jj jj' hjj,
                    fun jj jj' hjj ↦ by
                      simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at hjj
                      split at hjj
                      next heq =>
                        subst heq
                        simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
                        split
                        next heqq =>
                          subst heqq
                          simp only [true_and]
                          use hpr, hqr
                          simp only [OBdd.HSimilar] at ⊢ h h'
                          rw [OBdd.toTree_node (OBdd.root_subBdd ⟨.node j, _⟩)]
                          rw [OBdd.toTree_node (OBdd.root_subBdd ⟨.node j', _⟩)]
                          simp only [OBdd.heap_subBdd, OBdd.low_subBdd, OBdd.high_subBdd,
                            DecisionTree.branch.injEq]
                          exact ⟨hv, h, h'⟩
                        next heqq => injection hjj; contradiction
                      next heq =>
                        simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
                        split
                        next heqq =>
                          subst heqq
                          rw [(s.hr j jj' hjj).1] at hl
                          contradiction
                        next heqq =>
                          exact s.hr jj jj' hjj
                   ⟩ : State O U)
                return isTrue (by
                  simp only [OBdd.HSimilar] at ⊢ h h'
                  rw [OBdd.toTree_node (OBdd.root_subBdd ⟨.node j, _⟩)]
                  rw [OBdd.toTree_node (OBdd.root_subBdd ⟨.node j', _⟩)]
                  simp only [OBdd.heap_subBdd, OBdd.low_subBdd, OBdd.high_subBdd,
                    DecisionTree.branch.injEq]
                  exact ⟨hv, h, h'⟩
                )
              else
                return isFalse (fun c ↦ by
                  simp only [OBdd.HSimilar, OBdd.root_subBdd, Pointer.node.injEq, OBdd.toTree_node,
                    OBdd.high_subBdd, DecisionTree.branch.injEq] at c
                  exact h' c.2.2)
            else
              return isFalse (fun c ↦ by
                simp only [OBdd.HSimilar, OBdd.root_subBdd, Pointer.node.injEq, OBdd.toTree_node,
                  OBdd.heap_subBdd, -Fin.getElem_fin, OBdd.low_eq, Bdd.low_eq, OBdd.high_subBdd,
                  DecisionTree.branch.injEq] at c;
                simp? at h
                exact h c.2.1)
          | some i =>
            return isFalse (by
              rcases s.hr i j' hr with ⟨h1, h2, h3, h4⟩
              rcases s.hl i j' h1 with ⟨h1', h2', h3', h4'⟩
              intro contra
              have hsim : OBdd.SimilarRP O ⟨.node i, h2'⟩ ⟨.node j, hpr⟩ := by
                simp [OBdd.similarRP_iff]
                simp only [OBdd.HSimilar] at contra h4
                rw [contra]
                exact h4
              have h := hO.2 hsim
              simp [InvImage] at h
              subst h
              rw [h1] at hl
              contradiction
            )
        | some i' =>
          if heq : j' = i'
          then
            return isTrue (s.hl j j' (by simp_all)).2.2.2
          else
            return isFalse (fun c ↦ heq (by
              rcases s.hl j i' hl with ⟨h1, h2, h3, h4⟩
              rcases s.hr j i' h1 with ⟨h1', h2', h3', h4'⟩
              have hsim : OBdd.SimilarRP U ⟨.node j', hqr⟩ ⟨.node i', h3'⟩ := by
                simp [OBdd.similarRP_iff]
                simp only [OBdd.HSimilar] at c h4
                rw [c] at h4
                exact h4
              have := hU.2 hsim
              simp [InvImage] at this
              exact this
            ))
      else return isFalse (by simp_all [OBdd.HSimilar, OBdd.toTree_node])
termination_by OBdd.size' ⟨⟨O.1.heap, p⟩, O.ordered_of_reachable hpr⟩
decreasing_by
  · simp [OBdd.size'_node, OBdd.low_eq, Bdd.low_eq]; omega
  · simp [OBdd.size'_node, OBdd.high_eq, Bdd.high_eq]; omega

public def decidableRobddHSimilar {n m m'}
    (O : OBdd n m) (hO : O.Reduced)
    (U : OBdd n m') (hU : U.Reduced) :
    Decidable (O.HSimilar U) :=
  ((sim_helper O hO U hU O.1.root .refl U.1.root .refl)
    ⟨ Std.HashMap.emptyWithCapacity 0,
      Std.HashMap.emptyWithCapacity 0,
      by simp,
      by simp
    ⟩
  ).1

end Sim
