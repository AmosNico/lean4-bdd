module

public import Bdd.Basic
import Std.Data.HashMap.Lemmas
import Std.Tactic.Do
open Std.Do

namespace Sim

structure State m m' where
  lr : Std.HashMap (Fin m) (Fin m')
  rl : Std.HashMap (Fin m') (Fin m)

def sim_helper' {n m m'}
    (O : OBdd n m) (hO : OBdd.Reduced O)
    (U : OBdd n m') (hU : OBdd.Reduced U)
    (p : Pointer m) (hpr : Pointer.Reachable O.1.heap O.1.root p)
    (q : Pointer m') (hqr : Pointer.Reachable U.1.heap U.1.root q) :
    State m m' → (State m m') × Bool :=
  fun s => match p, q with
  | .terminal b, .terminal b' => (s, b = b')
  | .terminal _, .node _ => (s, false)
  | .node _, .terminal _ => (s, false)
  | .node j, .node j' =>
    if hv : O.1.heap[j].var = U.1.heap[j'].var
    then
      match s.lr[j]? with
      | some i' => (s, j' = i')
      | none =>
        match s.rl[j']? with
        | some i => (s, false)
        | none =>
          let (sl, bl) := sim_helper' O hO U hU
            O.1.heap[j].low (.snoc hpr .low) U.1.heap[j'].low (.snoc hqr .low) s
          if bl then
            let (sh, bh) := sim_helper' O hO U hU
              O.1.heap[j].high (.snoc hpr .high) U.1.heap[j'].high (.snoc hqr .high) sl
            if bh then
              (⟨s.lr.insert j j', s.rl.insert j' j⟩, true)
            else
              (sh, false)
          else (sl, false)
    else (s, false)
termination_by OBdd.size' ⟨⟨O.1.heap, p⟩, O.ordered_of_reachable hpr⟩
decreasing_by
  · simp [OBdd.size'_node, OBdd.low_eq, Bdd.low_eq]; omega
  · simp [OBdd.size'_node, OBdd.high_eq, Bdd.high_eq]; omega

def sim_helper {n m m'}
    (O : OBdd n m) (hO : OBdd.Reduced O)
    (U : OBdd n m') (hU : OBdd.Reduced U)
    (p : Pointer m) (hpr : Pointer.Reachable O.1.heap O.1.root p)
    (q : Pointer m') (hqr : Pointer.Reachable U.1.heap U.1.root q) :
    StateM (State m m') Bool :=
  match p, q with
  | .terminal b, .terminal b' => return b = b'
  | .terminal _, .node _ => return false
  | .node _, .terminal _ => return false
  | .node j, .node j' =>
    if hv : O.1.heap[j].var = U.1.heap[j'].var
    then do
      let s ← get
      match s.lr[j]? with
      | some i' => return j' = i'
      | none =>
        match s.rl[j']? with
        | some i => return false
        | none =>
          let hll ← sim_helper O hO U hU
            O.1.heap[j].low (.snoc hpr .low) U.1.heap[j'].low (.snoc hqr .low)
          if hll then
            let hhh ← sim_helper O hO U hU
              O.1.heap[j].high (.snoc hpr .high) U.1.heap[j'].high (.snoc hqr .high)
            match hhh with
            | true =>
              set <| State.mk (s.lr.insert j j') (s.rl.insert j' j)
              return true
            | false => return false
          else return false
    else return false
termination_by OBdd.size' ⟨⟨O.1.heap, p⟩, O.ordered_of_reachable hpr⟩
decreasing_by
  · simp [OBdd.size'_node, OBdd.low_eq, Bdd.low_eq]; omega
  · simp [OBdd.size'_node, OBdd.high_eq, Bdd.high_eq]; omega

structure Invariant {n m m'} (O : OBdd n m) (U : OBdd n m') (s : State m m') where
  hl : ∀ j j',
    s.lr[j]? = some j' → s.rl[j']? = some j           ∧
    Pointer.Reachable O.1.heap O.1.root (.node j) ∧
    ∃ hj : Bdd.Ordered ⟨O.1.heap, .node j⟩,
      ∃ hj' : Bdd.Ordered ⟨U.1.heap, .node j'⟩,
        OBdd.HSimilar ⟨⟨O.1.heap, .node j⟩, hj⟩ ⟨⟨U.1.heap, .node j'⟩, hj'⟩
  hr : ∀ j j',
    s.rl[j']? = some j → s.lr[j]? = some j'            ∧
    Pointer.Reachable U.1.heap U.1.root (.node j') ∧
    ∃ hj : Bdd.Ordered ⟨O.1.heap, .node j⟩,
      ∃ hj' : Bdd.Ordered ⟨U.1.heap, .node j'⟩,
        OBdd.HSimilar ⟨⟨O.1.heap, .node j⟩, hj⟩ ⟨⟨U.1.heap, .node j'⟩, hj'⟩

lemma sim_helper_invariant {n m m'}
    (O : OBdd n m) (hO : OBdd.Reduced O)
    (U : OBdd n m') (hU : OBdd.Reduced U)
    (p : Pointer m) (hpr : Pointer.Reachable O.1.heap O.1.root p)
    (q : Pointer m') (hqr : Pointer.Reachable U.1.heap U.1.root q) {b s s'} :
    (sim_helper O hO U hU p hpr q hqr).run s = pure (b, s') →
    Invariant O U s → Invariant O U s' := by
  fun_induction sim_helper generalizing s s' with
  | case4 j j' hr1 hr2 heq1 hr3 hr4 ih1 ih2 =>
    simp only [bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · rintro ⟨rfl, rfl⟩; simp only [imp_self]
    split
    · rintro ⟨rfl, rfl⟩; simp only [imp_self]
    simp_all only [StateT.run, getElem?_eq_none_iff, bind, StateT.bind]
    split
    split
    · simp_all only [bind, StateT.bind]
      split
      split
      ·
        sorry
      · rintro ⟨rfl, rfl⟩
        have := ih1 (by assumption)
        have := ih2 (by assumption)
        sorry
    · rintro ⟨rfl, rfl⟩
      sorry
  | _ =>
    rintro ⟨rfl, rfl⟩
    simp only [imp_self]


lemma sim_helper_invariant' {n m m'}
    (O : OBdd n m) (hO : OBdd.Reduced O)
    (U : OBdd n m') (hU : OBdd.Reduced U)
    (p : Pointer m) (hpr : Pointer.Reachable O.1.heap O.1.root p)
    (q : Pointer m') (hqr : Pointer.Reachable U.1.heap U.1.root q) {b s s'} :
    (sim_helper O hO U hU p hpr q hqr).run s = pure (b, s') →
    Invariant O U s → Invariant O U s' := by
  generalize h : (sim_helper O hO U hU p hpr q hqr).run s = x
  apply StateM.of_wp_run_eq h
  mvcgen
  intro heq i

  sorry

lemma sim_helper_correct {n m m'}
    (O : OBdd n m) (hO : OBdd.Reduced O)
    (U : OBdd n m') (hU : OBdd.Reduced U)
    (p : Pointer m) (hpr : Pointer.Reachable O.1.heap O.1.root p)
    (q : Pointer m') (hqr : Pointer.Reachable U.1.heap U.1.root q) {b s} :
    (sim_helper O hO U hU p hpr q hqr).run ⟨∅, ∅⟩ = pure (b, s) ↔ O.HSimilar U := by
  generalize h : (sim_helper O hO U hU p hpr q hqr).run ⟨∅, ∅⟩ = x
  apply StateM.of_wp_run_eq h
  mvcgen
  sorry
/-  match hp : p with
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
            match hll with
            | isTrue ht =>
              -- TODO : why is type declaration needed? Note that only `←` does not work, for some reason `:= ←` is needed
              let hhh : Decidable (OBdd.HSimilar ⟨Bdd.mk O.bdd.heap O.bdd.heap[j].high, _⟩ ⟨Bdd.mk U.bdd.heap U.bdd.heap[j'].high, _⟩) :=
                ← sim_helper O hO U hU
                O.1.heap[j].high (Pointer.Reachable.snoc hpr .high)
                U.1.heap[j'].high (Pointer.Reachable.snoc hqr .high)
              match hhh with
              | isTrue ht' =>
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
                          constructor
                          · exact hpr
                          · use OBdd.ordered_of_reachable hpr
                            use OBdd.ordered_of_reachable hqr
                            simp only [OBdd.HSimilar] at ⊢ ht ht'
                            rw [OBdd.toTree_node rfl, OBdd.toTree_node (j := j') rfl]
                            simp only [OBdd.low_eq, Bdd.low_eq, OBdd.high_eq, Bdd.high_eq,
                              DecisionTree.branch.injEq]
                            exact ⟨hv, ht, ht'⟩
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
                          constructor
                          · exact hqr
                          · use OBdd.ordered_of_reachable hpr
                            use OBdd.ordered_of_reachable hqr
                            simp only [OBdd.HSimilar] at ⊢ ht ht'
                            rw [OBdd.toTree_node rfl, OBdd.toTree_node (j := j') rfl]
                            simp only [OBdd.low_eq, Bdd.low_eq, OBdd.high_eq, Bdd.high_eq,
                              DecisionTree.branch.injEq]
                            exact ⟨hv, ht, ht'⟩
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
                  simp only [OBdd.HSimilar] at ⊢ ht ht'
                  rw [OBdd.toTree_node rfl, OBdd.toTree_node (j := j') rfl]
                  simp only [OBdd.low_eq, Bdd.low_eq, OBdd.high_eq, Bdd.high_eq,
                    DecisionTree.branch.injEq]
                  exact ⟨hv, ht, ht'⟩
                )
              | isFalse hf' => return isFalse (fun c ↦ by
                simp [OBdd.HSimilar, OBdd.toTree_node, OBdd.high_eq, Bdd.high_eq] at c;
                exact hf' c.2.2)
            | isFalse hf => return isFalse (fun c ↦ by
              simp [OBdd.HSimilar, OBdd.toTree_node, OBdd.low_eq, Bdd.low_eq] at c; exact hf c.2.1)
          | some i =>
            return isFalse (by
              rcases s.hr i j' hr with ⟨h1, h2, h3, h4, h5⟩
              rcases s.hl i j' h1 with ⟨h1', h2', h3', h4', h5'⟩
              intro contra
              have hsim : OBdd.SimilarRP O ⟨.node i, h2'⟩ ⟨.node j, hpr⟩ := by
                simp [OBdd.similarRP_iff]
                simp only [OBdd.HSimilar] at contra h5
                rw [contra]
                exact h5
              have h := hO.2 hsim
              simp [InvImage] at h
              subst h
              rw [h1] at hl
              contradiction
            )
        | some i' =>
          if heq : j' = i'
          then
            return isTrue (s.hl j j' (by simp_all)).2.2.2.2
          else
            return isFalse (fun c ↦ heq (by
              rcases s.hl j i' hl with ⟨h1, h2, h3, h4, h5⟩
              rcases s.hr j i' h1 with ⟨h1', h2', h3', h4', h5'⟩
              have hsim : OBdd.SimilarRP U ⟨.node j', hqr⟩ ⟨.node i', h2'⟩ := by
                simp [OBdd.similarRP_iff]
                simp only [OBdd.HSimilar] at c h5
                rw [c] at h5
                exact h5
              have := hU.2 hsim
              simp [InvImage] at this
              exact this
            ))
      else return isFalse (by simp_all [OBdd.HSimilar, OBdd.toTree_node])
termination_by OBdd.size' ⟨⟨O.1.heap, p⟩, O.ordered_of_reachable hpr⟩
decreasing_by
  · simp [OBdd.size'_node, OBdd.low_eq, Bdd.low_eq]; omega
  · simp [OBdd.size'_node, OBdd.high_eq, Bdd.high_eq]; omega-/

structure State {n m m'} (O : OBdd n m) (U : OBdd n m') where
  lr : Std.HashMap (Fin m) (Fin m')
  rl : Std.HashMap (Fin m') (Fin m)
  hl : ∀ j j',
    lr[j]? = some j' → rl[j']? = some j           ∧
    Pointer.Reachable O.1.heap O.1.root (.node j) ∧
    ∃ hj : Bdd.Ordered ⟨O.1.heap, .node j⟩,
      ∃ hj' : Bdd.Ordered ⟨U.1.heap, .node j'⟩,
        OBdd.HSimilar ⟨⟨O.1.heap, .node j⟩, hj⟩ ⟨⟨U.1.heap, .node j'⟩, hj'⟩
  hr : ∀ j j',
    rl[j']? = some j → lr[j]? = some j'            ∧
    Pointer.Reachable U.1.heap U.1.root (.node j') ∧
    ∃ hj : Bdd.Ordered ⟨O.1.heap, .node j⟩,
      ∃ hj' : Bdd.Ordered ⟨U.1.heap, .node j'⟩,
        OBdd.HSimilar ⟨⟨O.1.heap, .node j⟩, hj⟩ ⟨⟨U.1.heap, .node j'⟩, hj'⟩

def sim_helper' {n m m'}
    (O : OBdd n m) (hO : OBdd.Reduced O)
    (U : OBdd n m') (hU : OBdd.Reduced U)
    (p : Pointer m) (hpr : Pointer.Reachable O.1.heap O.1.root p)
    (q : Pointer m') (hqr : Pointer.Reachable U.1.heap U.1.root q) :
  StateM
    (State O U)
    (Decidable
      (OBdd.HSimilar
        ⟨⟨O.1.heap, p⟩, O.ordered_of_reachable hpr⟩
        ⟨⟨U.1.heap, q⟩, U.ordered_of_reachable hqr⟩)) :=
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
            match hll with
            | isTrue ht =>
              -- TODO : why is type declaration needed? Note that only `←` does not work, for some reason `:= ←` is needed
              let hhh : Decidable (OBdd.HSimilar ⟨Bdd.mk O.bdd.heap O.bdd.heap[j].high, _⟩ ⟨Bdd.mk U.bdd.heap U.bdd.heap[j'].high, _⟩) :=
                ← sim_helper O hO U hU
                O.1.heap[j].high (Pointer.Reachable.snoc hpr .high)
                U.1.heap[j'].high (Pointer.Reachable.snoc hqr .high)
              match hhh with
              | isTrue ht' =>
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
                          constructor
                          · exact hpr
                          · use OBdd.ordered_of_reachable hpr
                            use OBdd.ordered_of_reachable hqr
                            simp only [OBdd.HSimilar] at ⊢ ht ht'
                            rw [OBdd.toTree_node rfl, OBdd.toTree_node (j := j') rfl]
                            simp only [OBdd.low_eq, Bdd.low_eq, OBdd.high_eq, Bdd.high_eq,
                              DecisionTree.branch.injEq]
                            exact ⟨hv, ht, ht'⟩
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
                          constructor
                          · exact hqr
                          · use OBdd.ordered_of_reachable hpr
                            use OBdd.ordered_of_reachable hqr
                            simp only [OBdd.HSimilar] at ⊢ ht ht'
                            rw [OBdd.toTree_node rfl, OBdd.toTree_node (j := j') rfl]
                            simp only [OBdd.low_eq, Bdd.low_eq, OBdd.high_eq, Bdd.high_eq,
                              DecisionTree.branch.injEq]
                            exact ⟨hv, ht, ht'⟩
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
                  simp only [OBdd.HSimilar] at ⊢ ht ht'
                  rw [OBdd.toTree_node rfl, OBdd.toTree_node (j := j') rfl]
                  simp only [OBdd.low_eq, Bdd.low_eq, OBdd.high_eq, Bdd.high_eq,
                    DecisionTree.branch.injEq]
                  exact ⟨hv, ht, ht'⟩
                )
              | isFalse hf' => return isFalse (fun c ↦ by
                simp [OBdd.HSimilar, OBdd.toTree_node, OBdd.high_eq, Bdd.high_eq] at c;
                exact hf' c.2.2)
            | isFalse hf => return isFalse (fun c ↦ by
              simp [OBdd.HSimilar, OBdd.toTree_node, OBdd.low_eq, Bdd.low_eq] at c; exact hf c.2.1)
          | some i =>
            return isFalse (by
              rcases s.hr i j' hr with ⟨h1, h2, h3, h4, h5⟩
              rcases s.hl i j' h1 with ⟨h1', h2', h3', h4', h5'⟩
              intro contra
              have hsim : OBdd.SimilarRP O ⟨.node i, h2'⟩ ⟨.node j, hpr⟩ := by
                simp [OBdd.similarRP_iff]
                simp only [OBdd.HSimilar] at contra h5
                rw [contra]
                exact h5
              have h := hO.2 hsim
              simp [InvImage] at h
              subst h
              rw [h1] at hl
              contradiction
            )
        | some i' =>
          if heq : j' = i'
          then
            return isTrue (s.hl j j' (by simp_all)).2.2.2.2
          else
            return isFalse (fun c ↦ heq (by
              rcases s.hl j i' hl with ⟨h1, h2, h3, h4, h5⟩
              rcases s.hr j i' h1 with ⟨h1', h2', h3', h4', h5'⟩
              have hsim : OBdd.SimilarRP U ⟨.node j', hqr⟩ ⟨.node i', h2'⟩ := by
                simp [OBdd.similarRP_iff]
                simp only [OBdd.HSimilar] at c h5
                rw [c] at h5
                exact h5
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
