module

public import Bdd.Basic

namespace Collect

def collect_helper {n m} (O : OBdd n m) :
    Vector Bool m × List (Fin m) → Vector Bool m × List (Fin m) :=
  match h : O.1.root with
  | .terminal _ => id
  | .node j =>
    fun I ↦ bif I.1.get j then I else
      collect_helper (O.high h) (collect_helper (O.low h) ⟨I.1.set j true, j :: I.2⟩)
termination_by O

/-- Return a list of all reachable node indices. -/
public def collect {n m} (O : OBdd n m) : List (Fin m) :=
  (collect_helper O ⟨Vector.replicate m false, []⟩).2

lemma collect_helper_terminal {n m} {v : Vector (Node n m) m} {b h I} :
    collect_helper ⟨{heap := v, root := .terminal b}, h⟩ I = I := by
  simp only [collect_helper, id_eq]

lemma collect_helper_terminal' {n m} {O : OBdd n m} {b} (h : O.1.root = .terminal b) {I} :
    collect_helper O I = I := by
  rcases O with ⟨⟨M, r⟩, o⟩
  simp only at h
  simp_rw [h]
  exact collect_helper_terminal

public lemma collect_terminal {n m} {O : OBdd n m} {b} (h : O.1.root = .terminal b) :
    collect O = [] := by
  simp only [collect, collect_helper_terminal' h]

lemma collect_helper_node {n m} (O : OBdd n m) {j : Fin m} (h : O.1.root = .node j) {I} :
    collect_helper O I = if I.1[j] then I else
      collect_helper (O.high h) (collect_helper (O.low h) ⟨I.1.set j true, j :: I.2⟩) := by
  rcases O with ⟨⟨heap, root⟩, o⟩
  simp only at h
  subst h
  rw [collect_helper]
  simp only [cond_eq_ite]
  rfl

theorem collect_helper_retains_found {n m} {O : OBdd n m} {I j} :
    j ∈ I.2 → j ∈ (collect_helper O I).2 := by
  intro h
  cases O_root_def : O.1.root with
  | terminal b =>
    rwa [collect_helper_terminal' O_root_def]
  | node i =>
    rw [collect_helper_node O O_root_def]
    split_ifs
    · simpa
    · have : j ∈ (collect_helper (O.low O_root_def) (I.1.set i true, i :: I.2)).2 := by
        apply collect_helper_retains_found
        simp only [List.mem_cons, h, or_true]
      exact collect_helper_retains_found this
termination_by O

theorem collect_helper_retains_marked {n m} {O : OBdd n m} {I} {j : Fin m} :
    I.1[j] = true → (collect_helper O I).1[j] = true := by
  intro h
  cases O_root_def : O.1.root with
  | terminal b =>
    rwa [collect_helper_terminal' O_root_def]
  | node i =>
    rw [collect_helper_node O O_root_def]
    split_ifs
    · simpa
    · have : (collect_helper (O.low O_root_def) (I.1.set i true, i :: I.2)).1[j] = true := by
        apply collect_helper_retains_marked
        grind only [= Fin.getElem_fin, = Vector.getElem_set]
      exact collect_helper_retains_marked this
termination_by O

theorem collect_helper_only_marks_reachable {m n} {j : Fin m} {O : OBdd n m} {I} :
    I.1[j] = false → (collect_helper O I).1[j] = true →
    Pointer.Reachable O.1.heap O.1.root (.node j) := by
  intro h1 h2
  cases O_root_def : O.1.root with
  | terminal b =>
    rw [collect_helper_terminal' O_root_def, h1] at h2; contradiction
  | node i =>
    if h3 : i = j then
      rw [h3]
      exact .refl
    else
      rw [collect_helper_node O O_root_def] at h2
      have hh : I.1[i] = false := by grind
      simp only [hh, Bool.false_eq_true, ↓reduceIte] at h2
      rw [← O_root_def]
      cases hhh : (collect_helper (O.low O_root_def) (I.1.set i true, i :: I.2)).1[j] with
      | false =>
        trans O.bdd.heap[i].high
        · exact Bdd.reachable_high O_root_def
        · have h : Pointer.Reachable (O.high O_root_def).bdd.heap
              (O.high O_root_def).bdd.root (.node j) :=
            collect_helper_only_marks_reachable hhh h2
          rwa [OBdd.high_heap_eq_heap, OBdd.high_root_eq_high] at h
      | true =>
        trans O.bdd.heap[i].low
        · exact Bdd.reachable_low O_root_def
        · have h : Pointer.Reachable (O.low O_root_def).bdd.heap
              (O.low O_root_def).bdd.root (.node j) := by
            refine collect_helper_only_marks_reachable ?_ hhh
            simp only [Fin.getElem_fin]
            rwa [Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne h3)]
          rwa [OBdd.low_heap_eq_heap, OBdd.low_root_eq_low] at h
termination_by O

theorem collect_helper_spec {n m} {O : OBdd n m} {I} :
    (∀ i, (Pointer.Reachable O.1.heap O.1.root (.node i) → I.1[i] = true → i ∈ I.2)) →
    ∀ i, (Pointer.Reachable O.1.heap O.1.root (.node i) →
      (collect_helper O I).1[i] → i ∈ (collect_helper O I).2) := by
  intro h j re ma
  cases O_root_def : O.1.root with
  | terminal b => grind only [Pointer.Reachable.terminal_iff]
  | node k =>
    rw [collect_helper_node O O_root_def] at ma
    rw [collect_helper_node O O_root_def]
    split_ifs at ma
    case pos h1 =>
      simp only [h1, ↓reduceIte]
      exact h j re ma
    case neg h1 =>
      simp only [h1, Bool.false_eq_true, ↓reduceIte]
      if h2 : k = j then
        apply collect_helper_retains_found
        apply collect_helper_retains_found
        simp only [h2, List.mem_cons, true_or]
      else
        cases hhh : I.1[j] with
        | true =>
          apply collect_helper_retains_found
          apply collect_helper_retains_found
          right
          exact h j re hhh
        | false =>
          cases hhhh : (collect_helper (O.low O_root_def) (I.1.set k true, k :: I.2)).1[j] with
          | true =>
            have : j ∈ (collect_helper (O.low O_root_def) (I.1.set k true, k :: I.2)).2 := by
              apply collect_helper_spec
              · intro i' re' ma'
                simp only [OBdd.low_heap_eq_heap, OBdd.low_root_eq_low] at re'
                simp only
                if h3 :  k = i' then
                  simp only [h3, List.mem_cons, true_or]
                else
                  rw [Fin.getElem_fin, Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne h3)] at ma'
                  right
                  apply h
                  · exact .trans (O.bdd.reachable_low O_root_def) re'
                  · exact ma'
              · have : (I.1.set k true, k :: I.2).1[j] = false := by
                  rw [Fin.getElem_fin, Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne h2)]
                  exact hhh
                exact collect_helper_only_marks_reachable this hhhh
              · exact hhhh
            apply collect_helper_retains_found this
          | false =>
            apply collect_helper_spec
            · intro i' re' ma'
              simp at ma' re'
              have := h i' (Pointer.Reachable.trans (O.bdd.reachable_high O_root_def) re')
              cases hhhhh : I.1[i'] with
              | true =>
                apply this at hhhhh
                have : i' ∈ (I.1.set k true, k :: I.2).2 := by
                  simp only [List.mem_cons, hhhhh, or_true]
                exact collect_helper_retains_found this
              | false =>
                if h3 : k = i' then
                  apply collect_helper_retains_found
                  simp only [h3, List.mem_cons, true_or]
                else
                  have that : (I.1.set k true, k :: I.2).1[i'] = false := by
                    simp only [Fin.getElem_fin]
                    rw [Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne h3)]
                    exact hhhhh
                  apply collect_helper_spec
                  · intro i'' re'' ma''
                    simp only [OBdd.low_heap_eq_heap, OBdd.low_root_eq_low] at re''
                    simp only
                    if h4 : k = i'' then
                      simp only [h4, List.mem_cons, true_or]
                    else
                      rw [Fin.getElem_fin, Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne h4)] at ma''
                      right
                      apply h
                      · exact Pointer.Reachable.trans (O.bdd.reachable_low O_root_def) re''
                      · exact ma''
                  · exact collect_helper_only_marks_reachable that ma'
                  · exact ma'
            · exact collect_helper_only_marks_reachable hhhh ma
            · assumption
termination_by O

lemma collect_spec' {n m} {O : OBdd n m} {j : Fin m} {I : Vector Bool m × List (Fin m)} :
    Pointer.Reachable O.1.heap O.1.root (.node j) →
    (∀ i, Pointer.Reachable O.1.heap O.1.root (.node i) →
      Pointer.Reachable O.1.heap (.node i) (.node j) → I.1[i] = false) →
    (collect_helper O I).1[j] = true := by
  intro h1 h2
  cases O_root_def : O.1.root with
  | terminal b => grind only [Pointer.Reachable.terminal_iff]
  | node i =>
    rw [collect_helper_node O O_root_def]
    have : I.1[i] = false := by
      apply h2 i
      · rw [← O_root_def]
        exact .refl
      · rw [← O_root_def]
        exact h1
    rw [this]
    simp only [Bool.false_eq_true, ↓reduceIte]
    if h : i = j then
      apply collect_helper_retains_marked
      apply collect_helper_retains_marked
      simp only [h, Fin.getElem_fin, Vector.getElem_set_self]
    else
      cases OBdd.instDecidableReachable (O.low O_root_def) (.node j) with
      | isTrue ht  =>
        apply collect_helper_retains_marked
        apply collect_spec'
        · exact ht
        · intro i' re1 re2
          rw [OBdd.low_heap_eq_heap, OBdd.low_root_eq_low] at re1
          rw [OBdd.low_heap_eq_heap] at re2
          have h : i ≠ i' := by
            grind only [OBdd.not_reachable_low_root O_root_def]
          rw [Fin.getElem_fin, Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne h)]
          apply h2
          · exact Pointer.Reachable.trans (O.bdd.reachable_low O_root_def) re1
          · exact re2
      | isFalse hf =>
        apply collect_spec'
        · cases (OBdd.reachable_or_eq_low_high (p := .node j) h1) with
          | inl h => rw [O_root_def] at h; simp at h; contradiction
          | inr h =>
            rcases h with ⟨j', h', d⟩
            have rfl : i = j' := by
              rwa [O_root_def, Pointer.node.injEq] at h'
            simp_all only [OBdd.low_heap_eq_heap, false_or, OBdd.high_heap_eq_heap]
        · intro i' re ma
          contrapose hf
          simp only [Bool.not_eq_false] at hf
          simp only [OBdd.high_heap_eq_heap, OBdd.high_root_eq_high] at re ma
          apply collect_helper_only_marks_reachable (I := (I.1.set i true, i :: I.2))
          · rw [Fin.getElem_fin, Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne h)]
            apply h2
            · exact Pointer.Reachable.trans (O.bdd.reachable_high O_root_def) (.trans re ma)
            · exact .refl
          · apply collect_spec'
            · have that : Pointer.Reachable (O.low O_root_def).bdd.heap
                  (O.low O_root_def).bdd.root (.node i') := by
                apply collect_helper_only_marks_reachable (I := (I.1.set i true, i :: I.2))
                · have h : i ≠ i' := by
                    grind only [OBdd.not_reachable_high_root O_root_def]
                  rw [Fin.getElem_fin, Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne h)]
                  apply h2 i' (Pointer.Reachable.trans (O.bdd.reachable_high O_root_def) re) ma
                · exact hf
              simp only [OBdd.low_heap_eq_heap, OBdd.low_root_eq_low] at ⊢ that
              exact Pointer.Reachable.trans that ma
            · intro i'' re1 re2
              rw [OBdd.low_heap_eq_heap, OBdd.low_root_eq_low] at re1
              rw [OBdd.low_heap_eq_heap] at re2
              simp only
              have h : i ≠ i'' := by
                grind only [OBdd.not_reachable_low_root O_root_def]
              rw [Fin.getElem_fin, Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne h)]
              apply h2
              · exact Pointer.Reachable.trans (O.bdd.reachable_low O_root_def) re1
              · exact re2
termination_by O

/-- `collect` is correct. -/
public theorem collect_spec {n m} {O : OBdd n m} {j : Fin m} :
    Pointer.Reachable O.1.heap O.1.root (.node j) → j ∈ collect O := by
  intro h
  simp [collect]
  apply collect_helper_spec
  · intro i re ma
    simp only [Fin.getElem_fin] at ma
    rw [Vector.getElem_replicate _] at ma
    contradiction
  · assumption
  · apply collect_spec' h
    intro i re1 re2
    simp only [Fin.getElem_fin, Vector.getElem_replicate]

theorem collect_helper_spec_reverse {n m} (O : OBdd n m) (r : Pointer m) I :
    Pointer.Reachable O.1.heap r O.1.root →
    (∀ i ∈ I.2, Pointer.Reachable O.1.heap r (.node i)) →
    ∀ i ∈ (collect_helper O I).2, Pointer.Reachable O.1.heap r (.node i) := by
  intro h0 h1 i h2
  cases h : O.1.root with
  | terminal b =>
    rw [collect_helper_terminal' h] at h2
    exact h1 i h2
  | node j =>
    rw [collect_helper_node O h] at h2
    split at h2
    next ht =>
      exact h1 i h2
    next hf =>
      if h3 : i ∈ (j :: I.2) then
        grind only [= List.mem_cons]
      else if h4 : i ∈ (collect_helper (O.low h) (I.1.set j true, j :: I.2)).2 then
        rw [← OBdd.low_heap_eq_heap h]
        refine collect_helper_spec_reverse (O.low h) r _ ?_ ?_ i h4
        · rw [OBdd.low_heap_eq_heap, OBdd.low_root_eq_low]
          trans O.1.root
          · exact h0
          · exact O.bdd.reachable_low h
        · intro i' hi'
          simp only at hi'
          simp only [OBdd.low_heap_eq_heap]
          cases hi' with
          | head as => grind only
          | tail _ hi' => exact h1 i' hi'
      else
        rw [← OBdd.high_heap_eq_heap h]
        refine collect_helper_spec_reverse (O.high h) r _ ?_ ?_ i h2
        · simp only [OBdd.high_heap_eq_heap, OBdd.high_root_eq_high]
          trans O.1.root
          · exact h0
          · exact Bdd.reachable_high h
        · intro i' hi'
          rw [OBdd.high_heap_eq_heap, ← OBdd.low_heap_eq_heap (h := h)]
          refine collect_helper_spec_reverse (O.low h) r _ ?_ ?_ i' hi'
          · rw [OBdd.low_heap_eq_heap, OBdd.low_root_eq_low]
            trans O.1.root
            · exact h0
            · exact Bdd.reachable_low h
          · intro i'' hi''
            simp only at hi''
            cases hi'' with
            | head as     => grind only [OBdd.low_heap_eq_heap]
            | tail _ hi'' =>
              simp only [OBdd.low_heap_eq_heap]
              exact h1 i'' hi''
termination_by O

public theorem collect_spec_reverse {n m} {O : OBdd n m} {j : Fin m} :
    j ∈ collect O → Pointer.Reachable O.1.heap O.1.root (.node j) := by
  intro h
  simp only [collect] at h
  apply collect_helper_spec_reverse O O.1.root (Vector.replicate m false, []) .refl
  · simp
  · assumption

theorem collect_helper_nodup {m n} {I : Vector Bool m × List (Fin m)} {O : OBdd n m} :
    (∀ i ∈ I.2, I.1[i] = true) ∧ I.2.Nodup →
    (∀ i ∈ (collect_helper O I).2, (collect_helper O I).1[i] = true) ∧
      (collect_helper O I).2.Nodup := by
  intro h
  cases O_root_def : O.1.root with
  | terminal b => simpa [collect_helper_terminal' O_root_def]
  | node     j =>
    rw [collect_helper_node O O_root_def]
    split_ifs
    next => exact h
    next heq =>
      apply collect_helper_nodup
      apply collect_helper_nodup
      simp only [List.mem_cons, forall_eq_or_imp]
      split_ands
      · simp only [Fin.getElem_fin, Vector.getElem_set_self]
      · intro i hi
        if h' : j = i then
          simp only [h', Fin.getElem_fin, Vector.getElem_set_self]
        else
          rw [Fin.getElem_fin, Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne h')]
          exact h.1 i hi
      · grind only [= List.nodup_cons]
termination_by O

public theorem mem_collect_iff_reachable {n m} {O : OBdd n m} {j : Fin m} :
    j ∈ collect O ↔ Pointer.Reachable O.1.heap O.1.root (.node j) :=
  ⟨collect_spec_reverse, collect_spec⟩

public theorem collect_nodup {n m} {O : OBdd n m} : (collect O).Nodup := by
  simp only [collect]
  exact (collect_helper_nodup (by simp)).2

end Collect
