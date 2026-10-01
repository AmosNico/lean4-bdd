module

import Mathlib.Data.Vector.Basic

namespace Nary

public section

abbrev Func n α β := Vector α n → β

/-- `IndependentOf f i` if the output of `f` does not depend on the value of the `i`th input. -/
@[expose]
def IndependentOf {n α β} (f : Func n α β) (i : Fin n) := ∀ a v, f v = f (Vector.set v i a)

/-- `DependsOn f i` if the output of `f` depends on the value of the `i`th input. -/
def DependsOn {n α β} (f : Func n α β) (i : Fin n) := ¬ IndependentOf f i

-- TODO : use this as the definition instead?
lemma dependsOn_iff {n α β} {f : Func n α β} {i : Fin n} :
    DependsOn f i ↔ ∃ v1 v2, (∀ i' ≠ i, v1[i'] = v2[i']) ∧ f v1 ≠ f v2 := by
  simp only [DependsOn, IndependentOf, not_forall, ne_eq, Fin.getElem_fin]
  constructor
  · grind only [= Vector.getElem_set]
  · contrapose
    simp only [not_exists, not_not, not_and]
    intro h1 v1 v2 h2
    rw[h1 v2[i] v1]
    congr
    ext i' hi'
    by_contra h
    simp at h
    specialize h2 ⟨i', hi'⟩
    grind only [= Vector.getElem_set]

lemma eq_of_forall_dependency_getElem_eq'' {n α β} {f : Func n α β} {I J : Vector α n} :
    (∀ i, DependsOn f i →  I[i] = J[i]) → f I = f J := by
  contrapose
  simp only [dependsOn_iff, ne_eq, Fin.getElem_fin, forall_exists_index, and_imp, not_forall]
  intro h
  have h' : I ≠ J := by grind only
  obtain ⟨i, hi⟩ : ∃ i : Fin n, I[i] ≠ J[i] := by
    simp only [ne_eq, Vector.ext_iff, not_forall] at h'
    simp only [Fin.getElem_fin, Fin.exists_iff, h']
  use i, I, J, sorry, h, hi


lemma eq_of_forall_dependency_getElem_eq' {n α β} {f : Func n α β} {I J : Vector α n} :
    (∀ i, DependsOn f i →  I[i] = J[i]) → f I = f J := by
  intro h
  simp only [dependsOn_iff, ne_eq, Fin.getElem_fin, forall_exists_index, and_imp] at h
  induction n with
  | zero =>
    simp only [Vector.eq_empty, implies_true]
  | succ n ih =>
    intro h
    simp [dependsOn_iff] at h
    let g : Vector α n → β := fun v ↦ f (Vector.push v I[n])
    have h2 : ∀ V : Vector α (n + 1), I[n] = V[n] → f V = g V.pop := by
      intro V hV
      simp only [g]
      congr
      ext i hi
      rw [Vector.getElem_push]
      split
      next hh => simp only [Vector.getElem_pop']
      next hh =>
        have : i = n := by omega
        simp_all only [DependsOn, IndependentOf, Fin.getElem_fin]
    by_cases hf : DependsOn f ⟨n, Nat.lt_add_one n⟩
    · have h1 := h ⟨n, Nat.lt_add_one n⟩ hf
      rw [h2 I rfl]
      rw [h2 J h1]
      apply ih
      intro i hi
      simp only [g] at hi
      have : DependsOn f i.castSucc := by
        simp only [DependsOn, IndependentOf, not_forall] at hi
        rcases hi with ⟨a, V, hav⟩
        rw [show (V.set i a).push I[n] = (V.push I[n]).set i a by
          simp only [Vector.set_push, Fin.is_lt, ↓reduceDIte]] at hav
        simp only [DependsOn, IndependentOf, not_forall]
        use a, V.push I[n]
        exact hav
      have := h i.castSucc this
      simp_all only [DependsOn, IndependentOf, Fin.getElem_fin,
        Fin.val_castSucc, Vector.getElem_pop', g]
    · simp only [DependsOn, not_not, IndependentOf] at hf
      rw [hf I[n] J]
      rw [h2 I rfl]
      rw [h2 (J.set (Fin.mk n n.lt_add_one) I[n]) (by simp only [Vector.getElem_set_self])]
      apply ih
      intro i hi
      simp only [g] at hi
      have : DependsOn f i.castSucc := by
        simp only [DependsOn, IndependentOf, not_forall] at hi
        rcases hi with ⟨a, V, hav⟩
        rw [show (V.set i a).push I[n] = (V.push I[n]).set i a by simp [Vector.set_push]] at hav
        simp only [DependsOn, IndependentOf, not_forall]
        use a, V.push I[n]
        exact hav
      have := h i.castSucc this
      simp only [Fin.getElem_fin, Vector.getElem_pop']
      rw [Vector.getElem_set_ne _ _ (by omega)]
      simp_all only [DependsOn, IndependentOf, Fin.getElem_fin, Fin.val_castSucc]

lemma push_pop_last {α n} (I : Vector α (n + 1)) : I.pop.push I[n] = I := by
  have h: I[n] = I.back := by simp only [Vector.back_eq_getElem, Nat.add_one_sub_one]
  rw [h, Vector.push_pop_back]

lemma eq_of_forall_dependency_getElem_eq1 {n α β} {f : Func n α β} {I J : Vector α n} :
    (∀ i, DependsOn f i →  I[i] = J[i]) → f I = f J := by
  induction n with
  | zero =>
    simp only [Vector.eq_empty, implies_true]
  | succ n ih =>
    intro h1
    have h2 := h1
    simp only [dependsOn_iff, ne_eq, Fin.getElem_fin, forall_exists_index, and_imp] at h2
    let g : Vector α n → β := fun v ↦ f (Vector.push v I[n])
    have h4 : ∀ V : Vector α (n + 1), I[n] = V[n] → f V = g V.pop := by
      intro V hV
      simp only [g, hV, push_pop_last]
    by_contra h5
    have h6 : DependsOn f (Fin.last n) := by
      simp only [dependsOn_iff, ne_eq, Fin.getElem_fin]
      refine ⟨I, J, ?_, h5⟩

      intro i hi
      apply h2
      sorry
    specialize h1 (Fin.last n) h6
    specialize h2 (Fin.last n) I J (by sorry) h5
    simp only [Fin.val_last] at h2
    specialize @ih g I.pop J.pop (by simp; sorry)
    simp_rw [g, push_pop_last, h2, push_pop_last] at ih
    exact h5 ih


lemma eq_of_forall_dependency_getElem_eq {n α β} {f : Func n α β} {I J : Vector α n} :
    (∀ i, DependsOn f i →  I[i] = J[i]) → f I = f J := by
  induction n with
  | zero =>
    simp only [Vector.eq_empty, implies_true]
  | succ n ih =>
    intro h1
    have h2 := h1
    simp only [dependsOn_iff, ne_eq, Fin.getElem_fin, forall_exists_index, and_imp] at h2
    let g : Vector α n → β := fun v ↦ f (Vector.push v I[n])
    have h4 : ∀ V : Vector α (n + 1), I[n] = V[n] → f V = g V.pop := by
      intro V hV
      simp only [g, hV, push_pop_last]
    have h5 : ∀ (i : Fin n), DependsOn g i → I.pop[i] = J.pop[i] := by
        simp only [Nat.add_one_sub_one, Fin.getElem_fin, Vector.getElem_pop', g, dependsOn_iff]
        rintro i ⟨I', J', h8, h9⟩
        apply h1 i.castSucc
        rw [dependsOn_iff]
        refine ⟨I'.push I[n], J'.push I[n], ?_, h9⟩
        intro i' hi'
        simp only [Fin.getElem_fin, Vector.getElem_push]
        split
        · exact h8 ⟨i', by omega⟩ (by grind)
        · rfl
    specialize @ih g I.pop J.pop h5
    if h : DependsOn f (Fin.last n) then
      have h2 : I[Fin.last n] = J[Fin.last n] := h1 (Fin.last n) h
      simp only [Fin.getElem_fin, Fin.val_last] at h2
      simp_rw [g, push_pop_last, h2, push_pop_last] at ih
      exact ih
    else
      simp_rw [g, push_pop_last] at ih
      rw [ih]
      simp only [dependsOn_iff, ne_eq, Fin.getElem_fin, not_exists, not_and, not_not] at h
      apply h
      intro i hi
      have hi' : i < n := by grind only [usr Fin.val_last]
      simp only [Vector.getElem_push_lt hi', Vector.getElem_pop']
      sorry

lemma eq_of_forall_dependency_getElem_eq {n α β} {f : Func n α β} {I J : Vector α n} :
    (∀ i, DependsOn f i →  I[i] = J[i]) → f I = f J := by
  induction n with
  | zero =>
    simp only [Vector.eq_empty, implies_true]
  | succ n ih =>
    intro h
    let g : Vector α n → β := fun v ↦ f (Vector.push v I[n])
    have h2 : ∀ V : Vector α (n + 1), I[n] = V[n] → f V = g V.pop := by
      intro V hV
      simp only [g]
      congr
      ext i hi
      rw [Vector.getElem_push]
      split
      next hh => simp only [Vector.getElem_pop']
      next hh =>
        have : i = n := by omega
        simp_all only [DependsOn, IndependentOf, Fin.getElem_fin]
    by_cases hf : DependsOn f ⟨n, Nat.lt_add_one n⟩
    · have h1 := h ⟨n, Nat.lt_add_one n⟩ hf
      rw [h2 I rfl]
      rw [h2 J h1]
      apply ih
      intro i hi
      simp only [g] at hi
      have : DependsOn f i.castSucc := by
        simp only [DependsOn, IndependentOf, not_forall] at hi
        rcases hi with ⟨a, V, hav⟩
        rw [show (V.set i a).push I[n] = (V.push I[n]).set i a by
          simp only [Vector.set_push, Fin.is_lt, ↓reduceDIte]] at hav
        simp only [DependsOn, IndependentOf, not_forall]
        use a, V.push I[n]
        exact hav
      have := h i.castSucc this
      simp_all only [DependsOn, IndependentOf, Fin.getElem_fin,
        Fin.val_castSucc, Vector.getElem_pop', g]
    · simp only [DependsOn, not_not, IndependentOf] at hf
      rw [hf I[n] J]
      rw [h2 I rfl]
      rw [h2 (J.set (Fin.mk n n.lt_add_one) I[n]) (by simp only [Vector.getElem_set_self])]
      apply ih
      intro i hi
      simp only [g] at hi
      have : DependsOn f i.castSucc := by
        simp only [DependsOn, IndependentOf, not_forall] at hi
        rcases hi with ⟨a, V, hav⟩
        rw [show (V.set i a).push I[n] = (V.push I[n]).set i a by simp [Vector.set_push]] at hav
        simp only [DependsOn, IndependentOf, not_forall]
        use a, V.push I[n]
        exact hav
      have := h i.castSucc this
      simp only [Fin.getElem_fin, Vector.getElem_pop']
      rw [Vector.getElem_set_ne _ _ (by omega)]
      simp_all only [DependsOn, IndependentOf, Fin.getElem_fin, Fin.val_castSucc]


@[expose, simp]
def restrict {n α β} (f : Func n α β) : α → Fin n → Func n α β := fun a i I ↦ f (I.set i a)

@[simp]
lemma restrict_const {n α β} {c : α} {b : β} {i : Fin n} :
    restrict (fun _ ↦ b) c i = (fun _ ↦ b) := by
  ext; simp

lemma restrict_if {n α β} {f g : Func n α β} {b : α} {i : Fin n} {c : Func n α Bool} :
    restrict (fun I ↦ bif c I then f I else g I) b i =
    fun I ↦ bif (restrict c b i I) then (restrict f b i I) else (restrict g b i I) :=
  funext (fun _ ↦ rfl)

end

end Nary
