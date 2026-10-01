module

import Mathlib.Data.Vector.Basic

namespace Nary

public section

abbrev Func n α β := Vector α n → β

/-- `DependsOn f i` if the output of `f` depends on the value of the `i`th input. -/
def DependsOn {n α β} (f : Func n α β) (i : Fin n) :=
  ∃ v1 v2, (∀ i' ≠ i, v1[i'] = v2[i']) ∧ f v1 ≠ f v2

lemma dependsOn_iff {n α β} {f : Func n α β} {i : Fin n} :
    DependsOn f i ↔ ∃ v1 v2, (∀ i' ≠ i, v1[i'] = v2[i']) ∧ f v1 ≠ f v2 := by rfl

lemma push_pop_last {α n} (I : Vector α (n + 1)) : I.pop.push I[n] = I := by
  have h: I[n] = I.back := by simp only [Vector.back_eq_getElem, Nat.add_one_sub_one]
  rw [h, Vector.push_pop_back]

lemma eq_of_forall_dependency_getElem_eq {n α β} {f : Func n α β} {I J : Vector α n} :
    (∀ i, DependsOn f i →  I[i] = J[i]) → f I = f J := by
  induction n with
  | zero =>
    simp only [Vector.eq_empty, implies_true]
  | succ n ih =>
    intro h1
    let g : Vector α n → β := fun v ↦ f (Vector.push v I[n])
    have h2 : ∀ (i : Fin n), DependsOn g i → I.pop[i] = J.pop[i] := by
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
    specialize @ih g I.pop J.pop h2
    simp only [g, push_pop_last] at ih
    if h : DependsOn f (Fin.last n) then
      specialize h1 (Fin.last n) h
      simp only [Fin.getElem_fin, Fin.val_last] at h1
      rw [ih, h1, push_pop_last]
    else
      rw [ih]
      simp only [dependsOn_iff, ne_eq, Fin.getElem_fin, not_exists, not_and, not_not] at h
      apply h
      intro i hi
      have hi' : i < n := by grind only [usr Fin.val_last]
      simp only [Vector.getElem_push_lt hi', Vector.getElem_pop']

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
