import Std.Sat.CNF.Basic
import Bdd.BDD

namespace Sat

def BDD_of_literal (l : Std.Sat.Literal (Fin n)) : BDD := if l.2 then (BDD.var l.1) else (BDD.var l.1).not

def BDD_of_clause (c : Std.Sat.CNF.Clause (Fin n)) : BDD := (c.map BDD_of_literal).foldr BDD.or (BDD.const false)

def BDD_of_CNF (C : Std.Sat.CNF (Fin n)) : BDD := (C.clauses.map BDD_of_clause).foldr BDD.and (BDD.const true)

@[simp]
lemma BDD_of_literal_nvars : (BDD_of_literal (n := n) C).nvars ≤ n := by
  simp only [BDD_of_literal]
  split <;> (simp; omega)

@[simp]
lemma BDD_of_clause_nvars : (BDD_of_clause (n := n) C).nvars ≤ n := by
  induction C <;> simp_all [BDD_of_clause]

@[simp]
lemma BDD_of_CNF_nvars : (BDD_of_CNF (n := n) C).nvars ≤ n := by
  rcases C with ⟨⟨clauses⟩⟩
  induction clauses <;> simp_all [BDD_of_CNF]

lemma BDD_of_CNF_correct {n} {f : Fin n → Bool} (C : Std.Sat.CNF (Fin n)) :
    Std.Sat.CNF.eval f C = (BDD_of_CNF C).denotation (n := n) (by simp) (Vector.ofFn f) := by
  rcases C with ⟨⟨clauses⟩⟩
  simp only [Std.Sat.CNF.eval, List.size_toArray, List.all_toArray', BDD_of_CNF, List.map_toArray,
    List.length_map, List.foldr_toArray']
  induction clauses with
  | nil => simp only [List.all_nil, List.map_nil, List.foldr_nil, BDD.const_denotation,
    Function.const_apply]
  | cons head tail ih =>
    simp only [List.all_cons, List.map_cons, List.foldr_cons, BDD.and_denotation]
    rw [ih]
    congr 1
    induction head with
    | nil => simp [BDD_of_clause]
    | cons head tail ih =>
      simp only [Std.Sat.CNF.Clause.eval_cons]
      rw [ih]
      simp only [BDD_of_clause, List.map_cons, List.foldr_cons, BDD.or_denotation]
      congr 1
      simp only [BDD_of_literal]
      split <;> simp [*]

/-
For some reason the Lean type-checker takes a very long time for this instance.
I tried to make the proof simpler, but I didn't help. As a temporary fix
I increased the number of heartbeats, but it would be better to rewrite the proof.
-/
set_option maxHeartbeats 300000
instance instDecidableUnsat {n} (C : Std.Sat.CNF (Fin n)) : Decidable (Std.Sat.CNF.Unsat C) :=
  decidable_of_iff ((BDD_of_CNF C).SemanticEquiv (BDD.const false)) ⟨l_to_r, r_to_l⟩ where
    l_to_r h := by
      simp only [BDD.SemanticEquiv] at h
      contrapose h
      rw [funext_iff]
      simp only [Std.Sat.CNF.Unsat, not_forall, Bool.not_eq_false] at h
      rcases h with ⟨f, hf⟩
      rw [BDD_of_CNF_correct] at hf
      simp only [BDD.const_denotation, Function.const_apply, not_forall, Bool.not_eq_false]
      use Vector.cast (by simp) (Vector.ofFn fun i : Fin (BDD_of_CNF C).nvars ↦ f ⟨i.1, lt_of_lt_of_le i.2 BDD_of_CNF_nvars⟩)
      simp only [le_refl, BDD.denotation_cast]
      rw [BDD.denotation_take'] at hf
      rw [← hf]
      congr 1
      ext i hi
      have h := Vector.getElem_extract (as := (Vector.ofFn f)) (show i < (min (BDD_of_CNF C).nvars n) - 0 by simpa)
      simp_rw [Vector.take_eq_extract, Vector.getElem_cast, h,  Nat.zero_add, Vector.getElem_ofFn]
    r_to_l h1 := by
      simp only [Std.Sat.CNF.Unsat] at h1
      simp only [BDD.SemanticEquiv]
      ext I
      simp only [BDD.const_denotation, Function.const_apply]
      have h2:= h1 (fun i ↦ if hi : i < (max (BDD_of_CNF C).nvars (BDD.const false).nvars) then I[i] else false)
      simp only [BDD.const_nvars, Nat.zero_le, sup_of_le_left] at h2
      rw [BDD_of_CNF_correct] at h2
      rw [BDD.denotation_take (m := max (BDD_of_CNF C).nvars (BDD.const false).nvars)] at h2
      · rw [← h2]
        simp only [BDD.const, Vector.take_eq_extract]
        conv => lhs; rw [BDD.denotation_take' (hn := by omega)]
        conv => rhs; rw [BDD.denotation_take' (hn := by grind only [= min_def])]
        congr 1
        simp_rw [Vector.take_eq_extract, Vector.cast_eq_cast, Vector.extract_extract, Vector.cast_cast, Nat.add_zero, Nat.sub_zero]
        ext i hi
        rw [Vector.getElem_cast]
        have h3 := Vector.getElem_extract (as := I) (show i < (min (BDD_of_CNF C).nvars (max (BDD_of_CNF C).nvars (BDD.const false).nvars)) - 0 by simp; omega)
        simp only [Nat.sub_zero, zero_add] at h3
        have h4 := Vector.getElem_extract (as := (Vector.ofFn fun i : Fin n ↦ if h : i.1 < (BDD_of_CNF C).nvars then I[i.1] else false)) (show i < min ((min (0 + (BDD_of_CNF C).nvars) (max (BDD_of_CNF C).nvars 0))) n - 0 by simp_all; omega)
        simp only [Nat.sub_zero, zero_add, Vector.getElem_ofFn] at h4
        simp only [Nat.sub_zero]
        grind only [= Fin.getElem_fin]
      · simp
      · simp


-- #eval Std.Sat.CNF.eval (fun _ : Nat ↦ true) []
-- #eval Std.Sat.CNF.eval (fun _ : Nat ↦ true) []
--#eval! instDecidableUnsat (n := 3) [[⟨1, true⟩], [⟨2, false⟩]]
-- #eval! (BDD_of_CNF (n := 3) [[⟨1, true⟩, ⟨2, false⟩]]).size

end Sat
