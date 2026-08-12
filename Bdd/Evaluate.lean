module

public import Bdd.Basic

namespace Evaluate

public section

def evaluate (O : OBdd n m) : Vector Bool n → Bool := fun I ↦
  match h : O.1.root with
  | .terminal b => b
  | .node j => if I[O.1.heap[j].var] then evaluate (O.high h) I else evaluate (O.low h) I
termination_by O

lemma evaluate_evaluate : evaluate O = OBdd.evaluate O := by
  ext I
  unfold evaluate
  split
  next b hb => simp [OBdd.evaluate_terminal hb]
  next j hj =>
    have := evaluate_evaluate (O := O.low hj)
    have := evaluate_evaluate (O := O.high hj)
    simp [OBdd.evaluate_node'' hj, *]
termination_by O

lemma evaluate_terminal {O : OBdd n m} : O.1.root = .terminal b → evaluate O = Function.const _ b := by
  rw [evaluate_evaluate]
  exact OBdd.evaluate_terminal

lemma evaluate_node {O : OBdd n m} (h : O.1.root = .node j) :
    evaluate O = fun I ↦ if I[O.1.heap[j].var] then evaluate (O.high h) I else evaluate (O.low h) I := by
  rw [evaluate_evaluate]
  rw [OBdd.evaluate_node'' h]
  simp [evaluate_evaluate]

/--
A simp attribute that is used in `BDD.lean` to infer the size of `BDDs` when during evaluation. -/
register_simp_attr bdd_nvars

-- Macro for a common pattern
macro "bdd_bounds" : tactic => `(tactic|
  first
  | assumption
  | simp only [bdd_nvars] at *; omega
)

macro_rules
  | `(tactic| get_elem_tactic_extensible) => `(tactic| bdd_bounds)

end

end Evaluate
