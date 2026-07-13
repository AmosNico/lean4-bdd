module

import Mathlib.Algebra.Group.Nat.Even

public import Bdd.BDD
import all Bdd.BDD
import Bdd.Reduce

def unexpectedLine (expected found : String) : String :=
  s!"Expected {expected}, but found {found} while parsing the BDD."

def throwUnexpectedLine {α} (expected found : String) : IO α :=
  throw <| IO.userError <| unexpectedLine expected found

def checkLine (h : IO.FS.Handle) (s : String) : IO Unit := do
  let line ← h.getLine
  if line.trimAscii == s then
    return
  else
    throwUnexpectedLine (repr s).pretty s!"{repr line} {repr (← h.readToEnd)}"

def readNamedLine (h : IO.FS.Handle) (name : String) : IO (List String) := do
  let line ← h.getLine
  let line := line.trimAscii.copy
  let x :: xs := line.splitOn
    | throwUnexpectedLine s!"{repr name} followed by something" (repr line).pretty
  if x == name then
    return xs
  else
    throwUnexpectedLine (repr name).pretty (repr x).pretty

def readNamedNat (h : IO.FS.Handle) (name : String) : IO Nat := do
  let l ←  readNamedLine h name
  let e := IO.userError s!"{name} should be followed by a single natural number."
  let [s] := l | throw e
  let some n := s.toNat? | throw e
  return n

def readNamedPos (h : IO.FS.Handle) (name : String) : IO { n : Nat // 0 < n } := do
  let l ←  readNamedLine h name
  let e := IO.userError s!"{name} should be followed by a single positive number."
  let [s] := l | throw e
  let some n := s.toNat? | throw e
  if h : 0 < n then
    return ⟨n, h⟩
  else
    throw e

def String.toFin? (n : ℕ) (s : String) : Option (Fin n) := do
  let i ← s.toNat?
  if h : i < n then some ⟨i, h⟩ else none

def readNamedVectorFin (h : IO.FS.Handle) (name : String) (n m : ℕ) : IO (Vector (Fin n) m) := do
  let l ←  readNamedLine h name
  let e := IO.userError s!"{name} should be followed by {m} natural numbers smaller then {n}."
  let as := l.toArray
  let some as := as.mapM (String.toFin? n) | throw e
  if h : as.size = m then
    return ⟨as, h⟩
  else
    throw e

/--
The DDDMP library uses a node for representing `⊤`. In contrast, in this bdd library there is
no separate node for `⊤`, instead `Pointer` stores references to `⊤` and `⊥`.
In the current implementation, the DDDMP library the BDD nodes are listed using a post-order
strategy, in such a way that a node is never listed before its Then/Else children. This seems
to imply that the first node is always `⊤`, which is checked here to ensure that the further parsing
is correct.
-/
def checkTopNode (h : IO.FS.Handle) : IO Unit := do
  let l ← readNamedLine h "1"
  let [info, _, high, low] := l | throw (IO.userError "TODO 1")
  if info ≠ "T" ∨ high ≠ "0" ∨ low ≠ "0" then
    throw (IO.userError "The first node should represent ⊤, \
      and the line is expected to be of the form \"1 ⊤ <var> 0 0\"")

/--
The DDDMP format supports complemented edges, but the library does not. The nodes in the
DDDMP format follow a 0-based numbering, whereas the libray uses a 0-based numbering.
In addition the DDDMP-format has a node for `⊤`, but the libray does not. Therefore, each
original non-terminal node `n` is mapped to `2 * (n - 2)` and its negation `-n` is mapped
to `2 * (n - 2) + 1`.
-/
def String.toPointer? (s : String) (nNodes : ℕ) :
    Except IO.Error (Pointer (2 * (nNodes - 1))) := do
  let e := IO.userError s!"Expected a non-zero integer between -{nNodes} and {nNodes}, but got {s}."
  let some x := s.toInt? | throw e
  match x with
  | .ofNat (n + 2) =>
    if h : n + 1 < nNodes then
      return .node ⟨2 * n, by omega⟩
    else
      throw e
  | .negSucc (n + 1) =>
    if h : n + 1 < nNodes then
      return .node ⟨2 * n + 1, by omega⟩
    else
      throw e
  | .ofNat 1 => return .terminal true
  | .negSucc 0 => return .terminal false
  | .ofNat 0 => throw e

/--
The DDDMP format makes a distiction between variables and support variables. For each bdd,
the support variables are the variables actually occuring in the (internal representation of) the
bdd (listed in `support_ids`). When representing the nodes in the DDDMP file, the support varibles
are used, where each of the support variables is identified by its position in `support_ids`.
-/
def String.toVar? {nVars nSupportVars} (support_ids : Vector (Fin nVars) nSupportVars)
    (s : String) : Except IO.Error (Fin nVars) := do
  let some i := s.toFin? nSupportVars
    | throw <| IO.userError s!"Expected a natural number less then {nSupportVars}, but got {s}."
  return support_ids[i]

/--
Read the node with the given id. Each node is expected to be on a separate line in the following
format: `<id> <var-extrainfo> <var-index> <index-high> <index-low>`.
-/
-- TODO : <var-extrainfo> should be optional
def readNode (h : IO.FS.Handle) (nNodes : ℕ) {nVars nSupportVars}
    (support_ids : Vector (Fin nVars) nSupportVars) (id : ℕ) :
    IO (Node nVars (2 * (nNodes - 1))) := do
  let l ← readNamedLine h (toString id)
  let [_, var, high, low] := l | throw (IO.userError
    s!"Expected \"{id} <var-extrainfo> <var-index> <index-high> <index-low>\"")
  let .ok var := var.toVar? support_ids | throw (IO.userError "The variable id is not valid.")
  let .ok high := high.toPointer? nNodes | throw (IO.userError "The then-index is not valid.")
  let .ok low := low.toPointer? nNodes | throw (IO.userError "The else-index is not valid.")
  return Node.mk var low high

def Pointer.compl {m} : Pointer (2 * m) → Pointer (2 * m)
  | terminal b => terminal (not b)
  | node i =>
    if h : Even i.val then
      node ⟨i + 1, by grind only [= Nat.even_iff]⟩
    else
      node ⟨i - 1, by omega⟩

def Node.compl {n m} (N : Node n (2 * m)) : Node n (2 * m) :=
  ⟨N.var, N.low.compl, N.high.compl⟩

def parseBdd (h : IO.FS.Handle) : IO ((n m : ℕ) × Bdd n m) := do
  checkLine h ".ver DDDMP-2.0"
  checkLine h ".mode A"
  checkLine h ".varinfo 0"
  let n_nodes ← readNamedPos h ".nnodes"
  let n_vars ← readNamedNat h ".nvars"
  let n_supvars ← readNamedNat h ".nsuppvars"
  let ids ← readNamedVectorFin h ".ids" n_vars n_supvars
  let perm_ids ← readNamedVectorFin h ".permids" n_vars n_supvars
  if ids ≠ perm_ids then
    throw <| IO.userError "Permutations of variables are currently not supported."
  let n_roots ← readNamedNat h ".nroots"
  let root_ids ← List.mapM (String.toPointer? · n_nodes) <$> readNamedLine h ".rootids"
  checkLine h ".nodes"
  checkTopNode h
  let pos_nodes ← (Vector.range' 2 (n_nodes - 1)).mapM (readNode h n_nodes ids ·)
  checkLine h ".end"
  let .ok [root] := root_ids | throw (IO.userError "Expected a single root node.")
  let nodes := (pos_nodes.flatMap fun N ↦ #v[N, N.compl]).cast (by omega)
  return ⟨n_vars, 2 * (n_nodes - 1), Bdd.mk nodes root⟩

/-- An incomplete test to check whether a `Bdd` is ordered. -/
def Bdd.isOrdered {n m} (B : Bdd n m) : Bool :=
  B.heap.all fun N =>  N.var.val < N.low.toVar B.heap ∧ N.var.val < N.high.toVar B.heap

lemma Bdd.Orderd_of_isOrderd {n m} {B : Bdd n m} (h1 : B.isOrdered) : B.Ordered := by
  simp only [isOrdered, Bool.decide_and, Vector.all_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h1
  rw [ordered_iff']
  rintro p q hp ⟨⟩
  case low => simp_all [Fin.lt_def, Pointer.toVar_node]
  case high => simp_all [Fin.lt_def, Pointer.toVar_node]

public def parseBDD' (h : IO.FS.Handle) : IO BDD := do
  let ⟨n, m, B⟩ ← parseBdd h
  if h : B.isOrdered then
    let O : OBdd n m := ⟨B, B.Orderd_of_isOrderd h⟩
    let ⟨⟨s, O'⟩, h, _⟩ := Reduce.oreduce O
    return ⟨n, s, O', h⟩
  else throw (IO.userError "The given bdd is not ordered")

public def parseBDD (path : System.FilePath) : IO BDD := do
  IO.FS.Handle.mk path IO.FS.Mode.read >>= parseBDD'
