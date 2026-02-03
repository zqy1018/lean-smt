/-
Copyright (c) 2021-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Pîrlea
-/

import cvc5

namespace Smt.Minimize

open cvc5

/-- Create an SMT constraint that the given sort has cardinality *at most* `n`.
    `∃c₁, ..., cₙ. ∀x. (x = c₁) ∨ ... ∨ (x = cₙ)` -/
def mkSortCardinalityConstraint (tm : TermManager) (s : cvc5.Sort) (n : Nat) : Env Term := do
  let existVars ← (List.range n).toArray.mapM fun i => tm.mkVar s s!"_card_{i}"
  let x ← tm.mkVar s "_card_x"
  let eqs ← existVars.mapM fun c => tm.mkTerm .EQUAL #[x, c]
  let disj ← if eqs.size == 1 then pure eqs[0]! else tm.mkTerm .OR eqs
  let forallBody ← tm.mkTerm .FORALL #[← tm.mkTerm .VARIABLE_LIST #[x], disj]
  tm.mkTerm .EXISTS #[← tm.mkTerm .VARIABLE_LIST existVars, forallBody]


/-- Create an SMT constraint that the given relation has at most `n` true tuples.
    `∃c₁...cₙ. ∀x. R(x) → (x = c₁) ∨ ... ∨ (x = cₙ)` (where x, cᵢ are tuples) -/
def mkRelationCardinalityConstraint (tm : TermManager) (rel : cvc5.Term) (n : Nat) : Env Term := do
  let domainSorts := rel.getSort.getFunctionDomainSorts!
  let univVars ← domainSorts.mapIdxM fun j s => tm.mkVar s s!"_rel_x_{j}"
  let relApp ← tm.mkTerm .APPLY_UF (#[rel] ++ univVars)
  if n == 0 then
    return ← tm.mkTerm .FORALL #[← tm.mkTerm .VARIABLE_LIST univVars, ← tm.mkTerm .NOT #[relApp]]
  let tuples ← (List.range n).toArray.mapM fun i =>
    domainSorts.mapIdxM fun j s => tm.mkVar s s!"_rel_{i}_{j}"
  let existVars := tuples.foldl (· ++ ·) #[]
  let disjs ← tuples.mapM fun tuple => do
    let conjs ← (tuple.zip univVars).mapM fun (c, x) => tm.mkTerm .EQUAL #[x, c]
    if conjs.size == 1 then pure conjs[0]! else tm.mkTerm .AND conjs
  let disj ← if disjs.size == 1 then pure disjs[0]! else tm.mkTerm .OR disjs
  let impl ← tm.mkTerm .IMPLIES #[relApp, disj]
  let forallBody ← tm.mkTerm .FORALL #[← tm.mkTerm .VARIABLE_LIST univVars, impl]
  tm.mkTerm .EXISTS #[← tm.mkTerm .VARIABLE_LIST existVars, forallBody]


/-- Generic minimization using exponential + binary search.
    - `mkConstraint n` builds a constraint for cardinality at most `n`
    - `start` is the initial value to test (1 for sorts, 0 for relations)
    We use exponential search to find bounds first, which is efficient when the minimum
    cardinality is small (common case). -/
partial def minimizeCardinality (slv : Solver) (mkConstraint : Nat → Env Term)
    (start : Nat) (checkTimeout : Env Bool) : Env (Option Nat) := do
  let checkCard (n : Nat) : Env (Option Bool) := do
    if ← checkTimeout then return none
    let constraint ← mkConstraint n
    let result ← slv.checkSatAssuming #[constraint]
    if result.isUnknown then return none
    return some result.isSat

  -- Exponential search: test start, start*2, start*4, ... until SAT.
  let rec findBounds (prev n : Nat) : Env (Option (Nat × Nat)) := do
    if n > 100 then return none
    match ← checkCard n with
    | none => return none
    | some true => return some (if start == 0 then prev else prev + 1, n)
    | some false => findBounds n (if n == 0 then 1 else n * 2)

  -- Binary search for minimum in [lo, hi] where hi is known to succeed
  let rec binarySearch (lo hi : Nat) : Env (Option Nat) := do
    if lo >= hi then return some lo
    let mid := (lo + hi) / 2
    match ← checkCard mid with
    | none => return none
    | some true => binarySearch lo mid
    | some false => binarySearch (mid + 1) hi

  match ← findBounds 0 start with
  | none => return none
  | some (lo, hi) =>
    match ← binarySearch lo hi with
    | none => return none
    | some n =>
      slv.assertFormula (← mkConstraint n)
      return some n

/-- Check if a term represents a minimizable relation (function with arity > 0 returning Bool). -/
def isMinimizableRelation (t : cvc5.Term) : Bool :=
  let s := t.getSort
  if s.getKind != .FUNCTION_SORT then false
  else
    let domainSorts := s.getFunctionDomainSorts!
    if domainSorts.size == 0 then false  -- Constants not minimizable
    else s.getFunctionCodomainSort!.getKind == .BOOLEAN_SORT

/-- Minimize sort cardinalities and relation sizes.
    Takes an optional timeout in milliseconds for the overall minimization budget.
    Returns `true` if minimization succeeded (or there was nothing to minimize),
    `false` if minimization failed/timed out and the caller should use the original model. -/
def minimizeSorts (slv : Solver) (tm : TermManager)
    (uss : Array cvc5.Sort) (ufs : Array cvc5.Term := #[])
    (timeoutMs : Option Nat := none) : Env Bool := do
  let startTime ← IO.monoMsNow
  let checkTimeout : Env Bool := do
    if let some budget := timeoutMs then
      return (← IO.monoMsNow) - startTime > budget
    return false

  -- Minimize sort cardinalities
  let uninterpSorts := uss.filter (·.isUninterpretedSort)
  let mut sortCards : Array (cvc5.Sort × Nat) := #[]
  for s in uninterpSorts do
    match ← minimizeCardinality slv (mkSortCardinalityConstraint tm s) 1 checkTimeout with
    | some n => sortCards := sortCards.push (s, n)
    | none => return false

  -- Minimize relation sizes
  let mut relCards : Array (cvc5.Term × Nat) := #[]
  for rel in ufs do
    if isMinimizableRelation rel then
      match ← minimizeCardinality slv (mkRelationCardinalityConstraint tm rel) 0 checkTimeout with
      | some n => relCards := relCards.push (rel, n)
      | none => return false

  -- dbg_trace "Minimized sort cardinalities: {sortCards}"
  -- dbg_trace "Minimized relation sizes: {relCards}"

  -- Re-check satisfiability after adding constraints so the solver is in a
  -- valid state for model extraction
  let res ← slv.checkSat
  return res.isSat

end Smt.Minimize
