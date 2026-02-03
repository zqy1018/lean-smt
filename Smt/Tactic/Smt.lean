/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean
import Lean.Meta.Tactic.TryThis

import Smt.Dsl.Sexp
import Smt.Reconstruct
import Smt.Reconstruct.Prop.Lemmas
import Smt.Translate.Query
import Smt.Preprocess
import Smt.Util

namespace Smt

open Lean hiding Command
open Elab Tactic Qq
open Smt Translate Query Reconstruct Util

/-- Configuration options for the SMT tactic. -/
structure Config where
  /-- The timeout for the SMT solver in seconds. -/
  timeout : Option Nat := .none
  /-- Whether to enable native components for proof reconstruction. Speeds up normalization and
      reduction proof steps. However, it adds the Lean compiler to the trusted code base. -/
  native : Bool := false
  /-- Whether to monomorphize the Lean goal before sending it to the SMT solver. The monomorphization
      step reduces the goal from Lean's dependent type theory to a simpler, first-order logic. -/
  mono : Bool := false
  /-- Whether to normalize the Lean goal before sending it to the SMT solver. The normalization
      step performs unconditional rewrites to ensure that the goal is in a standard form suitable
      for SMT solving. -/
  normalize : Bool := true
  /-- Whether to embed subtypes (e.g., `Nat`, `Bool`, `Rat`) into types understood by the SMT solver. -/
  embeddings : Bool := true
  /-- Whether to trust the result of the SMT solver. Closes the current goal with a `sorry` if the
      SMT solver returns `unsat`. **Warning**: use with caution, as this may lead to unsoundness.
      Additionally adds the translation from Lean to SMT to the trusted code base, which is not
      always sound. -/
  trust : Bool := false
  /-- Whether to show a potential counter-example when the SMT solver returns `sat`. -/
  model : Bool := false
  /-- Just show the SMT query without invoking a solver. Useful for debugging. -/
  showQuery : Bool := false
  /-- Options to pass to the solver, in addition to the default ones. -/
  extraSolverOptions : List (String × String) := []
  /-- Whether to minimize the model by finding smallest sort cardinalities. -/
  minimizeModel : Bool := false
  /-- Timeout in seconds for model minimization. Uses main timeout if not set. -/
  minimizeTimeout : Option Nat := none
deriving Inhabited, Repr

/-- A context for elaborating the metavariables in the model. Necessary to
enable storing the model and printing it at a later time. This is the same as
the `ExprWithCtx` structure in `ProofWidgets.Compat`, but without the `expr`
field. -/
structure ModelContext where
  ci : Elab.ContextInfo
  lctx : LocalContext
  linsts : LocalInstances
deriving TypeName

def ModelContext.save: MetaM ModelContext :=
  return {
    ci := { ← CommandContextInfo.save with }
    lctx := ← getLCtx
    linsts := ← Meta.getLocalInstances
  }

structure Model where
  /-- Context information for the free variables in the model. -/
  ctx : ModelContext
  /-- Pairs of free variables and their values in the model. -/
  sorts : Array (Expr × Expr)
  /-- Pairs of free variables and their values in the model. -/
  values : Array (Expr × Expr)

def Model.isEmpty (model : Model) : Bool :=
  model.sorts.isEmpty && model.values.isEmpty

inductive Result where
  | sat (model : Option Model)
  | unsat (mvs : List MVarId) (usedHints : Array Expr)
  | unknown (reason : String)

inductive AsyncOutput where
  | queryString (query : String)
  | rawResult (raw : Except cvc5.Error cvc5Result)
  | result (result : Smt.Result)
  | exception (ex : Exception)
deriving Inhabited

structure AsyncState where
  /-- The name of the query currently being processed. Multiple calls to `smt`
  can have the same name — the `smt` tactic will automatically give them
  different indices. -/
  name : Name := `smt
  index : Nat := 0
  sendQuery : Bool := false
  sendRawResult : Bool := false
  sendResult : Bool := true
  /-- The channel to send the output through. -/
  ch :  Option (Std.CloseableChannel ((Name × Nat) × AsyncOutput)) := .none
deriving Inhabited

/-
  Async interface to the `smt` tactic. If users set this channel in the
  environment, `smt` will send relevant output through that channel as soon as it
  becomes available.

  An use-case for this is that of informing the user of an `unsat` result
  _before_ the proof reconstruction is completed.
-/

initialize asyncState : SimpleScopedEnvExtension AsyncState AsyncState ← registerSimpleScopedEnvExtension {
  name := `asyncState
  initial := default
  addEntry := fun _ state' => state'
}

/-- Initialize the async state with the given name and (optional) channel. If
no channel is provided, a new one is created and returned. -/
def initAsyncState [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] [MonadLiftT (ST IO.RealWorld) m] [MonadFinally m] (name : Name) (ch : Option (Std.CloseableChannel ((Name × Nat) × AsyncOutput)) := .none) (sendQuery := false) (sendRawResult := false) (sendResult := true): m (Std.CloseableChannel ((Name × Nat) × AsyncOutput)) := do
  let ch := ch.getD (← Std.CloseableChannel.new)
  Lean.modifyEnv (asyncState.modifyState · (fun _st =>
    {name := name, index := 0, sendQuery := sendQuery, sendRawResult := sendRawResult, sendResult := sendResult, ch := ch }))
  return ch

private def getAsyncStateAndIncreaseIndex [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] [MonadLiftT (ST IO.RealWorld) m] [MonadFinally m] : m AsyncState := do
  let st := asyncState.getState (← getEnv)
  if st.ch.isSome then
    Lean.modifyEnv (asyncState.modifyState · (fun _st => { st with index := st.index + 1 }))
  return st

def genUniqueFVarNames : MetaM (Std.HashMap FVarId String × Std.HashMap String Expr) := do
  let lCtx ← getLCtx
  let st : NameSanitizerState := { options := {}}
  let (lCtx, _) := (lCtx.sanitizeNames st).run
  return lCtx.getFVarIds.foldl (init := ({}, {})) fun (m₁, m₂) fvarId =>
    let m₁ := m₁.insert fvarId (lCtx.getRoundtrippingUserName? fvarId).get!.toString
    let m₂ := m₂.insert (lCtx.getRoundtrippingUserName? fvarId).get!.toString (.fvar fvarId)
    (m₁, m₂)

def prepareSmtQuery (hs : List Expr) (goalType : Expr) (fvNames : Std.HashMap FVarId String) : MetaM (List Command) := do
  let goalId ← Lean.mkFreshMVarId
  Lean.Meta.withLocalDeclD goalId.name (mkNot goalType) fun g =>
  Query.generateQuery g hs fvNames

private def traceSmtResult (r : Except Exception Result) : MetaM MessageData :=
  return match r with
  | .ok (.unsat ..)   => m!"{checkEmoji} unsat"
  | .ok (.sat ..)     => m!"sat"
  | .ok (.unknown r)  => m!"unknown: {r}"
  | .error _          => m!"{bombEmoji}"

def smt (cfg : Config) (mv : MVarId) (hs : Array Expr) : MetaM Result :=
  mv.withContext do
  -- Retrieve and update the async state.
  let st ← getAsyncStateAndIncreaseIndex
  let (id, sendQuery, sendRawResult, sendResult, asyncChannel) := ((st.name, st.index), st.sendQuery, st.sendRawResult, st.sendResult, st.ch)
  try
  -- 0. Create a duplicate goal to preserve the original goal.
  let mv₀ := (← Meta.mkFreshExprMVar (← mv.getType)).mvarId!
  -- 2. Preprocess the hints and goal.
  let steps := if cfg.mono then #[Preprocess.mono] else #[Preprocess.pushHintsToCtx]
  let steps := if cfg.normalize then steps.push Preprocess.normalize else steps
  let steps := if cfg.embeddings then steps.push Preprocess.embedding else steps
  let ⟨map, hs₁, mv₁⟩ ← withTraceNode `smt.perf.preprocess (fun _ => return "preprocess") do
    Preprocess.applySteps mv₀ hs steps
  mv₁.withContext do
  let goalType : Q(Prop) ← mv₁.getType
  -- 3. Generate the SMT query.
  let (fvNames₁, fvNames₂) ← genUniqueFVarNames
  let cmds ← withTraceNode `smt.perf.translate (fun _ => return "translate") do
    prepareSmtQuery hs₁.toList (← mv₁.getType) fvNames₁
  let cmds := .setLogic "ALL" :: cmds
  if cfg.showQuery then
    logInfo m!"goal: {goalType}\n\nquery:\n{Command.cmdsAsQuery (cmds ++ [.checkSat])}"
    -- Return original goal.
    return .unsat [mv] hs₁
  else
    trace[smt] "goal: {goalType}"
    let query := Command.cmdsAsQuery (cmds ++ [.checkSat])
    trace[smt] "\nquery:\n{query}"
    asyncChannel.forM fun channel => do if sendQuery then let _ ← channel.send ((id, .queryString query))
  -- 4. Run the solver.
  let res ← withTraceNode `smt.perf.solve (fun _ => return "solve") do
    solve (Command.cmdsAsQuery cmds) cfg.timeout
      (defaultSolverOptions ++ cfg.extraSolverOptions) cfg.minimizeModel cfg.minimizeTimeout
  -- trace[smt] "\nresult: {res}"
  asyncChannel.forM fun channel => do if sendRawResult then let _ ← channel.send ((id, .rawResult res))
  match res with
  | .error e =>
    -- 5a. Print error reason.
    trace[smt.solve] "\nerror:\n{repr e}\n"
    throwError e.toString
  | .ok (.unknown r) =>
    -- 5b. Print unknown reason.
    trace[smt.solve] "\nunknown reason:\n{r}\n"
    return .unknown r.toString
  | .ok (.unsat pf uc) =>
    -- 5.c Reconstruct unsat core proofs.
    let ctx := { userNames := fvNames₂, native := cfg.native }
    let (uc, _) ← (uc.mapM Reconstruct.reconstructTerm).run ctx {}
    trace[smt] "unsat core: {uc}"
    let ts₁ ← hs₁.mapM Meta.inferType
    let uc ← uc.filterMapM fun p => ts₁.findIdxM? (Meta.isDefEq p)
    let uc := uc.filterMap fun p => (hs₁[p]?)
    let uc := uc.filterMap (map[·]?)
    let uc := hs.filter uc.flatten.contains
    if cfg.trust then
      -- 6. Trust the result by admitting original goal.
      -- We make this a non-synthetic `sorry` because morally it is requested
      -- by the user rather than showing a tactic failure.
      mv.admit (synthetic := false)
      asyncChannel.forM fun channel => do let _ ← channel.send ((id, .result (.unsat [] uc)))
      return .unsat [] uc
    -- 7. Reconstruct proof.
    let (_, ps, p, hp, mvs) ← withTraceNode `smt.perf.reconstruct (fun _ => return "reconstruct") do
      reconstructProof pf ctx
    let mv₂ ← mv₁.assert (← mkFreshId) p hp
    let ⟨_, mv₃⟩ ← mv₂.intro1
    let gs ← mv₃.apply (← Meta.mkAppOptM ``Prop.implies_of_not_and #[listExpr ps.dropLast q(Prop), goalType])
    mv₃.withContext (gs.forM (·.assumption))
    mv.assign (.mvar mv₀)
    asyncChannel.forM fun channel => do let _ ← channel.send ((id, .result (.unsat mvs uc)))
    return .unsat mvs uc
  | .ok (.sat model) =>
    -- 5d. Return potential counter-example.
    if !cfg.model then
      asyncChannel.forM fun channel => do let _ ← channel.send ((id, .result (.sat none)))
      return .sat none
    let (uss, es) := model.iss.unzip
    let cs := es.map Array.size
    let sortCard := Std.HashMap.insertMany ∅ (uss.zip cs)
    let ctx := { userNames := fvNames₂, sortCard := sortCard, native := cfg.native }
    let (uss', _) ← (uss.mapM Reconstruct.reconstructSort).run ctx {}
    let uss' := uss'.map fun us => (map[us]?.getD #[us])[0]?.getD us
    let cs' := cs.map (fun n => .app (.const ``Fin []) (toExpr n))
    let state := { sortCache := Std.HashMap.insertMany ∅ (uss.zip cs') }
    let (ufs, vs) := model.ifs.unzip
    let (ufs', state) ← (ufs.mapM Reconstruct.reconstructTerm).run ctx state
    let ufs' := ufs'.map fun uf => (map[uf]?.getD #[uf])[0]?.getD uf
    let (vs', _) ← (vs.mapM Reconstruct.reconstructTerm).run ctx state
    let model := { ctx := ← mv₀.withContext ModelContext.save, sorts := uss'.zip cs', values := ufs'.zip vs' }
    asyncChannel.forM fun channel => do if sendResult then let _ ← channel.send ((id, .result (.sat (.some model))))
    return .sat (.some model)
  catch ex =>
    -- Close the channel in case of an error, so users don't wait for results
    -- that will never come. We don't close in a `finally` block, since we
    -- want upstream users to be able to listen for results from multiple `smt`
    -- calls with the same name/channel.
    asyncChannel.forM fun channel => do
      let _ ← channel.send ((id, .exception ex))
      channel.close
    throw ex

namespace Tactic

syntax smtStar := "*"

syntax smtHintElem := smtStar <|> term

syntax smtHints := (" [" withoutPosition(smtHintElem,*,?) "]")?

open Lean.Parser.Tactic in
/-- `smt` converts the current goal into an SMT query and checks if it is
satisfiable. By default, `smt` generates the minimum valid SMT query needed to
assert the current goal. However, that is not always enough:
```lean
theorem modus_ponens (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt
```
For the theorem above, `smt` generates the query below:
```smt2
(declare-const q Bool)
(assert (not q))
(check-sat)
```
which is missing the hypotheses `hp` and `hpq` required to prove the theorem. To
pass hypotheses to the solver, use `smt [h₁, h₂, ..., hₙ]` syntax:
```lean
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt [hp, hpq]
```
The tactic then generates the query below:
```smt2
(declare-const q Bool)
(assert (not q))
(declare-const p Bool)
(assert p)
(assert (=> p q))
(check-sat)
```
The tactic also supports the `*` wildcard hint, which means "all hypotheses".
So, the following also works:
```lean
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt [*]
```
The tactic can be configured with additional options. For example, to set a
timeout of 1 second for the SMT solver, use:
```lean
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt (timeout := .some 1) [*]
```
Please take a look at the `Smt.Config` structure for more options.
-/
syntax (name := smt) "smt " optConfig smtHints : tactic

open Lean.Parser.Tactic in
/--
`smt?` takes the same arguments as `smt`, but reports an equivalent call to
`smt` that would be sufficient to close the goal. This is useful for reducing
the size of the hints in a local invocation to speed up processing.
```
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  smt? -- prints "Try this: simp only [ite_true]"
```
-/
syntax (name := smtTrace) "smt?" optConfig smtHints : tactic

open Lean.Parser.Tactic in
/-- `smt_show` is short-hand for `smt +showQuery`. -/
macro "smt_show " c:optConfig h:smtHints : tactic => do
  let `(optConfig| $cs*) := c | Macro.throwUnsupported
  match h with
  | `(smtHints| )        => `(tactic| (smt +showQuery $cs*))
  | `(smtHints| [$hs,*]) => `(tactic| (smt +showQuery $cs* [$hs,*]))
  | _                    => Macro.throwUnsupported

declare_config_elab elabConfig Smt.Config

def elabSmtHintElem : TSyntax ``smtHintElem → TacticM (Array (Expr × (TSyntax ``smtHintElem)) × Array Expr)
  | `(smtHintElem| *) => do
    let fvs ← Smt.Preprocess.getPropHyps
    let hs := fvs.map Expr.fvar
    let lctx ← getLCtx
    let ss : Array (TSyntax ``smtHintElem) ← fvs.mapM fun fv => do
      if let some ldecl := lctx.find? fv then
        if !ldecl.userName.isInaccessibleUserName && !ldecl.userName.hasMacroScopes &&
            (lctx.findFromUserName? ldecl.userName).get!.fvarId == ldecl.fvarId then
          `(smtHintElem| $(mkIdent ldecl.userName):ident)
        else
          `(smtHintElem| *)
      else
        `(smtHintElem| *)
    return (hs.zip ss, hs)
  | `(smtHintElem| $h:term) => do
    let h' ← Auto.Prep.elabLemma h (.leaf s!"❰{h}❱")
    return (#[(h'.proof, ← `(smtHintElem| $h:term))], #[h'.proof])
  | _ => throwUnsupportedSyntax

def elabHints : TSyntax ``smtHints → TacticM (Std.HashMap Expr (TSyntax ``smtHintElem) × Array Expr)
  | `(smtHints| [ $[$hs],* ]) => withMainContext do
    hs.foldlM (init := ({}, #[])) fun (map, acc) h => do
      let (m, a) ← elabSmtHintElem h
      return (map.insertMany m, acc ++ a)
  | `(smtHints| ) => return ({}, #[])
  | _ => throwUnsupportedSyntax

def evalSmtCore (cfg : TSyntax ``Parser.Tactic.optConfig) (hs : TSyntax ``smtHints) := withMainContext do
  let cfg ← elabConfig cfg
  let mv ← Tactic.getMainGoal
  let (map, hs) ← elabHints hs
  let res ← Smt.smt cfg mv hs
  match res with
    | .sat none =>
      throwError "unable to prove goal, either it is false or you need to provide more facts. Try adding '+model' config option to display a potential counter-example (experimental)."
    | .sat (.some model) =>
      if model.isEmpty then
        throwError "unable to prove goal, either it is false or you need to provide more facts. Could not produce a counter-example. Try introducing variables into the local context to get a counter-example."
      else
        let mut md := m!""
        for (v, t) in (model.sorts ++ model.values) do
          md := md ++ m!"\n  {v} = {t}"
        throwError "unable to prove goal, either it is false or you need to provide more facts. Here is a potential counter-example:\n{md}"
    | .unsat mvs uc =>
      Tactic.replaceMainGoal mvs
      let uc := uc.filterMap map.get?
      let uc := uc.toList.eraseDups.toArray
      return uc
    | .unknown r =>
      throwError "unable to prove goal. Try providing more hints. Reason: {r}"

@[tactic smt] def evalSmt : Tactic := fun stx => match stx with
  | `(tactic| smt $cfg:optConfig $hs:smtHints) => do
    _ ← evalSmtCore cfg hs
  | _ => throwUnsupportedSyntax

@[tactic smtTrace] def evalSmtTrace : Tactic := fun stx => withMainContext do
  match stx with
  | `(tactic| smt?%$tk $cfg:optConfig $hs:smtHints) => do
    let uc ← evalSmtCore cfg hs
    let stx ← if uc.isEmpty then `(tactic| smt%$tk) else `(tactic| smt%$tk $cfg [$uc,*])
    Lean.Meta.Tactic.TryThis.addSuggestion tk stx (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax

end Smt.Tactic
