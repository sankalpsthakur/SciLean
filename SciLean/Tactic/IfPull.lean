import Lean
import SciLean.Util.RewriteBy

namespace SciLean.Tactic

open Lean Meta

universe u v

initialize registerTraceClass `Meta.Tactic.if_pull

private theorem apply_ite' {α : Sort u} {β : Sort v} (f : α → β)
    (c : Prop) [Decidable c] (t e : α) :
    f (if c then t else e) = if c then f t else f e := by
  by_cases h : c <;> simp [h]

private theorem ite_apply' {α : Sort u} {σ : α → Sort v}
    (c : Prop) [Decidable c] (t e : (a : α) → σ a) (a : α) :
    (if c then t else e) a = if c then t a else e a := by
  by_cases h : c <;> simp [h]

private def mkFunExtN (xs : Array Expr) (proof : Expr) : MetaM Expr := do
  let mut proof := proof
  for x in xs.reverse do
    proof ← mkFunExt (← mkLambdaFVars #[x] proof)
  return proof

/-- Simproc that pulls `if` out of applications and lambda functions.

For example:
- `(if 0 ≤ x then x else -x) + y` is transformed to
  `if 0 ≤ x then x + y else -x + y`.
- `fun y => if 0 ≤ x then y + x else y - x` is transformed to
  `if 0 ≤ x then (fun y => y + x) else (fun y => y - x)`. -/
simproc_decl if_pull (_) := fun e => do
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs

    if e.isAppOf ``ite then
      -- Do not pull an unapplied `if` out of itself. This would cause an infinite loop.
      if args.size ≤ 5 then
        return .continue

      let α := e.getArg! 0
      let cond := e.getArg! 1
      let inst := e.getArg! 2
      let t := e.getArg! 3
      let f := e.getArg! 4
      let extraArgs := args[5:]
      let context ← withLocalDeclD `branch α fun branch =>
        mkLambdaFVars #[branch] (mkAppN branch extraArgs)
      let contextType ← whnf (← inferType context)
      unless contextType.isArrow do
        return .continue
      let thn := mkApp context t
      let els := mkApp context f
      let e' ← mkAppOptM ``ite #[none, cond, inst, thn, els]
      let proof ← mkAppOptM ``apply_ite' #[α, none, context, cond, inst, t, f]

      trace[Meta.Tactic.if_pull] s!"if_pull: \n{← ppExpr e}\n==>\n{← ppExpr e'}\n"
      return .visit { expr := e', proof? := some proof }

    -- Locate an argument containing an `if` statement.
    let some i := args.findIdx? fun arg => arg.isAppOfArity ``ite 5
      | return .continue
    let arg := args[i]!
    let α := arg.getArg! 0
    let cond := arg.getArg! 1
    let inst := arg.getArg! 2
    let t := arg.getArg! 3
    let f := arg.getArg! 4
    let context ← withLocalDeclD `branch α fun branch =>
      mkLambdaFVars #[branch] (mkAppN fn (args.set! i branch))
    let contextType ← whnf (← inferType context)
    unless contextType.isArrow do
      return .continue
    let thn := mkApp context t
    let els := mkApp context f
    let e' ← mkAppOptM ``ite #[none, cond, inst, thn, els]
    let proof ← mkAppOptM ``apply_ite' #[α, none, context, cond, inst, t, f]

    trace[Meta.Tactic.if_pull] s!"if_pull: \n{← ppExpr e}\n==>\n{← ppExpr e'}\n"
    return .visit { expr := e', proof? := some proof }

  | .lam .. =>
    lambdaTelescope e fun xs b => do
      unless b.isAppOfArity ``ite 5 do
        return .continue

      let cond := b.getArg! 1
      let inst := b.getArg! 2
      let i := xs.reverse.findIdx? (fun x => cond.containsFVar x.fvarId!) |>.getD xs.size
      unless i > 0 do
        return .continue

      let xs' := xs[0 : xs.size - i]
      let xs'' := xs[xs.size - i :]
      let thn ← mkLambdaFVars xs'' (b.getArg! 3)
      let els ← mkLambdaFVars xs'' (b.getArg! 4)
      let inner ← mkAppOptM ``ite #[none, cond, inst, thn, els]
      let e' ← mkLambdaFVars xs' inner

      -- Repeated `ite_apply'` steps show that applying the pulled-out `if` to the
      -- trailing binders gives the original body. Function extensionality then
      -- reconstructs the two lambda telescopes.
      let mut proof ← mkEqRefl inner
      let mut thnApp := thn
      let mut elsApp := els
      for x in xs'' do
        proof ← mkCongrFun proof x
        let step ← mkAppOptM ``ite_apply' #[none, none, cond, inst, thnApp, elsApp, x]
        proof ← mkEqTrans proof step
        thnApp := mkApp thnApp x
        elsApp := mkApp elsApp x
      proof ← mkEqSymm proof
      proof ← mkFunExtN xs'' proof
      proof ← mkFunExtN xs' proof

      trace[Meta.Tactic.if_pull] s!"if_pull: \n{← ppExpr e}\n==>\n{← ppExpr e'}\n"
      return .visit { expr := e', proof? := some proof }

  -- Pulling an `if` through a `let` body needs a separate congruence proof. Until
  -- that proof is implemented, leave let-expressions unchanged rather than using
  -- an axiom to justify the rewrite.
  | .letE .. => return .continue
  | _ => return .continue


-- #check ((if 0 < 1 then (fun x : Float => x + 2) else (fun x : Float => x + 3)) 42).log rewrite_by
--   simp only [if_pull]

-- #check (let y := 5;  ((if 0 < 1 then (fun x : Float => x + 2 + y) else (fun x : Float => x + 3 + y)) 42).log) rewrite_by
--   simp (config:={zeta:=false}) only [if_pull]
