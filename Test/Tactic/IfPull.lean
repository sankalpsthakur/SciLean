import SciLean.Tactic.IfPull

open SciLean
open SciLean.Tactic

example (c : Prop) [Decidable c] (t e y : Nat) :
    (((if c then t else e) + y) rewrite_by simp only [if_pull]) =
      (if c then t + y else e + y) := by
  rfl

example (c : Prop) [Decidable c] (f g : Nat → Nat) (x : Nat) :
    (((if c then f else g) x) rewrite_by simp only [if_pull]) =
      (if c then f x else g x) := by
  rfl

example (c : Prop) [Decidable c] (f g : Nat → Nat) :
    ((fun x => if c then f x else g x) rewrite_by simp only [if_pull]) =
      (if c then f else g) := by
  rfl

example (f g : Nat → Nat → Nat) :
    ((fun x y => if x = 0 then f x y else g x y) rewrite_by simp only [if_pull]) =
      fun x => if x = 0 then f x else g x := by
  rfl

-- A dependent application context cannot be rewritten using ordinary `ite`.
-- The simproc must leave it unchanged rather than constructing an ill-typed branch expression.
example (c : Prop) [Decidable c] (P : Bool → Type) (x : (b : Bool) → P b) :
    ((x (if c then true else false)) rewrite_by simp only [if_pull]) =
      x (if c then true else false) := by
  rfl
