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
