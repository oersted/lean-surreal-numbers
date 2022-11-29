/-
Rule 1: Every number corresponds to two sets of previously created numbers, such that no member of
the left set is greater than or equal to any member of the right set.

Rule 2: One number is less than or equal to another number if an only if no member of the first
number's left set is greater than or equal to the second number, and no member of the second 
number's right set is less than or equal to the first number.
-/

/-
Discussion with community:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.E2.9C.94.20defining.20surreal.20numbers
-/

def is_surreal (α: Type*) [has_le α] (left right: α → set α) : Prop := 
  ∀ (s : α) (l ∈ left s) (r ∈ right s), ¬(l ≥ r)

namespace surreal

def le 
  {α: Type*} [has_le α] [has_lt α] {left right: α → set α} {h: is_surreal α left right} (x y: α)
: Prop := (∀ (l ∈ left x), ¬(l ≥ y)) ∧ (∀ (r ∈ right y), ¬(r ≤ x))

end surreal
