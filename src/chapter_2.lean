import chapter_1
import tactic.simps

namespace surreal

/-
This chapter is mostly about the protagonists trying to make sense of the text they found my defining some cleaner mathematical notation.

They define surreals concisely like this: `x = (Xₗ, Xᵣ) where Xₗ ≱ Xᵣ`
Here by `Xₗ ≱ Xᵣ` they mean that every `xₗ ≱ xᵣ` where `xₗ ∈ Xₗ` and `xᵣ ∈ Xᵣ`.

Capitals are generally used to denote sets, and the same lowercase letters denote elements from those sets.

In our case, the equivalent of `Xₗ` is simply `x.left`, and `Xᵣ` is `x.right`. For elements of those
sets, we tend to call them `xl` and `xr`, because it's just more confortable to read and write without those tiny subscripts.
-/

/-
We'll not take a small pause to define ≱ both for surreals and sets of surreals, since Lean's `has_le` doesn't include this variant automatically, and it is used extensively moving forward. Note that < might not strictly equivalent to ≱, we might prove it later on, but we shouldn't take it for granted.
-/

@[notation_class]
class has_nge (α β: Type*) := (nge : α → β → Prop)

/-
Left-binding power 50 is the same as other inequality operators.
https://leanprover.github.io/theorem_proving_in_lean/interacting_with_lean.html#notation
https://github.com/leanprover/lean/blob/master/library/init/core.lean#L50
-/ 
infix ` ≱ `:50 := has_nge.nge

def nge_num_num (x y: surreal): Prop :=
  ¬(x ≥ y)
@[simps] instance has_nge_num_num : has_nge surreal surreal := ⟨nge_num_num⟩

def nge_set_set (X Y: set surreal): Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, x ≱ y
@[simps] instance has_nge_set_set : has_nge (set surreal) (set surreal) := ⟨nge_set_set⟩

/-
Let's take a moment to consider `x = (Xₗ, Xᵣ) where Xₗ ≱ Xᵣ`. It is nice and concise, but in my opinion it doesn't exactly match the wording from the rules.

It says: `no member of the left is greater than or equal to any member of the right set`

This, to me, literally translates to something like: there doesn't exist a pair of members of the left and right sets that are greater than or equal to each other. Or in mathematical notation: `¬∃ xl ∈ x.left, ∃ xr ∈ x.right, xl ≥ xr`, which is our definition for `valid`.

Whereas `Xₗ ≱ Xᵣ` here implies `∀ xl ∈ x.left, ∀ xr ∈ x.right, xl ≱ xr`, which is intuitively equivalent, but we should prove it is, just to be safe.
-/


lemma rule_1_nge (x: surreal): valid x.left x.right ↔ x.left ≱ x.right :=
begin
  simp [valid, nge_num_num, nge_set_set],
end

/-
Then they redefine the numbers with the new notation: `0 = (∅,∅)`, `-1 = (∅, {0})`, `1 = ({0}, ∅)`

Then they check if they are valid, and they find out that:
> If Xₗ or Xᵣ is empty, the condition Xₗ ≱ Xᵣ is true no matter what is in the other set.
-/

lemma valid_empty (L R: set surreal): L = ∅ ∨ R = ∅ → valid L R :=
begin
  simp [valid],
  intro h0,
  apply or.elim h0,
  begin
    intro L0,
    intros l lL r rR hge,
    rw L0 at lL,
    exact lL,
  end,
  begin
    intro R0,
    intros l lL r rR hge,
    rw R0 at rR,
    exact rR,
  end
end

/-
They also express `rule_2` with the new notation: `x ≤ y means Xₗ ≱ y and x ≱ Yᵣ`
-/

/-
They have now introduced ≱ between sets and numbers and viceversa. Let's define those then.
-/

def nge_set_num (X: set surreal) (y: surreal) :=
  ∀ x ∈ X, x ≱ y
@[simps] instance has_nge_set_num : has_nge (set surreal) surreal := ⟨nge_set_num⟩


def nge_num_set (x: surreal) (Y: set surreal) :=
  ∀ y ∈ Y, x ≱ y
@[simps] instance has_nge_num_set : has_nge surreal (set surreal) := ⟨nge_num_set⟩

/-
Again, the semantics differ somewhat from the original wording, so let's check that they are indeed
equivalent to our original definition from `rule_2`.
-/

lemma rule_2_nge (x y: surreal): x ≤ y ↔ x.left ≱ y ∧ x ≱ y.right :=
begin
  rw rule_2,
  simp [nge_set_num, nge_num_set, nge_num_num],
end

end surreal