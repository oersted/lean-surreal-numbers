import chapter_1
import chapter_2

namespace surreal

/-
This chapter starts by verifying the proofs written at the end of the stone they found.

> Conway proved that zero was less than or equal to zero
> And he proved that minus one is less than but not equal to zero and zero is less than but not equal to one.
-/

/-
As they say, `0 ≤ 0` is fairly trivial. 

> By rule (2), he must show that no element of the empty set is greater than or like 0, and that 0
is not greater than or line any element of the empty set.
-/

lemma zero_le_zero: zero ≤ zero :=
begin
  rw rule_2,
  simp,
  split,
  begin
    intros hx hxl hle,
    rw zero.has_left at hxl,
    exact hxl,
  end,
  begin
    intros hx hxr hle,
    rw zero.has_right at hxr,
    exact hxr,
  end
end

/-
It finally starts being a bit more meaty. How to prove that a number is not equal to another with the existing rules?

> More interesting is how he could prove that -1 is not like 0 (they say "like" instead of "equals" here for a while to avoid getting confused by their existing intuitions aobut equality). The only
way I can think of is that he proved that 0 is not less-than-or-like -1. I mean, we have rule (2) to
tell wether one number is less than or like another; and if x is not less-than-or-like y, it isn't less than y and it isn't like y.

> I see, we want to show at 0 ≤ -1 is false. This is rule (2) with x = 0 and Yᵣ = {0}, so 0 ≤ -1 if
and only if 0 ≱ 0. But 0 is ≥ 0, we know that, so 0 ≰ -1. He was right.

First they use some simple logic to deduce that `¬(0 ≤ -1) → ¬(0 = -1)`.
They go about it like this: `¬(0 ≤ -1) → ¬(0 < -1 ∨ 0 = -1) → ¬(0 < -1) ∧ ¬(0 = -1) → ¬(0 = -1)`

We could easily generalize this to any two numbers, but let's stick to 0 and -1 for now.

Then they prove `¬(0 ≤ -1)` by contradiction using `rule_2`, like this: TODO

There's a couple caveats to proving this with Lean not:
* We don't actually have a < operation defined yet on surreals, and we shoudln't assume it behaves like with other numbers without deriving it from the axioms.
* What we did above was forward reasoing, but it is generally preferred to do backwards proving in Lean, the tools are a bit more mature.

Through my brief experimentation, 

**Note**: You might we wondering why I don't make a few aliases like `zero ⇒ 0` to make things cleaner; they do in the book after all. It's mainly because I don't want to give the impression that surreal numbers are like natural numbers or any other common number system. If I showed them like numbers, it would be easier to get confused by our existing intuitions about how they behave. There is a concept of positive and negative (either side of 0), but we will soon discover many more numbers that can't be represented with natural numbers, so let's stick to textual names the whole time so that we don't get confused.
-/

lemma not_le_to_not_eq_zero_minus_one: ¬(zero ≤ minus_one) → ¬(zero = minus_one) :=
begin
  intro hnge,
  sorry
end


end surreal