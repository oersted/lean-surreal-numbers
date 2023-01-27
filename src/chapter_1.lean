import tactic.suggest

/-
In this project I will work on formalizing Donald Knuth's lovely classic Surreal Numbers.

My strategy for the formalization will be to define the initial rules as axioms, without proving
that they are consistent with Lean's axiomatic foundations. This is not how Lean is supposed to be
used, it is generally frowned upon to use axioms since it can be quite easy to introduce
contradictions and invalidate the whole theory. It is "unsafe", but I have my reasons for it.

I've already spent many hours getting an understanding of mathlib's definition of surreal numbers,
on attempting (and failing) to find a simpler alternative definition, and to prove the initial rules
on mathlib's surreals.

All of this has been proven to be surprisingly hard, too damn hard for my introductory understanding
of Lean. Mathlib's proof library on surreal is itself very limited, and proving multiplication
is an ongoing effort and it sounds like it's becoming into a huge project. Surreals just seem
to clash with Lean's fundamental design, and people way more experienced that me are already
struggling with it. Indeed, I keep seeing indirect comments implying Conway's theory of games (with 
surreals within) is perhaps still not formally linked to set theory and wider maths, not sure.

I tried using mathlib's definition to prove the initial rules, so that then I could build on it
without going into implementation details. But mathlib doesn't even have a simple operation to get
the left and right sets for a surreal, so I cannot even express the first rule cleanly to prove it.

Discussion with the community about it:
https://leanprover-community.github.io/archive/stream/113489-new-members/topic/defining.20surreal.20numbers.html

Turns out someone else was also trying to do the exact same thing:
https://leanprover-community.github.io/archive/stream/217875-Is-there-code-for-X%3F/topic/Surreal.20numbers.html

This was always intended to be a nice chill introductory learning experience, I don't really care
about being too formal, which is also in the spirit of Knuth's book. Every time I try to tie surreals to existing Lean constructs it instead becomes a nightmare of fighting against extremely
advanced and obscure Lean features. I'll just prove all of this as an isolated island, and we can
leave it for later to think about proving that it is consistent with the fundamental axioms, in
other words, that surreal numbers indeed "exist".
-/

/-
These are the two rules that define surreal numbers in the book:

> **Rule 1**: Every number corresponds to two sets of previously created numbers, such that no member of the left is greater than or equal to any member of the right set.

> **Rule 2**: One number is less than or equal to another number if and only if no member of the first number's left set is greater than or equal to the second number, and no member of the second number's right set is less than or equal to the first number.

First we define an empty type to represent surreals.

You may think that it would make more sense to create a struct with two sets. Go ahead, try. As it
can be seen in the discussion I linked to above, this is black-hole. Lean can't handle this type
of recursive struct, and even if you define it as an inductive type, it apparently contradicts
Cantor's Theorem (which I still don't fully understand, but fair enough).

https://leanprover-community.github.io/archive/stream/217875-Is-there-code-for-X%3F/topic/Surreal.20numbers.html#214704929

The fact that it violates Cantor may bite me in the ass down the line, perhaps my axioms are 
not sound. But, honestly, I don't really care, this is supposed to be some light fun to learn Lean.
-/

constant surreal: Type

namespace surreal

/-
Similarly, we define two empty functions to represent the operations for extracting the two sets
that constitute a surreal number. They are both the same, the distinction between the two sets
is merely symbolic and will only take on meaning through their usage in the axioms below.
-/

constant left: surreal → set surreal
constant right: surreal → set surreal


/-
We will need a ≥ and ≤ operation to define the initial axioms. ≥ comes for free if we define ≤ with Lean's standard type class `has_le`.

Again, we define it as an empty function, just saying that such a function exists.

Indeed, one of the core challenges of defining surreals in Lean seems to be the requirement for 
having to define the type simultaneously with its ordering. This is hard, and can only be done by 
bootstrapping the type with a lower-level more general type with defined ordering, but that is still
quite a challenge.
-/

constant le: surreal → surreal → Prop
noncomputable instance : has_le surreal := ⟨le⟩

/-
> **Rule 1**: Every number corresponds to two sets of previously created numbers, such that no member of the left is greater than or equal to any member of the right set.
-/

def valid (L R: set surreal): Prop :=
  ¬∃ l ∈ L, ∃ r ∈ R, l ≥ r
axiom rule_1 (x: surreal): valid x.left x.right

/-
> **Rule 2**: One number is less than or equal to another number if and only if no member of the first number's left set is greater than or equal to the second number, and no member of the second
number's right set is less than or equal to the first number.
-/

axiom rule_2 (x y: surreal):
  x ≤ y ↔
    (¬∃ xl ∈ x.left, xl ≥ y) ∧
    (¬∃ yr ∈ y.right, yr ≤ x)

/-
> And the first number was created from the void left set and the void right set. Conway called this
number "zero", and said that it shall be a sign to separate positive numbers from negative numbers.

This is the first number we define, so I'd like to note a subtle design decision regarding how they are represented.

If you look carefully, there's nothing forcing us to prove that `zero` is `valid` (as in `rule_1`). In fact, we already claim it is `valid` when we say its type is `surreal`.

Again, all my attempts to include a proof for `valid` as part of the `surreal` type have failed
after several hours-long sessions of unpleasant head-wall-hitting. A structure, an inductive type, a type class... It all looks like it should be easy a-priori, but the recursive nature of the type makes everything really hard. You can't easily define a type that requires a proof that all its subelements of the same type fullfil a certain criteria, because, well, the type is not defined yet so you can't really talk about it.

And, from a different perspective, you cannot really prove that a surreal is valid, because we have
no concept of a non-valid surreal. What about its internal surreals? Would those be valid or not?
It just becomes a mess. Surreals are valid by definition, its an axiom.

When we name a specific surreal number, like `zero` here, and we describe the contets of its two
sets, we do it to our own risk. Lean allows us to define non-valid surreals, and it will think they
are valid, which will introduce a contradiction and break things. It is fairly obvious for `zero` 
to see that it is valid, but we need to be careful moving forward.

As a compromise, I've isolated `valid` above (from `rule_1`) and I will prove it for every
specific surreal number I define. Again, Lean doesn't enforce this, but it is a handy convention
to avoid intorducing footguns.
-/

constant zero: surreal
axiom zero.has_left: zero.left = ∅
axiom zero.has_right: zero.right = ∅
lemma zero.is_valid: valid zero.left zero.right := 
begin
  rw [valid, zero.has_left, zero.has_right],
  rw not_bex,
  intros l hl,
  rw not_bex,
  intros r hr,
  intro hge,
  exact hl,
end

/-
> On the next day, two more numbers were created, one with zero as its left set and one with zero as
its right set. And Conway called the former number "one", and the latter he called "minus one".
-/

constant one: surreal
axiom one.has_left: one.left = {zero}
axiom one.has_right: one.right = ∅
lemma one.is_valid: valid one.left one.right := 
begin
  rw [valid, one.has_left, one.has_right],
  rw not_bex, intros l hl,
  rw not_bex, intros r hr,
  intro hge,
  exact hr,
end


constant minus_one: surreal
axiom minus_one.has_left: minus_one.left = ∅
axiom minus_one.has_right: minus_one.right = {zero}
lemma minus_one.is_valid: valid minus_one.left minus_one.right := 
begin
  rw [valid, minus_one.has_left, minus_one.has_right],
  rw not_bex, intros l hl,
  rw not_bex, intros r hr,
  intro hge,
  exact hl,
end

/-
> Conway proved that zero was less than or equal to zero
> And he proved that minus one is less than but not equal to zero and zero is less than but not equal to one.

Proofs for these are discussed in `chapter_3`, so let's wait until then.
-/

end surreal
