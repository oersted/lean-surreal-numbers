import tactic.suggest
import chapter_1

namespace surreal

/-
Chapter 2 start simply with the protagonists figuring out some mathematical notation to express the
initial rules, I'll summarize it here.

A surreal number is denoted as: `x = (Xₗ, Xᵣ) where Xₗ ≱  Xᵣ`

`Xₗ` and `Xᵣ` are sets, hence the capital numbers.
`Xₗ ≱  Xᵣ` is a shorthand for `∀ xₗ ∈ Xₗ, ∀ xᵣ ∈ Xᵣ, xₗ ≱  xᵣ`.
As you can see, we conventionally name elements of `Xₗ` as `xₗ` and elements of `Xᵣ` as `xᵣ`.

In our case, `Xₗ` is `x.left` and `Xᵣ` is `x.right`. As you've seen in the previous chapter, we also
conventionally refer to `xₗ` as `xl` and to `xᵣ` as `xr`, it's just more confortable to type.
-/

/-
Last chapter we defined an ordering of surreals, but in this chapter `Xₗ ≱  Xᵣ` refers to an ordering
of sets of surreals. Let's define one for completeness, it might be handy to have it in later.
-/

def set.lt (X Y: set surreal): Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, x < y
instance : has_lt (set surreal) := ⟨set.lt⟩ 

def set.le (X Y: set surreal): Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, x ≤ y
instance : has_le (set surreal) := ⟨set.le⟩

/-
Just to be sure, let's write a small proof to verify that Lean indeed derived the meaning of `≱`
correctly from `<` and `≤`. It seems that Lean doesn't like the `≱ ` symbol, so we'll just use `¬`
and `≥` instead.
-/

lemma set.nge_iff (X Y: set surreal): ¬(X ≥ Y) ↔ ∀ x ∈ X, ∀ y ∈ Y, ¬(x ≥ y) :=
begin
  split,
  begin
    intro hnge_XY,
    intros x hx,
    intros y hy,
    intro hge_xy,
    apply hnge_XY,
    rw ge,
    sorry,
  end
  sorry
end

#check set.le

/-
It is a bit pedantic, but since the wording in this definition is subtly different from last chapter
I'd like to verify that it is indeed equivalent to our `valid`.
-/

lemma alt_valid (x: surreal): valid x.left x.right ↔ ¬(x.left ≥ x.right) :=
begin
  sorry
end 

end surreal