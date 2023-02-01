import tactic.suggest
import tactic.linarith

namespace surreal

-- TODO: separate set and number
inductive number : Type
| zero : number
| add_left : number → number → number
| add_right : number → number → number

instance : has_union (set number) := ⟨λ (X Y : set number), {n | n ∈ X ∨ n ∈ Y}⟩

def number.left : number → set number
| number.zero := ∅
| (number.add_left n l) := {l} ∪ n.left
| (number.add_right n r) := n.left

def number.right : number → set number
| number.zero := ∅
| (number.add_left n l) := n.right
| (number.add_right n r) := {r} ∪ n.right

def number.day : number → ℕ
| number.zero := 0
| (number.add_left n l) := max (l.day + 1) n.day
| (number.add_right n r) := max (r.day + 1) n.day

def number.size : number → ℕ
| number.zero := 0
| (number.add_left n l) := 1 + l.size + n.size
| (number.add_right n r) := 1 + r.size + n.size

-- TODO: more like the original text
-- Great explanation of well-founded: https://exlean.org/well-founded-recursion/
def number.le : number → number → Prop
| number.zero number.zero := true
| (number.add_left x xl) y := 
    have y.size + xl.size < (x.add_left xl).size + y.size, from begin rw number.size, linarith end,
    have x.size + y.size < (x.add_left xl).size + y.size, from begin rw number.size, linarith end,
  ¬(number.le y xl) ∧ (number.le x y)
| (number.add_right x xr) y := 
    have x.size + y.size < (x.add_right xr).size + y.size, from begin rw number.size, linarith end,
  number.le x y
| x (number.add_left y yl) :=
    have x.size + y.size < x.size + (y.add_left yl).size, from begin rw number.size, linarith end,
  number.le x y
| x (number.add_right y yr) := 
    have yr.size + x.size < x.size + (y.add_right yr).size, from begin rw number.size, linarith end,
    have x.size + y.size < x.size + (y.add_right yr).size, from begin rw number.size, linarith end,
  ¬(number.le yr x) ∧ (number.le x y) 
using_well_founded {
  dec_tac := `[assumption],
  rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ s, s.1.size + s.2.size)⟩]}

instance has_le : has_le number := ⟨number.le⟩

def number.surreal : number → Prop
| number.zero := true
| (number.add_left n l) := n.surreal ∧ l.surreal ∧ ∀r ∈ n.right, ¬(l ≥ r)
| (number.add_right n r) := n.surreal ∧ r.surreal ∧ ∀l ∈ n.left, ¬(l ≥ r)


-- lemma left_mem (x y z : number) : x ∈ (y.add_left z).left → x ∈ y.left :=
-- begin
--   intro h,
--   rw [number.left] at h,
--   sorry
-- end

-- theorem member_is_older (x : number) : 
--   (∀xl ∈ x.left, (number.day xl) < (number.day x)) ∧
--   (∀xr ∈ x.right, (number.day xr) < (number.day x)) :=
-- begin
--   split,
--   begin
--     intros xl hmem,
--     induction x with hx hxl ihx ihxl hx hxr ihx ihxr,
--     begin
--       rw number.day,
--       apply false.rec,
--       exact hmem,
--     end,
--     begin
--       rw number.day,
--       refine lt_max_iff.mpr _,
--       apply or.intro_right,
--       apply ihx,
--       apply left_mem,
--       exact hmem,
--     end,
--     begin
--       sorry
--     end
--   end,
--   begin
--     sorry
--   end
-- end


-- def le : number → number → Prop
-- | x y := ∀ xl ∈ x.left, ¬(le y xl)
-- using_well_founded 
--   { rel_tac := λ _ _, 
--     `[exact ⟨_, measure_wf (λ s, s.1.day + s.2.day)⟩] }
  
-- def mem : number → set → Prop
-- | x set.empty  := false
-- | x (set.add y tail) := x == y ∨ mem x tail

-- instance : has_mem number set := ⟨mem⟩

-- def le : number → number → Prop
-- | (number.mk Xl Xr) (number.mk Yl Yr) := ∀ xl ∈ Xl, ¬(le (number.mk Yl Yr) xl)
-- using_well_founded 
--   { rel_tac := λ _ _, 
--     `[exact ⟨_, measure_wf (λ t, number.sizeof t.1 + number.sizeof t.2)⟩] }

-- def valid : number → Prop
-- | (number.mk L R) := ∀ l ∈ L, ∀ r ∈ R, ¬(l ≥ r) ∧ (valid l) ∧ (valid r)

-- inductive number : Type
-- | zero : number
-- | left : number → number → number
-- | right : number → number → number

-- def valid : number → Prop
-- | number.zero := true
-- | (number.left n l) := false
-- | (number.right n r) := false


end surreal