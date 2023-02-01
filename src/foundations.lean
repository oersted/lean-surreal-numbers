import tactic.suggest
import tactic.linarith
import init.meta.well_founded_tactics

namespace surreal

mutual inductive number, pocket
with number : Type
| mk : pocket → pocket → number
with pocket : Type
| empty : pocket
| add : pocket → number → pocket

def pocket.set : pocket → set number
| (pocket.empty)   := ∅
| (pocket.add P n) := P.set ∪ {n}

def number.left : number → set number
| (number.mk L R) := L.set

def number.right : number → set number
| (number.mk L R) := L.set

mutual def number.size, pocket.size
with number.size : number → ℕ
| (number.mk L R)  := L.size + R.size
with pocket.size : pocket → ℕ
| (pocket.empty)   := 0
| (pocket.add P n) := P.size + n.size + 1

def number.le : number → number → Prop
| (number.mk pocket.empty pocket.empty) (number.mk pocket.empty pocket.empty) := true
| (number.mk (pocket.add Xl xl) Xr) y := 
    have y.size + xl.size < (number.mk (Xl.add xl) Xr).size + y.size, from 
      begin simp [number.size, pocket.size], linarith end,
    have (number.mk Xl Xr).size < (number.mk (Xl.add xl) Xr).size, from
      begin simp [number.size, pocket.size], linarith end,
  ¬(y.le xl) ∧ ((number.mk Xl Xr).le y)
| (number.mk Xl (pocket.add Xr xr)) y := 
    have (number.mk Xl Xr).size < (number.mk Xl (Xr.add xr)).size, from
      begin simp [number.size, pocket.size], linarith end,
  ((number.mk Xl Xr).le y)
| x (number.mk (pocket.add Yl yl) Yr) := 
    have (number.mk Yl Yr).size < (number.mk (Yl.add yl) Yr).size, from
      begin simp [number.size, pocket.size], linarith end,
  (x.le (number.mk Yl Yr))
| x (number.mk Yl (pocket.add Yr yr)) := 
    have yr.size + x.size < x.size + (number.mk Yl (Yr.add yr)).size, from
      begin simp [number.size, pocket.size], linarith end,
    have (number.mk Yl Yr).size < (number.mk Yl (Yr.add yr)).size, from
      begin simp [number.size, pocket.size], linarith end,
  ¬(yr.le x) ∧ (x.le (number.mk Yl Yr))
using_well_founded {
  dec_tac := `[try {well_founded_tactics.default_dec_tac}, try {assumption}],
  rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ s, s.1.size + s.2.size)⟩]}

instance : has_le number := ⟨number.le⟩

def number.surreal : number → Prop
| n := ∀l ∈ n.left, ∀r ∈ n.right, ¬(l ≥ r)

end surreal