inductive surreal : ∀ (n: ℕ), Type
| zero : surreal 0
| node 
  (day left_day right_day : ℕ)
  (left_before: left_day < day)
  (right_before: right_day < day)
  (left: surreal left_day)
  (right: surreal right_day)
: surreal day


inductive le : ∀ (x_day y_day : ℕ) (x: surreal x_day) (y: surreal y_day), Prop
| zero (y_day : ℕ) (y : surreal y_day) : le 0 y_day surreal.zero y
| node 
  (x_day y_day x_left_day x_right_day y_left_day y_right_day : ℕ)
  (x_left : surreal x_left_day) (x_right : surreal x_right_day) 
  (y_left : surreal y_left_day) (y_right : surreal y_right_day) 
  (x_left_le_x_right : le x_left_day x_right_day x_left x_right) 
  (y_left_le_y_right : le y_left_day y_right_day y_left y_right) : 
    (∀ xl : surreal x_left_day, le x_left_day y_right_day xl y_right → le x_left_day y_right_day xl y_right) → 
    (∀ yr : surreal y_right_day, le x_right_day y_right_day x_right yr → le y_left_day y_right_day y_left yr) → 
    le x_day y_day (surreal.node x_day x_left_day x_right_day (nat.sub_lt_succ x_day x_left_day) (nat.sub_lt_succ x_day x_right_day) x_left x_right) (surreal.node y_day y_left_day y_right_day (nat.sub_lt_succ y_day y_left_day) (nat.sub_lt_succ y_day y_right_day) y_left y_right)


