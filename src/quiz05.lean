-- Math 52: Quiz 5
-- Open this file in a folder that contains 'utils'.

import utils
open classical

definition divides (a b : ℤ) : Prop := ∃ (k : ℤ), b = a * k
local infix ∣ := divides

axiom not_3_divides : ∀ (m : ℤ), ¬ (3 ∣ m) ↔ 3 ∣ m - 1 ∨ 3 ∣ m + 1

lemma not_3_divides_of_3_divides_minus_1 : 
∀ (m : ℤ), 3 ∣ m - 1 → ¬ (3 ∣ m) :=
begin
intros m H,
rw not_3_divides,
left,
assumption, 
end

lemma not_3_divides_of_3_divides_plus_1 : 
∀ (m : ℤ), 3 ∣ m + 1 → ¬ (3 ∣ m) :=
begin
intros m H,
rw not_3_divides,
right,
assumption, 
end

theorem main : ∀ (n : ℤ), 3 ∣ n * n - 1 → ¬ (3 ∣ n) :=
begin
sorry
end
