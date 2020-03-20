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
intro n,
intro H,
rw not_3_divides,

--I checked the case where n=1 by using
--a trichotomy, but the calc expressions still didn't
--like the division in the cases where n≠1. 

--I haven't been able to figure out
--mul_left_cancel_of_nonzero.

by_trichotomy(n,1),
    {intro H1,
    left,
    unfold divides,
    existsi(0:ℤ ),
    rw H1,
    refl},
    {intro H2,
    right,
    unfold divides,
    cases H with a b,
    existsi((a/(n-1))),
    symmetry,
    calc 3 * (a / (n - 1))
        = (3*a/(n-1)): by sorry...
        = (n*n-1)/(n-1): by rw b...
        = n+1: by sorry},
    {intro H3,
    right,
    unfold divides,
    cases H with c d,
    existsi((c/(n-1))),
    symmetry,
    calc 3 * (c / (n - 1))
        = (3*c/(n-1)): by sorry...
        = (n*n-1)/(n-1): by rw d...
        = n+1: by sorry},     
end

--Proof: Let n be an arbitrary integer. Assume
--that 3 divides n * n - 1, meaning that there
--exists some integer c for which n * n - 1 = 3c. 
--The goal is to prove that 3 does not divide n. 
--We consider 2 cases: 

--First, we consider the case that n=1. 
--3 does not divide 1. 

--Second, we consider the case that n≠1. By the 
--lemma, we know that 3 divides either n-1 or n or 
--n+1, but only one of these possibilities is true. 
--If we want to prove that 3 does not divide
--n, we must prove that either 3 divides n-1 or 
--3 divides n+1. Assume that 3 does not divide
--n-1. The goal is now to prove that 3 divides n+1,
--meaning that there exists some integer k for 
--which n + 1 = 3k. Consider k = c / (n - 1). 
--Then, 3k = 3c / (n - 1) = n * n - 1 / (n - 1)
-- = n + 1. 

--Both cases lead us to the conclusion that
--3 does not divide n. 

--So I'm realizing I can't prove that c/(n-1) is
--an integer, but Lean seems to be okay with it. 


--Below is my attempt to prove it using a P3 method
--(contrapositive)


theorem contrapositive : ∀ (n : ℤ), (3 ∣ n)  → ¬ (3 ∣ n * n - 1) :=
begin
intro n,
intro H,
unfold divides at H ⊢ ,
cases H with c Ha,
intro Hb,
cases Hb with k Hc,
--Now, by substituting 3c for n, we get 9c^2-1=3k,
--and k=3c^2-(1/3). Since 3c^2 is an integer, we 
--know that 3c^2-(1/3) is not an integer, and we
--have proven a contradiction. But this seems to 
--be showing that the contrapositive is false, 
--and the contrapositive should be true because
--it is logically equivalent to the initial 
--theorem. This makes me think I'm misusing
--or misinterpreting lean.
sorry
end