-- Theorem 1.1.1
-- There is no rational number whose square is 2.

-- Still in progress --

def even (n : Nat) : Prop := ∃ k : Nat, n = 2 * k

theorem not_even_and_coprime (a b : Nat) (h₁ : even a) (h₂ : even b) : False := 
  match h₁, h₂ with
  | ⟨k1, hk1⟩ , ⟨k2, hk2⟩ =>
    False.elim (by
      admit)


theorem sqrt2_irratioanl : ¬ ∃ a b : Nat, b != 0 ∧ Nat.gcd a b = 1 ∧ a^2 = 2 * b^2 := by
    intro h
    obtain ⟨a, b, b_ne_zero, gcd_ab, eq⟩ := h

    have even_a : even a := by 
      have hsq_even : even (a^2) := ⟨b^2, eq⟩
        by_contra a_not_even
        admit
 
    obtain ⟨k, a_eq⟩ := even_a

    have eq2 : (2*b^2) = (2*2*(k^2)) := by
      rw [a_eq]
      simp [Nat.pow]
      rw [←eq]

    have even_b : even b :=
      by 
        admit

    exact not_even_and_coprime a b even_a even_b
