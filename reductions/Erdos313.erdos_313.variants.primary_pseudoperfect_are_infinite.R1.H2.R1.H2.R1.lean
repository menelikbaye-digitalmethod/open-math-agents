import OMAReductions.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1_H2_R1
import Mathlib

-- Reduction of the remaining Erdős 313 step.
-- Credit: @menelikbaye-digitalmethod

namespace OMA.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1_H2_R1_H2_R1

private theorem primeSuccessor : Nat.Prime 5998279018951962403 := by
  apply lucas_primality _ 3 (by simp only [Nat.reduceSub]; reduce_mod_char)
  intro q hq hd
  rw [show 5998279018951962403 - 1 = 2 * (3 * (11 * (17 * (101 * (157 * (1979 * (10093 * (16879)))))))) by decide] at hd
  simp only [hq.dvd_mul] at hd
  rcases hd with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2)).mp h0
    subst q
    simp only [Nat.reduceSub, Nat.reduceDiv]
    reduce_mod_char
    decide
  · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3)).mp h1
    subst q
    simp only [Nat.reduceSub, Nat.reduceDiv]
    reduce_mod_char
    decide
  · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 11)).mp h2
    subst q
    simp only [Nat.reduceSub, Nat.reduceDiv]
    reduce_mod_char
    decide
  · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 17)).mp h3
    subst q
    simp only [Nat.reduceSub, Nat.reduceDiv]
    reduce_mod_char
    decide
  · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 101)).mp h4
    subst q
    simp only [Nat.reduceSub, Nat.reduceDiv]
    reduce_mod_char
    decide
  · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 157)).mp h5
    subst q
    simp only [Nat.reduceSub, Nat.reduceDiv]
    reduce_mod_char
    decide
  · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 1979)).mp h6
    subst q
    simp only [Nat.reduceSub, Nat.reduceDiv]
    reduce_mod_char
    decide
  · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 10093)).mp h7
    subst q
    simp only [Nat.reduceSub, Nat.reduceDiv]
    reduce_mod_char
    decide
  · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 16879)).mp h8
    subst q
    simp only [Nat.reduceSub, Nat.reduceDiv]
    reduce_mod_char
    decide

def H1 : Prop :=
  ∃ P : Finset ℕ, 10 ≤ P.card ∧ P.Nonempty ∧
    (∀ p ∈ P, p.Prime) ∧
    (∀ p ∈ P, p ∣ (∏ q ∈ P.erase p, q) + 1) ∧
    (∑ p ∈ P, (1 : ℚ) / p) < 1

def H2 : Prop :=
  ∀ k : ℕ, 11 ≤ k → ∃ P : Finset ℕ, k ≤ P.card ∧ P.Nonempty ∧
    (∀ p ∈ P, p.Prime) ∧
    (∀ p ∈ P, p ∣ (∏ q ∈ P.erase p, q) + 1) ∧
    (∑ p ∈ P, (1 : ℚ) / p) < 1

/-- Han Wang's ten-prime example from arXiv:2605.21518. -/
theorem ten_prime_case : H1 := by
  let small : Finset ℕ := {2, 3, 11, 17, 101, 157, 1979, 10093, 16879}
  let P : Finset ℕ := insert 5998279018951962403 small
  refine ⟨P, by decide, by decide, ?_, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | h
    · exact primeSuccessor
    · simp only [small, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · decide +kernel
  · decide +kernel

theorem main : H1 → H2 → OMA.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1_H2_R1.H2 := by
  intro hfinite htail k hk
  by_cases h : 11 ≤ k
  · exact htail k h
  obtain ⟨P, hc, hP⟩ := hfinite
  exact ⟨P, (show k ≤ 10 by omega).trans hc, hP⟩

end OMA.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1_H2_R1_H2_R1
