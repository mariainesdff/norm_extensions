import seminormed_rings
import ring_theory.adjoin.basic

open_locale nnreal

variables {R S : Type*} [field R] [field S] [algebra R S]

-- Lemma 3.1.5/2
lemma eq_of_pow_mult_faithful {g : R → ℝ≥0} (hg : is_mul_norm g) {f₁ : S → ℝ≥0}
  (hf₁_pm : is_pow_mult f₁) (hf₁_an : is_algebra_norm (hg.to_is_norm) f₁) {f₂ : S → ℝ≥0}
  (hf₂_pm : is_pow_mult f₁) (hf₂_an : is_algebra_norm (hg.to_is_norm) f₂)
  (h_eq : ∀ (y : S), ∃ (C₁ C₂ : ℝ≥0), ∀ (x : (algebra.adjoin R {y})), f₁ x.val = f₂ x.val) : 
  f₁ = f₂ := 
begin
  sorry
end