import field_theory.is_alg_closed.algebraic_closure
import number_theory.padics.padic_numbers
import spectral_norm

noncomputable theory

variables (p : ℕ)  [fact p.prime]

@[reducible] def Q_p_alg : Type* := algebraic_closure ℚ_[p]

instance : field (Q_p_alg p) := algebraic_closure.field _

noncomputable! instance : algebra ℚ_[p] (Q_p_alg p) := by apply_instance

lemma Q_p_alg.is_algebraic : algebra.is_algebraic ℚ_[p] (Q_p_alg p) := 
algebraic_closure.is_algebraic _


instance : normed_field (Q_p_alg p) := spectral_norm.normed_field

