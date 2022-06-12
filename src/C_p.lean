import field_theory.is_alg_closed.algebraic_closure
import number_theory.padics.padic_numbers
import topology.metric_space.cau_seq_filter
import spectral_norm

noncomputable theory

variables (p : ℕ)  [fact p.prime]

@[reducible] def Q_p_alg : Type* := algebraic_closure ℚ_[p]

lemma Q_p_alg.is_algebraic : algebra.is_algebraic ℚ_[p] (Q_p_alg p) := 
algebraic_closure.is_algebraic _

instance Q_p_alg.normed_field : normed_field (Q_p_alg p) := 
spectral_norm.normed_field (Q_p_alg.is_algebraic p)

instance Q_p_alg.abv : is_absolute_value (Q_p_alg.normed_field p).norm :=
normed_field.is_absolute_value

def C_p :=  @cau_seq.completion.Cauchy _ _ _ _ _ (Q_p_alg.abv p) _

noncomputable! instance Q_p_alg.valued_field : valued (Q_p_alg p) nnreal := 
sorry