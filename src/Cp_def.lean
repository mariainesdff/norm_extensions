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

def C_p :=  @cau_seq.completion.Cauchy ℝ _ (Q_p_alg p) _ _ (Q_p_alg.abv p)

notation `ℂ_[`p`]` := C_p p
instance : field ℂ_[p] := sorry

instance : has_norm ℂ_[p] := sorry

def C_p_integers := {x : ℂ_[p] // ∥x∥ ≤ 1}

notation `𝓞_ℂ_[`p`]` := C_p_integers p

instance : comm_ring 𝓞_ℂ_[p] := sorry

/- noncomputable! instance Q_p_alg.valued_field : valued (Q_p_alg p) nnreal := 
sorry -/
