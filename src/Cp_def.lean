import analysis.normed.field.unit_ball
import field_theory.is_alg_closed.algebraic_closure
import number_theory.padics.padic_numbers
import topology.metric_space.cau_seq_filter
import topology.algebra.valued_field
import spectral_norm
import normed_valued

noncomputable theory

open_locale nnreal

lemma nat.one_div_cast_lt_one {n : ℕ} (hn : 1 < n) :  1/(n : ℝ) < 1 := 
begin
  rw [one_div, ← inv_one,
    inv_lt_inv (nat.cast_pos.mpr (lt_trans zero_lt_one hn)) zero_lt_one],
  exact nat.one_lt_cast.mpr hn,
  apply_instance, apply_instance,
end

variables (p : ℕ) [fact p.prime]
--include hp

@[reducible] def Q_p_alg : Type* := algebraic_closure ℚ_[p]

lemma Q_p_alg.is_algebraic : algebra.is_algebraic ℚ_[p] (Q_p_alg p) := 
algebraic_closure.is_algebraic _

instance : has_coe ℚ_[p] (Q_p_alg p) := ⟨algebra_map ℚ_[p] (Q_p_alg p)⟩

protected lemma coe_eq : (coe : ℚ_[p] → (Q_p_alg p)) = algebra_map ℚ_[p] (Q_p_alg p) := rfl

lemma padic.is_nonarchimedean : is_nonarchimedean (λ (k : ℚ_[p]), ∥k∥₊) :=
begin
  intros x y,
  simp only [← nnreal.coe_le_coe, nnreal.coe_max, coe_nnnorm],
  rw sub_eq_add_neg,
  convert padic_norm_e.nonarchimedean x (-y) using 2,
  rw norm_neg,
end

instance Q_p_alg.normed_field : normed_field (Q_p_alg p) := 
spectral_norm.normed_field (Q_p_alg.is_algebraic p) (padic.is_nonarchimedean p)

/- instance Q_p_alg.abv : is_absolute_value (Q_p_alg.normed_field p).norm :=
normed_field.is_absolute_value

def C_p :=  @cau_seq.completion.Cauchy _ _ (Q_p_alg p) _ _ (normed_field.is_absolute_value) -/

/- lemma Q_p_alg.is_nonarchimedean : is_nonarchimedean (spectral_norm (Q_p_alg.is_algebraic p)) :=
spectral_norm.is_nonarchimedean (Q_p_alg.is_algebraic p) (padic.is_nonarchimedean p) -/

lemma Q_p_alg.is_nonarchimedean : is_nonarchimedean (nnnorm : (Q_p_alg p) → ℝ≥0) :=
begin
  convert spectral_norm.is_nonarchimedean (Q_p_alg.is_algebraic p) (padic.is_nonarchimedean p),
  ext x,
  rw [coe_nnnorm], refl,
end

noncomputable! instance Q_p_alg.valued_field : valued (Q_p_alg p) ℝ≥0 :=
normed_field.to_valued (Q_p_alg p) (Q_p_alg.is_nonarchimedean p)

lemma Q_p_alg.v_def (x : Q_p_alg p) : 
  valued.v x = spectral_norm (Q_p_alg.is_algebraic p) x :=
by { ext, refl }

--lemma Q_p_alg.v_ext (x : ℚ_[p]) : valued.v (x : Q_p_alg p) = ∥ (x : Q_p_alg p)  ∥₊ := rfl

def C_p := uniform_space.completion (Q_p_alg p) 

notation `ℂ_[`p`]` := C_p p

instance : field ℂ_[p] := uniform_space.completion.field

noncomputable! instance C_p.valued_field : valued (ℂ_[p]) ℝ≥0 := valued.valued_completion 

instance : has_coe_t (Q_p_alg p) ℂ_[p] := uniform_space.completion.has_coe_t _

lemma C_p.valuation_extends (x : Q_p_alg p) : valued.v (x : ℂ_[p]) = valued.v x := 
valued.extension_extends _

instance : algebra (Q_p_alg p) ℂ_[p] := 
uniform_space.completion.algebra' _

example {p : ℕ} [fact p.prime] : ((p : ℚ_[p]) : Q_p_alg p) = (p : Q_p_alg p) :=
by rw [coe_eq, map_nat_cast]

protected lemma C_p.coe_eq : (coe : (Q_p_alg p) → ℂ_[p]) = algebra_map (Q_p_alg p) ℂ_[p] := rfl

protected lemma C_p.coe_zero : ((0 : Q_p_alg p) : ℂ_[p]) = 0 := rfl


example {p : ℕ} [fact p.prime] : ((p : Q_p_alg p) : ℂ_[p]) = (p : ℂ_[p]) :=
by rw [C_p.coe_eq, map_nat_cast]

lemma Q_p_alg.valuation_p (p : ℕ) [fact p.prime] : valued.v (p : Q_p_alg p) = 1/(p : ℝ≥0) :=
begin
  have hp : (p : Q_p_alg p) = ((p : ℚ_[p]) : Q_p_alg p),
  { rw [coe_eq, map_nat_cast] },
  ext,
  rw [Q_p_alg.v_def, hp, coe_eq, spectral_norm.extends, coe_nnnorm, padic_norm_e.norm_p, one_div, 
    nonneg.coe_inv, nnreal.coe_nat_cast],
end

instance : is_rank_one (C_p.valued_field p).v := 
{ rank_le_one := sorry,
  nontrivial  := 
  begin
    use p,
    haveI hp : nat.prime p := _inst_1.elim,
    have hpv : valued.v (p : ℂ_[p]) = 1/(p : ℝ≥0),
    { have : ((p : Q_p_alg p) : ℂ_[p]) = (p : ℂ_[p]),
      { rw [C_p.coe_eq, map_nat_cast] },
      rw ← this,
      rw C_p.valuation_extends,
      exact Q_p_alg.valuation_p p, },
    simp only [hpv,one_div, ne.def, inv_eq_zero, nat.cast_eq_zero, inv_eq_one, nat.cast_eq_one],
    exact ⟨hp.ne_zero, hp.ne_one⟩,
  end }

instance : normed_field ℂ_[p] := valued_field.to_normed_field 
  (nat.one_div_cast_pos (nat.prime.pos _inst_1.elim))
  (nat.one_div_cast_lt_one (nat.prime.one_lt _inst_1.elim))

lemma C_p.norm_def :
 (norm : ℂ_[p] → ℝ )= norm_def (nat.one_div_cast_pos (nat.prime.pos _inst_1.elim)) := rfl

lemma C_p.nnnorm_extends (x : Q_p_alg p) : ∥ (x : ℂ_[p]) ∥₊ = ∥ x ∥₊ := 
begin
  ext,
  rw coe_nnnorm, rw coe_nnnorm,
  by_cases hx : x = 0,
  { rw [hx, C_p.coe_zero, norm_zero, norm_zero],},
  { simp only [C_p.norm_def, norm_def, C_p.valuation_extends,
      mult_with_top_R_to_R_monoid_with_zero_hom, monoid_with_zero_hom.coe_mk, mult_with_top_R_to_R],
    rw dif_neg,
    { sorry }, --TODO: is choice of base necessary??
    { sorry }}
end

#exit

lemma C_p.is_nonarchimedean : is_nonarchimedean (λ (x : ℂ_[p]), ∥x∥₊) :=
begin
  intros x y,
  apply uniform_space.completion.induction_on₂ x y,
  { apply is_closed_le,
    { apply continuous.comp _ continuous_sub,
      --exact @continuous_nnnorm ℂ_[p] _, TODO: fix diamond
      sorry, },
    { apply continuous.max,
      apply continuous.comp _ (continuous.fst continuous_id),
      { sorry },
      apply continuous.comp _ (continuous.snd continuous_id),
      { sorry }}},
  { intros a b,
    simp only [← uniform_space.completion.coe_sub, C_p.nnnorm_extends],
    exact Q_p_alg.is_nonarchimedean p a b, },
end

def C_p_integers := metric.closed_ball (0 : ℂ_[p]) 1 --{x : ℂ_[p] // ∥x∥ ≤ 1}

notation `𝓞_ℂ_[`p`]` := C_p_integers p

instance : comm_monoid 𝓞_ℂ_[p] := metric.closed_ball.comm_monoid

--omit hp

lemma metric.mem_closed_ball_zero_add {α : Type*} [seminormed_add_comm_group α] {x y : α} {ε : ℝ}
  (hx : x ∈ metric.closed_ball (0 : α) ε) (hy : y ∈ metric.closed_ball (0 : α) ε)
  (h_na : is_nonarchimedean (λ x : α, ∥x∥₊)) :
  x + y ∈ metric.closed_ball (0 : α) ε := 
begin
  rw [mem_closed_ball_zero_iff, ← coe_nnnorm] at *,
  have h := is_nonarchimedean.add_le (nnnorm_zero) 
h_na x y, 
  simp only [← nnreal.coe_le_coe] at h,
  apply le_trans h,
  rw [nnreal.coe_max, max_le_iff],
  exact ⟨hx, hy⟩
end


lemma metric.mem_closed_ball_zero_neg {α : Type*} [seminormed_add_comm_group α] {x : α} {ε : ℝ}
  (hx : x ∈ metric.closed_ball (0 : α) ε) : - x ∈ metric.closed_ball (0 : α) ε := 
by { rw [mem_closed_ball_zero_iff, norm_neg, ← mem_closed_ball_zero_iff], exact hx }

def subring.unit_closed_ball (𝕜 : Type*) [semi_normed_ring 𝕜] [norm_one_class 𝕜] 
  (h_na : is_nonarchimedean (λ x : 𝕜, ∥x∥₊)) : subring 𝕜 := 
{ carrier   := metric.closed_ball (0 : 𝕜) 1,
  add_mem'  := λ x y hx hy, metric.mem_closed_ball_zero_add hx hy h_na,
  zero_mem' := metric.mem_closed_ball_self zero_le_one,
  neg_mem'  := λ x hx, metric.mem_closed_ball_zero_neg hx,
  .. submonoid.unit_closed_ball  𝕜 }

--include hp
instance : comm_ring 𝓞_ℂ_[p] :=
subring_class.to_comm_ring (subring.unit_closed_ball ℂ_[p] (C_p.is_nonarchimedean p))
