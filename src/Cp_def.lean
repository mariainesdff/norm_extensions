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

def C_p := uniform_space.completion (Q_p_alg p) 

notation `ℂ_[`p`]` := C_p p

instance : field ℂ_[p] := uniform_space.completion.field

noncomputable! instance C_p.valued_field : valued (ℂ_[p]) ℝ≥0 := valued.valued_completion 

instance : has_coe_t (Q_p_alg p) ℂ_[p] := uniform_space.completion.has_coe_t _

lemma C_p.valuation_extends (x : Q_p_alg p) : valued.extension_valuation (x : ℂ_[p]) = valued.v x := 
begin
  --simp only [valued.extension_valuation],
  --change valued.extension (x : ℂ_[p]) = valued.v x,
  exact valued.extension_extends _,
end

example {p : ℕ} [fact p.prime] : ((p : Q_p_alg p) : ℂ_[p]) = (p : ℂ_[p]) :=
begin
  sorry--unfold_coes,
end


instance : is_rank_one (C_p.valued_field p).v := 
{ rank_le_one := sorry,
  nontrivial  := 
  begin
    use p,
    haveI hp : nat.prime p := _inst_1.elim,
    have hpv : valued.v (p : ℂ_[p]) = 1/(p : ℝ≥0),
    { have : ((p : Q_p_alg p) : ℂ_[p]) = (p : ℂ_[p]),
      { sorry },
      rw ← this,
      unfold valued.v, 
      rw C_p.valuation_extends,
      --simp, 
      --simp only [valued.extension_valuation],
      
      
      /- simp [monoid_with_zero_hom.has_coe_to_fun.coe_to_fun],
      simp [valued.extension_extends],
      set x := (p : Q_p_alg p) with hx,
      have : valued.extension (x : ℂ_[p]) = valued.v x,
      { rw valued.extension_extends}, -/
      --change valued.extension (p : ℂ_[p]) = 1 / (p : ℝ),
      sorry
    },
    simp only [hpv,one_div, ne.def, inv_eq_zero, nat.cast_eq_zero, inv_eq_one, nat.cast_eq_one],
    exact ⟨hp.ne_zero, hp.ne_one⟩,
  end }


instance : normed_field ℂ_[p] := valued_field.to_normed_field 
  (nat.one_div_cast_pos (nat.prime.pos _inst_1.elim))
  (nat.one_div_cast_lt_one (nat.prime.one_lt _inst_1.elim))

lemma C_p.is_nonarchimedean : is_nonarchimedean (λ (x : ℂ_[p]), ∥x∥₊) := sorry

def C_p_integers := metric.closed_ball (0 : ℂ_[p]) 1 --{x : ℂ_[p] // ∥x∥ ≤ 1}

notation `𝓞_ℂ_[`p`]` := C_p_integers p

instance : comm_monoid 𝓞_ℂ_[p] := metric.closed_ball.comm_monoid

--omit hp

lemma metric.mem_closed_ball_zero_add {α : Type*} [semi_normed_group α] {x y : α} {ε : ℝ}
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


lemma metric.mem_closed_ball_zero_neg {α : Type*} [semi_normed_group α] {x : α} {ε : ℝ}
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
