--import data.real.nnreal
import ring_theory.valuation.basic
import number_theory.padics.padic_numbers
import analysis.special_functions.pow
import with_top

noncomputable theory

open function multiplicative

variables {R : Type*} [ring R] {Γ₀ : Type*} [linear_ordered_comm_group_with_zero Γ₀]

class is_rank_one (v : valuation R Γ₀) : Prop :=
(rank_le_one : ∃ f : Γ₀ →* multiplicative (order_dual (with_top ℝ)), strict_mono f) --(rank_le_one : ∃ f : Γ₀ →* nnreal, strict_mono f)
(nontrivial : ∃ r : R, v r ≠ 0 ∧ v r ≠ 1)

def is_rank_one_hom (v : valuation R Γ₀) [hv : is_rank_one v] :
  Γ₀ →* multiplicative (order_dual (with_top ℝ)) :=
classical.some hv.rank_le_one

lemma is_rank_one_strict_mono (v : valuation R Γ₀) [hv : is_rank_one v] :
  strict_mono (is_rank_one_hom v) :=
classical.some_spec hv.rank_le_one

structure is_discrete (v : valuation R Γ₀) : Prop :=
(rank_le_one : ∃ f : Γ₀ →* with_zero (multiplicative ℤ), strict_mono f)
(nontrivial : ∃ r : R, v r ≠ 0 ∧ v r ≠ 1)

variables {G H : Type*} [group G] [group H] (f : G →* H) [decidable_eq (with_zero G)]

def with_zero.some {x : with_zero G} (hx : x ≠ 0) : G :=
classical.some (with_zero.ne_zero_iff_exists.mp hx)

def with_zero.some_spec {x : with_zero G} (hx : x ≠ 0) : ↑(with_zero.some hx) = x :=
classical.some_spec (with_zero.ne_zero_iff_exists.mp hx)

@[simp] lemma with_zero.some_coe {g : G} : with_zero.some (@with_zero.coe_ne_zero G g) = g :=
with_zero.coe_inj.mp
  (classical.some_spec (with_zero.ne_zero_iff_exists.mp (@with_zero.coe_ne_zero G g)))

def with_zero.some_mul {x y : with_zero G} (hxy : x * y ≠ 0) :
  with_zero.some hxy = with_zero.some (left_ne_zero_of_mul hxy) *
    with_zero.some (right_ne_zero_of_mul hxy) :=
by rw [← with_zero.coe_inj, with_zero.coe_mul, with_zero.some_spec, with_zero.some_spec,
  with_zero.some_spec]

def with_zero.coe_monoid_hom : with_zero G →* with_zero H := 
{ to_fun := λ x, if hx : x = 0 then 0 else f (with_zero.some hx),
  map_one' := 
  begin
    have h1 : (1 : with_zero G) ≠ 0 := one_ne_zero,
    have h := (classical.some_spec (with_zero.ne_zero_iff_exists.mp h1)),
    rw dif_neg h1,
    simp_rw ← with_zero.coe_one at h ⊢,
    rw [with_zero.coe_inj, with_zero.some_coe, f.map_one],
  end,
  map_mul' := λ x y,
  begin
    by_cases hxy : x * y = 0,
    { rw dif_pos hxy,
      cases zero_eq_mul.mp (eq.symm hxy) with hx hy,
      { rw [dif_pos hx, zero_mul] },
      { rw [dif_pos hy, mul_zero] }},
    { rw [dif_neg hxy, dif_neg (left_ne_zero_of_mul hxy),
        dif_neg (right_ne_zero_of_mul hxy), ← with_zero.coe_mul,
        with_zero.coe_inj, ← f.map_mul, with_zero.some_mul hxy] }
  end }

instance : linear_ordered_comm_monoid_with_zero nnreal := infer_instance
open_locale classical

def val_p (p : ℕ) [fact p.prime] : valuation ℚ_[p] (multiplicative (order_dual (with_top ℤ))) :=
padic.add_valuation.valuation

--variables (Γ : Type*) [linear_ordered_add_comm_monoid_with_top Γ]

--instance : linear_ordered_comm_monoid_with_zero nnreal := infer_instance
def int.mulcast_hom_R :
  multiplicative (order_dual (with_top ℤ)) →* multiplicative (order_dual (with_top ℝ)) := 
mulcast (int.cast_add_hom ℝ)

lemma int.cast_add_strict_mono : strict_mono (int.cast_add_hom ℝ) := λ x y hxy,
by { rw [int.coe_cast_add_hom, int.cast_lt], exact hxy }

lemma bar {p : ℕ} [hp : fact p.prime] : is_rank_one (val_p p) :=
{ rank_le_one := 
  begin
    use int.mulcast_hom_R,
    intros x y hxy,
    exact (mulcast_lt_mulcast int.cast_add_strict_mono x y).mpr hxy,
  end,
  nontrivial := 
  begin
    use p,
    rw [valuation.ne_zero_iff, nat.cast_ne_zero, val_p, padic.add_valuation.valuation_apply,
      ne.def, ne.def, of_add_eq_one, padic.add_valuation.apply
      ((@nat.cast_ne_zero ℚ_[p] _ _ _ _).mpr (nat.prime.ne_zero hp.elim)), padic.valuation_p],
    exact ⟨nat.prime.ne_zero hp.elim, one_ne_zero⟩,
  end }

-- Requires choice
/- def mult_with_top_R_to_nnreal {e : nnreal} (he : 0 ≠ e) :
  multiplicative (order_dual (with_top ℝ)) → nnreal := λ x,
begin
  let y : order_dual (with_top ℝ) := to_add x,
  by_cases hy : y = ⊥,
  { exact 0 },
  { exact e^(classical.some (with_bot.ne_bot_iff_exists.mp hy)) }
end -/

lemma ne_dual_top_iff_exists {α : Type*} {x : order_dual (with_top α)} :
  order_dual.of_dual x ≠ ⊤ ↔ ∃ (a : α), ↑a = order_dual.of_dual x :=
option.ne_none_iff_exists

def mult_with_top_R_to_nnreal {e : nnreal} (he : 0 ≠ e) :
  multiplicative (order_dual (with_top ℝ)) → nnreal := λ x,
begin
  let y : order_dual (with_top ℝ) := to_add x,
  by_cases hy : order_dual.of_dual y = ⊤,
  { exact 0 },
  { exact e^(classical.some (ne_dual_top_iff_exists.mp hy)) }
end

/- def mult_with_top_R_to_nnreal (e : nnreal) :
  multiplicative (order_dual (with_top ℝ)) → nnreal := λ x,
begin
  let y : order_dual (with_top ℝ) := to_add x,
  by_cases hy : y = none,
  { exact 0 },
  { rw [← ne.def, with_bot.none_eq_bot, with_bot.ne_bot_iff_exists] at hy,
    exact e^(classical.some hy) }
end -/

/- lemma foo (e : nnreal) (r : ℝ) (hr : r ≠ 0) :
  mult_with_top_R_to_nnreal e (r : order_dual (with_top ℝ)) = r :=
sorry -/

/- lemma foo (e : nnreal) (r : order_dual (with_top ℝ)) (hr : r ≠ ⊥) :
  classical.some_spec (with_bot.ne_bot_iff_exists.mp hr)  :=
begin
  have r := classical.some (with_bot.ne_bot_iff_exists.mp hr),
  have h := classical.some_spec (with_bot.ne_bot_iff_exists.mp hr),
  /- rw ← with_top.coe_eq_coe,
  exact classical.some_spec (with_bot.ne_bot_iff_exists.mp (with_bot.coe_ne_bot r)), -/
end -/

/- lemma mult_with_top_apply (r : ℝ) :
 classical.some (with_bot.ne_bot_iff_exists.mp (with_bot.coe_ne_bot r)) = r :=
begin
  rw ← with_bot.coe_eq_coe,
  exact classical.some_spec (with_bot.ne_bot_iff_exists.mp (with_bot.coe_ne_bot r)),
end 

lemma mult_with_top_apply (r : ℝ) :
 classical.some (with_top.ne_top_iff_exists.mp (@with_top.coe_ne_top ℝ r)) = r :=
begin
  rw ← with_bot.coe_eq_coe,
  exact classical.some_spec (with_top.ne_top_iff_exists.mp (@with_top.coe_ne_top ℝ r)),
end-/

lemma mult_with_top_apply (r : ℝ) :
 classical.some (ne_dual_top_iff_exists.mp (@with_top.coe_ne_top ℝ r)) = r :=
begin
  rw ← with_bot.coe_eq_coe,
  let s := (order_dual.of_dual (some r) : with_top ℝ),
  exact classical.some_spec (with_top.ne_top_iff_exists.mp (@with_top.coe_ne_top ℝ r)),
end

lemma with_top.of_dual_eq_top_iff {α : Type*} {x : order_dual (with_top α)} :
  order_dual.of_dual x = ⊤ ↔ x = ⊥ := iff.rfl

lemma mult_with_top_R_to_nnreal_strict_mono {e : nnreal} (he0 : 0 < e) (he1 : e < 1) :
  strict_mono (mult_with_top_R_to_nnreal (ne_of_lt he0)) :=
begin
  intros x y hxy,
  simp only [mult_with_top_R_to_nnreal],
  by_cases hy  : order_dual.of_dual (y.to_add) = ⊤,
    { have hxy' : x.to_add < y .to_add := hxy,
      have hy' : y.to_add = ⊥ := hy,
      simp only [hy', not_lt_bot] at hxy',
      exfalso,
      exact hxy' },
    { by_cases hx : order_dual.of_dual (x.to_add) = ⊤,
      { rw [dif_neg hy, dif_pos hx],
        exact nnreal.rpow_pos he0, },
      { have hxy' : x.to_add < y .to_add := hxy,
        rw [dif_neg hx, dif_neg hy],
        apply nnreal.rpow_lt_rpow_of_exponent_gt he0 he1,
        have hx' := classical.some_spec (with_bot.ne_bot_iff_exists.mp hx),
        rw [← with_top.coe_lt_coe,
          classical.some_spec (with_bot.ne_bot_iff_exists.mp hx),
          classical.some_spec (with_bot.ne_bot_iff_exists.mp hy)], 
        exact hxy }}, 
end

def mult_with_top_R_to_nnreal_monoid_hom {e : nnreal} (he : 0 ≠ e) :
  multiplicative (order_dual (with_top ℝ)) →* nnreal :=
{ to_fun   := mult_with_top_R_to_nnreal he,
  map_one' := begin
    simp only [mult_with_top_R_to_nnreal, to_add_one],
    erw [dif_neg with_bot.coe_ne_bot, mult_with_top_apply (0 : ℝ)],
    exact nnreal.rpow_zero e,
  end,
  map_mul' := λ x y,
  begin
    simp only [mult_with_top_R_to_nnreal],
    by_cases  hx : order_dual.of_dual (x.to_add) = ⊤,
    { have hxy : order_dual.of_dual ((x * y).to_add) = ⊤,
      { rw [with_top.of_dual_eq_top_iff, to_add_mul, with_top.of_dual_eq_top_iff.mp hx,
          with_bot.bot_add] },
      rw [dif_pos hx, dif_pos hxy, zero_mul] },
    { by_cases hy : order_dual.of_dual (y.to_add) = ⊤,
      { have hxy : order_dual.of_dual ((x * y).to_add) = ⊤,
      { rw [with_top.of_dual_eq_top_iff, to_add_mul, with_top.of_dual_eq_top_iff.mp hy,
          with_bot.add_bot] },
        rw [dif_pos hy, dif_pos hxy, mul_zero] },
      { have hxy : order_dual.of_dual ((x * y).to_add) ≠ ⊤,
        { rw [ne.def, with_top.of_dual_eq_top_iff, to_add_mul, with_bot.add_eq_bot],
          exact not_or hx hy, },
        rw [dif_neg hx, dif_neg hy, dif_neg hxy, ← nnreal.rpow_add (ne.symm he)],
        apply congr_arg,
        rw [← with_bot.coe_eq_coe, with_bot.coe_add],
        rw [classical.some_spec (with_bot.ne_bot_iff_exists.mp hx),
          classical.some_spec (with_bot.ne_bot_iff_exists.mp hy),
          classical.some_spec (with_bot.ne_bot_iff_exists.mp hxy), to_add_mul],
        refl,
        }},   
  end, }

def mult_with_top_R_to_R {e : ℝ} (he : 0 ≠ e) :
  multiplicative (order_dual (with_top ℝ)) → ℝ := λ x,
begin
  let y : order_dual (with_top ℝ) := to_add x,
  by_cases hy : order_dual.of_dual y = ⊤,
  { exact 0 },
  { exact e^(classical.some (ne_dual_top_iff_exists.mp hy)) }
end

lemma mult_with_top_apply' (r : ℝ) :
 classical.some (ne_dual_top_iff_exists.mp (@with_top.coe_ne_top ℝ r)) = r :=
begin
  rw ← with_bot.coe_eq_coe,
  let s := (order_dual.of_dual (some r) : with_top ℝ),
  exact classical.some_spec (with_top.ne_top_iff_exists.mp (@with_top.coe_ne_top ℝ r)),
end


lemma mult_with_top_R_to_R_strict_mono {e : ℝ} (he0 : 0 < e) (he1 : e < 1) :
  strict_mono (mult_with_top_R_to_R (ne_of_lt he0)) :=
begin
  intros x y hxy,
  simp only [mult_with_top_R_to_R],
  by_cases hy  : order_dual.of_dual (y.to_add) = ⊤,
    { have hxy' : x.to_add < y .to_add := hxy,
      have hy' : y.to_add = ⊥ := hy,
      simp only [hy', not_lt_bot] at hxy',
      exfalso,
      exact hxy' },
    { by_cases hx : order_dual.of_dual (x.to_add) = ⊤,
      { rw [dif_neg hy, dif_pos hx],
        exact real.rpow_pos_of_pos he0 _, },
      { have hxy' : x.to_add < y .to_add := hxy,
        rw [dif_neg hx, dif_neg hy],
        apply real.rpow_lt_rpow_of_exponent_gt he0 he1,
        have hx' := classical.some_spec (with_bot.ne_bot_iff_exists.mp hx),
        rw [← with_top.coe_lt_coe,
          classical.some_spec (with_bot.ne_bot_iff_exists.mp hx),
          classical.some_spec (with_bot.ne_bot_iff_exists.mp hy)], 
        exact hxy, }}, 
end

def mult_with_top_R_to_R_monoid_hom {e : ℝ} (he : 0 < e) :
  multiplicative (order_dual (with_top ℝ)) →* ℝ :=
{ to_fun   := mult_with_top_R_to_R (ne_of_lt he),
  map_one' := begin
    simp only [mult_with_top_R_to_R, to_add_one],
    erw [dif_neg with_bot.coe_ne_bot, mult_with_top_apply (0 : ℝ)],
    exact real.rpow_zero e,
  end,
  map_mul' := λ x y,
  begin
    simp only [mult_with_top_R_to_R],
    by_cases  hx : order_dual.of_dual (x.to_add) = ⊤,
    { have hxy : order_dual.of_dual ((x * y).to_add) = ⊤,
      { rw [with_top.of_dual_eq_top_iff, to_add_mul, with_top.of_dual_eq_top_iff.mp hx,
          with_bot.bot_add] },
      rw [dif_pos hx, dif_pos hxy, zero_mul] },
    { by_cases hy : order_dual.of_dual (y.to_add) = ⊤,
      { have hxy : order_dual.of_dual ((x * y).to_add) = ⊤,
      { rw [with_top.of_dual_eq_top_iff, to_add_mul, with_top.of_dual_eq_top_iff.mp hy,
          with_bot.add_bot] },
        rw [dif_pos hy, dif_pos hxy, mul_zero] },
      { have hxy : order_dual.of_dual ((x * y).to_add) ≠ ⊤,
        { rw [ne.def, with_top.of_dual_eq_top_iff, to_add_mul, with_bot.add_eq_bot],
          exact not_or hx hy, },
        rw [dif_neg hx, dif_neg hy, dif_neg hxy, ← real.rpow_add he],
        apply congr_arg,
        rw [← with_bot.coe_eq_coe, with_bot.coe_add],
        rw [classical.some_spec (with_bot.ne_bot_iff_exists.mp hx),
          classical.some_spec (with_bot.ne_bot_iff_exists.mp hy),
          classical.some_spec (with_bot.ne_bot_iff_exists.mp hxy), to_add_mul],
        refl, }},   
  end, }

