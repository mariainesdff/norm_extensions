--import data.real.nnreal
import ring_theory.valuation.basic
import number_theory.padics.padic_numbers
import analysis.special_functions.pow

noncomputable theory

open function multiplicative

open_locale nnreal

variables {R : Type*} [ring R] {Γ₀ : Type*} [linear_ordered_comm_group_with_zero Γ₀]

lemma mult_with_top_R_zero : multiplicative.of_add (order_dual.to_dual ⊤) = 
  (0 : multiplicative (with_top ℝ)ᵒᵈ) := rfl 


section is_rank_one

class is_rank_one (v : valuation R Γ₀)  :=
(hom : Γ₀ →*₀ ℝ≥0) 
(strict_mono : strict_mono hom) 
(nontrivial : ∃ r : R, v r ≠ 0 ∧ v r ≠ 1)

/- def is_rank_one_hom (v : valuation R Γ₀) [hv : is_rank_one v] :
  Γ₀ →*₀ ℝ≥0:=
hv.hom

lemma is_rank_one_hom_strict_mono (v : valuation R Γ₀) [hv : is_rank_one v] :
  strict_mono (is_rank_one_hom v) :=
hv.strict_mono -/

lemma zero_of_is_rank_one_hom_zero (v : valuation R Γ₀) [hv : is_rank_one v] {x : Γ₀}
 (hx : is_rank_one.hom v x = 0) : x = 0 :=
begin
  have hx0 : 0 ≤ x := zero_le',
  cases le_iff_lt_or_eq.mp hx0 with h_lt h_eq,
  { have hs := is_rank_one.strict_mono h_lt,
    rw [map_zero, hx] at hs,
    exact absurd hs not_lt_zero', },
  { exact h_eq.symm }
end

@[simp] lemma is_rank_one_hom_eq_zero_iff (v : valuation R Γ₀) [hv : is_rank_one v] {x : Γ₀} :
  is_rank_one.hom v x = 0 ↔  x = 0 :=
⟨λ h, zero_of_is_rank_one_hom_zero v h, λ h, by rw [h, map_zero]⟩

def is_rank_one_unit (v : valuation R Γ₀) [hv : is_rank_one v] : Γ₀ˣ :=
units.mk0 (v (classical.some hv.nontrivial)) (classical.some_spec hv.nontrivial).1

lemma is_rank_one_unit_ne_one (v : valuation R Γ₀) [hv : is_rank_one v] : 
  is_rank_one_unit v ≠ 1 :=
begin
  rw [ne.def, ← units.eq_iff, units.coe_one],
  exact (classical.some_spec hv.nontrivial).2,
end

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

end is_rank_one