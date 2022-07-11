import algebra.order.monoid
import data.rat.basic
import topology.algebra.infinite_sum

open function

variables {M : Type*} {N : Type*}

def with_top.cast_fun (f : M → N) : with_top M → with_top N
| ⊤ := ⊤
| (x : M) := f x

variables [hM : add_monoid M] [hN : add_monoid N] {f : add_monoid_hom M N}
include hM hN 

lemma with_top.cast_fun_zero : with_top.cast_fun f (0 : M) = 0:=
by { rw with_top.cast_fun, rw map_zero, refl }

lemma with_top.cast_fun_add :
∀ a b : with_top M, (a + b).cast_fun f = a.cast_fun f + b.cast_fun f
| ⊤ b := show _ = ⊤ + _, by simp only [with_top.top_add]; refl
| a ⊤ := show _ = _ + ⊤, by simp only [with_top.add_top]; refl 
| (a : M) (b : M) := 
by rw [← with_top.coe_add, with_top.cast_fun, with_top.cast_fun, with_top.cast_fun,
    ← with_top.coe_add, with_top.coe_eq_coe, map_add]

lemma with_top.cast_fun_eq_top : ∀ {x : with_top M}, x.cast_fun f = ⊤ → x = ⊤
| ⊤ := λ h, rfl 
| (x : M) := λ h, absurd h with_top.coe_ne_top

lemma with_top.cast_fun_inj (hf : injective f) : injective (with_top.cast_fun f)
| ⊤ y h := (with_top.cast_fun_eq_top h.symm).symm
| x ⊤ h := with_top.cast_fun_eq_top h  
| (x : M) (y : M) h := 
by { injections, exact with_top.coe_eq_coe.mpr ((injective.eq_iff hf).mp h_1)}

variable (f)

def with_top.cast_add_monoid_hom : with_top M →+ with_top N :=
{ to_fun   := with_top.cast_fun f,
  map_zero' := with_top.cast_fun_zero,
  map_add' := with_top.cast_fun_add }

def mulcast : multiplicative (order_dual (with_top M)) →*
  multiplicative (order_dual (with_top N)) :=
{ to_fun   := with_top.cast_fun f,
  map_one' := with_top.cast_fun_zero,
  map_mul' := with_top.cast_fun_add }

omit hM hN

variable {f}

lemma mulcast_injective (hf : injective f) : function.injective (mulcast f):=
with_top.cast_fun_inj hf

section comm_group
variables (f) [linear_ordered_add_comm_group M] [linear_ordered_add_comm_group N]

lemma mulcast_map_zero : mulcast f 0 = 0 := rfl

variable {f}

lemma mulcast_eq_zero_iff (hf : injective f) (x : multiplicative (order_dual (with_top M))) :  
  mulcast f x = 0 ↔ x = 0 :=
begin
  rw [← mulcast_map_zero f],
  exact ⟨λ h, mulcast_injective hf h, congr_arg _⟩
end

/- lemma mulcast_map_gen : 
  mulcast (mul_gen (with_top ℤ)) = mul_gen (with_top ℚ) :=
show ↑_ = ↑_, by rw int.cast_one -/

lemma with_top_cast_le_with_top_cast (hf : strict_mono f) : ∀ (x y : with_top M),
  with_top.cast_fun f x ≤ with_top.cast_fun f y ↔  x ≤ y
| ⊤ b := 
by erw [top_le_iff, top_le_iff]; exact ⟨with_top.cast_fun_eq_top, λ h, h.symm ▸ rfl⟩
| a ⊤ := ⟨λ h, le_top, λ h, le_top⟩
| (a : M) (b : M) := by { rw [with_top.cast_fun, with_top.cast_fun, with_top.coe_le_coe,
  with_top.coe_le_coe], exact hf.le_iff_le}

lemma with_top_cast_lt_with_top_cast (hf : strict_mono f) : ∀ (x y : with_top M),
  with_top.cast_fun f x < with_top.cast_fun f y ↔  x < y
| ⊤ ⊤ := by simp only [lt_self_iff_false]
| ⊤ (b : M) := by { simp only [not_top_lt, iff_false, not_lt], exact le_top } 
| (a : M) ⊤ := ⟨λ h, with_top.coe_lt_top _, λ h, with_top.coe_lt_top _⟩
| (a : M) (b : M) := 
by { rw [with_top.cast_fun, with_top.cast_fun, with_top.coe_lt_coe, with_top.coe_lt_coe],
  exact hf.lt_iff_lt }

lemma mulcast_le_mulcast (hf : strict_mono f) (x y : multiplicative (order_dual (with_top M))) : 
  mulcast f x ≤ mulcast f y ↔ x ≤ y :=
with_top_cast_le_with_top_cast hf _ _

lemma mulcast_lt_mulcast (hf : strict_mono f) (x y : multiplicative (order_dual (with_top M))) : 
  mulcast f x < mulcast f y ↔ x < y :=
with_top_cast_lt_with_top_cast hf _ _

end comm_group

section ring

variables [linear_ordered_comm_ring M] -- [linear_ordered_comm_ring N]

lemma with_top_add_mul (m : M) (hm : m ≠ 0) : ∀ a b : with_top M,
  (a + b) * m = a * m + b * m
| ⊤ _ :=
by rw [top_add, with_top.top_mul (show (m : with_top M) ≠ 0, by norm_cast; exact hm), top_add]
| _ ⊤ :=
by rw [add_top, with_top.top_mul (show (m : with_top M) ≠ 0, by norm_cast; exact hm), add_top]
| (some a) (some b) :=
by simp only [with_top.some_eq_coe, ←with_top.coe_add, ←with_top.coe_mul, add_mul]

lemma mul_eq_top_iff (m : M) (hm : m ≠ 0) : ∀ a : with_top M,
  a * m = ⊤ ↔ a = ⊤
| ⊤ := ⟨λ h, rfl, λ h, by rw [with_top.top_mul]; norm_cast; exact hm⟩
| (some m) := 
⟨λ h, absurd (by rwa [with_top.some_eq_coe, ←with_top.coe_mul] at h) with_top.coe_ne_top, 
 λ h, absurd h with_top.coe_ne_top⟩

lemma succ_nsmul_top (m : ℕ) : ((m + 1) • ⊤ : with_top M) = ⊤ :=
begin
  induction m with m hm,
  { simp only [one_nsmul] },
  { simp only [succ_nsmul, with_top.top_add] },
end

lemma nsmul_top_mul (m : ℕ) (q : M) :
  (m • (⊤ : with_top M)) * q = ⊤ * (m * q : M) :=
begin  
  induction m with m hm,
  { simp only [zero_smul, zero_mul, nat.cast_zero, with_top.coe_zero, mul_zero], },  
  { rw succ_nsmul_top,
    by_cases q = 0,
    { simp only [h, with_top.coe_zero, mul_zero] },
    { rw with_top.top_mul (show (q : with_top M) ≠ 0, by norm_cast; exact h),
      refine (with_top.top_mul _).symm,
      norm_cast,
      exact (λ hn, h $ or.resolve_left (mul_eq_zero.1 hn)
        (by norm_cast; exact nat.succ_ne_zero _))}}
end

lemma zero_le_mul_inv (m : M) (hm : 0 < m) : ∀ x : with_top M,
  0 ≤ x ↔ 0 ≤ x * m
| ⊤ := by {rw with_top.top_mul, norm_cast, linarith }
| (some a) := 
begin
  simp only [with_top.some_eq_coe, ←with_top.coe_zero, ←with_top.coe_mul, 
    with_top.coe_le_coe, zero_le_mul_right hm],
end

lemma nsmul_coe (m : ℕ) (x : M) : m • (x : with_top M) = m * x :=
begin
  induction m with m hm,
  { rw [zero_smul, nat.cast_zero, zero_mul] },
  { rw [succ_nsmul, hm],
    norm_cast,
    rw [nat.cast_succ, add_mul, one_mul, add_comm] }
end

lemma nsmul_top (m : ℕ) : m • (⊤ : with_top M) = m * ⊤ :=
begin
  induction m with m hm,
  { simp only [zero_smul, nat.cast_zero, zero_mul] },
  { rw [succ_nsmul_top,  with_top.mul_top],
    exact nat.cast_ne_zero.mpr (nat.succ_ne_zero _) }
end

lemma nsmul_with_top (m : ℕ) : ∀ (x : with_top M), m • x = m * x 
| ⊤ := nsmul_top _ 
| (some x) := nsmul_coe _ _

lemma nsmul_coe_mul (m : ℕ) (x q : M) :
  (m • (x : with_top M)) * q = x * (m * q : M) :=
begin
  rw [nsmul_coe, mul_comm ↑m, mul_assoc],
  congr,
  norm_cast,
end 

lemma nsmul_mul (m : ℕ) (q : M) : ∀ x : with_top M,
  (m • x : with_top M) * q = x * (m * q : M) 
| ⊤ := nsmul_top_mul _ _
| (some x) := nsmul_coe_mul m x q

lemma nsmul_comm (m : ℕ) (q : M) (x : with_top M) :
  (m • x : with_top M) * q = m • (x * q) := 
begin 
  rw [nsmul_mul, with_top.coe_mul, ←mul_assoc, mul_comm x, mul_assoc, nsmul_with_top],
  congr' 1,
end

lemma mul_coe_one (x : with_top M) :
  x * (1 : M) = x := mul_one _

instance multiplicative_order_dual.has_pow :
  has_pow (multiplicative (order_dual (with_top M))) M := 
⟨λ x y, ((x : with_top M) * y : with_top M)⟩ 

lemma mulM_mul_pow {m : M} (hm : m ≠ 0) (g h : multiplicative (order_dual (with_top M)))  : 
  (g * h) ^ m = g ^ m * h ^ m :=
with_top_add_mul _ hm _ _

lemma mulM_zero_pow (n : M) (h : n ≠ 0) : (0 : multiplicative (order_dual (with_top M))) ^ n = 0 := 
with_top.top_mul (by norm_cast; exact h)

lemma mulM_one_pow (n : M) : (1 : multiplicative (order_dual (with_top M))) ^ n = 1 := zero_mul _ 

lemma mulM_pow_one (x : multiplicative (order_dual (with_top M))) : x ^ (1 : M) = x := 
mul_coe_one x 

lemma mulM_pow_le_one (q : M) (h : 0 < q) (x : multiplicative (order_dual (with_top M))) :
 x ≤ 1 ↔ x ^ q ≤ 1 :=
zero_le_mul_inv _ h _

lemma mulM_pow_eq_zero_iff (x : multiplicative (order_dual (with_top M))) {q : M} (h : q ≠ 0) :
  x ^ q = 0 ↔ x = 0 :=
mul_eq_top_iff _ h _ 

lemma mulM_pow_mul (n : ℕ) (q : M) (x : multiplicative (order_dual (with_top M))) :
  (x ^ n) ^ q = x ^ ((n : M) * q) :=
nsmul_mul _ _ _

lemma mulM_pow_comm (n : ℕ) (q : M) (x : multiplicative (order_dual (with_top M))) :
  (x ^ n) ^ q = (x ^ q) ^ n :=
nsmul_comm _ _ _

end ring

section field

variable [linear_ordered_field M]

lemma mul_inv_le_mul_inv (m : ℕ) (h : m ≠ 0) :
  ∀ g h : with_top M, g ≤ h → g * (m⁻¹ : M) ≤ h * (m⁻¹ : M) 
| ⊤ a H := 
begin
  rw [top_le_iff.1 H, with_top.top_mul],
  { exact le_refl _},
  { simp [h] }
end
| a ⊤ H := 
begin
  rw with_top.top_mul,
  { exact le_top },
  { simp [h] }
end
| (some a) (some b) H := by { simp only [with_top.some_eq_coe, ←with_top.coe_mul,
    with_top.coe_le_coe, with_top.some_eq_coe] at ⊢ H,
    exact (mul_le_mul_right (by {rw [inv_pos], norm_cast, exact pos_iff_ne_zero.2 h})).2 H }

lemma mulM_pow_le_of_le {m : ℕ} {g h : multiplicative (order_dual (with_top M))} (hm : m ≠ 0)
  (H : h ≤ g) : h ^ (m⁻¹ : M) ≤ g ^ (m⁻¹ : M) :=
mul_inv_le_mul_inv m hm g h H

end field

--#lint