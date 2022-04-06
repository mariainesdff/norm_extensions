import analysis.normed.normed_field

class normed_field' (α : Type*) extends has_norm α, field α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b)

@[priority 100] -- see Note [lower instance priority]
instance normed_field'.to_normed_comm_ring {α : Type*} [normed_field' α] :
  normed_comm_ring α :=
{ norm_mul := λ a b, normed_field'.norm_mul a b,
  ..‹normed_field' α› }

def is_pow_mult {α : Type*} [ring α] (f : α → ℝ) :=
∀ (a : α) (n : ℕ), f (a^n) = (f a) ^ n

structure is_seminorm {α : Type*} [ring α] (f : α → ℝ) : Prop :=
(nonneg : ∀ a, 0 ≤ f a)
(zero : f 0 = 0)
(mul : ∀ a b, f (a * b) ≤ f a * f b)

structure is_norm {α : Type*} [ring α] (f : α → ℝ) extends (is_seminorm f) :=
(ne_zero : ∀ a, a ≠ 0 → 0 < f a)

structure is_algebra_norm (α : Type*) [normed_comm_ring α] {β : Type*} [ring β] [algebra α β]
  (f : β → ℝ) extends (is_norm f) :=
(smul : ∀ (a : α) (x : β) , f (a • x) ≤ ∥ a ∥ * f x)

def is_nonarchimedean {α : Type*} [ring α] (f : α → ℝ) : Prop := 
∀ a b, f (a + b) ≤ max (f a) (f b)