/-
Copyright (c) 2026 Liangze Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liangze Zhao
-/
import Mathlib
/-!
# JSP-000256 (Erdős Problem #305): Denominators of Unit Fractions
**Problem Statement.**
How small can the largest denominator be in a representation of a given
positive rational number by distinct unit fractions?
**Mathematical History.**
- M. N. Bleicher and P. Erdős (1976) proved that for any a < b, a/b can be
  represented with denominators bounded by O(b (log b)^2).
- H. Yokota (1988, J. Number Theory 30: 198-207) proved the conjecture:
  the largest denominator can be bounded by b * (log b)^{1 + o(1)}.
-/
namespace JSP000256

/-- 谓词：有限自然数集合 S 是有理数 q 的合法单位分数分解（互异且分母严格大于 1） -/
def IsEgyptianRep (q : ℚ) (S : Finset ℕ) : Prop :=
  (∀ d ∈ S, 1 < d) ∧ S.sum (fun d => (1 : ℚ) / (d : ℚ)) = q

/--
核心有界分解谓词：有理数 a/b 是否存在一个所有分母均不超过 M 的互异单位分数分解。
这正是定义 Bleicher-Erdős 上界 D(a, b) ≤ M 的正规形式化陈述。
-/
def HasEgyptianRepBounded (a b : ℕ) (M : ℕ) : Prop :=
  ∃ S : Finset ℕ, IsEgyptianRep ((a : ℚ) / (b : ℚ)) S ∧ ∀ d ∈ S, d ≤ M

/-- 基础引理：单个单位分数 1/b 本身构成合法平凡分解（当 b > 1 时） -/
lemma isEgyptianRep_single {b : ℕ} (hb : 1 < b) :
    IsEgyptianRep ((1 : ℚ) / (b : ℚ)) {b} := by
  constructor
  · intro d hd
    simp only [Finset.mem_singleton] at hd
    rw [hd]
    exact hb
  · simp only [Finset.sum_singleton]

/-- 平凡基础定理：对于 a = 1，其最大分母上界自然不超过 b 本身 -/
theorem egyptianRep_one_bounded {b : ℕ} (hb : 1 < b) :
    HasEgyptianRepBounded 1 b b := by
  use {b}
  constructor
  · exact isEgyptianRep_single hb
  · intro d hd
    simp only [Finset.mem_singleton] at hd
    rw [hd]

/--
核心并集引理：若两个单位分数分解不相交，它们的并集即构成和的合法单位分数分解。
-/
lemma isEgyptianRep_union {q₁ q₂ : ℚ} {S₁ S₂ : Finset ℕ}
    (h₁ : IsEgyptianRep q₁ S₁) (h₂ : IsEgyptianRep q₂ S₂)
    (hdisj : Disjoint S₁ S₂) :
    IsEgyptianRep (q₁ + q₂) (S₁ ∪ S₂) := by
  constructor
  · intro d hd
    rw [Finset.mem_union] at hd
    cases hd with
    | inl h => exact h₁.1 d h
    | inr h => exact h₂.1 d h
  · rw [Finset.sum_union hdisj]
    rw [h₁.2, h₂.2]

/--
有界分解的加法上界传递：不相交的分解相加后，最大分母上界为 max(M₁, M₂)。
-/
lemma hasEgyptianRepBounded_add {a₁ b₁ a₂ b₂ M₁ M₂ : ℕ}
    {S₁ S₂ : Finset ℕ}
    (h₁ : IsEgyptianRep ((a₁ : ℚ) / (b₁ : ℚ)) S₁) (hM₁ : ∀ d ∈ S₁, d ≤ M₁)
    (h₂ : IsEgyptianRep ((a₂ : ℚ) / (b₂ : ℚ)) S₂) (hM₂ : ∀ d ∈ S₂, d ≤ M₂)
    (hdisj : Disjoint S₁ S₂) :
    ∃ S : Finset ℕ, IsEgyptianRep (((a₁ : ℚ) / (b₁ : ℚ)) + ((a₂ : ℚ) / (b₂ : ℚ))) S ∧
      ∀ d ∈ S, d ≤ max M₁ M₂ := by
  use S₁ ∪ S₂
  constructor
  · exact isEgyptianRep_union h₁ h₂ hdisj
  · intro d hd
    rw [Finset.mem_union] at hd
    cases hd with
    | inl h => exact le_trans (hM₁ d h) (le_max_left M₁ M₂)
    | inr h => exact le_trans (hM₂ d h) (le_max_right M₁ M₂)

/--
Sylvester 经典裂项恒等式（代数有理数形式）：
对于任意正自然数 n，1/n = 1/(n+1) + 1/(n(n+1))
-/
lemma unit_fraction_split {n : ℕ} (hn : 0 < n) :
    (1 : ℚ) / (n : ℚ) = (1 : ℚ) / (n + 1 : ℚ) + (1 : ℚ) / ((n * (n + 1) : ℕ) : ℚ) := by
  have hn_ne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have hn1_ne : (n + 1 : ℚ) ≠ 0 := by positivity
  have hprod_ne : (n : ℚ) * (n + 1 : ℚ) ≠ 0 := mul_ne_zero hn_ne hn1_ne
  push_cast
  field_simp

/--
Bézout 裂项代数引理：
若整数 u, v 满足 u * M + v * N = a，则 a / (M * N) = v / M + u / N。
这是 Bleicher-Erdős 乘法递推的基础代数恒等式。
-/
lemma bezout_fraction_decomp (a : ℤ) {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (u v : ℤ) (h_bezout : u * (M : ℤ) + v * (N : ℤ) = a) :
    (a : ℚ) / ((M * N : ℕ) : ℚ) = (v : ℚ) / (M : ℚ) + (u : ℚ) / (N : ℚ) := by
  have hM_ne : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hM)
  have hN_ne : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
  push_cast
  field_simp
  have h_cast : (u : ℚ) * (M : ℚ) + (v : ℚ) * (N : ℚ) = (a : ℚ) := by
    exact_mod_cast h_bezout
  rw [← h_cast]
  ring

/--
单因子倒数恒等式：
若 d 是正自然数 N 的因数，则 d / N = 1 / (N / d)。
-/
lemma div_over_self_eq_one_div {N d : ℕ} (hN : 0 < N) (hd : d ∣ N) (hd_pos : 0 < d) :
    (d : ℚ) / (N : ℚ) = (1 : ℚ) / ((N / d : ℕ) : ℚ) := by
  have hd_ne : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hd_pos)
  have hNd : N = d * (N / d) := (Nat.mul_div_cancel' hd).symm
  have hNd_pos : 0 < N / d := Nat.div_pos (Nat.le_of_dvd hN hd) hd_pos
  have hNd_ne : ((N / d : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hNd_pos)
  nth_rw 1 [hNd]
  push_cast
  field_simp

/--
因数除法映射单射性引理：
在正自然数 N 的所有正因数上，映射 d ↦ N / d 严格单射。
-/
lemma div_injective_on_divisors {N : ℕ} (hN : 0 < N) {d₁ d₂ : ℕ}
    (hd₁ : d₁ ∣ N) (hd₂ : d₂ ∣ N) (_hd₁_pos : 0 < d₁) (hd₂_pos : 0 < d₂)
    (h : N / d₁ = N / d₂) : d₁ = d₂ := by
  have h1 : N = d₁ * (N / d₁) := (Nat.mul_div_cancel' hd₁).symm
  have h2 : N = d₂ * (N / d₂) := (Nat.mul_div_cancel' hd₂).symm
  have hNd₂_pos : 0 < N / d₂ := Nat.div_pos (Nat.le_of_dvd hN hd₂) hd₂_pos
  rw [h] at h1
  exact Nat.eq_of_mul_eq_mul_right hNd₂_pos (by
    calc
      d₁ * (N / d₂) = N := h1.symm
      _ = d₂ * (N / d₂) := h2)

/--
分母严格大于 1 引理：
若 d 是 N 的严格真因数 (d < N)，则 N / d > 1。
-/
lemma one_lt_div_of_dvd_lt {N d : ℕ} (_hN : 0 < N) (hd : d ∣ N) (_hd_pos : 0 < d) (hd_lt : d < N) :
    1 < N / d := by
  have hNd : N = d * (N / d) := (Nat.mul_div_cancel' hd).symm
  by_contra h_le
  push Not at h_le
  have h_le' : d * (N / d) ≤ d * 1 := Nat.mul_le_mul_left d h_le
  rw [← hNd, mul_one] at h_le'
  exact lt_irrefl d (lt_of_lt_of_le hd_lt h_le')

/--
Bleicher-Erdős 核心桥梁定理 (Lemma 1 Bridge):
若自然数子集 D 中均为 N 的正因数，且其和严格小于 N (保证无 d = N 项)，
则由映射 d ↦ N / d 构成的集合是 (∑ D) / N 的合法互异单位分数分解。
-/
theorem divisors_sum_to_egyptian {N : ℕ} (hN : 0 < N) {D : Finset ℕ}
    (hD : ∀ d ∈ D, d ∣ N) (hDpos : ∀ d ∈ D, 0 < d)
    (hr_lt : D.sum id < N) :
    IsEgyptianRep (((D.sum id : ℕ) : ℚ) / (N : ℚ)) (D.image (fun d => N / d)) := by
  constructor
  · -- 1. 证明所有分母 > 1
    intro m hm
    rw [Finset.mem_image] at hm
    rcases hm with ⟨d, hd, rfl⟩
    have hd_le_sum : d ≤ D.sum id := Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hd
    have hd_lt : d < N := lt_of_le_of_lt hd_le_sum hr_lt
    exact one_lt_div_of_dvd_lt hN (hD d hd) (hDpos d hd) hd_lt
  · -- 2. 证明单位分数和等于 (∑ D) / N
    have hinj : ∀ x ∈ D, ∀ y ∈ D, N / x = N / y → x = y := by
      intro x hx y hy hxy
      exact div_injective_on_divisors hN (hD x hx) (hD y hy) (hDpos x hx) (hDpos y hy) hxy
    rw [Finset.sum_image hinj]
    have h_term : ∀ d ∈ D, (1 : ℚ) / ((N / d : ℕ) : ℚ) = (d : ℚ) / (N : ℚ) := by
      intro d hd
      exact (div_over_self_eq_one_div hN (hD d hd) (hDpos d hd)).symm
    rw [Finset.sum_congr rfl h_term]
    push_cast
    rw [Finset.sum_div]
    simp [id_eq]

/--
Bleicher-Erdős 核心上界落地定理：
若 r 可拆为 N 的正因数之和且 r < N，则 r/N 存在最大分母不超过 N 的单位分数分解！
即直接证明了 D(r, N) ≤ N。
-/
theorem hasEgyptianRepBounded_of_divisor_sum {N : ℕ} (hN : 0 < N) {D : Finset ℕ}
    (hD : ∀ d ∈ D, d ∣ N) (hDpos : ∀ d ∈ D, 0 < d)
    (hr_lt : D.sum id < N) :
    HasEgyptianRepBounded (D.sum id) N N := by
  use D.image (fun d => N / d)
  constructor
  · exact divisors_sum_to_egyptian hN hD hDpos hr_lt
  · intro m hm
    rw [Finset.mem_image] at hm
    rcases hm with ⟨d, hd, rfl⟩
    exact Nat.div_le_self N d

end JSP000256
