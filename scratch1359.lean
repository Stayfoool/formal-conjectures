/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib

/-!
# Lesser of twin primes

Primes $p$ such that $p+2$ is also prime.

This file contains a complete proof of the Ordowski--Israel characterization
recorded on the OEIS page: for $k > 1$, with $P$ the $k$-th prime and $q$ the
$(k+1)$-st prime, $P! \equiv 1 \pmod q$ holds if and only if $P + 2$ is prime,
or $k = 991$, or the gap exceeds $2$ and the gap product
$(P+1)(P+2)\cdots(q-2)$ is $\equiv 1 \pmod q$.

The proof is a short Wilson-theorem argument: from
$(q-1)! = P! \cdot W \cdot (q-1)$ and Wilson's theorem one gets
$P! \cdot W \equiv 1 \pmod q$, so the congruence on $P!$ is equivalent to
$W \equiv 1 \pmod q$; the case $q = P + 2$ gives the twin branch ($W$ is the
empty product), the case $q > P + 2$ gives the third branch, and the single
remaining content is the finite fact $7841! \equiv 1 \pmod{7853}$ at the
exceptional index $k = 991$.

*References:*
- [A001359](https://oeis.org/A001359)
-/


namespace OeisA1359

open Nat Finset

/-- The $n$-th lesser twin prime, with $a(0) = 0$. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n > 0 then
    Nat.nth (fun p => p.Prime ∧ (p + 2).Prime) (n - 1)
  else
    0

/-- Value of the sequence `a` at 0. -/
theorem a_0 : a 0 = 0 := by rfl

/-- Value of the sequence `a` at 1. -/
theorem a_1 : a 1 = 3 := by
  norm_num[a]
  exact(((congr_arg _) (by constructor) )).trans.comp (3).nth_count (by decide)

/-- Value of the sequence `a` at 2. -/
theorem a_2 : a 2 = 5 := by
  delta a
  apply((congr_arg _) (by constructor) ).trans (Nat.nth_count (by decide ) )

/-- Value of the sequence `a` at 3. -/
theorem a_3 : a 3 = 11 := by
  (inhabit ℝ)
  norm_num[a]
  exact (congr_arg _ (by decide)).trans (Nat.nth_count (by decide))

/-- Value of the sequence `a` at 4. -/
theorem a_4 : a 4 = 17 := by
  simp_all[a]
  exact (congr_arg _ (by constructor) ).trans (Nat.nth_count (by decide))

/-- `7841` is prime. -/
lemma prime_7841 : Nat.Prime 7841 := by native_decide

/-- There are `990` primes below `7841`. -/
lemma count_7841 : Nat.count Nat.Prime 7841 = 990 := by native_decide

/-- `7853` is prime. -/
lemma prime_7853 : Nat.Prime 7853 := by native_decide

/-- There are `991` primes below `7853`. -/
lemma count_7853 : Nat.count Nat.Prime 7853 = 991 := by native_decide

/-- The `991`-st prime is `7841`. -/
lemma nth_prime_990_eq_7841 : Nat.nth Nat.Prime 990 = 7841 := by
  rw [← count_7841]
  exact Nat.nth_count prime_7841

/-- The `992`-nd prime is `7853`. -/
lemma nth_prime_991_eq_7853 : Nat.nth Nat.Prime 991 = 7853 := by
  rw [← count_7853]
  exact Nat.nth_count prime_7853

/-- The exceptional congruence `7841! ≡ 1 (mod 7853)`. -/
lemma factorial_7841_mod_7853 : Nat.factorial 7841 % 7853 = 1 := by
  native_decide

/-- Splitting the factorial: for `P + 2 ≤ q`,
`(q-1)! = P! * (∏ i ∈ [P+1, q-2], i) * (q-1)`. -/
lemma factorial_mul_prod (P q : ℕ) (h : P + 2 ≤ q) :
    (q - 1).factorial = P.factorial * (∏ i ∈ Icc (P + 1) (q - 2), i) * (q - 1) := by
  have h1 : (q - 1).factorial = ∏ i ∈ Ico 1 q, i := by
    rw [← Finset.prod_Ico_id_eq_factorial (q - 1),
      show (q - 1) + 1 = q from by omega]
  have hs : ∏ i ∈ Ico 1 q, i
      = (∏ i ∈ Ico 1 (P + 1), i) * (∏ i ∈ Ico (P + 1) q, i) :=
    (Finset.prod_Ico_consecutive (fun i => i)
      (by omega : (1 : ℕ) ≤ P + 1) (by omega : (P + 1 : ℕ) ≤ q)).symm
  rw [h1, hs, Finset.prod_Ico_id_eq_factorial P]
  have h3 : ∏ i ∈ Ico (P + 1) q, i = (∏ i ∈ Icc (P + 1) (q - 2), i) * (q - 1) := by
    have key : ∀ b : ℕ, P + 1 ≤ b →
        ∏ i ∈ Ico (P + 1) (b + 1), i = (∏ i ∈ Icc (P + 1) (b - 1), i) * b := by
      intro b hb
      rw [Finset.prod_Ico_succ_top hb]
      congr 1
      refine Finset.prod_congr (Finset.ext fun x => ?_) fun x _ => rfl
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    have hq1 : q = (q - 1) + 1 := by omega
    rw [hq1]
    exact key (q - 1) (by omega)
  rw [h3]
  ring

/-- **Wilson bridge**: for a prime `q` and `P + 2 ≤ q`,
`P! * (∏ i ∈ [P+1, q-2], i) ≡ 1 (mod q)`. -/
lemma factorial_mul_prod_congr_one {P q : ℕ} (hq : q.Prime) (h : P + 2 ≤ q) :
    P.factorial * (∏ i ∈ Icc (P + 1) (q - 2), i) ≡ 1 [MOD q] := by
  have hfact : Fact q.Prime := ⟨hq⟩
  have h1 : (q - 1).factorial ≡ q - 1 [MOD q] := by
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.wilsons_lemma]
    have hqe : (((q - 1) + 1 : ℕ) : ZMod q) = 0 := by
      have hsum : ((q - 1) + 1 : ℕ) = q := by omega
      rw [hsum]
      exact ZMod.natCast_eq_zero_iff q q |>.mpr (Nat.dvd_refl q)
    rw [Nat.cast_add, Nat.cast_one] at hqe
    exact (eq_neg_of_add_eq_zero_left hqe).symm
  rw [factorial_mul_prod P q h] at h1
  have hsq : (q - 1) * (q - 1) ≡ 1 [MOD q] := by
    obtain ⟨r, hr⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
    subst hr
    rw [Nat.modEq_iff_dvd]
    refine ⟨-r, ?_⟩
    push_cast
    ring
  have h2 := h1.mul_right (q - 1)
  rw [Nat.mul_assoc] at h2
  have h4 := hsq.symm.mul_left (P.factorial * (∏ i ∈ Icc (P + 1) (q - 2), i))
  rw [Nat.mul_one] at h4
  exact h4.trans (h2.trans hsq)

/-- The central equivalence: for a prime `q` and `P + 2 ≤ q`,
`P! ≡ 1 (mod q) ↔ (∏ i ∈ [P+1, q-2], i) ≡ 1 (mod q)`. -/
lemma congr_one_iff_prod_one {P q : ℕ} (hq : q.Prime) (h : P + 2 ≤ q) :
    P.factorial ≡ 1 [MOD q] ↔ ((∏ i ∈ Icc (P + 1) (q - 2), i) ≡ 1 [MOD q]) := by
  have hbrid := factorial_mul_prod_congr_one hq h
  constructor
  · intro hP1
    have h := hP1.mul_right (∏ i ∈ Icc (P + 1) (q - 2), i)
    rw [Nat.one_mul] at h
    exact h.symm.trans hbrid
  · intro hW
    have h := hW.mul_left P.factorial
    rw [Nat.mul_one] at h
    exact h.symm.trans hbrid

/-- Unfolded restatement of the characterization. -/
lemma conjecture_unfolded (k : ℕ) (hk : k > 1) :
    (Nat.nth Nat.Prime (k - 1)).factorial ≡ 1 [MOD Nat.nth Nat.Prime k] ↔
      ((Nat.nth Nat.Prime (k - 1) + 2).Prime ∨ k = 991 ∨
        (Nat.nth Nat.Prime k - Nat.nth Nat.Prime (k - 1) > 2 ∧
          (∏ i ∈ Finset.Icc (Nat.nth Nat.Prime (k - 1) + 1)
            (Nat.nth Nat.Prime k - 2), i) ≡ 1 [MOD Nat.nth Nat.Prime k])) := by
  have hinf : (Set.ofPred Nat.Prime).Infinite := fun hf =>
    Nat.not_bddAbove_setOfPred_prime (Set.Finite.bddAbove hf)
  have hP : (Nat.nth Nat.Prime (k - 1)).Prime := Nat.nth_mem_of_infinite hinf (k - 1)
  have hq : (Nat.nth Nat.Prime k).Prime := Nat.nth_mem_of_infinite hinf k
  have hPge3 : 3 ≤ Nat.nth Nat.Prime (k - 1) := by
    have h3 : Nat.nth Nat.Prime 1 ≤ Nat.nth Nat.Prime (k - 1) :=
      (Nat.nth_le_nth hinf).mpr (by omega)
    rw [Nat.nth_prime_one_eq_three] at h3
    omega
  have hPltq : Nat.nth Nat.Prime (k - 1) < Nat.nth Nat.Prime k :=
    (Nat.nth_lt_nth hinf).mpr (by omega)
  have hPodd : Nat.nth Nat.Prime (k - 1) % 2 = 1 := by
    rcases hP.eq_two_or_odd with h2 | hodd
    · omega
    · exact hodd
  have hqodd : Nat.nth Nat.Prime k % 2 = 1 := by
    rcases hq.eq_two_or_odd with h2 | hodd
    · omega
    · exact hodd
  have hqne1 : Nat.nth Nat.Prime k ≠ Nat.nth Nat.Prime (k - 1) + 1 := by
    intro hqp
    have hpp : (Nat.nth Nat.Prime (k - 1) + 1).Prime := hqp ▸ hq
    rcases hpp.eq_two_or_odd with h2 | hodd
    · omega
    · omega
  have hmin : ∀ m : ℕ, m.Prime → Nat.nth Nat.Prime (k - 1) < m →
      Nat.nth Nat.Prime k ≤ m := by
    intro m hm hPm
    have hle : ∀ j, j < k → Nat.nth Nat.Prime j ≤ Nat.nth Nat.Prime (k - 1) := by
      intro j hj
      exact (Nat.nth_le_nth hinf).mpr (by omega)
    have hisleast := Nat.isLeast_nth_of_infinite (p := Nat.Prime) hinf k
    have hmem : m ∈ {x : ℕ | Nat.Prime x ∧ ∀ j < k, Nat.nth Nat.Prime j < m} := by
      refine ⟨hm, fun j hj => ?_⟩
      have hjle := hle j hj
      omega
    exact hisleast.2 hmem
  have hkey := congr_one_iff_prod_one
    (P := Nat.nth Nat.Prime (k - 1)) (q := Nat.nth Nat.Prime k) hq (by omega)
  by_cases hk991 : k = 991
  · subst hk991
    rw [nth_prime_990_eq_7841, nth_prime_991_eq_7853]
    refine iff_of_true ?_ (Or.inr (Or.inl rfl))
    show Nat.factorial 7841 % 7853 = 1
    exact factorial_7841_mod_7853
  · constructor
    · intro hcong
      have hW := hkey.mp hcong
      by_cases hg : Nat.nth Nat.Prime k - Nat.nth Nat.Prime (k - 1) = 2
      · refine Or.inl ?_
        have hqeq : Nat.nth Nat.Prime (k - 1) + 2 = Nat.nth Nat.Prime k := by omega
        exact hqeq ▸ hq
      · refine Or.inr (Or.inr ⟨?_, hW⟩)
        omega
    · rintro (htwin | h991 | ⟨hgt, hW1⟩)
      · have hqeq : Nat.nth Nat.Prime k = Nat.nth Nat.Prime (k - 1) + 2 := by
          have hle := hmin (Nat.nth Nat.Prime (k - 1) + 2) htwin (by omega)
          omega
        have hWemp : (∏ i ∈ Finset.Icc (Nat.nth Nat.Prime (k - 1) + 1)
            (Nat.nth Nat.Prime k - 2), i) ≡ 1 [MOD Nat.nth Nat.Prime k] := by
          rw [hqeq]
          have hIcc : Icc (Nat.nth Nat.Prime (k - 1) + 1)
              (Nat.nth Nat.Prime (k - 1) + 2 - 2) = ∅ :=
            Finset.Icc_eq_empty_iff.mpr (by omega)
          rw [hIcc]
          simp only [Finset.prod_empty]
          exact Nat.ModEq.rfl
        exact hkey.mpr hWemp
      · exact absurd h991 hk991
      · exact hkey.mpr hW1

/--
Primes $p_k$ such that $p_k! \equiv 1 \pmod{p_{k+1}}$ with the exception of $p_{991} = 7841$ and
other unknown primes $p_k$ for which $(p_k+1)(p_k+2)\cdots(p_{k+1}-2) \equiv 1 \pmod{p_{k+1}}$
where $p_{k+1} - p_k > 2$.

This is now proved: by Wilson's theorem $P! \cdot \prod_{i=P+1}^{q-2} i \equiv 1
\pmod{q}$ for consecutive primes $P < q$, so the congruence on $P!$ is
equivalent to the congruence on the gap product; the twin-prime branch is the
empty-product case $q = P + 2$, and the single further content is the finite
fact $7841! \equiv 1 \pmod{7853}$ (equivalently $7853 \mid 11! - 1$) at the
exceptional index $k = 991$.
-/
theorem conjecture (k : ℕ) (hk : k > 1) :
    let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])) :=
  conjecture_unfolded k hk

end OeisA1359
