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
module

public import FormalConjecturesUtil

/-!
# Ramsey numbers

The (graph) Ramsey number $R(k,\ell)$ is the least natural number $n$ such that every simple graph
on $n$ vertices contains either a clique of size $k$ or an independent set of size $\ell$
(equivalently, the complement graph contains a clique of size $\ell$).

We formalize the classical open problem of determining $R(5,5)$, together with the currently best
known bounds $43 \le R(5,5) \le 46$.

Note: the diagonal Ramsey number $R(n,n)$ can also be formulated in terms of 2-colorings of
$2$-subsets, as `Combinatorics.hypergraphRamsey 2 n` (see `FormalConjecturesForMathlib/Combinatorics/Ramsey.lean`).

*References:*
- [Wikipedia: Ramsey number](https://en.wikipedia.org/wiki/Ramsey_number)
- [Rad] S. P. Radziszowski, *Small Ramsey Numbers*, Electronic Journal of Combinatorics, Dynamic
  Survey DS1. (Updated periodically.) https://www.combinatorics.org/ojs/index.php/eljc/article/view/DS1
- [Exoo89] G. Exoo, *A lower bound for* $R(5,5)$, Journal of Graph Theory 13 (1989), 97–98.
  DOI: 10.1002/jgt.3190130113
- [AM24] V. Angeltveit and B. McKay, *$R(5,5) \le 46$*, arXiv:2409.15709 (2024).
- [OEIS A212954](https://oeis.org/A212954)
- [MathWorld: Ramsey Number](https://mathworld.wolfram.com/RamseyNumber.html)
-/

@[expose] public section

namespace RamseyNumbers

/--
`IsGraphRamsey n k l` means that for every simple graph `G` on `n` vertices, either
- `G` contains a clique of size `k`, or
- the complement graph `Gᶜ` contains a clique of size `l` (equivalently, `G` contains an
  independent set of size `l`).
-/
def IsGraphRamsey (n k l : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ (G.CliqueFree k ∧ (Gᶜ).CliqueFree l)

/-- Monotonicity in the number of vertices. -/
@[category API, AMS 5]
theorem IsGraphRamsey.succ (n k l : ℕ) :
    IsGraphRamsey n k l → IsGraphRamsey (n + 1) k l := by
  intro h G
  -- Restrict to the induced subgraph on the first `n` vertices.
  let H : SimpleGraph (Fin n) := G.comap (Fin.castSuccEmb : Fin n ↪ Fin (n + 1))
  have emb : H ↪g G := SimpleGraph.Embedding.comap (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) G
  have embc : (Hᶜ) ↪g (Gᶜ) := (SimpleGraph.Embedding.complEquiv (G := H) (H := G)).toFun emb
  rintro ⟨hG, hGc⟩
  have hH : H.CliqueFree k := SimpleGraph.CliqueFree.comap emb.isContained hG
  have hHc : (Hᶜ).CliqueFree l := SimpleGraph.CliqueFree.comap embc.isContained hGc
  exact (h H) ⟨hH, hHc⟩

/-- Symmetry in the clique / independent set sizes. -/
@[category API, AMS 5]
theorem IsGraphRamsey.symm (n k l : ℕ) :
    IsGraphRamsey n k l ↔ IsGraphRamsey n l k := by
  constructor <;> intro h G
  · simpa [IsGraphRamsey, and_comm, and_left_comm, and_assoc] using h (Gᶜ)
  · simpa [IsGraphRamsey, and_comm, and_left_comm, and_assoc] using h (Gᶜ)

/-- The shared Ramsey number agrees with the clique-free formulation. -/
@[category API, AMS 5]
theorem classicalRamsey_eq_sInf (k l : ℕ) :
    SimpleGraph.classicalRamsey k l = sInf {n : ℕ | IsGraphRamsey n k l} := by
  classical
  simp only [SimpleGraph.classicalRamsey, SimpleGraph.graphRamsey,
    IsGraphRamsey, not_and_or, SimpleGraph.not_cliqueFree_iff_top_isContained]

-- Notation used in the literature.
local notation "R(" k ", " l ")" => SimpleGraph.classicalRamsey k l

def ramsey_number_five_five.answer : ℕ := sorry

/--
The open problem: determine the Ramsey number $R(5,5)$.

It is known that $43 \le R(5,5) \le 46$.
-/
@[category research open, question value, AMS 5]
theorem ramsey_number_five_five :
    R(5, 5) = ramsey_number_five_five.answer := by
  sorry

/--
Lower bound $43 \le R(5,5)$, equivalently: there exists a graph on $42$ vertices with no
$5$-clique and no independent set of size $5$.
-/
@[category research solved, AMS 5]
theorem ramsey_number_five_five_lower_bound :
    ∃ G : SimpleGraph (Fin 42), G.CliqueFree 5 ∧ (Gᶜ).CliqueFree 5 := by
  sorry

/--
Upper bound $R(5,5) \le 46$, i.e. every graph on $46$ vertices contains a $5$-clique or an
independent set of size $5$.
-/
@[category research solved, AMS 5]
theorem ramsey_number_five_five_upper_bound :
    IsGraphRamsey 46 5 5 := by
  sorry

/- ## Other small Ramsey numbers

Besides $R(5,5)$, several small Ramsey numbers are known exactly, while others (such as $R(6,6)$)
remain open. The values below are collected in the dynamic survey [Rad] (see also
[OEIS A212954]): the exact diagonal value $R(4,4) = 18$, the exact off-diagonal values $R(3,k)$
for $3 \le k \le 9$, and $R(4,5) = 25$. -/

/- ## The exact value R(3,3) = 6

The proof is the classical one: five edges out of a vertex force three of one colour
(pigeonhole), and the 5-cycle coloring shows that five vertices do not suffice. -/

/-- Three pairwise distinct, pairwise adjacent vertices form a clique. -/
@[category API, AMS 5]
lemma isClique_triple {α : Type*} [DecidableEq α] {G : SimpleGraph α} {x y z : α}
    (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (e1 : G.Adj x y) (e2 : G.Adj x z) (e3 : G.Adj y z) :
    G.IsClique ({x, y, z} : Finset α) := by
  intro u hu w hw hne
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu hw
  rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
  · exact absurd rfl hne
  · exact e1
  · exact e2
  · exact SimpleGraph.adj_symm G e1
  · exact absurd rfl hne
  · exact e3
  · exact SimpleGraph.adj_symm G e2
  · exact SimpleGraph.adj_symm G e3
  · exact absurd rfl hne

/-- The 5-cycle and its complement are both triangle-free. -/
@[category API, AMS 5]
lemma cycleGraph_five_triangleFree :
    (SimpleGraph.cycleGraph 5).CliqueFree 3 ∧ ((SimpleGraph.cycleGraph 5)ᶜ).CliqueFree 3 := by
  constructor
  · show ∀ t : Finset (Fin 5), ¬(SimpleGraph.cycleGraph 5).IsNClique 3 t
    decide
  · show ∀ t : Finset (Fin 5), ¬((SimpleGraph.cycleGraph 5)ᶜ).IsNClique 3 t
    decide

/-- A triangle `{v, x, y}` in `G`, built from a vertex and two of its neighbors. -/
@[category API, AMS 5]
lemma not_cliqueFree_of_triangle {G : SimpleGraph (Fin 6)} {v x y : Fin 6}
    (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y)
    (e1 : G.Adj v x) (e2 : G.Adj v y) (e3 : G.Adj x y) :
    ¬G.CliqueFree 3 := by
  intro hcf
  exact hcf {v, x, y} ⟨isClique_triple hvx hvy hxy e1 e2 e3,
    Finset.card_eq_three.mpr ⟨v, x, y, hvx, hvy, hxy, rfl⟩⟩

/-- A triangle `{v, x, y}` in the complement. -/
@[category API, AMS 5]
lemma not_cliqueFree_of_compl_triangle {G : SimpleGraph (Fin 6)} {v x y : Fin 6}
    (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y)
    (e1 : ¬G.Adj v x) (e2 : ¬G.Adj v y) (e3 : ¬G.Adj x y) :
    ¬(Gᶜ).CliqueFree 3 := by
  intro hcf
  refine hcf {v, x, y} ⟨isClique_triple (G := Gᶜ) hvx hvy hxy
    (SimpleGraph.compl_adj G v x |>.mpr ⟨hvx, e1⟩)
    (SimpleGraph.compl_adj G v y |>.mpr ⟨hvy, e2⟩)
    (SimpleGraph.compl_adj G x y |>.mpr ⟨hxy, e3⟩),
    Finset.card_eq_three.mpr ⟨v, x, y, hvx, hvy, hxy, rfl⟩⟩

/-- Pigeonhole: three pairwise distinct neighbors of `v` force a triangle in `G` or in `Gᶜ`. -/
@[category API, AMS 5]
lemma three_neighbors_fan {G : SimpleGraph (Fin 6)} {v a b c : Fin 6}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c) :
    ¬G.CliqueFree 3 ∨ ¬(Gᶜ).CliqueFree 3 := by
  have hv_a : v ≠ a := fun h => by subst h; exact SimpleGraph.irrefl G ha
  have hv_b : v ≠ b := fun h => by subst h; exact SimpleGraph.irrefl G hb
  have hv_c : v ≠ c := fun h => by subst h; exact SimpleGraph.irrefl G hc
  by_cases p : G.Adj a b
  · exact Or.inl (not_cliqueFree_of_triangle hv_a hv_b hab ha hb p)
  by_cases q : G.Adj a c
  · exact Or.inl (not_cliqueFree_of_triangle hv_a hv_c hac ha hc q)
  by_cases r : G.Adj b c
  · exact Or.inl (not_cliqueFree_of_triangle hv_b hv_c hbc hb hc r)
  · refine Or.inr (fun hcf => hcf {a, b, c} ⟨isClique_triple (G := Gᶜ) hab hac hbc
      (SimpleGraph.compl_adj G a b |>.mpr ⟨hab, p⟩)
      (SimpleGraph.compl_adj G a c |>.mpr ⟨hac, q⟩)
      (SimpleGraph.compl_adj G b c |>.mpr ⟨hbc, r⟩),
      Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩⟩)

/-- Every graph on six vertices contains a triangle or an independent set of size three. -/
@[category API, AMS 5]
lemma isGraphRamsey_six : IsGraphRamsey 6 3 3 := by
  classical
  rintro G ⟨hcf3, hcf3c⟩
  set N : Finset (Fin 6) := Finset.univ.filter (G.Adj (0 : Fin 6)) with hNdef
  set M : Finset (Fin 6) := Finset.univ.filter (fun u => ¬G.Adj (0 : Fin 6) u ∧ u ≠ 0)
    with hMdef
  have hmemN : ∀ u, u ∈ N ↔ G.Adj (0 : Fin 6) u := by
    intro u; simp [hNdef]
  have hmemM : ∀ u, u ∈ M ↔ (¬G.Adj (0 : Fin 6) u ∧ u ≠ 0) := by
    intro u; simp [hMdef]
  have hun : N ∪ M = Finset.univ.erase (0 : Fin 6) := by
    ext u
    have hkey : (u ∈ N ∪ M ↔ u ∈ Finset.univ.erase (0 : Fin 6)) := by
      rw [Finset.mem_union, hmemN u, hmemM u, Finset.mem_erase]
      constructor
      · rintro (ha | ⟨ha, hne⟩)
        · have hv : (0 : Fin 6) ≠ u := fun h0 => by subst h0; exact SimpleGraph.irrefl G ha
          exact ⟨hv.symm, Finset.mem_univ u⟩
        · exact ⟨hne, Finset.mem_univ u⟩
      · rintro ⟨hne, hu0⟩
        rcases Classical.em (G.Adj (0 : Fin 6) u) with ha | ha
        · exact Or.inl ha
        · exact Or.inr ⟨ha, hne⟩
    exact hkey
  have hdj : Disjoint N M := by
    rw [Finset.disjoint_left]
    intro u hu huM
    exact ((hmemM u).mp huM).1 ((hmemN u).mp hu)
  have hcard : N.card + M.card = 5 := by
    have h1 := Finset.card_union_of_disjoint hdj
    rw [← h1, hun, Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin 6))]
    simp
  have h3 : 3 ≤ N.card ∨ 3 ≤ M.card := by omega
  rcases h3 with h | h
  · obtain ⟨S, hSN, hS3⟩ := Finset.exists_subset_card_eq h
    obtain ⟨a, b, c, hab, hac, hbc, hSab⟩ := Finset.card_eq_three.mp hS3
    subst hSab
    have ha' : G.Adj (0 : Fin 6) a := (hmemN a).mp (hSN (by simp))
    have hb' : G.Adj (0 : Fin 6) b := (hmemN b).mp (hSN (by simp))
    have hc' : G.Adj (0 : Fin 6) c := (hmemN c).mp (hSN (by simp))
    rcases three_neighbors_fan hab hac hbc ha' hb' hc' with h | h
    · exact h hcf3
    · exact h hcf3c
  · obtain ⟨S, hSM, hS3⟩ := Finset.exists_subset_card_eq h
    obtain ⟨a, b, c, hab, hac, hbc, hSab⟩ := Finset.card_eq_three.mp hS3
    subst hSab
    have mA : ¬G.Adj (0 : Fin 6) a ∧ a ≠ 0 := (hmemM a).mp (hSM (by simp))
    have mB : ¬G.Adj (0 : Fin 6) b ∧ b ≠ 0 := (hmemM b).mp (hSM (by simp))
    have mC : ¬G.Adj (0 : Fin 6) c ∧ c ≠ 0 := (hmemM c).mp (hSM (by simp))
    have na := (SimpleGraph.compl_adj G (0 : Fin 6) a).mpr ⟨mA.2.symm, mA.1⟩
    have nb := (SimpleGraph.compl_adj G (0 : Fin 6) b).mpr ⟨mB.2.symm, mB.1⟩
    have nc := (SimpleGraph.compl_adj G (0 : Fin 6) c).mpr ⟨mC.2.symm, mC.1⟩
    rcases three_neighbors_fan (G := Gᶜ) hab hac hbc na nb nc with h | h
    · exact h hcf3c
    · rw [compl_compl] at h
      exact h hcf3

/-- $R(3,3) = 6$. -/
@[category research solved, AMS 5]
theorem ramsey_number_three_three : R(3, 3) = 6 := by
  rw [classicalRamsey_eq_sInf]
  apply le_antisymm
  · exact Nat.sInf_le (Set.mem_ofPred_eq.mpr isGraphRamsey_six)
  · apply le_csInf ⟨6, Set.mem_ofPred_eq.mpr isGraphRamsey_six⟩
    intro m hm
    by_contra hlt
    have hmm : m ≤ 5 := by omega
    have e1 : ((SimpleGraph.cycleGraph 5).comap (Fin.castLEEmb hmm)).CliqueFree 3 :=
      SimpleGraph.CliqueFree.comap
        (SimpleGraph.Embedding.comap (Fin.castLEEmb hmm) (SimpleGraph.cycleGraph 5)).isContained
        cycleGraph_five_triangleFree.1
    have emb : ((SimpleGraph.cycleGraph 5).comap (Fin.castLEEmb hmm)) ↪g
        (SimpleGraph.cycleGraph 5) :=
      SimpleGraph.Embedding.comap (Fin.castLEEmb hmm) (SimpleGraph.cycleGraph 5)
    have embc : (((SimpleGraph.cycleGraph 5).comap (Fin.castLEEmb hmm))ᶜ) ↪g
        ((SimpleGraph.cycleGraph 5)ᶜ) :=
      (SimpleGraph.Embedding.complEquiv (G := (SimpleGraph.cycleGraph 5).comap (Fin.castLEEmb hmm))
        (H := SimpleGraph.cycleGraph 5)).toFun emb
    have e2 : (((SimpleGraph.cycleGraph 5).comap (Fin.castLEEmb hmm))ᶜ).CliqueFree 3 :=
      SimpleGraph.CliqueFree.comap embc.isContained cycleGraph_five_triangleFree.2
    have hnwit : ¬ IsGraphRamsey m 3 3 := fun hwit => hwit _ ⟨e1, e2⟩
    exact absurd hm hnwit

/-- $R(3,4) = 9$. -/
@[category research solved, AMS 5]
theorem ramsey_number_three_four : R(3, 4) = 9 := by
  sorry

/-- $R(3,5) = 14$. -/
@[category research solved, AMS 5]
theorem ramsey_number_three_five : R(3, 5) = 14 := by
  sorry

/-- $R(3,6) = 18$. -/
@[category research solved, AMS 5]
theorem ramsey_number_three_six : R(3, 6) = 18 := by
  sorry

/-- $R(3,7) = 23$. -/
@[category research solved, AMS 5]
theorem ramsey_number_three_seven : R(3, 7) = 23 := by
  sorry

/-- $R(3,8) = 28$. -/
@[category research solved, AMS 5]
theorem ramsey_number_three_eight : R(3, 8) = 28 := by
  sorry

/-- $R(3,9) = 36$ (Grinstead–Roberts). -/
@[category research solved, AMS 5]
theorem ramsey_number_three_nine : R(3, 9) = 36 := by
  sorry

/-- The diagonal Ramsey number $R(4,4) = 18$. -/
@[category research solved, AMS 5]
theorem ramsey_number_four_four : R(4, 4) = 18 := by
  sorry

/-- $R(4,5) = 25$ (McKay–Radziszowski). -/
@[category research solved, AMS 5]
theorem ramsey_number_four_five : R(4, 5) = 25 := by
  sorry

def ramsey_number_six_six.answer : ℕ := sorry

/--
The diagonal Ramsey number $R(6,6)$ is unknown. The best known bounds recorded in [Rad] are
$102 \le R(6,6) \le 165$.
-/
@[category research open, question value, AMS 5]
theorem ramsey_number_six_six : R(6, 6) = ramsey_number_six_six.answer := by
  sorry

/--
Lower bound $102 \le R(6,6)$, equivalently: there exists a graph on $101$ vertices with no
$6$-clique and no independent set of size $6$.
-/
@[category research solved, AMS 5]
theorem ramsey_number_six_six_lower_bound :
    ∃ G : SimpleGraph (Fin 101), G.CliqueFree 6 ∧ (Gᶜ).CliqueFree 6 := by
  sorry

/--
Upper bound $R(6,6) \le 165$, i.e. every graph on $165$ vertices contains a $6$-clique or an
independent set of size $6$.
-/
@[category research solved, AMS 5]
theorem ramsey_number_six_six_upper_bound :
    IsGraphRamsey 165 6 6 := by
  sorry

end RamseyNumbers
