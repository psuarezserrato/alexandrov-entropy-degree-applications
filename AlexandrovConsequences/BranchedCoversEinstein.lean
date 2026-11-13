import AlexandrovConsequences.Foundation

/-!
# Branched Coverings (Hamenstädt's Question) and Einstein $4$-Orbifold Obstructions

This file formalizes **Corollary 1.2** (`cor:hamenstadt-gen`) and **Corollary 1.3**
(`cor:einstein-obstruction`) of P. Suárez-Serrato, *"The entropy-degree theorem for Alexandrov
spaces"* (`arXiv:2606.30403`, §1.1 & §7.1–7.2).

## Main Results
1. **Corollary 1.2 (`cor:hamenstadt-gen`, Cyclic Branched Coverings of Hyperbolic Manifolds)**:
   - `branchedConeAngle`, `branchedCoverConeAngle_bounds`: For a cyclic $d$-fold branched cover
     $M_d \to M$ ($d \ge 2$), the quotient orbifold $X = M_d / \mathbb{Z}_d$ has cone angle
     $2\pi / d \le \pi < 2\pi$ along the codimension-2 branch locus $\Sigma$.
   - `hamenstadt_quotient_strict_volume_gap`: $\mathcal{H}^N(M_d / \mathbb{Z}_d) > \mathcal{H}^N(M)$
     for $N \ge 3, d \ge 2$ (equality would force $\mathcal{S}(X) = \emptyset$ by Theorem 1.1).
   - `hamenstadt_branched_cover_volume_gap`: $\mathrm{Vol}(M_d) > d \cdot \mathrm{Vol}(M)$.
2. **Corollary 1.3 (`cor:einstein-obstruction`, Obstructions to Negative Einstein $4$-Orbifolds)**:
   - `SatakeEinsteinFourOrbifoldData`: Satake Chern–Gauss–Bonnet bound
     $\mathrm{Vol}(X, g_E) \le \frac{4\pi^2}{3} \chi_{\mathrm{orb}}(X)$ and Bishop–Gromov entropy bound
     $h(\overline{X}) \le 3$ for $\mathrm{Ric}(g_E) = -3 g_E$, compared against a closed hyperbolic
     $4$-manifold $Y$ ($\mathrm{Vol}(Y) = \frac{4\pi^2}{3}\chi(Y)$, $h(\widetilde{Y}) = 3$).
   - `einstein_four_orbifold_euler_obstruction`: $\chi_{\mathrm{orb}}(X) \ge |\deg(f)| \, \chi(Y)$.
   - `einstein_four_orbifold_strict_euler_obstruction`: When $\mathcal{S}_X \neq \emptyset$ and
     $|\deg(f)| = [\pi_1(Y) : f_* \pi_1(X)] \ge 1$ (which automatically implies $\deg(f) \neq 0$),
     strict inequality $\chi_{\mathrm{orb}}(X) > |\deg(f)| \, \chi(Y)$ holds.
   - `gromov_thurston_branch_locus_euler_neg`: For $X = M_d / \mathbb{Z}_d$ ($d \ge 2$) via the
     orbifold Riemann–Hurwitz formula $\chi_{\mathrm{orb}}(X) = \chi(M) - (1 - 1/d)\chi(\Sigma)$,
     any Einstein metric $\mathrm{Ric} = -3 g_E$ forces $\chi(\Sigma) < 0$.
-/

noncomputable section

open MeasureTheory Set Filter RCDEntropyDegree.MetricMeasure RCDEntropyDegree.RCD

namespace AlexandrovConsequences

section BranchedCoveringsHamenstadt

/-- Normal cone angle $2\pi / d$ along the singular branch locus of the orbifold quotient
$X = M_d / \mathbb{Z}_d$ (`cor:hamenstadt-gen`, proof lines 1468–1473). -/
def branchedConeAngle (d : ℕ) : ℝ :=
  2 * Real.pi / (d : ℝ)

/-- **Cone Angle Bounds for Cyclic Branched Covers ($d \ge 2$)**:
For any $d \ge 2$, the transverse cone angle along the codimension-2 singular locus satisfies
$$\frac{2\pi}{d} \le \pi < 2\pi.$$ -/
theorem branchedCoverConeAngle_bounds {d : ℕ} (hd : 2 ≤ d) :
    branchedConeAngle d ≤ Real.pi ∧ branchedConeAngle d < 2 * Real.pi := by
  unfold branchedConeAngle
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hd_ge2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hpi : 0 < Real.pi := Real.pi_pos
  have hle : 2 * Real.pi / (d : ℝ) ≤ Real.pi := by
    rw [div_le_iff₀ hd_pos]
    nlinarith
  have hlt : 2 * Real.pi / (d : ℝ) < 2 * Real.pi := by
    linarith
  exact ⟨hle, hlt⟩

/-- Any point $x_0 \in X$ of a non-collapsed $\mathsf{RCD}(K, N)$ space whose Bishop–Gromov
density equals $\alpha / (2\pi)$ with $\alpha < 2\pi$ has density strictly less than $1$ and hence
lies outside the regular set $\mathcal{R}_N(X)$. -/
theorem not_mem_regularSet_of_coneAngle_lt_two_pi
    {X : Type*} [MetricSpace X] [MeasurableSpace X] {K : ℝ} {N : ℕ}
    (S : NonCollapsedRCDStructure X K N)
    {x₀ : X} {α : ℝ} (hα : α < 2 * Real.pi)
    (hdensity : S.density x₀ = α / (2 * Real.pi)) :
    x₀ ∈ S.regularSetᶜ := by
  have hlt1 : S.density x₀ < 1 := by
    rw [hdensity, div_lt_one (by linarith [Real.pi_pos])]
    exact hα
  intro hx_reg
  have heq1 : S.density x₀ = 1 := (S.mem_regularSet_iff_density_eq_one x₀).mp hx_reg
  linarith

/-- For a cyclic $d$-fold branched cover ($d \ge 2$) of a manifold along a nonempty codimension-2
submanifold $\Sigma$, the quotient Alexandrov space $X = M_d / \mathbb{Z}_d$ has nonempty singular
locus $\mathcal{S}_X \neq \emptyset$. -/
theorem branchedQuotient_singularSet_nonempty
    {X : Type*} {d : ℕ} (hd : 2 ≤ d) {S_X : Set X} {x₀ : X}
    (h_branch_sing : branchedConeAngle d < 2 * Real.pi → x₀ ∈ S_X) :
    S_X.Nonempty :=
  ⟨x₀, h_branch_sing (branchedCoverConeAngle_bounds hd).2⟩

/-- **Corollary 1.2 Part 1 (`cor:hamenstadt-gen`, Quotient Strict Volume Gap)**:
Let $M$ be a closed hyperbolic $N$-manifold ($N \ge 3$, $h(\widetilde{M}) = N - 1$), $d \ge 2$,
and $X = M_d / \mathbb{Z}_d$ be the Alexandrov quotient of a cyclic $d$-fold branched cover along a
nonempty codimension-2 submanifold $\Sigma$ equipped with a negatively curved metric
($0 \le h(\overline{X}) \le N - 1$) and degree-$1$ projection $f : X \to M$ ($|\deg(f)| = [\pi_1(M) : f_* \pi_1(X)] = 1$).
Because cone angle $2\pi/d < 2\pi$ forces $\mathcal{S}_X \neq \emptyset$, Theorem 1.1 yields strict
volume domination:
$$\mathcal{H}^N(M) < \mathcal{H}^N(M_d / \mathbb{Z}_d).$$ -/
theorem hamenstadt_quotient_strict_volume_gap
    {X : Type*} {N d : ℕ} (hN : 3 ≤ N) (hd : 2 ≤ d)
    {S_X : Set X} {x₀ : X}
    {h_Xbar vol_X vol_M : ℝ}
    (hh_Xbar_nonneg : 0 ≤ h_Xbar) (hh_Xbar_le : h_Xbar ≤ (N - 1 : ℝ))
    (hvol_X_nonneg : 0 ≤ vol_X)
    (h_branch_sing : branchedConeAngle d < 2 * Real.pi → x₀ ∈ S_X)
    (h_ineq : |((1 : ℤ) : ℝ)| * (N - 1 : ℝ) ^ N * vol_M ≤ h_Xbar ^ N * vol_X)
    (h_rigidity : h_Xbar ^ N * vol_X = |((1 : ℤ) : ℝ)| * (N - 1 : ℝ) ^ N * vol_M → S_X = ∅) :
    vol_M < vol_X := by
  have hS_ne : S_X.Nonempty := branchedQuotient_singularSet_nonempty hd h_branch_sing
  have hh0_pos : (0 : ℝ) < (N - 1 : ℝ) := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have h_strict : |((1 : ℤ) : ℝ)| * (N - 1 : ℝ) ^ N * vol_M < h_Xbar ^ N * vol_X :=
    strict_entropy_volume_of_singularSet_nonempty h_ineq hS_ne
      (le_refl 1) (by norm_num) h_rigidity
  have h_vol : |((1 : ℤ) : ℝ)| * vol_M < vol_X :=
    same_entropy_strict_volume_degree_bound hh0_pos hh_Xbar_nonneg hh_Xbar_le hvol_X_nonneg h_strict
  simpa using h_vol

/-- **Corollary 1.2 Part 2 (`cor:hamenstadt-gen`, Branched Cover Strict Volume Gap, `[Hamenstadt26]`)**:
Since $\mathbb{Z}_d$ acts isometrically on $M_d$ of degree $d$ so that $\mathrm{Vol}(M_d) = d \cdot \mathcal{H}^N(M_d / \mathbb{Z}_d)$,
we obtain
$$\mathrm{Vol}(M_d) > d \cdot \mathrm{Vol}(M).$$ -/
theorem hamenstadt_branched_cover_volume_gap
    {X : Type*} {N d : ℕ} (hN : 3 ≤ N) (hd : 2 ≤ d)
    {S_X : Set X} {x₀ : X}
    {h_Xbar vol_X vol_M vol_Md : ℝ}
    (hh_Xbar_nonneg : 0 ≤ h_Xbar) (hh_Xbar_le : h_Xbar ≤ (N - 1 : ℝ))
    (hvol_X_nonneg : 0 ≤ vol_X)
    (h_branch_sing : branchedConeAngle d < 2 * Real.pi → x₀ ∈ S_X)
    (h_ineq : |((1 : ℤ) : ℝ)| * (N - 1 : ℝ) ^ N * vol_M ≤ h_Xbar ^ N * vol_X)
    (h_rigidity : h_Xbar ^ N * vol_X = |((1 : ℤ) : ℝ)| * (N - 1 : ℝ) ^ N * vol_M → S_X = ∅)
    (h_cover_vol : vol_Md = (d : ℝ) * vol_X) :
    (d : ℝ) * vol_M < vol_Md := by
  have hgap : vol_M < vol_X :=
    hamenstadt_quotient_strict_volume_gap hN hd hh_Xbar_nonneg hh_Xbar_le hvol_X_nonneg
      h_branch_sing h_ineq h_rigidity
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  rw [h_cover_vol]
  exact mul_lt_mul_of_pos_left hgap hd_pos

end BranchedCoveringsHamenstadt

section EinsteinFourOrbifoldObstructions

/-- Chern–Gauss–Bonnet constant $4\pi^2 / 3 > 0$ linking volume and orbifold Euler characteristic
for negative Einstein $4$-orbifolds with $\mathrm{Ric}(g_E) = -3 g_E$. -/
def fourManifoldGaussBonnetConst : ℝ :=
  4 * Real.pi ^ 2 / 3

theorem fourManifoldGaussBonnetConst_pos : 0 < fourManifoldGaussBonnetConst := by
  unfold fourManifoldGaussBonnetConst
  have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  linarith

/-- **Satake–Chern–Gauss–Bonnet & Bishop–Gromov Data for Negative Einstein $4$-Orbifolds**
(`cor:einstein-obstruction`, §7.2):
Packages:
1. $0 \le h(\overline{X}) \le 3$ from Bishop–Gromov volume comparison for $\mathrm{Ric}(g_E) = -3 g_E$,
2. Satake's orbifold Chern–Gauss–Bonnet bound
   $\mathrm{Vol}(X, g_E) \le \frac{4\pi^2}{3} \chi_{\mathrm{orb}}(X)$ (since $|W|^2 \ge 0$ and $\mathrm{Ric}_0 = 0$),
3. Hyperbolic $4$-manifold target identity $\mathrm{Vol}(Y) = \frac{4\pi^2}{3} \chi(Y)$ ($W \equiv 0$,
   $h(\widetilde{Y}) = 3$). -/
structure SatakeEinsteinFourOrbifoldData where
  vol_X : ℝ
  vol_Y : ℝ
  χ_orb_X : ℝ
  χ_Y : ℝ
  h_Xbar : ℝ
  hvol_X_pos : 0 < vol_X
  hvol_Y_pos : 0 < vol_Y
  hh_Xbar_nonneg : 0 ≤ h_Xbar
  hh_Xbar_le : h_Xbar ≤ 3
  hsatake_X : vol_X ≤ fourManifoldGaussBonnetConst * χ_orb_X
  hsatake_Y : vol_Y = fourManifoldGaussBonnetConst * χ_Y

/-- **Corollary 1.3(a) (`cor:einstein-obstruction`, Orbifold Euler Characteristic Bound)**:
Under a continuous map $f : X \to Y$ from a closed oriented $4$-orbifold $X$ admitting an Einstein
metric $g_E$ with $\mathrm{Ric}(g_E) = -3 g_E$ to a closed hyperbolic $4$-manifold $Y$,
$$|\deg(f)| \, \chi(Y) \le \chi_{\mathrm{orb}}(X).$$ -/
theorem einstein_four_orbifold_euler_obstruction
    (D : SatakeEinsteinFourOrbifoldData) {deg_f : ℤ}
    (h_ineq : |(deg_f : ℝ)| * (3 : ℝ) ^ 4 * D.vol_Y ≤ D.h_Xbar ^ 4 * D.vol_X) :
    |(deg_f : ℝ)| * D.χ_Y ≤ D.χ_orb_X := by
  have hvol_ineq : |(deg_f : ℝ)| * D.vol_Y ≤ D.vol_X :=
    same_entropy_volume_degree_bound (by norm_num : (0 : ℝ) < 3)
      D.hh_Xbar_nonneg D.hh_Xbar_le D.hvol_X_pos.le h_ineq
  have hgb :
      |(deg_f : ℝ)| * (fourManifoldGaussBonnetConst * D.χ_Y) ≤
        fourManifoldGaussBonnetConst * D.χ_orb_X := by
    calc
      |(deg_f : ℝ)| * (fourManifoldGaussBonnetConst * D.χ_Y)
        = |(deg_f : ℝ)| * D.vol_Y := by rw [D.hsatake_Y]
      _ ≤ D.vol_X := hvol_ineq
      _ ≤ fourManifoldGaussBonnetConst * D.χ_orb_X := D.hsatake_X
  have hgb' :
      fourManifoldGaussBonnetConst * (|(deg_f : ℝ)| * D.χ_Y) ≤
        fourManifoldGaussBonnetConst * D.χ_orb_X := by
    linarith [hgb]
  exact le_of_mul_le_mul_left hgb' fourManifoldGaussBonnetConst_pos

/-- **Corollary 1.3(b) (`cor:einstein-obstruction`, Strict Orbifold Euler Gap for Non-Empty $\mathcal{S}_X$)**:
When $\mathcal{S}_X \neq \emptyset$ and $|\deg(f)| = [\pi_1(Y) : f_* \pi_1(X)] \ge 1$
(note $1 \le \mathrm{index}$ automatically forces $\deg(f) \neq 0$), Theorem 1.1 forbids equality, yielding
$$|\deg(f)| \, \chi(Y) < \chi_{\mathrm{orb}}(X).$$ -/
theorem einstein_four_orbifold_strict_euler_obstruction
    {X : Type*} {S_X : Set X}
    (D : SatakeEinsteinFourOrbifoldData) {deg_f : ℤ} {index_f : ℕ}
    (hS_ne : S_X.Nonempty)
    (hindex_pos : 1 ≤ index_f)
    (hindex_eq : |(deg_f : ℝ)| = (index_f : ℝ))
    (h_ineq : |(deg_f : ℝ)| * (3 : ℝ) ^ 4 * D.vol_Y ≤ D.h_Xbar ^ 4 * D.vol_X)
    (h_rigidity : D.h_Xbar ^ 4 * D.vol_X = |(deg_f : ℝ)| * (3 : ℝ) ^ 4 * D.vol_Y → S_X = ∅) :
    deg_f ≠ 0 ∧ |(deg_f : ℝ)| * D.χ_Y < D.χ_orb_X := by
  have hdeg_pos : 0 < |(deg_f : ℝ)| := by
    rw [hindex_eq]
    exact_mod_cast (Nat.succ_le_iff.mp hindex_pos)
  have hdeg_ne : deg_f ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero, abs_zero] at hdeg_pos
    exact lt_irrefl 0 hdeg_pos
  have h_strict_ent : |(deg_f : ℝ)| * (3 : ℝ) ^ 4 * D.vol_Y < D.h_Xbar ^ 4 * D.vol_X :=
    strict_entropy_volume_of_singularSet_nonempty h_ineq hS_ne hindex_pos hindex_eq h_rigidity
  have h_strict_vol : |(deg_f : ℝ)| * D.vol_Y < D.vol_X :=
    same_entropy_strict_volume_degree_bound (by norm_num : (0 : ℝ) < 3)
      D.hh_Xbar_nonneg D.hh_Xbar_le D.hvol_X_pos.le h_strict_ent
  have hgb :
      fourManifoldGaussBonnetConst * (|(deg_f : ℝ)| * D.χ_Y) <
        fourManifoldGaussBonnetConst * D.χ_orb_X := by
    calc
      fourManifoldGaussBonnetConst * (|(deg_f : ℝ)| * D.χ_Y)
        = |(deg_f : ℝ)| * D.vol_Y := by rw [D.hsatake_Y]; ring
      _ < D.vol_X := h_strict_vol
      _ ≤ fourManifoldGaussBonnetConst * D.χ_orb_X := D.hsatake_X
  exact ⟨hdeg_ne, lt_of_mul_lt_mul_left hgb fourManifoldGaussBonnetConst_pos.le⟩

/-- **Corollary 1.3(c) (`cor:einstein-obstruction`, Gromov–Thurston Branch-Locus Euler Obstruction)**:
If $X = M_d / \mathbb{Z}_d$ ($d \ge 2$) is the cyclic branched orbifold quotient of a hyperbolic
$4$-manifold $M$ along an embedded closed surface $\Sigma \subset M$, then by the orbifold
Riemann–Hurwitz formula $\chi_{\mathrm{orb}}(X) = \chi(M) - (1 - 1/d)\chi(\Sigma)$, any Einstein
metric $g_E$ on $X$ with $\mathrm{Ric}(g_E) = -3 g_E$ satisfies
$$\chi(\Sigma) < 0.$$ -/
theorem gromov_thurston_branch_locus_euler_neg
    {X : Type*} {d : ℕ} (hd : 2 ≤ d)
    {S_X : Set X} {x₀ : X}
    (D : SatakeEinsteinFourOrbifoldData)
    {χ_Sigma : ℝ}
    (h_branch_sing : branchedConeAngle d < 2 * Real.pi → x₀ ∈ S_X)
    (h_ineq : |((1 : ℤ) : ℝ)| * (3 : ℝ) ^ 4 * D.vol_Y ≤ D.h_Xbar ^ 4 * D.vol_X)
    (h_rigidity : D.h_Xbar ^ 4 * D.vol_X = |((1 : ℤ) : ℝ)| * (3 : ℝ) ^ 4 * D.vol_Y → S_X = ∅)
    (h_riemann_hurwitz : D.χ_orb_X = D.χ_Y - (1 - 1 / (d : ℝ)) * χ_Sigma) :
    χ_Sigma < 0 := by
  have hS_ne : S_X.Nonempty := branchedQuotient_singularSet_nonempty hd h_branch_sing
  have hstrict :=
    (einstein_four_orbifold_strict_euler_obstruction D hS_ne
      (le_refl 1) (by norm_num) h_ineq h_rigidity).2
  have hχ : D.χ_Y < D.χ_orb_X := by simpa using hstrict
  have hcoeff_pos : 0 < 1 - 1 / (d : ℝ) := by
    have hd_ge2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hdiv : 1 / (d : ℝ) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hd_ge2
    linarith
  have hneg_mul : (1 - 1 / (d : ℝ)) * (-χ_Sigma) > 0 := by
    linarith [hχ, h_riemann_hurwitz]
  nlinarith

end EinsteinFourOrbifoldObstructions

end AlexandrovConsequences
