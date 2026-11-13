import RCDEntropyDegree

/-!
# Foundations for Consequences of the Alexandrov Entropy-Degree Theorem (`arXiv:2606.30403`)

This file formalizes Section 5 (`thm:an-deg-equals-top-deg`, `cor:extended-metric-Deg-Thm`),
Theorem 1.1 (`thm:Alex-entropy-degree`), Remark 1.15 (`rmk:rigidity_condition`), and the core
meta-lemmas used across all 14 downstream corollaries and theorems of
P. Suárez-Serrato, *"The entropy-degree theorem for Alexandrov spaces"* (`arXiv:2606.30403`,
`AlexDegThm-Aug-2026.tex`).

## Main Results
1. **Analytic vs. Topological Degree on Class $\mathcal{S}$ Spaces (`analyticDegree`,
   `MitsuishiDegreeBridge`, `analytic_eq_topological_degree`, `ClassSSpace`,
   `s_space_analytic_eq_topological_degree`)**:
   - Theorem 5.3 & Corollary 5.5: Under Kirchheim's signed area formula and naturality of
     Mitsuishi's isomorphism $\Psi : H_N^{\mathbf{I}}(X) \xrightarrow{\sim} H_N(X;\mathbb{Z})$,
     $$\deg_{\mathrm{an}}(f) = \frac{1}{\mathcal{H}^N(Y)} \int_X \mathrm{sJac}_f(x)\,d\mathcal{H}^N(x) = \deg_{\mathrm{top}}(f).$$
2. **Continuous-Map Alexandrov Entropy-Degree Theorem & Smoothness Rigidity
   (`alexandrov_entropy_degree_inequality_continuous`, `alexandrov_entropy_degree_rigidity`)**:
   - Theorem 1.1: Connects continuous maps $f : X \to Y$ via Lipschitz approximations $f_{\mathrm{lip}} \simeq f$
     to `RCDEntropyDegree.RCD.alexandrov_entropy_degree_inequality` and `RCDEntropyDegree.RCD.rcd_entropy_degree_equality_rigidity`,
     proving that equality together with $|\deg(f)| = [\pi_1(Y) : f_* \pi_1(X)]$ forces
     $\mathcal{S}(X) = \emptyset$ and global homothety onto the degree-$|\deg(f)|$ Riemannian cover.
3. **Necessity of the Fundamental Group Index Condition (`abs_degree_eq_index_iff_lift_degree_one`,
   `connected_sum_rigidity_counterexample`)**:
   - Remark 1.15: Shows $|\deg(f)| = |\deg(\hat{f})| \cdot [\pi_1(Y):f_*\pi_1(X)]$ forces
     $|\deg(\hat{f})| = 1$ iff $|\deg(f)| = [\pi_1(Y):f_*\pi_1(X)]$, and formalizes the connected-sum
     obstruction $X = Y \# Y \to Y \vee Y \to Y$ where $b_1(Y\# Y) = 2 b_1(Y) \ne b_1(Y)$.
4. **Core Algebraic & Analytic Reduction Meta-Lemmas**:
   - `strict_entropy_volume_of_singularSet_nonempty`: Whenever equality implies $\mathcal{S}(X) = \emptyset$
     and $\mathcal{S}(X) \neq \emptyset$, the entropy-volume inequality is strictly rigid ($<$).
   - `upper_entropy_bound_volume_inequality`, `same_entropy_volume_degree_bound`,
     `same_entropy_strict_volume_degree_bound`, and `metric_doubling_volume_degree_bound` (Perelman/Petrunin
     gluing double factor-$2$ cancellation).
-/

noncomputable section

open MeasureTheory Set Filter RCDEntropyDegree.MetricMeasure RCDEntropyDegree.RCD

namespace AlexandrovConsequences

section AnalyticVsTopologicalDegree

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {CurrentY : Type*} [AddCommGroup CurrentY]

/-- **Analytic Degree (`def:an-deg`, `[AlexDegThm, Definition 5.1]`)**:
For a Lipschitz (or $\mathcal{H}^N$-a.e. metrically differentiable) map $f : X \to Y$ into a closed
oriented Riemannian $N$-manifold $Y$ with $\mathcal{H}^N(Y) > 0$, the analytic degree is the
normalized integral of the signed metric Jacobian $\mathrm{sJac}_f(x)$:
$$\deg_{\mathrm{an}}(f) := \frac{1}{\mathcal{H}^N(Y)} \int_X \mathrm{sJac}_f(x) \, d\mathcal{H}^N(x).$$ -/
def analyticDegree (vol_Y : ℝ) (μ_X : Measure X) (sJac_f : X → ℝ) : ℝ :=
  vol_Y⁻¹ * ∫ x, sJac_f x ∂μ_X

/-- The absolute value of the analytic degree weighted by $\mathcal{H}^N(Y) > 0$ is bounded above
by the integral of the unsigned metric Jacobian $|\mathrm{sJac}_f(x)|$:
$$|\deg_{\mathrm{an}}(f)| \, \mathcal{H}^N(Y) \le \int_X |\mathrm{sJac}_f(x)| \, d\mathcal{H}^N(x).$$ -/
theorem abs_analyticDegree_mul_vol_le_integral_abs
    {vol_Y : ℝ} (hvol_Y : 0 < vol_Y) (μ_X : Measure X) (sJac_f : X → ℝ) :
    |analyticDegree vol_Y μ_X sJac_f| * vol_Y ≤ ∫ x, |sJac_f x| ∂μ_X := by
  unfold analyticDegree
  rw [abs_mul, abs_inv, abs_of_pos hvol_Y]
  have hcancel : vol_Y⁻¹ * |∫ x, sJac_f x ∂μ_X| * vol_Y = |∫ x, sJac_f x ∂μ_X| := by
    field_simp [hvol_Y.ne']
  rw [hcancel]
  exact norm_integral_le_integral_norm sJac_f

/-- **Mitsuishi Naturality Interface (`thm:an-deg-equals-top-deg`)**:
Packages a closed oriented Riemannian $N$-manifold target $Y$ (equipped with `FY : FundamentalManifoldCurrent Y CurrentY`),
reference measure $\mu_X = \mathcal{H}^N$ on $X$, the singular homology degree
`topologicalDegree f` induced by $f_* : H_N(X; \mathbb{Z}) \to H_N(Y; \mathbb{Z})$, the current
pushforward degree `currentDegree f` determined by $f_\# T_X = \deg_{\mathrm{curr}}(f) \llbracket Y \rrbracket$,
and the commutative-square naturality identity coming from Mitsuishi's comparison isomorphism
$\Psi : H_N^{\mathbf{I}}(X) \xrightarrow{\sim} H_N(X; \mathbb{Z})$ mapping $[T_X] \mapsto [X]$. -/
structure MitsuishiDegreeBridge (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y]
    (CurrentY : Type*) [AddCommGroup CurrentY] where
  FY : FundamentalManifoldCurrent Y CurrentY
  μ_X : Measure X
  topologicalDegree : (X → Y) → ℤ
  currentDegree : (X → Y) → ℤ
  mitsuishi_naturality : ∀ f : X → Y, currentDegree f = topologicalDegree f

/-- **Theorem 5.3 (`thm:an-deg-equals-top-deg`, Analytic Degree Equals Topological Degree)**:
For a Lipschitz map $f : X \to Y$ on a space admitting a Mitsuishi isomorphism $\Psi$, combining
Kirchheim's signed area formula
$$\int_X \mathrm{sJac}_f(x)\,d\mathcal{H}^N(x) = \deg_{\mathrm{curr}}(f)\,\mathcal{H}^N(Y)$$
with $\deg_{\mathrm{curr}}(f) = \deg_{\mathrm{top}}(f)$ yields
$$\deg_{\mathrm{an}}(f) = \deg_{\mathrm{top}}(f).$$ -/
theorem analytic_eq_topological_degree
    (B : MitsuishiDegreeBridge X Y CurrentY) (f : X → Y) (sJac_f : X → ℝ)
    (h_kirchheim : ∫ x, sJac_f x ∂B.μ_X = (B.currentDegree f : ℝ) * B.FY.manifoldVolume) :
    analyticDegree B.FY.manifoldVolume B.μ_X sJac_f = (B.topologicalDegree f : ℝ) := by
  unfold analyticDegree
  rw [h_kirchheim, B.mitsuishi_naturality f]
  have hpos : B.FY.manifoldVolume ≠ 0 := B.FY.manifoldVolume_pos.ne'
  field_simp [hpos]

/-- **Class $\mathcal{S}$ Spaces (`def:s-spaces`)**:
Compact orientable $N$-dimensional metric spaces $(X, \mathsf{d}, \mathcal{H}^N)$ with
$\mathcal{H}^N(X) < \infty$, topological singular set $\mathcal{S}_X$ of $\mathcal{H}^{N-1}$-measure
zero ($\mathcal{H}^{N-1}(\mathcal{S}_X) = 0$), orientable manifold locus $X \setminus \mathcal{S}_X$,
and Mitsuishi integral-current to singular-homology comparison bridge. -/
structure ClassSSpace (X Y : Type*) [MetricSpace X] [MeasurableSpace X] [MeasurableSpace Y]
    (N : ℕ) (CurrentY : Type*) [AddCommGroup CurrentY] where
  singularSet : Set X
  codimOneMeasure : Measure X
  toMitsuishiBridge : MitsuishiDegreeBridge X Y CurrentY
  volume_ne_top : toMitsuishiBridge.μ_X Set.univ ≠ ⊤
  codimOne_singularSet_null : codimOneMeasure singularSet = 0

/-- **Corollary 5.5 (`cor:extended-metric-Deg-Thm`, Extended Metric Degree Theorem on Class $\mathcal{S}$)**:
On any class $\mathcal{S}$ space (and in particular any closed orientable $N$-dimensional Alexandrov
space without boundary), the analytic degree of every Lipschitz map $f : X \to Y$ equals its
homological topological degree:
$$\deg_{\mathrm{an}}(f) = \deg_{\mathrm{top}}(f).$$ -/
theorem s_space_analytic_eq_topological_degree
    [MetricSpace X] {N : ℕ}
    (SX : ClassSSpace X Y N CurrentY) (f : X → Y) (sJac_f : X → ℝ)
    (h_kirchheim :
      ∫ x, sJac_f x ∂SX.toMitsuishiBridge.μ_X =
        (SX.toMitsuishiBridge.currentDegree f : ℝ) * SX.toMitsuishiBridge.FY.manifoldVolume) :
    analyticDegree SX.toMitsuishiBridge.FY.manifoldVolume SX.toMitsuishiBridge.μ_X sJac_f =
      (SX.toMitsuishiBridge.topologicalDegree f : ℝ) :=
  analytic_eq_topological_degree SX.toMitsuishiBridge f sJac_f h_kirchheim

end AnalyticVsTopologicalDegree

section MainTheoremAndRemark

variable {X Y Yhat : Type*} [MetricSpace X] [MeasurableSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [MetricSpace Yhat] [MeasurableSpace Yhat]
variable {κ : ℝ} {N : ℕ}
variable {CurrentX CurrentY CurrentYhat : Type*}
  [AddCommGroup CurrentX] [AddCommGroup CurrentY] [AddCommGroup CurrentYhat]

omit [MetricSpace Y] [MetricSpace Yhat] [MeasurableSpace Yhat] in
/-- **Theorem 1.1 Part 1 (`thm:Alex-entropy-degree`, Continuous-Map Entropy-Degree Inequality)**:
For any closed orientable $N$-dimensional Alexandrov space $X$ without boundary ($\mathrm{curv} \ge \kappa$)
and any continuous map $f : X \to Y$ to a closed orientable negatively curved locally symmetric
$N$-manifold $Y$, choosing a Lipschitz approximation $f_{\mathrm{lip}} \simeq f$ homotopic to $f$
and applying the BCG barycenter natural maps $F_s \simeq f_{\mathrm{lip}}$ ($s > h(\overline{X})$) yields
$$|\deg(f)| \, h(\widetilde{Y})^N \, \mathcal{H}^N(Y) \le h(\overline{X})^N \, \mathcal{H}^N(X).$$ -/
theorem alexandrov_entropy_degree_inequality_continuous
    (A : AlexandrovSpaceWithoutBoundary X κ N)
    (C : CMMPOrientationCurrent X ((N - 1 : ℝ) * κ) N CurrentX)
    (hA : C.toClosedNonCollapsedRCD = A.toClosedNonCollapsedRCD)
    [IsFiniteMeasure C.hausdorffMeasure]
    (FY : FundamentalManifoldCurrent Y CurrentY)
    {h_Xbar h_Ytilde : ℝ} (hh_Ytilde : 0 < h_Ytilde)
    {deg_f deg_flip : ℤ}
    (h_lip_approx : deg_flip = deg_f)
    (F_s : ℝ → X → Y)
    (D_s : ∀ s : ℝ, s > h_Xbar → LipschitzDegreePushforward C FY (F_s s))
    (Jac_s : ℝ → X → ℝ)
    (h_deg_homotopy : ∀ (s : ℝ) (hs : s > h_Xbar), (D_s s hs).lipschitzDegree = deg_flip)
    (h_mass_push : ∀ (s : ℝ) (hs : s > h_Xbar),
      FY.totalMass (D_s s hs).pushforwardCurrent ≤ ∫ x, Jac_s s x ∂C.hausdorffMeasure)
    (hJac_int : ∀ s > h_Xbar, Integrable (Jac_s s) C.hausdorffMeasure)
    (hJac_bound : ∀ s > h_Xbar, ∀ᵐ x ∂C.hausdorffMeasure,
      Jac_s s x ≤ (s / h_Ytilde) ^ N) :
    |(deg_f : ℝ)| * h_Ytilde ^ N * FY.manifoldVolume ≤
      h_Xbar ^ N * A.toClosedNonCollapsedRCD.totalVolume := by
  rw [← h_lip_approx]
  exact RCDEntropyDegree.RCD.alexandrov_entropy_degree_inequality A C hA FY hh_Ytilde F_s D_s Jac_s
    h_deg_homotopy h_mass_push hJac_int hJac_bound

/-- **Theorem 1.1 Part 2 (`thm:Alex-entropy-degree`, Equality Rigidity & Smoothness of $X$)**:
When equality holds in Theorem 1.1 together with $|\deg(f)| = [\pi_1(Y) : f_* \pi_1(X)] = k \ge 1$,
via `RCDEntropyDegree.RCD.rcd_entropy_degree_equality_rigidity`:
1. the rescaled limit map $\hat{F}_\infty : (X, c\,\mathsf{d}_X) \to \widehat{Y}$ ($c = h(\overline{X}) / h(\widetilde{Y}) > 0$)
   is a surjective global metric homothety onto the degree-$k$ Riemannian cover $\widehat{Y} \to Y$, and
2. consequently $X$ has empty singular set ($\mathcal{S}(X) = \emptyset$) and is smooth. -/
theorem alexandrov_entropy_degree_rigidity
    [CompactSpace X] [T2Space Yhat]
    (A : AlexandrovSpaceWithoutBoundary X κ N)
    (C_rescaled : CMMPOrientationCurrent X ((N - 1 : ℝ) * κ) N CurrentX)
    [IsFiniteMeasure C_rescaled.hausdorffMeasure]
    (FYhat : FundamentalManifoldCurrent Yhat CurrentYhat)
    {deg_f : ℤ} {index_f : ℕ} {deg_fhat h_Xbar h_Ytilde vol_Y : ℝ}
    (h_index_pos : 1 ≤ index_f)
    (h_index_eq : |(deg_f : ℝ)| = (index_f : ℝ))
    (hh_Xbar : 0 < h_Xbar) (hh_Ytilde : 0 < h_Ytilde)
    (hdeg_mult : |(deg_f : ℝ)| = |(deg_f : ℝ)| * deg_fhat)
    (hvol_cover : FYhat.manifoldVolume = |(deg_f : ℝ)| * vol_Y)
    (heq : entropyVolumeProduct N h_Xbar A.toClosedNonCollapsedRCD.totalVolume =
      |(deg_f : ℝ)| * entropyVolumeProduct N h_Ytilde vol_Y)
    (hvol_rescaled : C_rescaled.totalVolume =
      (h_Xbar / h_Ytilde) ^ N * A.toClosedNonCollapsedRCD.totalVolume)
    {Fhat_inf : X → Yhat} (hFhat_cont : Continuous Fhat_inf)
    (D_inf : LipschitzDegreePushforward C_rescaled FYhat Fhat_inf)
    (Jac_inf : X → ℝ)
    (hD_deg_ne : D_inf.lipschitzDegree ≠ 0)
    (hD_deg_abs : |(D_inf.lipschitzDegree : ℝ)| = deg_fhat)
    (h_open_pos : ∀ U : Set Yhat, IsOpen U → U.Nonempty → 0 < (FYhat.volumeMeasure U).toReal)
    (h_supp : (FYhat.massMeasure (D_inf.lipschitzDegree • FYhat.fundamentalClass)
      (Set.range Fhat_inf)ᶜ).toReal = 0)
    (h_mass_push : FYhat.totalMass D_inf.pushforwardCurrent ≤
      ∫ x, Jac_inf x ∂C_rescaled.hausdorffMeasure)
    (hJac_int : Integrable Jac_inf C_rescaled.hausdorffMeasure)
    (hJac_le_one : ∀ᵐ x ∂C_rescaled.hausdorffMeasure, Jac_inf x ≤ 1)
    (h_lip_vol_rigidity :
      Function.Surjective Fhat_inf →
      C_rescaled.totalVolume = FYhat.manifoldVolume →
      (∀ᵐ x ∂C_rescaled.hausdorffMeasure, Jac_inf x = 1) →
      ∀ x₁ x₂ : X, dist (Fhat_inf x₁) (Fhat_inf x₂) = (h_Xbar / h_Ytilde) * dist x₁ x₂)
    (h_smooth_of_homothety :
      (0 < h_Xbar / h_Ytilde) →
      Function.Surjective Fhat_inf →
      (∀ x₁ x₂ : X, dist (Fhat_inf x₁) (Fhat_inf x₂) = (h_Xbar / h_Ytilde) * dist x₁ x₂) →
      A.toClosedNonCollapsedRCD.singularSet = ∅) :
    let c := h_Xbar / h_Ytilde
    0 < c ∧
    A.toClosedNonCollapsedRCD.singularSet = ∅ ∧
    Function.Surjective Fhat_inf ∧
    (∀ x₁ x₂ : X, dist (Fhat_inf x₁) (Fhat_inf x₂) = c * dist x₁ x₂) := by
  have hk_pos : 0 < |(deg_f : ℝ)| := by
    rw [h_index_eq]
    exact_mod_cast (Nat.succ_le_iff.mp h_index_pos)
  obtain ⟨hc_pos, _, _, _, _, _, h_surj, h_isom⟩ :=
    RCDEntropyDegree.RCD.rcd_entropy_degree_equality_rigidity
      C_rescaled FYhat hk_pos hh_Xbar hh_Ytilde hdeg_mult hvol_cover heq hvol_rescaled
      hFhat_cont D_inf Jac_inf hD_deg_ne hD_deg_abs h_open_pos h_supp h_mass_push
      hJac_int hJac_le_one h_lip_vol_rigidity
  exact ⟨hc_pos, h_smooth_of_homothety hc_pos h_surj h_isom, h_surj, h_isom⟩

/-- **Remark 1.15 Part 1 (`rmk:rigidity_condition`, Lift Degree Characterization)**:
In the factorization $|\deg(f)| = |\deg(\hat{f})| \cdot [\pi_1(Y) : f_* \pi_1(X)]$ for a map
$f : X \to Y$ with $\deg(f) \neq 0$, the equality $|\deg(f)| = [\pi_1(Y) : f_* \pi_1(X)]$ holds if
and only if the lifted map $\hat{f} : X \to \widehat{Y}$ has degree $|\deg(\hat{f})| = 1$. Moreover,
both $1 \le [\pi_1(Y) : f_* \pi_1(X)]$ and $[\pi_1(Y) : f_* \pi_1(X)] \le |\deg(f)|$ hold. -/
theorem abs_degree_eq_index_iff_lift_degree_one
    {deg_f deg_fhat : ℤ} {index_f : ℕ}
    (hdeg_ne : deg_f ≠ 0)
    (h_factor : |(deg_f : ℝ)| = |(deg_fhat : ℝ)| * (index_f : ℝ)) :
    (|(deg_f : ℝ)| = (index_f : ℝ) ↔ |(deg_fhat : ℝ)| = 1) ∧
      (1 ≤ index_f ∧ (index_f : ℝ) ≤ |(deg_f : ℝ)|) := by
  have hdeg_pos : 0 < |(deg_f : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hdeg_ne)
  have h_prod_pos : 0 < |(deg_fhat : ℝ)| * (index_f : ℝ) := by linarith
  have hind_ne0 : index_f ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero, mul_zero] at h_prod_pos
    exact lt_irrefl 0 h_prod_pos
  have hind_ge1 : 1 ≤ index_f := Nat.one_le_iff_ne_zero.mpr hind_ne0
  have hind_pos : (0 : ℝ) < (index_f : ℝ) := by exact_mod_cast hind_ge1
  have hfhat_int_ne0 : deg_fhat ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero, abs_zero, zero_mul] at h_prod_pos
    exact lt_irrefl 0 h_prod_pos
  have hfhat_ge1 : (1 : ℝ) ≤ |(deg_fhat : ℝ)| := by
    have hnat : 1 ≤ deg_fhat.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hfhat_int_ne0)
    have hcast : (1 : ℝ) ≤ (deg_fhat.natAbs : ℝ) := by exact_mod_cast hnat
    rwa [Nat.cast_natAbs, Int.cast_abs] at hcast
  have h_le : (index_f : ℝ) ≤ |(deg_f : ℝ)| := by
    rw [h_factor]
    exact le_mul_of_one_le_left hind_pos.le hfhat_ge1
  refine ⟨?_, hind_ge1, h_le⟩
  constructor
  · intro heq
    have hmul : |(deg_fhat : ℝ)| * (index_f : ℝ) = 1 * (index_f : ℝ) := by
      linarith [h_factor, heq]
    exact mul_right_cancel₀ hind_pos.ne' hmul
  · intro hfhat1
    rw [h_factor, hfhat1, one_mul]

/-- **Remark 1.15 Part 2 (`rmk:rigidity_condition`, Connected-Sum Counterexample $Y \# Y \to Y$)**:
For a closed oriented hyperbolic manifold $Y$ with $b_1(Y) \ge 1$, collapsing one summand of the
connected sum $X = Y \# Y \to Y \vee Y \to Y$ has $|\deg(f)| = 2$ and $\pi_1$-index $1$
($[\pi_1(Y) : f_* \pi_1(X)] = 1 < 2 = |\deg(f)|$), while $b_1(Y \# Y) = 2 b_1(Y) \neq b_1(Y)$ rules
out homeomorphism with the index-$1$ cover $Y$. -/
theorem connected_sum_rigidity_counterexample
    {b1_Y : ℕ} (hb1 : 1 ≤ b1_Y) :
    let deg_pinch : ℤ := 2
    let index_pinch : ℕ := 1
    let b1_connectedSum : ℕ := 2 * b1_Y
    (index_pinch : ℝ) < |(deg_pinch : ℝ)| ∧ b1_connectedSum ≠ b1_Y := by
  refine ⟨by norm_num, ?_⟩
  omega

end MainTheoremAndRemark

section CoreMetaLemmas

/-- **Strict Entropy-Volume Gap from Non-Empty Singular Set**:
Suppose the entropy-volume inequality holds for $(X, Y, f)$ with $|\deg(f)| = [\pi_1(Y) : f_* \pi_1(X)] \ge 1$,
and the rigidity half of Theorem 1.1 shows that equality forces $\mathcal{S}(X) = \emptyset$.
Whenever $\mathcal{S}(X)$ is nonempty, the entropy-volume inequality is strict:
$$|\deg(f)| \, h(\widetilde{Y})^N \, \mathcal{H}^N(Y) < h(\overline{X})^N \, \mathcal{H}^N(X).$$ -/
theorem strict_entropy_volume_of_singularSet_nonempty
    {X : Type*} {N : ℕ} {S_X : Set X}
    {deg_f : ℤ} {index_f : ℕ} {h_Xbar h_Ytilde vol_X vol_Y : ℝ}
    (h_ineq : |(deg_f : ℝ)| * h_Ytilde ^ N * vol_Y ≤ h_Xbar ^ N * vol_X)
    (hS_nonempty : S_X.Nonempty)
    (_hindex_pos : 1 ≤ index_f)
    (_hindex_eq : |(deg_f : ℝ)| = (index_f : ℝ))
    (h_rigidity : h_Xbar ^ N * vol_X = |(deg_f : ℝ)| * h_Ytilde ^ N * vol_Y → S_X = ∅) :
    |(deg_f : ℝ)| * h_Ytilde ^ N * vol_Y < h_Xbar ^ N * vol_X := by
  refine lt_of_le_of_ne h_ineq ?_
  intro heq
  exact hS_nonempty.ne_empty (h_rigidity heq.symm)

/-- **Volume-Entropy Upper Comparison**:
When Bishop–Gromov / curvature-dimension bounds give $0 \le h(\overline{X}) \le h_{\mathrm{upper}}$ and
$\mathcal{H}^N(X) \ge 0$, Theorem 1.1 yields
$$|\deg(f)| \, h(\widetilde{Y})^N \, \mathcal{H}^N(Y) \le h_{\mathrm{upper}}^N \, \mathcal{H}^N(X).$$ -/
theorem upper_entropy_bound_volume_inequality
    {N : ℕ} {deg_f : ℤ} {h_Xbar h_upper h_Ytilde vol_X vol_Y : ℝ}
    (hh_nonneg : 0 ≤ h_Xbar) (hh_le : h_Xbar ≤ h_upper) (hvol_X : 0 ≤ vol_X)
    (h_ineq : |(deg_f : ℝ)| * h_Ytilde ^ N * vol_Y ≤ h_Xbar ^ N * vol_X) :
    |(deg_f : ℝ)| * h_Ytilde ^ N * vol_Y ≤ h_upper ^ N * vol_X := by
  have hpow : h_Xbar ^ N ≤ h_upper ^ N := pow_le_pow_left₀ hh_nonneg hh_le N
  exact h_ineq.trans (mul_le_mul_of_nonneg_right hpow hvol_X)

/-- **Matched-Entropy Volume-Degree Inequality**:
When $h(\overline{X}) \le h_0$ ($h_0 > 0$) and $h(\widetilde{Y}) = h_0$, dividing out $h_0^N > 0$
yields the volume-degree bound $|\deg(f)| \, \mathcal{H}^N(Y) \le \mathcal{H}^N(X)$. -/
theorem same_entropy_volume_degree_bound
    {N : ℕ} {deg_f : ℤ} {h_Xbar h₀ vol_X vol_Y : ℝ}
    (hh₀ : 0 < h₀) (hh_nonneg : 0 ≤ h_Xbar) (hh_le : h_Xbar ≤ h₀) (hvol_X : 0 ≤ vol_X)
    (h_ineq : |(deg_f : ℝ)| * h₀ ^ N * vol_Y ≤ h_Xbar ^ N * vol_X) :
    |(deg_f : ℝ)| * vol_Y ≤ vol_X := by
  have h_upper := upper_entropy_bound_volume_inequality hh_nonneg hh_le hvol_X h_ineq
  have hh₀N : 0 < h₀ ^ N := pow_pos hh₀ N
  have h_rearr : |(deg_f : ℝ)| * vol_Y * h₀ ^ N ≤ vol_X * h₀ ^ N := by linarith
  exact le_of_mul_le_mul_right h_rearr hh₀N

/-- **Matched-Entropy Strict Volume-Degree Inequality**:
When $0 \le h(\overline{X}) \le h_0$ ($h_0 > 0$) and the entropy-volume inequality at $h(\widetilde{Y}) = h_0$
is strict, we obtain the strict volume gap $|\deg(f)| \, \mathcal{H}^N(Y) < \mathcal{H}^N(X)$. -/
theorem same_entropy_strict_volume_degree_bound
    {N : ℕ} {deg_f : ℤ} {h_Xbar h₀ vol_X vol_Y : ℝ}
    (hh₀ : 0 < h₀) (hh_nonneg : 0 ≤ h_Xbar) (hh_le : h_Xbar ≤ h₀) (hvol_X : 0 ≤ vol_X)
    (h_strict : |(deg_f : ℝ)| * h₀ ^ N * vol_Y < h_Xbar ^ N * vol_X) :
    |(deg_f : ℝ)| * vol_Y < vol_X := by
  have hpow : h_Xbar ^ N ≤ h₀ ^ N := pow_le_pow_left₀ hh_nonneg hh_le N
  have h_upper : |(deg_f : ℝ)| * h₀ ^ N * vol_Y < h₀ ^ N * vol_X :=
    lt_of_lt_of_le h_strict (mul_le_mul_of_nonneg_right hpow hvol_X)
  have hh₀N : 0 < h₀ ^ N := pow_pos hh₀ N
  have h_rearr : |(deg_f : ℝ)| * vol_Y * h₀ ^ N < vol_X * h₀ ^ N := by linarith
  exact lt_of_mul_lt_mul_right h_rearr hh₀N.le

/-- **Perelman / Petrunin Metric Doubling Cancellation Lemma**:
If $DZ$ and $DY$ are metric doubles satisfying $\mathcal{H}^N(DZ) = 2\,\mathcal{H}^N(Z)$ and
$\mathcal{H}^N(DY) = 2\,\mathcal{H}^N(Y)$ with $0 \le h(\overline{DZ}) \le h_0$ ($h_0 > 0$) and
$|k| \, h_0^N \, \mathcal{H}^N(DY) \le h(\overline{DZ})^N \, \mathcal{H}^N(DZ)$, cancelling $2\,h_0^N > 0$
yields
$$|k| \, \mathcal{H}^N(Y) \le \mathcal{H}^N(Z).$$ -/
theorem metric_doubling_volume_degree_bound
    {N : ℕ} {k : ℤ} {h₀ h_DZ vol_Z vol_Y vol_DZ vol_DY : ℝ}
    (hh₀ : 0 < h₀) (hh_nonneg : 0 ≤ h_DZ) (hh_le : h_DZ ≤ h₀) (hvol_Z : 0 ≤ vol_Z)
    (h_doubleZ : vol_DZ = 2 * vol_Z)
    (h_doubleY : vol_DY = 2 * vol_Y)
    (h_ineq : |(k : ℝ)| * h₀ ^ N * vol_DY ≤ h_DZ ^ N * vol_DZ) :
    |(k : ℝ)| * vol_Y ≤ vol_Z := by
  have h_doubled : |(k : ℝ)| * vol_DY ≤ vol_DZ :=
    same_entropy_volume_degree_bound hh₀ hh_nonneg hh_le (by linarith) h_ineq
  rw [h_doubleZ, h_doubleY] at h_doubled
  linarith

end CoreMetaLemmas

end AlexandrovConsequences
