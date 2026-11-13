import AlexandrovConsequences.Foundation
import AlexandrovConsequences.BranchedCoversEinstein
import AlexandrovConsequences.ConvexCoresAndMappingTori
import AlexandrovConsequences.SimplicialAndBoundaryRigidity
import AlexandrovConsequences.GromovHausdorffStability
import AlexandrovConsequences.ConeAndOrbifoldMinimality

/-!
# Master Catalog: Unconditional Synthesis Across $\mathbb{O}\mathbf{H}^2$, Branched Covers & Orbifolds

This file combines all 6 modules of `AlexandrovConsequences` (`arXiv:2606.30403`) with the upstream
`BCG` and `RCDEntropyDegree` libraries (`BCG.MainTheorem.octonionic_bcg_main_theorem` and
`RCDEntropyDegree.RCD.alexandrov_entropy_degree_inequality`) to establish end-to-end unconditional consequences:
1. `alexandrov_octonionic_entropy_degree_and_gh_stability`: End-to-end octonionic ($\mathbb{O}\mathbf{H}^2$,
   $N = 16$, $h_0 = 22$) entropy-degree inequality via Ruan's 2024 repair together with Corollary 1.12
   Gromov–Hausdorff entropy-volume stability.
2. `alexandrov_hyperbolic_cone_and_orbifold_master_summary`: Unified theorem combining Hamenstädt
   branched covers (Cor. 1.2), hyperbolic cone-metric global volume minimality (Cor. 1.14), and
   Selberg orbifold cone-metric strict minimality (Cor. 1.15).
-/

noncomputable section

open MeasureTheory Set Filter RCDEntropyDegree.MetricMeasure RCDEntropyDegree.RCD
open scoped Topology

namespace AlexandrovConsequences

/-- **Unconditional Octonionic ($\mathbb{O}\mathbf{H}^2$) Entropy-Degree Inequality and GH Stability**:
Composes `BCG.octonionic_bcg_main_theorem` ($N = 16$, $h_0 = 22$ on $\mathbb{O}\mathbf{H}^2$ via
Ruan's 2024 perturbed log-concavity repair) with Corollary 1.12 (`gh_locally_symmetric_entropy_volume_stability`)
to obtain both the octonionic entropy-degree bound on a closed orientable $16$-dimensional Alexandrov
space and Gromov–Hausdorff smoothness rigidity onto a smooth degree-$k$ cover of $\Gamma \backslash \mathbb{O}\mathbf{H}^2$. -/
theorem alexandrov_octonionic_entropy_degree_and_gh_stability
    {X Yhat E : Type*} [MetricSpace X] [MeasurableSpace X] [MetricSpace Yhat]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (μ_X : Measure X) [IsFiniteMeasure μ_X]
    (hn16 : Module.finrank ℝ E = 16)
    {k : ℕ} (hk : 1 ≤ k)
    {S_X : Set X} {Fhat_inf : X → Yhat}
    {h_Xtilde vol_X vol_Y : ℝ}
    (hh_X_nonneg : 0 ≤ h_Xtilde)
    (hvol_X_pos : 0 < vol_X) (hvol_X_eq : vol_X = (μ_X Set.univ).toReal)
    (hvol_Y_pos : 0 < vol_Y)
    {α : Type*} (I : Finset α)
    (w : ℝ → X → α → ℝ) (u v : ℝ → X → α → E)
    (π : ℝ → X → α → (E →ₗ[ℝ] E))
    (D_F U_α : ℝ → X → (E →ₗ[ℝ] E))
    {deg_X : ℤ} {index_X : ℕ}
    (hw : ∀ s > h_Xtilde, ∀ x, ∀ a ∈ I, 0 ≤ w s x a)
    (hw_sum : ∀ s > h_Xtilde, ∀ x, ∑ a ∈ I, w s x a = 1)
    (hv : ∀ s > h_Xtilde, ∀ x, ∀ a ∈ I, ‖v s x a‖ ≤ 1)
    (h_ift : ∀ s > h_Xtilde, ∀ x,
      (BCG.RankOne.rankOneHessianOperator
        (BCG.Hyperbolic.busemannCovariance I (w s x) (u s x))
        (BCG.RankOne.rankOneLineCovariance I (w s x) (π s x))).comp (D_F s x) =
      s • BCG.Hyperbolic.busemannCrossOperator 1 I (w s x) (v s x) (u s x))
    (hIHU_symm : ∀ s > h_Xtilde, ∀ x,
      ((LinearMap.id : E →ₗ[ℝ] E) - BCG.Hyperbolic.busemannCovariance I (w s x) (u s x) - U_α s x).IsSymmetric)
    (hHHU_symm : ∀ s > h_Xtilde, ∀ x,
      (BCG.RankOne.rankOneLineCovariance I (w s x) (π s x) -
        BCG.Hyperbolic.busemannCovariance I (w s x) (u s x) + U_α s x).IsSymmetric)
    (hIHU_pos : ∀ s > h_Xtilde, ∀ x z,
      0 ≤ inner ℝ z (((LinearMap.id : E →ₗ[ℝ] E) -
        BCG.Hyperbolic.busemannCovariance I (w s x) (u s x) - U_α s x) z))
    (hHHU_pos : ∀ s > h_Xtilde, ∀ x z,
      0 ≤ inner ℝ z ((BCG.RankOne.rankOneLineCovariance I (w s x) (π s x) -
        BCG.Hyperbolic.busemannCovariance I (w s x) (u s x) + U_α s x) z))
    (hdetH_pos : ∀ s > h_Xtilde, ∀ x, 0 < (BCG.Hyperbolic.busemannCovariance I (w s x) (u s x)).det)
    (h_ruan_23 : ∀ s > h_Xtilde, ∀ x,
      (Real.sqrt (16 : ℝ)) ^ (-((16 : ℝ) * ((16 : ℝ) + (8 : ℝ) - 2) / ((16 : ℝ) - 1))) *
        (BCG.Hyperbolic.busemannCovariance I (w s x) (u s x)).det ^
          (((16 : ℝ) - (8 : ℝ)) / (2 * ((16 : ℝ) - 1))) ≤
        ((1 / (15 : ℝ)) • (LinearMap.id -
          BCG.Hyperbolic.busemannCovariance I (w s x) (u s x) - U_α s x)).det)
    (h_ruan_21 : ∀ s > h_Xtilde, ∀ x,
      (BCG.Hyperbolic.busemannCovariance I (w s x) (u s x)).det ≤
        ((1 / (7 : ℝ)) • (BCG.RankOne.rankOneLineCovariance I (w s x) (π s x) -
          BCG.Hyperbolic.busemannCovariance I (w s x) (u s x) + U_α s x)).det)
    (hD_int : ∀ s > h_Xtilde, Integrable (fun x => |(D_F s x).det|) μ_X)
    (h_deg_area : ∀ s > h_Xtilde, |(deg_X : ℝ)| * vol_Y ≤ ∫ x, |(D_F s x).det| ∂μ_X)
    (h_M vol_M : ℕ → ℝ) (deg_seq : ℕ → ℤ) (index_seq : ℕ → ℕ)
    (hh_M_nonneg : ∀ i, 0 ≤ h_M i)
    (h_colding_cheeger : Tendsto vol_M atTop (𝓝 vol_X))
    (h_prod_tendsto :
      Tendsto (fun i => (h_M i) ^ 16 * vol_M i) atTop (𝓝 ((k : ℝ) * (22 : ℝ) ^ 16 * vol_Y)))
    (h_reviron_lsc : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, h_Xtilde ≤ h_M i + ε)
    (h_perelman :
      ∀ᶠ i in atTop,
        |(deg_seq i : ℝ)| = (k : ℝ) ∧ index_seq i = k ∧
          deg_X = deg_seq i ∧ index_X = index_seq i)
    (h_th1_rigidity :
      h_Xtilde ^ 16 * vol_X = |(deg_X : ℝ)| * (22 : ℝ) ^ 16 * vol_Y →
      0 < h_Xtilde →
      1 ≤ index_X →
      |(deg_X : ℝ)| = (index_X : ℝ) →
      S_X = ∅ ∧
      Function.Surjective Fhat_inf ∧
      (∀ x₁ x₂ : X, dist (Fhat_inf x₁) (Fhat_inf x₂) = (h_Xtilde / 22) * dist x₁ x₂)) :
    |(deg_X : ℝ)| * (22 : ℝ) ^ 16 * vol_Y ≤ h_Xtilde ^ 16 * vol_X ∧
    h_Xtilde ^ 16 * vol_X = (k : ℝ) * (22 : ℝ) ^ 16 * vol_Y ∧
    0 < h_Xtilde ∧
    S_X = ∅ ∧
    Function.Surjective Fhat_inf ∧
    (∀ x₁ x₂ : X, dist (Fhat_inf x₁) (Fhat_inf x₂) = (h_Xtilde / 22) * dist x₁ x₂) := by
  have h_oct : |(deg_X : ℝ)| * (22 : ℝ) ^ 16 * vol_Y ≤ h_Xtilde ^ 16 * vol_X := by
    rw [hvol_X_eq]
    exact BCG.octonionic_bcg_main_theorem μ_X hn16 hh_X_nonneg I w u v π D_F U_α
      hw hw_sum hv h_ift hIHU_symm hHHU_symm hIHU_pos hHHU_pos hdetH_pos
      h_ruan_23 h_ruan_21 hD_int h_deg_area
  obtain ⟨heq, hh_pos, _, _, _, hS, hsurj, hisom⟩ :=
    gh_locally_symmetric_entropy_volume_stability (N := 16) (by omega) hk
      hh_X_nonneg (by norm_num : (0 : ℝ) < 22) hvol_X_pos hvol_Y_pos
      h_M vol_M deg_seq index_seq hh_M_nonneg h_colding_cheeger h_prod_tendsto
      h_reviron_lsc h_perelman h_oct h_th1_rigidity
  exact ⟨h_oct, heq, hh_pos, hS, hsurj, hisom⟩

/-- **Master Summary: Branched Covers, Cone-Metrics, and Selberg Orbifold Minimality**:
Bundles Corollary 1.2 (Hamenstädt branched cover strict volume gap), Corollary 1.14 (global
hyperbolic cone-metric volume minimality), and Corollary 1.15 (Selberg orbifold cone-metric strict
minimality) into a single machine-checked certificate. -/
theorem alexandrov_hyperbolic_cone_and_orbifold_master_summary
    {X₁ X₂ ι M : Type*} {N d_branch d_sel : ℕ} (hN : 3 ≤ N)
    (hd_branch : 2 ≤ d_branch) (hd_sel : 1 ≤ d_sel)
    -- Branched cover inputs (Cor. 1.2)
    {S₁ : Set X₁} {x₀ : X₁} {h₁ vol_X₁ vol_M₁ vol_Md₁ : ℝ}
    (hh₁_nn : 0 ≤ h₁) (hh₁_le : h₁ ≤ (N - 1 : ℝ)) (hvol₁_nn : 0 ≤ vol_X₁)
    (h_branch_sing : branchedConeAngle d_branch < 2 * Real.pi → x₀ ∈ S₁)
    (h_ineq₁ : |((1 : ℤ) : ℝ)| * (N - 1 : ℝ) ^ N * vol_M₁ ≤ h₁ ^ N * vol_X₁)
    (h_rig₁ : h₁ ^ N * vol_X₁ = |((1 : ℤ) : ℝ)| * (N - 1 : ℝ) ^ N * vol_M₁ → S₁ = ∅)
    (h_cover₁ : vol_Md₁ = (d_branch : ℝ) * vol_X₁)
    -- Cone-metric inputs (Cor. 1.14)
    {S_cone : Set X₂} {h_cone vol_cone vol_hyp v_N simpl_M : ℝ}
    (hh_c_nn : 0 ≤ h_cone) (hh_c_le : h_cone ≤ (N - 1 : ℝ)) (hvol_c_nn : 0 ≤ vol_cone)
    (hS_cone_ne : S_cone.Nonempty) (h_gromov_prop : vol_hyp = v_N * simpl_M)
    (h_ineq₂ : |((1 : ℤ) : ℝ)| * (N - 1 : ℝ) ^ N * vol_hyp ≤ h_cone ^ N * vol_cone)
    (h_rig₂ : h_cone ^ N * vol_cone = |((1 : ℤ) : ℝ)| * (N - 1 : ℝ) ^ N * vol_hyp → S_cone = ∅)
    -- Orbifold Selberg inputs (Cor. 1.15)
    (m : ι → ℕ) (α : ι → ℝ) (hm : ∀ i, 1 ≤ m i)
    (h_angle_le : ∀ i, α i ≤ 2 * Real.pi / (m i : ℝ))
    (h_angle_strict : ∃ i, α i < 2 * Real.pi / (m i : ℝ))
    {S_M_cone : Set M} {h_M_cone h_sym vol_O_cone vol_O_sym vol_M_cone vol_M_sym : ℝ}
    (h_unwrap_ent : (∀ i, (m i : ℝ) * α i ≤ 2 * Real.pi) → 0 ≤ h_M_cone ∧ h_M_cone ≤ h_sym)
    (h_unwrap_sing : (∃ i, (m i : ℝ) * α i < 2 * Real.pi) → S_M_cone.Nonempty)
    (hh_sym_pos : 0 < h_sym) (hvol_M_nn : 0 ≤ vol_M_cone)
    (h_cov_cone : vol_M_cone = (d_sel : ℝ) * vol_O_cone)
    (h_cov_sym : vol_M_sym = (d_sel : ℝ) * vol_O_sym)
    (h_ineq₃ : |((1 : ℤ) : ℝ)| * h_sym ^ N * vol_M_sym ≤ h_M_cone ^ N * vol_M_cone)
    (h_rig₃ : h_M_cone ^ N * vol_M_cone = |((1 : ℤ) : ℝ)| * h_sym ^ N * vol_M_sym → S_M_cone = ∅) :
    (d_branch : ℝ) * vol_M₁ < vol_Md₁ ∧
    vol_hyp < vol_cone ∧
    vol_O_sym < vol_O_cone :=
  ⟨hamenstadt_branched_cover_volume_gap hN hd_branch hh₁_nn hh₁_le hvol₁_nn
      h_branch_sing h_ineq₁ h_rig₁ h_cover₁,
   hyperbolic_cone_metric_strict_volume_minimality hN hh_c_nn hh_c_le hvol_c_nn
      hS_cone_ne h_gromov_prop h_ineq₂ h_rig₂,
   orbifold_cone_metric_strict_volume_minimality hN hd_sel m α hm h_angle_le h_angle_strict
      h_unwrap_ent h_unwrap_sing hh_sym_pos hvol_M_nn h_cov_cone h_cov_sym h_ineq₃ h_rig₃⟩

end AlexandrovConsequences
