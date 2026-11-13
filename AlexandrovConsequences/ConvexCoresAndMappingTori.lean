import AlexandrovConsequences.Foundation

/-!
# Cone-Manifolds, Convex-Boundary Doubling, Convex Cores, Weil–Petersson Bounds & Mapping Tori

This file formalizes **Corollaries 1.4, 1.5, 1.6, 1.7, and 1.8** of
P. Suárez-Serrato, *"The entropy-degree theorem for Alexandrov spaces"* (`arXiv:2606.30403`,
§1.2 & §7.3–7.5).

## Main Results
1. **Corollary 1.4 (`cor:cone-manifold`, `cone_manifold_entropy_degree_bound`)**:
   For a compact orientable $N$-dimensional cone-manifold $Z$ ($N \ge 3$) with cone angles $\le 2\pi$
   and regular sectional curvature $K_{\mathrm{reg}} \ge -1$, Bishop–Gromov gives
   $h(\overline{Z}) \le N - 1$, hence $(N-1)^N \mathcal{H}^N(Z) \ge |\deg(f)| \, h(\widetilde{Y})^N \mathcal{H}^N(Y)$.
2. **Corollary 1.5 (`cor:manifold-boundary`, `convex_manifold_boundary_volume_bound`)**:
   Via Perelman's metric doubling theorem $DZ = Z \cup_{\partial Z} Z \to DY_{\mathrm{geod}}$,
   $$\mathrm{Vol}(Z) \ge |k| \, \mathrm{Vol}(Y_{\mathrm{geod}}).$$
3. **Corollary 1.6 (`cor:bonahon-degree`, `geometrically_finite_convex_core_volume_bound`,
   `geometrically_finite_convex_core_volume_bound_limit`)**:
   Specializing to convex cores $C_M \to C_{M_g}$ of geometrically finite hyperbolic $3$-manifolds
   ($N = 3, h = 2$) via Perelman doubling and smooth $\varepsilon$-neighborhood approximations yields
   $$\mathrm{Vol}(C_M) \ge |k| \, \mathrm{Vol}(C_{M_g}).$$
4. **Corollary 1.7 (`cor:unified-volume`, `unified_degree_weil_petersson_core_bound`)**:
   Combines Corollary 1.6 for $f \circ h$ with Bridgeman–Brock–Bromberg `[Bridgeman23]`
   (faithfully fixing the parenthesization typo in line 1621 of `AlexDegThm-Aug-2026.tex`):
   $$\mathrm{Vol}(C_{M'}) \ge |k| \, \mathrm{Vol}(C_{M_{\mathrm{geod}}}) + A(\partial Z')\, d_{\mathrm{WP}}(\partial_c M', \partial_c M'_{\mathrm{geod}}) - \delta.$$
5. **Corollary 1.8 (`cor:translation-length`, `infimalConvexHyperbolicVolume`,
   `mapping_torus_infimal_volume_bound`, `end_periodic_translation_length_bound`)**:
   Defines the infimal convex-hyperbolic volume via `sInf`, proves $\underline{\mathrm{Vol}}(\overline{M}_\phi) \ge |k|\,\mathrm{Vol}(Y)$,
   and combines with Field–Kim–Leininger–Loving `[Field23]` to prove
   $$\tau(\phi) \ge \frac{|k|}{V_{\mathrm{oct}}} \, \mathrm{Vol}(Y).$$
-/

noncomputable section

open MeasureTheory Set Filter RCDEntropyDegree.MetricMeasure RCDEntropyDegree.RCD
open scoped Topology

namespace AlexandrovConsequences

section ConeManifoldsAndConvexBoundary

/-- **Corollary 1.4 (`cor:cone-manifold`, Cone-Manifolds with Cone Angles $\le 2\pi$)**:
Let $Z$ be a compact orientable $N$-dimensional cone-manifold ($N \ge 3$) whose cone angles along all
codimension-2 strata satisfy $\alpha \le 2\pi$ and whose regular part satisfies $K_{\mathrm{reg}} \ge -1$
(so $\mathrm{curv} \ge -1$ in the Alexandrov sense and Bishop–Gromov gives $0 \le h(\overline{Z}) \le N - 1$).
For any continuous map $f : Z \to Y$ to a closed orientable negatively curved locally symmetric
$N$-manifold $Y$, Theorem 1.1 yields
$$|\deg(f)| \, h(\widetilde{Y})^N \, \mathcal{H}^N(Y) \le (N - 1)^N \, \mathcal{H}^N(Z).$$ -/
theorem cone_manifold_entropy_degree_bound
    {N : ℕ} (_hN : 3 ≤ N) {deg_f : ℤ} {h_Zbar h_Ytilde vol_Z vol_Y : ℝ}
    (hh_Zbar_nonneg : 0 ≤ h_Zbar) (hh_Zbar_le : h_Zbar ≤ (N - 1 : ℝ))
    (hvol_Z : 0 ≤ vol_Z)
    (h_ineq : |(deg_f : ℝ)| * h_Ytilde ^ N * vol_Y ≤ h_Zbar ^ N * vol_Z) :
    |(deg_f : ℝ)| * h_Ytilde ^ N * vol_Y ≤ ((N - 1 : ℝ) ^ N) * vol_Z :=
  upper_entropy_bound_volume_inequality hh_Zbar_nonneg hh_Zbar_le hvol_Z h_ineq

/-- **Corollary 1.5 (`cor:manifold-boundary`, Hyperbolic Boundary-Manifold Volume via Doubling)**:
Let $Z$ be a compact oriented $N$-manifold ($N \ge 3$) with locally convex boundary and
$\mathrm{sec} \ge -1$, mapped via $f : (Z, \partial Z) \to (Y_{\mathrm{geod}}, \partial Y_{\mathrm{geod}})$
of relative degree $k \in \mathbb{Z}$ to a compact hyperbolic $N$-manifold with totally geodesic
boundary. Passing to the Perelman metric doubles $DZ = Z \cup_{\partial Z} Z$ and $DY_{\mathrm{geod}}$
(with $\mathrm{Vol}(DZ) = 2\,\mathrm{Vol}(Z)$, $\mathrm{Vol}(DY_{\mathrm{geod}}) = 2\,\mathrm{Vol}(Y_{\mathrm{geod}})$,
$h(\overline{DZ}) \le N - 1$, $h(\widetilde{DY_{\mathrm{geod}}}) = N - 1$) gives
$$|k| \, \mathrm{Vol}(Y_{\mathrm{geod}}) \le \mathrm{Vol}(Z).$$ -/
theorem convex_manifold_boundary_volume_bound
    {N : ℕ} (hN : 3 ≤ N) {k : ℤ}
    {h_DZ vol_Z vol_Ygeod vol_DZ vol_DY : ℝ}
    (hh_DZ_nonneg : 0 ≤ h_DZ) (hh_DZ_le : h_DZ ≤ (N - 1 : ℝ))
    (hvol_Z : 0 ≤ vol_Z)
    (h_doubleZ : vol_DZ = 2 * vol_Z)
    (h_doubleY : vol_DY = 2 * vol_Ygeod)
    (h_ineq : |(k : ℝ)| * (N - 1 : ℝ) ^ N * vol_DY ≤ h_DZ ^ N * vol_DZ) :
    |(k : ℝ)| * vol_Ygeod ≤ vol_Z := by
  have hh₀ : (0 : ℝ) < (N - 1 : ℝ) := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  exact metric_doubling_volume_degree_bound hh₀ hh_DZ_nonneg hh_DZ_le hvol_Z
    h_doubleZ h_doubleY h_ineq

end ConeManifoldsAndConvexBoundary

section ConvexCoresAndWeilPetersson

/-- **Corollary 1.6 (`cor:bonahon-degree`, Direct Doubled Convex-Core Inequality at $N = 3$)**:
For convex cores $C_M \to C_{M_g}$ of geometrically finite hyperbolic $3$-manifolds ($N = 3$, $h_0 = 2$)
of relative degree $k \in \mathbb{Z}$, applying Theorem 1.1 to the Perelman doubles yields
$$|k| \, \mathrm{Vol}(C_{M_g}) \le \mathrm{Vol}(C_M).$$ -/
theorem geometrically_finite_convex_core_volume_bound
    {k : ℤ} {h_DCM vol_CM vol_CMg vol_DCM vol_DCMg : ℝ}
    (hh_DCM_nonneg : 0 ≤ h_DCM) (hh_DCM_le : h_DCM ≤ 2)
    (hvol_CM : 0 ≤ vol_CM)
    (h_doubleM : vol_DCM = 2 * vol_CM)
    (h_doubleMg : vol_DCMg = 2 * vol_CMg)
    (h_ineq : |(k : ℝ)| * (2 : ℝ) ^ 3 * vol_DCMg ≤ h_DCM ^ 3 * vol_DCM) :
    |(k : ℝ)| * vol_CMg ≤ vol_CM := by
  have h2' : h_DCM ≤ ((3 : ℕ) - 1 : ℝ) := by norm_num; exact hh_DCM_le
  have hineq' : |(k : ℝ)| * ((3 : ℕ) - 1 : ℝ) ^ (3 : ℕ) * vol_DCMg ≤ h_DCM ^ (3 : ℕ) * vol_DCM := by
    convert h_ineq using 2; norm_num
  exact convex_manifold_boundary_volume_bound (le_refl 3) hh_DCM_nonneg h2' hvol_CM
    h_doubleM h_doubleMg hineq'

/-- **Corollary 1.6 (`cor:bonahon-degree`, $\varepsilon$-Neighborhood Approximation Limit)**:
Passing to the limit $r \to 0^+$ along smooth strictly convex $r$-neighborhoods $Z_i = \overline{N_{r_i}(C_M)}$
satisfying $\mathrm{Vol}(Z_i) \to \mathrm{Vol}(C_M)$ and Corollary 1.5 at every step $i$ yields
$$|k| \, \mathrm{Vol}(C_{M_g}) \le \mathrm{Vol}(C_M).$$ -/
theorem geometrically_finite_convex_core_volume_bound_limit
    {k : ℤ} {vol_CM vol_CMg : ℝ}
    (vol_Z_seq h_DZ_seq vol_DZ_seq vol_DY_seq : ℕ → ℝ)
    (hh_nonneg : ∀ i, 0 ≤ h_DZ_seq i) (hh_le : ∀ i, h_DZ_seq i ≤ 2)
    (hvol_nonneg : ∀ i, 0 ≤ vol_Z_seq i)
    (h_doubleZ : ∀ i, vol_DZ_seq i = 2 * vol_Z_seq i)
    (h_doubleY : ∀ i, vol_DY_seq i = 2 * vol_CMg)
    (h_ineq : ∀ i, |(k : ℝ)| * (2 : ℝ) ^ 3 * vol_DY_seq i ≤ h_DZ_seq i ^ 3 * vol_DZ_seq i)
    (h_tendsto : Tendsto vol_Z_seq atTop (𝓝 vol_CM)) :
    |(k : ℝ)| * vol_CMg ≤ vol_CM := by
  have h_seq : ∀ i, |(k : ℝ)| * vol_CMg ≤ vol_Z_seq i := fun i =>
    geometrically_finite_convex_core_volume_bound
      (hh_nonneg i) (hh_le i) (hvol_nonneg i) (h_doubleZ i) (h_doubleY i) (h_ineq i)
  exact ge_of_tendsto h_tendsto (Eventually.of_forall h_seq)

/-- **Corollary 1.7 (`cor:unified-volume`, Unified Degree & Weil–Petersson Core Volume Bound)**:
Combines the topological degree bound for $f \circ h : M'_{\mathrm{geod}} \to M_{\mathrm{geod}}$
(where $h : M' \to M'_{\mathrm{geod}}$ is an orientation-preserving/reversing homeomorphism of degree
$|\deg(h)| = 1$ so $|\deg(f \circ h)| = |k|$) with the Bridgeman–Brock–Bromberg `[Bridgeman23]`
Weil–Petersson comparison $\mathrm{Vol}(C_{M'}) - \mathrm{Vol}(C_{M'_{\mathrm{geod}}}) \ge
A(\partial Z')\,d_{\mathrm{WP}}(\partial_c M', \partial_c M'_{\mathrm{geod}}) - \delta$ to yield
$$|k| \, \mathrm{Vol}(C_{M_{\mathrm{geod}}}) + A(\partial Z')\,d_{\mathrm{WP}} - \delta \le \mathrm{Vol}(C_{M'}).$$
*(Note: formalizes the true additive error $-\delta$ as in lines 416, 845, and 1606 of
`AlexDegThm-Aug-2026.tex`, rather than the typographical parenthesis shift on line 1621.)* -/
theorem unified_degree_weil_petersson_core_bound
    {k deg_h deg_comp : ℤ}
    {h_DCMg vol_CM' vol_CM'geod vol_CMgeod vol_DCM'geod vol_DCMgeod A_bdry d_WP δ : ℝ}
    (h_deg_h : |(deg_h : ℝ)| = 1)
    (h_comp : deg_comp = k * deg_h)
    (hh_nonneg : 0 ≤ h_DCMg) (hh_le : h_DCMg ≤ 2)
    (hvol_M'geod : 0 ≤ vol_CM'geod)
    (h_doubleM'g : vol_DCM'geod = 2 * vol_CM'geod)
    (h_doubleMg : vol_DCMgeod = 2 * vol_CMgeod)
    (h_core_ineq : |(deg_comp : ℝ)| * (2 : ℝ) ^ 3 * vol_DCMgeod ≤ h_DCMg ^ 3 * vol_DCM'geod)
    (h_bbb : A_bdry * d_WP - δ ≤ vol_CM' - vol_CM'geod) :
    |(k : ℝ)| * vol_CMgeod + A_bdry * d_WP - δ ≤ vol_CM' := by
  have h_deg_comp_abs : |(deg_comp : ℝ)| = |(k : ℝ)| := by
    rw [h_comp, Int.cast_mul, abs_mul, h_deg_h, mul_one]
  have h_bonahon : |(deg_comp : ℝ)| * vol_CMgeod ≤ vol_CM'geod :=
    geometrically_finite_convex_core_volume_bound hh_nonneg hh_le hvol_M'geod
      h_doubleM'g h_doubleMg h_core_ineq
  rw [h_deg_comp_abs] at h_bonahon
  linarith

end ConvexCoresAndWeilPetersson

section EndPeriodicMappingTori

/-- **Infimal Convex-Hyperbolic Volume $\underline{\mathrm{Vol}}(\overline{M}_\phi)$**:
Given a parameterized family $S \subseteq \iota$ of convex hyperbolic metrics on the compactified
end-periodic mapping torus $\overline{M}_\phi$ with volume functional `vol : ι → ℝ`, defines
$$\underline{\mathrm{Vol}}(\overline{M}_\phi) := \inf_{g \in S} \mathrm{Vol}(\overline{M}_\phi, g).$$ -/
def infimalConvexHyperbolicVolume {ι : Type*} (S : Set ι) (vol : ι → ℝ) : ℝ :=
  sInf (vol '' S)

/-- **Corollary 1.8 Part 1 (`cor:translation-length`, Infimal Volume Lower Bound)**:
If $S$ is a nonempty collection of convex hyperbolic metrics on $\overline{M}_\phi$ and every metric
$g \in S$ admits a map to a closed convex hyperbolic $3$-manifold $Y$ with totally geodesic boundary
of degree $k \in \mathbb{Z}$ satisfying Corollary 1.5, then taking the infimum yields
$$|k| \, \mathrm{Vol}(Y) \le \underline{\mathrm{Vol}}(\overline{M}_\phi).$$ -/
theorem mapping_torus_infimal_volume_bound
    {ι : Type*} {S : Set ι} (hS : S.Nonempty) (vol : ι → ℝ)
    {k : ℤ} {vol_Y : ℝ}
    (h_DZ vol_DZ vol_DY : ι → ℝ)
    (hh_nonneg : ∀ g ∈ S, 0 ≤ h_DZ g) (hh_le : ∀ g ∈ S, h_DZ g ≤ 2)
    (hvol_nonneg : ∀ g ∈ S, 0 ≤ vol g)
    (h_doubleZ : ∀ g ∈ S, vol_DZ g = 2 * vol g)
    (h_doubleY : ∀ g ∈ S, vol_DY g = 2 * vol_Y)
    (h_ineq : ∀ g ∈ S, |(k : ℝ)| * (2 : ℝ) ^ 3 * vol_DY g ≤ (h_DZ g) ^ 3 * vol_DZ g) :
    |(k : ℝ)| * vol_Y ≤ infimalConvexHyperbolicVolume S vol := by
  unfold infimalConvexHyperbolicVolume
  refine le_csInf (hS.image vol) ?_
  rintro _ ⟨g, hg, rfl⟩
  have h2' : h_DZ g ≤ ((3 : ℕ) - 1 : ℝ) := by norm_num; exact hh_le g hg
  have hineq' :
      |(k : ℝ)| * ((3 : ℕ) - 1 : ℝ) ^ (3 : ℕ) * vol_DY g ≤ (h_DZ g) ^ (3 : ℕ) * vol_DZ g := by
    convert h_ineq g hg using 2; norm_num
  exact convex_manifold_boundary_volume_bound (le_refl 3)
    (hh_nonneg g hg) h2' (hvol_nonneg g hg) (h_doubleZ g hg) (h_doubleY g hg) hineq'

/-- **Corollary 1.8 Part 2 (`cor:translation-length`, Mapping-Class Translation Length Lower Bound)**:
Combining `mapping_torus_infimal_volume_bound` with the Field–Kim–Leininger–Loving `[Field23]`
upper bound $\underline{\mathrm{Vol}}(\overline{M}_\phi) \le V_{\mathrm{oct}} \cdot \tau(\phi)$
($V_{\mathrm{oct}} > 0$ the volume of the regular ideal octahedron) gives
$$\frac{|k|}{V_{\mathrm{oct}}} \, \mathrm{Vol}(Y) \le \tau(\phi).$$ -/
theorem end_periodic_translation_length_bound
    {ι : Type*} {S : Set ι} (hS : S.Nonempty) (vol : ι → ℝ)
    {k : ℤ} {vol_Y V_oct τ_φ : ℝ}
    (hV_oct : 0 < V_oct)
    (h_DZ vol_DZ vol_DY : ι → ℝ)
    (hh_nonneg : ∀ g ∈ S, 0 ≤ h_DZ g) (hh_le : ∀ g ∈ S, h_DZ g ≤ 2)
    (hvol_nonneg : ∀ g ∈ S, 0 ≤ vol g)
    (h_doubleZ : ∀ g ∈ S, vol_DZ g = 2 * vol g)
    (h_doubleY : ∀ g ∈ S, vol_DY g = 2 * vol_Y)
    (h_ineq : ∀ g ∈ S, |(k : ℝ)| * (2 : ℝ) ^ 3 * vol_DY g ≤ (h_DZ g) ^ 3 * vol_DZ g)
    (h_fkll : infimalConvexHyperbolicVolume S vol ≤ V_oct * τ_φ) :
    (|(k : ℝ)| / V_oct) * vol_Y ≤ τ_φ := by
  have h_inf :=
    mapping_torus_infimal_volume_bound hS vol h_DZ vol_DZ vol_DY
      hh_nonneg hh_le hvol_nonneg h_doubleZ h_doubleY h_ineq
  have h_mul : |(k : ℝ)| * vol_Y ≤ V_oct * τ_φ := h_inf.trans h_fkll
  rw [div_mul_eq_mul_div, div_le_iff₀ hV_oct]
  linarith

end EndPeriodicMappingTori

end AlexandrovConsequences
