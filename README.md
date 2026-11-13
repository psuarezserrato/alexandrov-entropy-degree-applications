# Geometric and Topological Consequences of the Alexandrov Entropy-Degree Theorem (`arXiv:2606.30403`, Lean 4)

Machine-checked Lean 4 (`leanprover/lean4:v4.35.0`) formalization accompanying:

> **P. Suárez-Serrato**, *"The entropy-degree theorem for Alexandrov spaces"*, `arXiv:2606.30403` (2026).

This standalone repository formalizes the degree-theoretic bridge (§5), Theorem 1.1, Remark 1.15, and all 14 geometric and topological consequences (Corollaries 1.2–1.8, Theorems 1.9–1.10, and Corollaries 1.11–1.15) atop [`rcd-entropy-degree-rigidity`](https://github.com/psuarezserrato/rcd-entropy-degree-rigidity) (`RCDEntropyDegree`) and [`formalized-barycenter-methods`](https://github.com/psuarezserrato/formalized-barycenter-methods) (`BCG`).

---

## Verification Summary

- **Toolchain:** `leanprover/lean4:v4.35.0` (Mathlib `v4.35.0`)
- **Upstream Dependencies:** [`RCDEntropyDegree`](https://github.com/psuarezserrato/rcd-entropy-degree-rigidity) and [`BCG`](https://github.com/psuarezserrato/formalized-barycenter-methods)
- **Modules & Scale:** 8 library modules (`AlexandrovConsequences`), 1,745 lines of Lean code, 54 tracked blueprint declarations
- **Kernel & Axiom Audit:** **`0` `sorryAx`**, **`0` custom axioms** (standard Lean axioms only: `propext`, `Classical.choice`, `Quot.sound`)
- **Blueprint DAG:** 28 nodes (`blueprint/dep_graph.dot`) — **100% green** (23 `#1CAC78` proved theorem nodes, 5 `#B0ECA3` definition nodes), `0` `plasTeX` errors
- **Executive Audit Report:** [`report/alexandrov_consequences_report.pdf`](report/alexandrov_consequences_report.pdf) (4 pages, `0` LaTeX errors, `0` overfull boxes)

---

## Module & Paper Traceability Overview (`AlexandrovConsequences`)

| Module | Paper Section & Main Formalized Results |
| :--- | :--- |
| [`AlexandrovConsequences.lean`](AlexandrovConsequences.lean) | Root aggregator importing all seven `AlexandrovConsequences.*` modules |
| [`AlexandrovConsequences/Foundation.lean`](AlexandrovConsequences/Foundation.lean) | §5 (`analyticDegree`, `MitsuishiDegreeBridge`, `analytic_eq_topological_degree`), Theorem 1.1 (`alexandrov_entropy_degree_inequality_continuous`, `alexandrov_entropy_degree_rigidity`), Remark 1.15 (`abs_degree_eq_index_iff_lift_degree_one`, `connected_sum_rigidity_counterexample`), and core strictness & metric-doubling lemmas |
| [`AlexandrovConsequences/BranchedCoversEinstein.lean`](AlexandrovConsequences/BranchedCoversEinstein.lean) | Corollaries 1.2–1.3: Hamenstädt branched cover volume gap (`hamenstadt_branched_cover_volume_gap`) and Satake–Einstein 4-orbifold Euler obstruction (`gromov_thurston_branch_locus_euler_neg`, `einstein_four_orbifold_strict_euler_obstruction`) |
| [`AlexandrovConsequences/ConvexCoresAndMappingTori.lean`](AlexandrovConsequences/ConvexCoresAndMappingTori.lean) | Corollaries 1.4–1.8: $N$-cone-manifolds, Perelman doubling on boundary manifolds, geometrically finite convex cores, Bridgeman–Brock–Bromberg Weil–Petersson core bound (`unified_degree_weil_petersson_core_bound`), and end-periodic mapping-torus translation length bound (`end_periodic_translation_length_bound`) |
| [`AlexandrovConsequences/SimplicialAndBoundaryRigidity.lean`](AlexandrovConsequences/SimplicialAndBoundaryRigidity.lean) | Theorems 1.9–1.10: Acylindrical convex core Gromov simplicial volume bound (`acylindrical_convex_core_simplicial_bound`) and Petrunin gluing boundary volume rigidity (`alexandrov_boundary_volume_rigidity`) |
| [`AlexandrovConsequences/GromovHausdorffStability.lean`](AlexandrovConsequences/GromovHausdorffStability.lean) | Corollaries 1.11–1.12: Reviron entropy lower-semicontinuity (`limit_entropy_pow_le_of_eventually_add_eps`), hyperbolic GH volume stability (`gh_hyperbolic_volume_stability`), and general locally symmetric GH entropy-volume stability (`gh_locally_symmetric_entropy_volume_stability`) |
| [`AlexandrovConsequences/ConeAndOrbifoldMinimality.lean`](AlexandrovConsequences/ConeAndOrbifoldMinimality.lean) | Corollaries 1.13–1.15: Homotopy simplicial volume rigidity (`alexandrov_homotopy_simplicial_rigidity`), global path-independent hyperbolic cone-metric strict minimality (`hyperbolic_cone_metric_strict_volume_minimality`), and Selberg orbifold cone-metric volume minimality |
| [`AlexandrovConsequences/MasterCatalog.lean`](AlexandrovConsequences/MasterCatalog.lean) | Unconditional octonionic ($\mathbb{O}\mathbf{H}^2$) synthesis with Ruan's 2024 repair (`alexandrov_octonionic_entropy_degree_and_gh_stability`) and unified cone/orbifold catalog theorem (`alexandrov_hyperbolic_cone_and_orbifold_master_summary`) |

---

## Blueprint, Print PDF, and Executive Report

- **Interactive Dependency Graph:** [`blueprint/web/dep_graph_document.html`](blueprint/web/dep_graph_document.html) (rendered HTML & inline SVG from [`blueprint/src/content.tex`](blueprint/src/content.tex))
- **Blueprint Print PDF:** [`blueprint/print/print.pdf`](blueprint/print/print.pdf)
- **Executive Audit Report:** [`report/alexandrov_consequences_report.pdf`](report/alexandrov_consequences_report.pdf)

---

## Reproducing the Build & Audit Locally

This repository requires access to [`psuarezserrato/rcd-entropy-degree-rigidity`](https://github.com/psuarezserrato/rcd-entropy-degree-rigidity) and [`psuarezserrato/formalized-barycenter-methods`](https://github.com/psuarezserrato/formalized-barycenter-methods): if cloned as private repositories, ensure Git credentials (SSH or HTTPS PAT) are configured before fetching Lake dependencies. When cloned inside `formalized-barycenter-methods`, run from this directory:

```bash
# Build all Lean modules (requires Mathlib v4.35.0, BCG, & RCDEntropyDegree)
lake build

# Regenerate the blueprint web & PDF dependency graph
./blueprint/export_dep_graph.sh
```

## License

Licensed under the GNU Affero General Public License v3.0 (AGPLv3) with non-commercial use notice ([`LICENSE.md`](LICENSE.md)).
