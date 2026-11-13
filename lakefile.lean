import Lake
open Lake DSL

package «AlexandrovConsequences» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.backward.isDefEq.respectTransparency, false⟩
  ]

require «RCDEntropyDegree» from git
  "https://github.com/psuarezserrato/rcd-entropy-degree-rigidity.git" @ "main"

@[default_target]
lean_lib «AlexandrovConsequences» where
  -- Formalized consequences of the Alexandrov entropy-degree theorem (arXiv:2606.30403)
