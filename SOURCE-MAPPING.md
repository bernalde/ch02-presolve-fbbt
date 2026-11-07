# Source correspondence and component scope

Original thesis convexminlpreview.tex lines186–192 / printed p36 / PDF74 describes housekeeping, sequential FBBT, relaxed coordinate optimization and lifting context. The finite affine preservation route uses image extrema, signed inverse bounds and a literal finite row fold; coordinate and redundancy certificates make bounded subclaims precise. formal/CH02-presolve-bounds-certificate.md and formal/CH02-affine-propagation-certificate.md delimit prior accepted scopes. formal/CH02-fbbt-source-certificate.md binds the distinct qualified Belotti2010 simultaneous interpretation: final COCOA2010 printed pp71–73/PDF7–9, equations9–11 and13–34, with normalized row indices, sign branch and explicit zero products, clipping both(X,B). The thesis overview does not itself state this LP theorem. Belotti2012 sequential recurrence and X-only objective remain distinct. Existing certificate evidence is reused, with later Lean4.35 migration pins; no new source-science certification is claimed.

The finite affine row-fold contracts and preserves the explicitly bounded full original model and its minimizers. Attained relaxed coordinate enclosures, closed incumbent-cutoff bounds and final-retained-row redundancy certificates are exposed. The distinct finite simultaneous real (X,B) procedure is exposed through its complete qualified theory and full source-model bridge: actual-run/fixed-state/scalar-LP equivalence, and conditional endpoint convergence, greatest fixed box and unique attained entire-assignment width optimum. LP infeasibility gives bounded-source infeasibility without assuming a nonempty run.

Sequential visits and the simultaneous operator remain different procedures. Both variable and row intervals are clipped to the initial box; signs, zero products, empty families and canonical empty states persist. No graph point follows from a nonempty fixed interval box. No unbounded-source equivalence, nonlinear/integer propagation, rounding, finite stabilization, historical implementation, general presolve completeness, runtime or empirical claim is certified. The full-width LP result is not transferred to a variable-only objective.

Byte-identical control modules are retained as support: negative/zero coefficients, empty input, zero dimensions, unchanged infeasible boxes, compact/open/unbounded relaxations, closed ties and integer-only redundancy; simultaneous contraction with positive width at every finite step, fixed inconsistent boxes without graph points, zero rows/columns, empty index families, incomparable LP boxes and a full nonlinear/integer source model. These controls support nonvacuity without additional entry counts.

| Exact advertised interface | Accepted source endpoint |
| --- | --- |
| `Chapter02.palomar_affine_propagate_contracts` | `Chapter02.affine_propagate_contracts` |
| `Chapter02.palomar_affine_source_preservation` | `Chapter02.affine_source_preservation` |
| `Chapter02.palomar_affine_source_empty_certificate` | `Chapter02.affine_source_empty_certificate` |
| `Chapter02.palomar_affine_source_minimizer_iff` | `Chapter02.affine_source_minimizer_iff` |
| `Chapter02.palomar_compact_tightest_coordinate_enclosure` | `Chapter02.compact_tightest_coordinate_enclosure` |
| `Chapter02.palomar_cutoff_bounds_preserve_minimizers` | `Chapter02.cutoff_bounds_preserve_minimizers` |
| `Chapter02.BBPolyData.palomar_retained_feasible_eq_of_certificates` | `Chapter02.BBPolyData.retained_feasible_eq_of_certificates` |
| `Chapter02.BBPolyData.palomar_retained_minimizer_iff_of_certificates` | `Chapter02.BBPolyData.retained_minimizer_iff_of_certificates` |
| `Chapter02.BBPolyData.palomar_feasible_coordinate_bounds` | `Chapter02.BBPolyData.feasible_coordinate_bounds` |
| `Chapter02.BBPolyData.palomar_feasible_cutoff_bounds_minimizer_iff` | `Chapter02.BBPolyData.feasible_cutoff_bounds_minimizer_iff` |
| `Chapter02FBBT.palomar_qualified_simultaneous_fbbt` | `Chapter02FBBT.qualified_simultaneous_fbbt` |
| `Chapter02FBBT.palomar_qualified_source_fbbt` | `Chapter02FBBT.qualified_source_fbbt` |

SOURCE-MANIFEST.json binds literal definition bodies, exact complete statement headers, source line locations and all byte-identical copied modules. Unadvertised support/control theorems in those modules are not additional entry claims. Current check/review stages live in VERIFICATION.json and formalization.yaml.

The independent Challenge explicitly names the source-generated recursors for Chapter02.affineRowStep, Chapter02.affineSourceRow. Lean module-local matcher memoization otherwise reuses different generated names when the independent surface is flattened. Complete printed recursor/outer bodies are retained; SOURCE-MANIFEST.json binds exact bounded diagnostic evidence and syntax/body hashes. Every computational body remains subject to recursive genuine Comparator checks, with no exemption.

Structured source authors, titles and held versions

- A review and comparison of solvers for convex MINLP — Jan Kronqvist, David E. Bernal, Andreas Lundell, Ignacio E. Grossmann. Optimization and Engineering, 20, 397--455, 2019 Joint source review underlying Chapter2; bibliographic authorship does not imply responsibility for this formalization or endorsement. Actual retained theorem scopes and source-version identities are in SOURCE-MAPPING.md.
- Feasibility-based bounds tightening via fixed points — Pietro Belotti, Sonia Cafieri, Jon Lee, Leo Liberti. COCOA 2010 final printed article, pp.65–76; finite simultaneous operator/LP correspondence at printed pp.71–73, equations9–34. Source authorship is distinct from formalization responsibility; no other author endorsement or new mathematical novelty is claimed. Qualified simultaneous (X,B) interpretation only; source index/sign/zero-product/clipping normalizations are disclosed in SOURCE-MAPPING.md. The held2012sequential extension and its X-only objective remain separate.
- Mixed-integer nonlinear optimization — Pietro Belotti, Christian Kirches, Sven Leyffer, Jeff Linderoth, James Luedtke, Ashutosh Mahajan. Held author manuscript with cover dated November22,2012 (bibliographic key Belotti2013),123PDFpages; relaxed coordinate-bound, presolve and model context. Actual held SHA256 c898a3780a3de6ccec1f3fa283f417e9b8d491e2c7d3469c8ff56dccc323c8fa. The 2013 Acta Numerica journal citation is distinct from the author-version cover date; final journal byte identity is not assumed. Source authorship is distinct from formalization responsibility; no other author endorsement or new mathematical novelty is claimed. The held author manuscript is not asserted identical to a final journal edition; native final-row deletion and finite-schedule details are labelled formal interpretations.
