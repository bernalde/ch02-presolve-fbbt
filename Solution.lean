module

public import Chapter02AffineBox
public import Chapter02AffinePropagation
public import Chapter02AffinePropagationExamples
public import Chapter02AffinePropagationSource
public import Chapter02FBBTBoundaryControls
public import Chapter02FBBTBounds
public import Chapter02FBBTContinuity
public import Chapter02FBBTContractionApplication
public import Chapter02FBBTContractionControl
public import Chapter02FBBTControlData
public import Chapter02FBBTControls
public import Chapter02FBBTLP
public import Chapter02FBBTLimit
public import Chapter02FBBTNegativeRhsControl
public import Chapter02FBBTOperator
public import Chapter02FBBTOrder
public import Chapter02FBBTPreservation
public import Chapter02FBBTSourceControl
public import Chapter02FBBTSourceData
public import Chapter02FBBTSourceTheorem
public import Chapter02FBBTTheorem
public import Chapter02PresolveBounds
public import Chapter02PresolveBoundsExamples
public import Chapter02PresolveRedundancy

@[expose] public section

/-! Exact aliases of accepted source statements; no import of Challenge. -/
noncomputable section
open scoped BigOperators Topology
open Classical Filter Function Set

namespace Chapter02


/-- Every literal finite schedule contracts its input Cartesian members. -/
theorem palomar_affine_propagate_contracts {n : ℕ} (rows : List (AffineIntervalRow n))
    (X : AffineBox n) : (affinePropagate rows X).members ⊆ X.members := by
  exact Chapter02.affine_propagate_contracts (n := n) (rows := rows) (X := X)

end Chapter02

namespace Chapter02


/-- The bounded full original affine/nonlinear/integer model and unchanged objective are retained for arbitrary finite visits, including repeats or omissions. -/
theorem palomar_affine_source_preservation {n l r : ℕ} (D : BBPolyData n l r)
    (I : Finset (Fin n)) (X0 : AffineBox n) (visits : List (Fin r)) :
    D.feasible I ∩ (affineSourcePropagate D X0 visits).members =
      D.feasible I ∩ X0.members := by
  exact Chapter02.affine_source_preservation (n := n) (l := l) (r := r) (D := D) (I := I) (X0 := X0) (visits := visits)

end Chapter02

namespace Chapter02


/-- The bounded full original affine/nonlinear/integer model and unchanged objective are retained for arbitrary finite visits, including repeats or omissions. -/
theorem palomar_affine_source_empty_certificate {n l r : ℕ} (D : BBPolyData n l r)
    (I : Finset (Fin n)) (X0 : AffineBox n) (visits : List (Fin r))
    (he : affineSourcePropagate D X0 visits = .empty) :
    D.feasible I ∩ X0.members = ∅ := by
  exact Chapter02.affine_source_empty_certificate (n := n) (l := l) (r := r) (D := D) (I := I) (X0 := X0) (visits := visits) (he := he)

end Chapter02

namespace Chapter02


/-- The bounded full original affine/nonlinear/integer model and unchanged objective are retained for arbitrary finite visits, including repeats or omissions. -/
theorem palomar_affine_source_minimizer_iff {n l r : ℕ} (D : BBPolyData n l r)
    (I : Finset (Fin n)) (X0 : AffineBox n) (visits : List (Fin r))
    (x : RealVector n) :
    IsMinimizer (D.feasible I ∩ (affineSourcePropagate D X0 visits).members) D.f x ↔
      IsMinimizer (D.feasible I ∩ X0.members) D.f x := by
  exact Chapter02.affine_source_minimizer_iff (n := n) (l := l) (r := r) (D := D) (I := I) (X0 := X0) (visits := visits) (x := x)

end Chapter02

namespace Chapter02


/-- Actual relaxed coordinate certificates or compact attained extrema and a closed feasible-incumbent cutoff; no original hull or assumed attained bound. -/
theorem palomar_compact_tightest_coordinate_enclosure {E : Type*} [TopologicalSpace E] {n : ℕ}
    {R : Set E} (q : Fin n → E → ℝ) (hR : IsCompact R) (hne : R.Nonempty)
    (hq : ∀ i, ContinuousOn (q i) R) :
    ∃ L U : Fin n → ℝ,
      (∀ i, L i ≤ U i) ∧ R ⊆ coordinateEnclosure q L U ∧
      (∀ i, (∃ x ∈ R, q i x = L i) ∧ ∃ x ∈ R, q i x = U i) ∧
      ∀ L' U', R ⊆ coordinateEnclosure q L' U' →
        coordinateEnclosure q L U ⊆ coordinateEnclosure q L' U' := by
  exact Chapter02.compact_tightest_coordinate_enclosure (E := E) (n := n) (R := R) (q := q) (hR := hR) (hne := hne) (hq := hq)

end Chapter02

namespace Chapter02


/-- Actual relaxed coordinate certificates or compact attained extrema and a closed feasible-incumbent cutoff; no original hull or assumed attained bound. -/
theorem palomar_cutoff_bounds_preserve_minimizers {E : Type*} {n : ℕ}
    {F R : Set E} {f : E → ℝ} {u : ℝ} (q : Fin n → E → ℝ) (L U : Fin n → ℝ)
    (hinc : HasUpperBoundWitness F f u) (hR : cutoffSet F f u ⊆ R)
    (hL : ∀ i, IsLowerBound R (q i) (L i))
    (hU : ∀ i, IsLowerBound R (fun x => -q i x) (-U i)) (x : E) :
    IsMinimizer F f x ↔ IsMinimizer (F ∩ coordinateEnclosure q L U) f x := by
  exact Chapter02.cutoff_bounds_preserve_minimizers (E := E) (n := n) (F := F) (R := R) (f := f) (u := u) (q := q) (L := L) (U := U) (hinc := hinc) (hR := hR) (hL := hL) (hU := hU) (x := x)

end Chapter02

namespace Chapter02.BBPolyData
variable {N l r : ℕ}

/-- All deletion certificates use the same final retained row set; original nonlinear/integer restrictions, arbitrary base and objective persist. -/
theorem palomar_retained_feasible_eq_of_certificates (D : BBPolyData N l r)
    (I : Finset (Fin N)) (B : Set (RealVector N)) (K : Finset (Fin r))
    (cert : ∀ j, j ∉ K → D.RetainedRowCertificate K j) :
    D.retainedFeasible I B K = B ∩ D.feasible I := by
  exact Chapter02.BBPolyData.retained_feasible_eq_of_certificates (D := D) (I := I) (B := B) (K := K) (cert := cert)

end Chapter02.BBPolyData

namespace Chapter02.BBPolyData
variable {N l r : ℕ}

/-- All deletion certificates use the same final retained row set; original nonlinear/integer restrictions, arbitrary base and objective persist. -/
theorem palomar_retained_minimizer_iff_of_certificates (D : BBPolyData N l r)
    (I : Finset (Fin N)) (B : Set (RealVector N)) (K : Finset (Fin r))
    (cert : ∀ j, j ∉ K → D.RetainedRowCertificate K j) (z : RealVector N) :
    IsMinimizer (D.retainedFeasible I B K) D.f z ↔ IsMinimizer (B ∩ D.feasible I) D.f z := by
  exact Chapter02.BBPolyData.retained_minimizer_iff_of_certificates (D := D) (I := I) (B := B) (K := K) (cert := cert) (z := z)

end Chapter02.BBPolyData

namespace Chapter02.BBPolyData
variable {N l r : ℕ}

/-- All deletion certificates use the same final retained row set; original nonlinear/integer restrictions, arbitrary base and objective persist. -/
theorem palomar_feasible_coordinate_bounds (D : BBPolyData N l r) (I : Finset (Fin N))
    (B R : Set (RealVector N)) (L U : RealVector N)
    (hR : B ∩ D.feasible I ⊆ R)
    (hL : ∀ i, IsLowerBound R (fun z => z i) (L i))
    (hU : ∀ i, IsLowerBound R (fun z => -z i) (-U i)) :
    (B ∩ D.feasible I) ∩ coordinateEnclosure (fun i z => z i) L U = B ∩ D.feasible I := by
  exact Chapter02.BBPolyData.feasible_coordinate_bounds (D := D) (I := I) (B := B) (R := R) (L := L) (U := U) (hR := hR) (hL := hL) (hU := hU)

end Chapter02.BBPolyData

namespace Chapter02.BBPolyData
variable {N l r : ℕ}

/-- All deletion certificates use the same final retained row set; original nonlinear/integer restrictions, arbitrary base and objective persist. -/
theorem palomar_feasible_cutoff_bounds_minimizer_iff (D : BBPolyData N l r)
    (I : Finset (Fin N)) (B R : Set (RealVector N)) (L U : RealVector N) (u : ℝ)
    (hinc : HasUpperBoundWitness (B ∩ D.feasible I) D.f u)
    (hR : cutoffSet (B ∩ D.feasible I) D.f u ⊆ R)
    (hL : ∀ i, IsLowerBound R (fun z => z i) (L i))
    (hU : ∀ i, IsLowerBound R (fun z => -z i) (-U i)) (z : RealVector N) :
    IsMinimizer (B ∩ D.feasible I) D.f z ↔
      IsMinimizer ((B ∩ D.feasible I) ∩ coordinateEnclosure (fun i z => z i) L U) D.f z := by
  exact Chapter02.BBPolyData.feasible_cutoff_bounds_minimizer_iff (D := D) (I := I) (B := B) (R := R) (L := L) (U := U) (u := u) (hinc := hinc) (hR := hR) (hL := hL) (hU := hU) (z := z)

end Chapter02.BBPolyData

namespace Chapter02FBBT


/-- Complete qualified finite simultaneous (X,B) theory: actual public/raw runs, fixed states, independent scalar LP, conditional limit and unique full-width optimum. -/
theorem palomar_qualified_simultaneous_fbbt {n m} (A : Matrix n m) (q0 : JointBounds n m)
    (h0 : Ordered q0) : SimultaneousTheory A q0 := by
  exact Chapter02FBBT.qualified_simultaneous_fbbt (n := n) (m := m) (A := A) (q0 := q0) (h0 := h0)

end Chapter02FBBT

namespace Chapter02FBBT
open Chapter02
variable {n l r : ℕ}

/-- Complete bounded original-coordinate source theory; unconditional LP infeasibility and separately conditional nonempty-run limit/minimizer conclusions. -/
theorem palomar_qualified_source_fbbt (D : BBPolyData n l r) (I : Finset (Fin n))
    (X : Bounds (Fin n)) (hX : Ordered X) : SourceTheory D I X := by
  exact Chapter02FBBT.qualified_source_fbbt (D := D) (I := I) (X := X) (hX := hX)

end Chapter02FBBT

