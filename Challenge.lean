module

public import Mathlib

@[expose] public section

/-! Independent source-definition surface for the exact advertised obligations.
Computational definitions retain their full source bodies. Only the advertised
theorems contain deliberate holes. Solution never imports this module. -/
noncomputable section
open scoped BigOperators Topology
open Classical Filter Function Set

namespace Chapter02


/-- RealVector retains its literal source body and full parameter domain. -/
abbrev RealVector (n : ℕ) := Fin n → ℝ

/-- IsMinimizer retains its literal source body and full parameter domain. -/
def IsMinimizer {A : Type*} (S : Set A) (f : A → ℝ) (x : A) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, f x ≤ f y

/-- IsLowerBound retains its literal source body and full parameter domain. -/
def IsLowerBound {A : Type*} (S : Set A) (f : A → ℝ) (v : ℝ) : Prop :=
  ∀ x ∈ S, v ≤ f x

/-- HasUpperBoundWitness retains its literal source body and full parameter domain. -/
def HasUpperBoundWitness {A : Type*} (S : Set A) (f : A → ℝ) (v : ℝ) : Prop :=
  ∃ x ∈ S, f x ≤ v

/-- BBPolyData retains its literal source body and full parameter domain. -/
structure BBPolyData (N l r : ℕ) where
  coefficient : Fin r → RealVector N
  rhs : RealVector r
  c : RealVector N → RealVector l
  f : RealVector N → ℝ

/-- AffineBox retains its literal source body and full parameter domain. -/
inductive AffineBox (n : ℕ) where
  | empty
  | interval (lower upper : RealVector n) (ordered : ∀ i, lower i ≤ upper i)

/-- AffineBox.members retains its literal source body and full parameter domain. -/
def AffineBox.members {n : ℕ} : AffineBox n → Set (RealVector n)
  | .empty => ∅
  | .interval l u _ => {x | ∀ i, l i ≤ x i ∧ x i ≤ u i}

/-- AffineBox.ofBounds retains its literal source body and full parameter domain. -/
def AffineBox.ofBounds {n : ℕ} (l u : RealVector n) : AffineBox n :=
  if h : ∀ i, l i ≤ u i then .interval l u h else .empty

/-- affineProductLo retains its literal source body and full parameter domain. -/
def affineProductLo (a l u : ℝ) : ℝ := if 0 ≤ a then a*l else a*u

/-- affineProductHi retains its literal source body and full parameter domain. -/
def affineProductHi (a l u : ℝ) : ℝ := if 0 ≤ a then a*u else a*l

/-- AffineIntervalRow retains its literal source body and full parameter domain. -/
structure AffineIntervalRow (n : ℕ) where
  coefficient : RealVector n
  offset : ℝ
  lower : ℝ
  upper : ℝ

/-- AffineIntervalRow.value retains its literal source body and full parameter domain. -/
def AffineIntervalRow.value {n : ℕ} (r : AffineIntervalRow n) (x : RealVector n) : ℝ :=
  r.offset + ∑ i, r.coefficient i * x i

/-- AffineIntervalRow.Holds retains its literal source body and full parameter domain. -/
def AffineIntervalRow.Holds {n : ℕ} (r : AffineIntervalRow n) (x : RealVector n) : Prop :=
  r.lower ≤ r.value x ∧ r.value x ≤ r.upper

/-- AffineIntervalRow.imageLo retains its literal source body and full parameter domain. -/
def AffineIntervalRow.imageLo {n : ℕ} (r : AffineIntervalRow n)
    (l u : RealVector n) : ℝ :=
  r.offset + ∑ i, affineProductLo (r.coefficient i) (l i) (u i)

/-- AffineIntervalRow.imageHi retains its literal source body and full parameter domain. -/
def AffineIntervalRow.imageHi {n : ℕ} (r : AffineIntervalRow n)
    (l u : RealVector n) : ℝ :=
  r.offset + ∑ i, affineProductHi (r.coefficient i) (l i) (u i)

/-- AffineIntervalRow.restLo retains its literal source body and full parameter domain. -/
def AffineIntervalRow.restLo {n : ℕ} (r : AffineIntervalRow n)
    (l u : RealVector n) (j : Fin n) : ℝ :=
  ∑ i ∈ Finset.univ.erase j, affineProductLo (r.coefficient i) (l i) (u i)

/-- AffineIntervalRow.restHi retains its literal source body and full parameter domain. -/
def AffineIntervalRow.restHi {n : ℕ} (r : AffineIntervalRow n)
    (l u : RealVector n) (j : Fin n) : ℝ :=
  ∑ i ∈ Finset.univ.erase j, affineProductHi (r.coefficient i) (l i) (u i)

/-- AffineIntervalRow.impliedLo retains its literal source body and full parameter domain. -/
def AffineIntervalRow.impliedLo {n : ℕ} (r : AffineIntervalRow n)
    (l u : RealVector n) (L U : ℝ) (j : Fin n) : ℝ :=
  if r.coefficient j = 0 then l j else
  if 0 < r.coefficient j then (L-r.offset-r.restHi l u j)/r.coefficient j
  else (U-r.offset-r.restLo l u j)/r.coefficient j

/-- AffineIntervalRow.impliedHi retains its literal source body and full parameter domain. -/
def AffineIntervalRow.impliedHi {n : ℕ} (r : AffineIntervalRow n)
    (l u : RealVector n) (L U : ℝ) (j : Fin n) : ℝ :=
  if r.coefficient j = 0 then u j else
  if 0 < r.coefficient j then (U-r.offset-r.restLo l u j)/r.coefficient j
  else (L-r.offset-r.restHi l u j)/r.coefficient j

/-- affineRowStep retains its literal source body and full parameter domain. -/
/- Exact independently completed source-generated recursor; preserves the source module matcher identity. -/
abbrev affineRowStep.match_1.{u_1} : {n : Nat} →
  (motive : Chapter02.AffineBox n → Sort u_1) →
    (x : Chapter02.AffineBox n) →
      (h_1 : (_ : Unit) → motive (@Chapter02.AffineBox.empty n)) →
        (h_2 :
            (l u : Chapter02.RealVector n) →
              (ordered : ∀ (i : Fin n), @LE.le.{0} Real Real.instLE (l i) (u i)) →
                motive (@Chapter02.AffineBox.interval n l u ordered)) →
          motive x :=
fun {n : Nat} (motive : Chapter02.AffineBox n → Sort u_1) (x : Chapter02.AffineBox n)
    (h_1 : (_ : Unit) → motive (@Chapter02.AffineBox.empty n))
    (h_2 :
      (l u : Chapter02.RealVector n) →
        (ordered : ∀ (i : Fin n), @LE.le.{0} Real Real.instLE (l i) (u i)) →
          motive (@Chapter02.AffineBox.interval n l u ordered)) =>
  @Chapter02.AffineBox.casesOn.{u_1} n (fun (x : Chapter02.AffineBox n) => motive x) x (h_1 Unit.unit)
    fun (lower upper : Chapter02.RealVector n)
      (ordered : ∀ (i : Fin n), @LE.le.{0} Real Real.instLE (lower i) (upper i)) =>
    h_2 lower upper ordered

def affineRowStep : {n : Nat} →
  (r : Chapter02.AffineIntervalRow n) → Chapter02.AffineBox n → Chapter02.AffineBox n :=
fun {n : Nat} (r : Chapter02.AffineIntervalRow n) (x : Chapter02.AffineBox n) =>
  @Chapter02.affineRowStep.match_1.{1} n (fun (x : Chapter02.AffineBox n) => Chapter02.AffineBox n) x
    (fun (_ : Unit) => @Chapter02.AffineBox.empty n)
    fun (l u : Chapter02.RealVector n) (ordered : ∀ (i : Fin n), @LE.le.{0} Real Real.instLE (l i) (u i)) =>
    have L : Real :=
      @Max.max.{0} Real Real.instMax (@Chapter02.AffineIntervalRow.lower n r)
        (@Chapter02.AffineIntervalRow.imageLo n r l u);
    have U : Real :=
      @Min.min.{0} Real Real.instMin (@Chapter02.AffineIntervalRow.upper n r)
        (@Chapter02.AffineIntervalRow.imageHi n r l u);
    @ite.{1} (Chapter02.AffineBox n) (@LE.le.{0} Real Real.instLE L U) (Real.decidableLE L U)
      (@Chapter02.AffineBox.ofBounds n
        (fun (j : Fin n) => @Max.max.{0} Real Real.instMax (l j) (@Chapter02.AffineIntervalRow.impliedLo n r l u L U j))
        fun (j : Fin n) => @Min.min.{0} Real Real.instMin (u j) (@Chapter02.AffineIntervalRow.impliedHi n r l u L U j))
      (@Chapter02.AffineBox.empty n)

/-- affinePropagate retains its literal source body and full parameter domain. -/
def affinePropagate {n : ℕ} : List (AffineIntervalRow n) → AffineBox n → AffineBox n
  | [], X => X
  | r :: rs, X => affinePropagate rs (affineRowStep r X)

/-- affineSourceRow retains its literal source body and full parameter domain. -/
/- Exact independently completed source-generated recursor; preserves the source module matcher identity. -/
abbrev affineSourceRow.match_1.{u_1} : {n : Nat} →
  (motive : Chapter02.AffineBox n → Sort u_1) →
    (X0 : Chapter02.AffineBox n) →
      (h_1 : (_ : Unit) → motive (@Chapter02.AffineBox.empty n)) →
        (h_2 :
            (a b : Chapter02.RealVector n) →
              (ordered : ∀ (i : Fin n), @LE.le.{0} Real Real.instLE (a i) (b i)) →
                motive (@Chapter02.AffineBox.interval n a b ordered)) →
          motive X0 :=
fun {n : Nat} (motive : Chapter02.AffineBox n → Sort u_1) (X0 : Chapter02.AffineBox n)
    (h_1 : (_ : Unit) → motive (@Chapter02.AffineBox.empty n))
    (h_2 :
      (a b : Chapter02.RealVector n) →
        (ordered : ∀ (i : Fin n), @LE.le.{0} Real Real.instLE (a i) (b i)) →
          motive (@Chapter02.AffineBox.interval n a b ordered)) =>
  @Chapter02.AffineBox.casesOn.{u_1} n (fun (x : Chapter02.AffineBox n) => motive x) X0 (h_1 Unit.unit)
    fun (lower upper : Chapter02.RealVector n)
      (ordered : ∀ (i : Fin n), @LE.le.{0} Real Real.instLE (lower i) (upper i)) =>
    h_2 lower upper ordered

def affineSourceRow : {n l r : Nat} →
  (D : Chapter02.BBPolyData n l r) → (X0 : Chapter02.AffineBox n) → (i : Fin r) → Chapter02.AffineIntervalRow n :=
fun {n l r : Nat} (D : Chapter02.BBPolyData n l r) (X0 : Chapter02.AffineBox n) (i : Fin r) =>
  @Chapter02.AffineIntervalRow.mk n (@Chapter02.BBPolyData.coefficient n l r D i)
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (@Chapter02.affineSourceRow.match_1.{1} n (fun (X0 : Chapter02.AffineBox n) => Real) X0
      (fun (_ : Unit) => @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      fun (a b : Chapter02.RealVector n) (ordered : ∀ (i : Fin n), @LE.le.{0} Real Real.instLE (a i) (b i)) =>
      @Finset.sum.{0, 0} (Fin n) Real Real.instAddCommMonoid (@Finset.univ.{0} (Fin n) (Fin.fintype n))
        fun (j : Fin n) => Chapter02.affineProductLo (@Chapter02.BBPolyData.coefficient n l r D i j) (a j) (b j))
    (@Chapter02.BBPolyData.rhs n l r D i)

/-- affineSourcePropagate retains its literal source body and full parameter domain. -/
def affineSourcePropagate {n l r : ℕ} (D : BBPolyData n l r)
    (X0 : AffineBox n) (visits : List (Fin r)) : AffineBox n :=
  affinePropagate (visits.map (affineSourceRow D X0)) X0

/-- coordinateEnclosure retains its literal source body and full parameter domain. -/
def coordinateEnclosure {E : Type*} {n : ℕ} (q : Fin n → E → ℝ)
    (L U : Fin n → ℝ) : Set E :=
  {x | ∀ i, L i ≤ q i x ∧ q i x ≤ U i}

/-- cutoffSet retains its literal source body and full parameter domain. -/
def cutoffSet {E : Type*} (F : Set E) (f : E → ℝ) (u : ℝ) : Set E :=
  {x | x ∈ F ∧ f x ≤ u}

end Chapter02

namespace Chapter02.BBPolyData
variable {N l r : ℕ}

/-- polyhedron retains its literal source body and full parameter domain. -/
def polyhedron (D : BBPolyData N l r) : Set (RealVector N) :=
  {z | ∀ j, ∑ i, D.coefficient j i * z i ≤ D.rhs j}

/-- feasible retains its literal source body and full parameter domain. -/
def feasible (D : BBPolyData N l r) (I : Finset (Fin N)) : Set (RealVector N) :=
  {z | z ∈ D.polyhedron ∧ (∀ j, D.c z j ≤ 0) ∧
    ∀ i : {i : Fin N // i ∈ I}, ∃ k : ℤ, (k : ℝ) = z i}

/-- retainedPolyhedron retains its literal source body and full parameter domain. -/
def retainedPolyhedron (D : BBPolyData N l r) (K : Finset (Fin r)) : Set (RealVector N) :=
  {z | ∀ j ∈ K, ∑ i, D.coefficient j i * z i ≤ D.rhs j}

/-- retainedContinuous retains its literal source body and full parameter domain. -/
def retainedContinuous (D : BBPolyData N l r) (B : Set (RealVector N))
    (K : Finset (Fin r)) : Set (RealVector N) :=
  {z | z ∈ B ∧ z ∈ D.retainedPolyhedron K ∧ ∀ j, D.c z j ≤ 0}

/-- retainedFeasible retains its literal source body and full parameter domain. -/
def retainedFeasible (D : BBPolyData N l r) (I : Finset (Fin N))
    (B : Set (RealVector N)) (K : Finset (Fin r)) : Set (RealVector N) :=
  {z | z ∈ D.retainedContinuous B K ∧
    ∀ i : {i : Fin N // i ∈ I}, ∃ k : ℤ, (k : ℝ) = z i}

/-- RetainedRowCertificate retains its literal source body and full parameter domain. -/
structure RetainedRowCertificate (D : BBPolyData N l r) (K : Finset (Fin r))
    (j : Fin r) where
  weight : Fin r → ℝ
  nonneg : ∀ k ∈ K, 0 ≤ weight k
  coefficient_eq : ∀ i, D.coefficient j i = ∑ k ∈ K, weight k * D.coefficient k i
  rhs_le : (∑ k ∈ K, weight k * D.rhs k) ≤ D.rhs j

end Chapter02.BBPolyData

namespace Chapter02FBBT


/-- Bounds retains its literal source body and full parameter domain. -/
abbrev Bounds (ι : Type*) := (ι → ℝ) × (ι → ℝ)

/-- Ordered retains its literal source body and full parameter domain. -/
def Ordered {ι : Type*} (q : Bounds ι) : Prop := ∀ i, q.1 i ≤ q.2 i

/-- Within retains its literal source body and full parameter domain. -/
def Within {ι : Type*} (q r : Bounds ι) : Prop :=
  ∀ i, r.1 i ≤ q.1 i ∧ q.2 i ≤ r.2 i

/-- members retains its literal source body and full parameter domain. -/
def members {ι : Type*} (q : Bounds ι) : Set (ι → ℝ) :=
  {x | ∀ i, q.1 i ≤ x i ∧ x i ≤ q.2 i}

/-- width retains its literal source body and full parameter domain. -/
def width {ι : Type*} [Fintype ι] (q : Bounds ι) : ℝ :=
  ∑ i, (q.2 i - q.1 i)

/-- clip retains its literal source body and full parameter domain. -/
def clip {ι : Type*} (q r : Bounds ι) : Bounds ι :=
  (fun i => max (q.1 i) (r.1 i), fun i => min (q.2 i) (r.2 i))

/-- Coordinates retains its literal source body and full parameter domain. -/
abbrev Coordinates (n m : ℕ) := Fin n ⊕ Fin m

/-- Matrix retains its literal source body and full parameter domain. -/
abbrev Matrix (n m : ℕ) := Fin m → Fin n → ℝ

/-- JointBounds retains its literal source body and full parameter domain. -/
abbrev JointBounds (n m : ℕ) := Bounds (Coordinates n m)

/-- productLo retains its literal source body and full parameter domain. -/
def productLo {n m} (A : Matrix n m) (q : JointBounds n m) (i : Fin m) (j : Fin n) :=
  Chapter02.affineProductLo (A i j) (q.1 (.inl j)) (q.2 (.inl j))

/-- productHi retains its literal source body and full parameter domain. -/
def productHi {n m} (A : Matrix n m) (q : JointBounds n m) (i : Fin m) (j : Fin n) :=
  Chapter02.affineProductHi (A i j) (q.1 (.inl j)) (q.2 (.inl j))

/-- imageLo retains its literal source body and full parameter domain. -/
def imageLo {n m} (A : Matrix n m) (q : JointBounds n m) (i : Fin m) :=
  ∑ j, productLo A q i j

/-- imageHi retains its literal source body and full parameter domain. -/
def imageHi {n m} (A : Matrix n m) (q : JointBounds n m) (i : Fin m) :=
  ∑ j, productHi A q i j

/-- restLo retains its literal source body and full parameter domain. -/
def restLo {n m} (A : Matrix n m) (q : JointBounds n m) (i : Fin m) (j : Fin n) :=
  ∑ k ∈ Finset.univ.erase j, productLo A q i k

/-- restHi retains its literal source body and full parameter domain. -/
def restHi {n m} (A : Matrix n m) (q : JointBounds n m) (i : Fin m) (j : Fin n) :=
  ∑ k ∈ Finset.univ.erase j, productHi A q i k

/-- inverseLo retains its literal source body and full parameter domain. -/
def inverseLo {n m} (A : Matrix n m) (q : JointBounds n m) (i : Fin m) (j : Fin n) :=
  if A i j = 0 then q.1 (.inl j) else
  if 0 < A i j then (q.1 (.inr i) - restHi A q i j) / A i j
  else (q.2 (.inr i) - restLo A q i j) / A i j

/-- inverseHi retains its literal source body and full parameter domain. -/
def inverseHi {n m} (A : Matrix n m) (q : JointBounds n m) (i : Fin m) (j : Fin n) :=
  if A i j = 0 then q.2 (.inl j) else
  if 0 < A i j then (q.2 (.inr i) - restLo A q i j) / A i j
  else (q.1 (.inr i) - restHi A q i j) / A i j

/-- seededMax retains its literal source body and full parameter domain. -/
def seededMax {m} (seed : ℝ) (v : Fin m → ℝ) : ℝ :=
  Finset.univ.sup' ⟨none, Finset.mem_univ _⟩ (fun o : Option (Fin m) => o.elim seed v)

/-- seededMin retains its literal source body and full parameter domain. -/
def seededMin {m} (seed : ℝ) (v : Fin m → ℝ) : ℝ :=
  Finset.univ.inf' ⟨none, Finset.mem_univ _⟩ (fun o : Option (Fin m) => o.elim seed v)

/-- upward retains its literal source body and full parameter domain. -/
def upward {n m} (A : Matrix n m) (q : JointBounds n m) : JointBounds n m :=
  (Sum.elim (fun j => q.1 (.inl j)) (fun i => max (q.1 (.inr i)) (imageLo A q i)),
   Sum.elim (fun j => q.2 (.inl j)) (fun i => min (q.2 (.inr i)) (imageHi A q i)))

/-- downward retains its literal source body and full parameter domain. -/
def downward {n m} (A : Matrix n m) (q : JointBounds n m) : JointBounds n m :=
  (Sum.elim (fun j => seededMax (q.1 (.inl j)) (fun i => inverseLo A q i j))
      (fun i => q.1 (.inr i)),
   Sum.elim (fun j => seededMin (q.2 (.inl j)) (fun i => inverseHi A q i j))
      (fun i => q.2 (.inr i)))

/-- rawF retains its literal source body and full parameter domain. -/
def rawF {n m} (A : Matrix n m) (q0 q : JointBounds n m) : JointBounds n m :=
  downward A (upward A (clip q q0))

/-- rawRun retains its literal source body and full parameter domain. -/
def rawRun {n m} (A : Matrix n m) (q0 : JointBounds n m) (k : ℕ) :=
  (rawF A q0)^[k] q0

/-- graph retains its literal source body and full parameter domain. -/
def graph {n m} (A : Matrix n m) (x : Fin n → ℝ) : Coordinates n m → ℝ :=
  Sum.elim x (fun i => ∑ j, A i j * x j)

/-- PublicState retains its literal source body and full parameter domain. -/
inductive PublicState (ι : Type*) where
  | empty
  | box (q : Bounds ι) (ordered : Ordered q)

/-- publicOfBounds retains its literal source body and full parameter domain. -/
def publicOfBounds {ι} (q : Bounds ι) : PublicState ι :=
  if h : Ordered q then .box q h else .empty

/-- PublicState.members retains its literal source body and full parameter domain. -/
def PublicState.members {ι} : PublicState ι → Set (ι → ℝ)
  | .empty => ∅
  | .box q _ => Chapter02FBBT.members q

/-- publicF retains its literal source body and full parameter domain. -/
def publicF {n m} (A : Matrix n m) (q0 : JointBounds n m) :
    PublicState (Coordinates n m) → PublicState (Coordinates n m)
  | .empty => .empty
  | .box q _ => publicOfBounds (rawF A q0 q)

/-- publicRun retains its literal source body and full parameter domain. -/
def publicRun {n m} (A : Matrix n m) (q0 : JointBounds n m) (k : ℕ) :=
  (publicF A q0)^[k] (publicOfBounds q0)

/-- LPAssignment retains its literal source body and full parameter domain. -/
structure LPAssignment (n m : ℕ) where
  bounds : JointBounds n m
  zLo : Fin m → Fin n → ℝ
  zHi : Fin m → Fin n → ℝ

/-- LPFeasible retains its literal source body and full parameter domain. -/
def LPFeasible {n m} (A : Matrix n m) (q0 : JointBounds n m)
    (p : LPAssignment n m) : Prop :=
  Ordered p.bounds ∧ Within p.bounds q0 ∧
  (∀ i j, p.zLo i j = productLo A p.bounds i j) ∧
  (∀ i j, p.zHi i j = productHi A p.bounds i j) ∧
  (∀ i, (∑ j, p.zLo i j) ≤ p.bounds.1 (.inr i) ∧
    p.bounds.2 (.inr i) ≤ ∑ j, p.zHi i j) ∧
  (∀ i j, 0 < A i j →
    (p.bounds.1 (.inr i) - ∑ k ∈ Finset.univ.erase j, p.zHi i k) / A i j ≤
      p.bounds.1 (.inl j) ∧
    p.bounds.2 (.inl j) ≤
      (p.bounds.2 (.inr i) - ∑ k ∈ Finset.univ.erase j, p.zLo i k) / A i j) ∧
  (∀ i j, A i j < 0 →
    (p.bounds.2 (.inr i) - ∑ k ∈ Finset.univ.erase j, p.zLo i k) / A i j ≤
      p.bounds.1 (.inl j) ∧
    p.bounds.2 (.inl j) ≤
      (p.bounds.1 (.inr i) - ∑ k ∈ Finset.univ.erase j, p.zHi i k) / A i j)

/-- canonicalAssignment retains its literal source body and full parameter domain. -/
def canonicalAssignment {n m} (A : Matrix n m) (q : JointBounds n m) : LPAssignment n m :=
  ⟨q, productLo A q, productHi A q⟩

/-- LPObjective retains its literal source body and full parameter domain. -/
def LPObjective {n m} (p : LPAssignment n m) : ℝ := width p.bounds

end Chapter02FBBT

namespace Chapter02FBBT
variable {ι : Type*}

/-- endpointLimit retains its literal source body and full parameter domain. -/
def endpointLimit (F : Bounds ι → Bounds ι) (q0 : Bounds ι) : Bounds ι :=
  (fun i => ⨆ k : ℕ, (F^[k] q0).1 i,
   fun i => ⨅ k : ℕ, (F^[k] q0).2 i)

end Chapter02FBBT

namespace Chapter02FBBT


/-- limitBounds retains its literal source body and full parameter domain. -/
def limitBounds {n m} (A : Matrix n m) (q0 : JointBounds n m) :=
  endpointLimit (rawF A q0) q0

/-- RunNonempty retains its literal source body and full parameter domain. -/
def RunNonempty {n m} (A : Matrix n m) (q0 : JointBounds n m) : Prop :=
  ∀ k, (publicRun A q0 k).members.Nonempty

/-- FixedExists retains its literal source body and full parameter domain. -/
def FixedExists {n m} (A : Matrix n m) (q0 : JointBounds n m) : Prop :=
  ∃ q, Ordered q ∧ rawF A q0 q = q

/-- SimultaneousConclusion retains its literal source body and full parameter domain. -/
structure SimultaneousConclusion {n m} (A : Matrix n m) (q0 : JointBounds n m) : Prop where
  limitOrdered : Ordered (limitBounds A q0)
  limitWithinInitial : Within (limitBounds A q0) q0
  actualEndpointConvergence : Tendsto (rawRun A q0) atTop (𝓝 (limitBounds A q0))
  actualFixed : rawF A q0 (limitBounds A q0) = limitBounds A q0
  greatestNonemptyFixed : ∀ q, Ordered q → rawF A q0 q = q → Within q (limitBounds A q0)
  attainedLP : LPFeasible A q0 (canonicalAssignment A (limitBounds A q0))
  globalWidthMaximum : ∀ p, LPFeasible A q0 p →
    LPObjective p ≤ LPObjective (canonicalAssignment A (limitBounds A q0))
  uniqueEntireAssignment : ∀ p, LPFeasible A q0 p →
    LPObjective (canonicalAssignment A (limitBounds A q0)) ≤ LPObjective p →
    p = canonicalAssignment A (limitBounds A q0)
  graphSurvivesEveryIteration : ∀ x, graph A x ∈ members q0 → ∀ k,
    graph A x ∈ members (rawRun A q0 k)
  graphSurvivesLimit : ∀ x, graph A x ∈ members q0 → graph A x ∈ members (limitBounds A q0)

/-- SimultaneousTheory retains its literal source body and full parameter domain. -/
structure SimultaneousTheory {n m} (A : Matrix n m) (q0 : JointBounds n m) : Prop where
  initialOrdered : Ordered q0
  runIffFixed : RunNonempty A q0 ↔ FixedExists A q0
  fixedIffLP : FixedExists A q0 ↔ ∃ p, LPFeasible A q0 p
  publicRawAgreement : ∀ k, publicRun A q0 k = publicOfBounds (rawRun A q0 k)
  conditionalConclusion : RunNonempty A q0 → SimultaneousConclusion A q0
  unconditionalInfeasibility : (¬ ∃ p, LPFeasible A q0 p) → ¬ ∃ x, graph A x ∈ members q0

end Chapter02FBBT

namespace Chapter02FBBT
open Chapter02
variable {n l r : ℕ}

/-- sourceLower retains its literal source body and full parameter domain. -/
def sourceLower (D : BBPolyData n l r) (X : Bounds (Fin n)) (i : Fin r) : ℝ :=
  min (∑ j, affineProductLo (D.coefficient i j) (X.1 j) (X.2 j)) (D.rhs i)

/-- sourceInitial retains its literal source body and full parameter domain. -/
def sourceInitial (D : BBPolyData n l r) (X : Bounds (Fin n)) :
    Bounds (Fin n ⊕ Fin r) :=
  (Sum.elim X.1 (sourceLower D X), Sum.elim X.2 D.rhs)

/-- sourceGraph retains its literal source body and full parameter domain. -/
def sourceGraph (D : BBPolyData n l r) (x : RealVector n) :
    (Fin n ⊕ Fin r) → ℝ :=
  Sum.elim x (fun i => ∑ j, D.coefficient i j * x j)

/-- sourceLimitX retains its literal source body and full parameter domain. -/
def sourceLimitX (D : BBPolyData n l r) (X : Bounds (Fin n)) : Bounds (Fin n) :=
  (fun j => (limitBounds D.coefficient (sourceInitial D X)).1 (.inl j),
   fun j => (limitBounds D.coefficient (sourceInitial D X)).2 (.inl j))

/-- SourceConclusion retains its literal source body and full parameter domain. -/
structure SourceConclusion (D : BBPolyData n l r) (I : Finset (Fin n))
    (X : Bounds (Fin n)) : Prop where
  originalBoundedSetEquality :
    D.feasible I ∩ members (sourceLimitX D X) = D.feasible I ∩ members X
  originalObjectiveMinimizerEquivalence : ∀ x,
    IsMinimizer (D.feasible I ∩ members (sourceLimitX D X)) D.f x ↔
      IsMinimizer (D.feasible I ∩ members X) D.f x
  finiteLimitOrdered : Ordered (sourceLimitX D X)
  finiteLimitWithin : Within (sourceLimitX D X) X

/-- SourceTheory retains its literal source body and full parameter domain. -/
structure SourceTheory (D : BBPolyData n l r) (I : Finset (Fin n))
    (X : Bounds (Fin n)) : Prop where
  core : SimultaneousTheory D.coefficient (sourceInitial D X)
  initialRowEquivalence : ∀ x,
    sourceGraph D x ∈ members (sourceInitial D X) ↔ x ∈ members X ∧ x ∈ D.polyhedron
  unconditionalSourceInfeasibility :
    (¬ ∃ p, LPFeasible D.coefficient (sourceInitial D X) p) → D.feasible I ∩ members X = ∅
  conditionalSourceConclusion : RunNonempty D.coefficient (sourceInitial D X) →
    SourceConclusion D I X

end Chapter02FBBT

namespace Chapter02


/-- Every literal finite schedule contracts its input Cartesian members. -/
theorem palomar_affine_propagate_contracts {n : ℕ} (rows : List (AffineIntervalRow n))
    (X : AffineBox n) : (affinePropagate rows X).members ⊆ X.members := by
  sorry

end Chapter02

namespace Chapter02


/-- The bounded full original affine/nonlinear/integer model and unchanged objective are retained for arbitrary finite visits, including repeats or omissions. -/
theorem palomar_affine_source_preservation {n l r : ℕ} (D : BBPolyData n l r)
    (I : Finset (Fin n)) (X0 : AffineBox n) (visits : List (Fin r)) :
    D.feasible I ∩ (affineSourcePropagate D X0 visits).members =
      D.feasible I ∩ X0.members := by
  sorry

end Chapter02

namespace Chapter02


/-- The bounded full original affine/nonlinear/integer model and unchanged objective are retained for arbitrary finite visits, including repeats or omissions. -/
theorem palomar_affine_source_empty_certificate {n l r : ℕ} (D : BBPolyData n l r)
    (I : Finset (Fin n)) (X0 : AffineBox n) (visits : List (Fin r))
    (he : affineSourcePropagate D X0 visits = .empty) :
    D.feasible I ∩ X0.members = ∅ := by
  sorry

end Chapter02

namespace Chapter02


/-- The bounded full original affine/nonlinear/integer model and unchanged objective are retained for arbitrary finite visits, including repeats or omissions. -/
theorem palomar_affine_source_minimizer_iff {n l r : ℕ} (D : BBPolyData n l r)
    (I : Finset (Fin n)) (X0 : AffineBox n) (visits : List (Fin r))
    (x : RealVector n) :
    IsMinimizer (D.feasible I ∩ (affineSourcePropagate D X0 visits).members) D.f x ↔
      IsMinimizer (D.feasible I ∩ X0.members) D.f x := by
  sorry

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
  sorry

end Chapter02

namespace Chapter02


/-- Actual relaxed coordinate certificates or compact attained extrema and a closed feasible-incumbent cutoff; no original hull or assumed attained bound. -/
theorem palomar_cutoff_bounds_preserve_minimizers {E : Type*} {n : ℕ}
    {F R : Set E} {f : E → ℝ} {u : ℝ} (q : Fin n → E → ℝ) (L U : Fin n → ℝ)
    (hinc : HasUpperBoundWitness F f u) (hR : cutoffSet F f u ⊆ R)
    (hL : ∀ i, IsLowerBound R (q i) (L i))
    (hU : ∀ i, IsLowerBound R (fun x => -q i x) (-U i)) (x : E) :
    IsMinimizer F f x ↔ IsMinimizer (F ∩ coordinateEnclosure q L U) f x := by
  sorry

end Chapter02

namespace Chapter02.BBPolyData
variable {N l r : ℕ}

/-- All deletion certificates use the same final retained row set; original nonlinear/integer restrictions, arbitrary base and objective persist. -/
theorem palomar_retained_feasible_eq_of_certificates (D : BBPolyData N l r)
    (I : Finset (Fin N)) (B : Set (RealVector N)) (K : Finset (Fin r))
    (cert : ∀ j, j ∉ K → D.RetainedRowCertificate K j) :
    D.retainedFeasible I B K = B ∩ D.feasible I := by
  sorry

end Chapter02.BBPolyData

namespace Chapter02.BBPolyData
variable {N l r : ℕ}

/-- All deletion certificates use the same final retained row set; original nonlinear/integer restrictions, arbitrary base and objective persist. -/
theorem palomar_retained_minimizer_iff_of_certificates (D : BBPolyData N l r)
    (I : Finset (Fin N)) (B : Set (RealVector N)) (K : Finset (Fin r))
    (cert : ∀ j, j ∉ K → D.RetainedRowCertificate K j) (z : RealVector N) :
    IsMinimizer (D.retainedFeasible I B K) D.f z ↔ IsMinimizer (B ∩ D.feasible I) D.f z := by
  sorry

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
  sorry

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
  sorry

end Chapter02.BBPolyData

namespace Chapter02FBBT


/-- Complete qualified finite simultaneous (X,B) theory: actual public/raw runs, fixed states, independent scalar LP, conditional limit and unique full-width optimum. -/
theorem palomar_qualified_simultaneous_fbbt {n m} (A : Matrix n m) (q0 : JointBounds n m)
    (h0 : Ordered q0) : SimultaneousTheory A q0 := by
  sorry

end Chapter02FBBT

namespace Chapter02FBBT
open Chapter02
variable {n l r : ℕ}

/-- Complete bounded original-coordinate source theory; unconditional LP infeasibility and separately conditional nonempty-run limit/minimizer conclusions. -/
theorem palomar_qualified_source_fbbt (D : BBPolyData n l r) (I : Finset (Fin n))
    (X : Bounds (Fin n)) (hX : Ordered X) : SourceTheory D I X := by
  sorry

end Chapter02FBBT
