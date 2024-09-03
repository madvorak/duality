import Mathlib.Algebra.Order.Pi
import Duality.LinearProgramming

/-!
We prove properties of "normal" linear programs as a corollary of properties of extended linear programs.
The only exception is the weak duality theorem, which is proved separately, to allow weaker assumptions.
-/


/-- Linear program in the standard form. Variables are of type `J`. Conditions are indexed by type `I`.
    The objective function is intended to be minimized. -/
structure StandardLP (I J R : Type*) where
  /-- The left-hand-side matrix -/
  A : Matrix I J R
  /-- The right-hand-side vector -/
  b : I → R
  /-- The objective function coefficients -/
  c : J → R


variable {I R : Type*}

@[coe] def coeNN [OrderedAddCommMonoid R] : (I → R≥0) → (I → R) := (Subtype.val ∘ ·)

instance [OrderedAddCommMonoid R] : Coe (I → R≥0) (I → R) := ⟨coeNN⟩

open scoped Matrix

variable {J : Type*} [Fintype J]

/-- Vector `x` is a solution to linear program `P` iff all entries of `x` are nonnegative and its
    multiplication by matrix `A` from the left yields a vector whose all entries are less or equal
    to corresponding entries of the vector `b`. -/
def StandardLP.IsSolution [OrderedSemiring R] (P : StandardLP I J R) (x : J → R≥0) : Prop :=
  P.A *ᵥ x ≤ P.b

/-- Linear program `P` reaches objective value `r` iff there is a solution `x` such that,
    when its entries are elementwise multiplied by the the coefficients `c` and summed up,
    the result is the value `r`. -/
def StandardLP.Reaches [OrderedSemiring R] (P : StandardLP I J R) (r : R) : Prop :=
  ∃ x : J → R≥0, P.IsSolution x ∧ P.c ⬝ᵥ x = r

/-- Linear program `P` is feasible iff there exists a vector `x` that is a solution to `P`. -/
def StandardLP.IsFeasible [OrderedSemiring R] (P : StandardLP I J R) : Prop :=
  ∃ r : R, P.Reaches r

/-- Linear program `P` is bounded by `r` iff every value reached by `P` is
    greater or equal to `r` (i.e., `P` is bounded from below). -/
def StandardLP.IsBoundedBy [OrderedSemiring R] (P : StandardLP I J R) (r : R) : Prop :=
  ∀ p : R, P.Reaches p → r ≤ p

/-- Linear program `P` is unbounded iff values reached by `P` have no lower bound. -/
def StandardLP.IsUnbounded [OrderedSemiring R] (P : StandardLP I J R) : Prop :=
  ¬∃ r : R, P.IsBoundedBy r

/-- Dualize a linear program in the standard form. Both LPs are intended to be minimized. -/
def StandardLP.dualize [Ring R] (P : StandardLP I J R) : StandardLP J I R :=
  ⟨-P.Aᵀ, P.c, P.b⟩


variable [Fintype I]

lemma Matrix.transpose_mulVec_dotProduct [CommSemiring R] (M : Matrix I J R) (v : I → R) (w : J → R) :
    Mᵀ *ᵥ v ⬝ᵥ w = M *ᵥ w ⬝ᵥ v := by
  rw [Matrix.dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem StandardLP.weakDuality [OrderedCommRing R] {P : StandardLP I J R}
    {p : R} (hP : P.Reaches p) {q : R} (hQ : P.dualize.Reaches q) :
    0 ≤ p + q := by
  obtain ⟨x, hxb, rfl⟩ := hP
  obtain ⟨y, hyc, rfl⟩ := hQ
  have hyxx : (-P.Aᵀ) *ᵥ ↑y ⬝ᵥ ↑x ≤ P.c ⬝ᵥ ↑x :=
    Matrix.dotProduct_le_dotProduct_of_nonneg_right hyc (fun j : J => (x j).property)
  have hxyy : P.A *ᵥ ↑x ⬝ᵥ ↑y ≤ P.b ⬝ᵥ ↑y :=
    Matrix.dotProduct_le_dotProduct_of_nonneg_right hxb (fun i : I => (y i).property)
  rw [Matrix.neg_mulVec, Matrix.neg_dotProduct, neg_le] at hyxx
  rw [Matrix.transpose_mulVec_dotProduct] at hyxx
  exact neg_le_iff_add_nonneg'.mp (hyxx.trans hxyy)


variable [LinearOrderedField R]

open scoped Classical in
/-- The "optimum" of "minimization LP" (the less the better). -/
noncomputable def StandardLP.optimum (P : StandardLP I J R) : Option R∞ :=
  if P.IsFeasible then
    if P.IsUnbounded then
      some ⊥ -- unbounded means that the minimum is `⊥`
    else
      if hf : ∃ r : R, P.Reaches r ∧ P.IsBoundedBy r then
        some (toE hf.choose) -- the minimum exists
      else
        none -- invalid finite value (infimum is not attained; later, we prove it cannot happen)
  else
    some ⊤ -- infeasible means that the minimum is `⊤`


private def StandardLP.toExtendedLP (P : StandardLP I J R) : ExtendedLP I J R :=
  ⟨P.A.map toE, toE ∘ P.b, toE ∘ P.c, by aesop, by aesop, by aesop, by aesop, by aesop, by aesop⟩

private lemma StandardLP.toE_dotProduct_apply (P : StandardLP I J R) (x : J → R≥0) :
    toE (P.c ⬝ᵥ ↑x) = (toE ∘ P.c ᵥ⬝ x) := by
  simp_rw [Matrix.dotProduct, Matrix.dotProd, mul_comm]
  apply Finset.sum_toE

private lemma StandardLP.toE_mulVec_apply (P : StandardLP I J R) (x : J → R≥0) (i : I) :
    toE ((P.A *ᵥ ↑x) i) = (P.A.map toE ₘ* x) i := by
  simp_rw [Matrix.mulVec, Matrix.mulWeig, Matrix.map, Matrix.dotProduct, Matrix.dotProd, Matrix.of_apply, mul_comm]
  apply Finset.sum_toE

private lemma StandardLP.toExtendedLP.IsSolution_iff (P : StandardLP I J R) (x : J → R≥0) :
    P.toExtendedLP.IsSolution x ↔ P.IsSolution x := by
  show P.A.map toE ₘ* x ≤ toE ∘ P.b ↔ P.A *ᵥ x ≤ P.b
  simp [Pi.le_def, ←EF.coe_le_coe_iff, StandardLP.toE_mulVec_apply]

private lemma StandardLP.toExtendedLP.Reaches_iff (P : StandardLP I J R) (r : R) :
    P.toExtendedLP.Reaches r ↔ P.Reaches r := by
  peel with x
  apply and_congr
  · apply StandardLP.toExtendedLP.IsSolution_iff
  · exact P.toE_dotProduct_apply x ▸ EF.coe_eq_coe_iff

private lemma StandardLP.toExtendedLP.IsFeasible_iff (P : StandardLP I J R) :
    P.toExtendedLP.IsFeasible ↔ P.IsFeasible := by
  constructor
  · intro ⟨r, ⟨x, hx, hxr⟩, hr⟩
    match r with
    | ⊥ =>
      exfalso
      rw [←Matrix.dotProd_eq_bot] at hxr
      simp [StandardLP.toExtendedLP] at hxr
    | ⊤ =>
      exfalso
      exact hr rfl
    | (p : R) =>
      refine ⟨p, x, ?_, ?_⟩
      · rwa [StandardLP.toExtendedLP.IsSolution_iff] at hx
      · rwa [←EF.coe_eq_coe_iff, P.toE_dotProduct_apply]
  · intro ⟨r, x, hx, hxr⟩
    refine ⟨toE r, ⟨x, ?_, ?_⟩, EF.coe_neq_top r⟩
    · rwa [StandardLP.toExtendedLP.IsSolution_iff]
    · rwa [←EF.coe_eq_coe_iff, P.toE_dotProduct_apply] at hxr

private lemma StandardLP.toExtendedLP.IsBoundedBy_iff (P : StandardLP I J R) (r : R) :
    P.toExtendedLP.IsBoundedBy r ↔ P.IsBoundedBy r := by
  unfold StandardLP.IsBoundedBy ExtendedLP.IsBoundedBy
  constructor <;> intro hP p hPp
  · simpa [EF.coe_le_coe_iff] using
      hP (toE p) (by simpa [StandardLP.toExtendedLP.Reaches_iff] using hPp)
  · match p with
    | ⊥ =>
      exfalso
      obtain ⟨_, -, impos⟩ := hPp
      rw [←Matrix.dotProd_eq_bot] at impos
      simp [StandardLP.toExtendedLP] at impos
    | ⊤ =>
      apply le_top
    | (_ : R) =>
      rw [EF.coe_le_coe_iff]
      apply hP
      simpa [StandardLP.toExtendedLP.Reaches_iff] using hPp

private lemma StandardLP.toExtendedLP.IsUnbounded_iff (P : StandardLP I J R) :
    P.toExtendedLP.IsUnbounded ↔ P.IsUnbounded := by
  constructor <;> intro hP hr <;> apply hP <;> simpa [StandardLP.toExtendedLP.IsBoundedBy_iff] using hr

private theorem StandardLP.toExtendedLP.optimum_eq (P : StandardLP I J R) :
    P.toExtendedLP.optimum = P.optimum := by
  if feas : P.IsFeasible then
    if unbo : P.IsUnbounded then
      convert @rfl _ (some (⊥ : R∞))
      · simp [ExtendedLP.optimum, feas, unbo, StandardLP.toExtendedLP.IsFeasible_iff, StandardLP.toExtendedLP.IsUnbounded_iff]
      · simp [StandardLP.optimum, feas, unbo]
    else
      simp only [StandardLP.optimum, ExtendedLP.optimum, feas, unbo,
        StandardLP.toExtendedLP.IsFeasible_iff, StandardLP.toExtendedLP.IsUnbounded_iff]
      if hr : ∃ r, P.Reaches r ∧ P.IsBoundedBy r then
        convert @rfl _ (some (toE (hr.choose)))
        · simp [hr, StandardLP.toExtendedLP.Reaches_iff, StandardLP.toExtendedLP.IsBoundedBy_iff]
        · simp [hr]
      else
        convert @rfl _ none
        · simp [hr, StandardLP.toExtendedLP.Reaches_iff, StandardLP.toExtendedLP.IsBoundedBy_iff]
        · simp [hr]
  else
    convert @rfl _ (some (⊤ : R∞))
    · simp [ExtendedLP.optimum, feas, StandardLP.toExtendedLP.IsFeasible_iff]
    · simp [StandardLP.optimum, feas]

private lemma StandardLP.toExtendedLP.dualize_eq (P : StandardLP I J R) :
    P.toExtendedLP.dualize = P.dualize.toExtendedLP :=
  rfl


variable [DecidableEq I] [DecidableEq J]

theorem StandardLP.optimum_neq_none (P : StandardLP I J R) :
    P.optimum ≠ none :=
  StandardLP.toExtendedLP.optimum_eq P ▸ P.toExtendedLP.optimum_neq_none

theorem StandardLP.strongDuality {P : StandardLP I J R} (hP : P.IsFeasible ∨ P.dualize.IsFeasible) :
    OppositesOpt P.optimum P.dualize.optimum := by
  simpa [StandardLP.toExtendedLP.optimum_eq, StandardLP.toExtendedLP.dualize_eq] using
    P.toExtendedLP.strongDuality (by
      simpa [StandardLP.toExtendedLP.IsFeasible_iff, StandardLP.toExtendedLP.dualize_eq] using
        hP)
