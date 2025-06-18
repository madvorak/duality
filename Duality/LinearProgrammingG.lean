import Duality.LinearProgramming

@[ext]
structure GeneralizedELP (I I_ J J' F : Type*) [LinearOrderedField F] where
  /-- The left-hand-side matrix `≤` part. -/
  A : Matrix I J F∞
  /-- The left-hand-side matrix `≤` part. -/
  A' : Matrix I J' F
  /-- The left-hand-side matrix `=` part. -/
  A_ : Matrix I_ J F
  /-- The left-hand-side matrix `=` part. -/
  A'_ : Matrix I_ J' F
  /-- The right-hand-side vector `≤` part. -/
  b : I → F∞
  /-- The right-hand-side vector `=` part. -/
  b_ : I_ → F
  /-- The objective function coefficients. -/
  c : J → F∞
  /-- The objective function coefficients. -/
  c' : J' → F

/-- Extended linear program with properties that are needed for duality theorems. -/
structure ValidGELP (I I_ J J' F : Type*) [LinearOrderedField F] extends GeneralizedELP I I_ J J' F where
  /-- No `⊥` and `⊤` in the same row. -/
  hAi : ¬∃ i : I, (∃ j : J, A i j = ⊥) ∧ (∃ j : J, A i j = ⊤)
  /-- No `⊥` and `⊤` in the same column. -/
  hAj : ¬∃ j : J, (∃ i : I, A i j = ⊥) ∧ (∃ i : I, A i j = ⊤)
  /-- No `⊥` in the row where the right-hand-side vector has `⊥`. -/
  hbA : ¬∃ i : I, (∃ j : J, A i j = ⊥) ∧ b i = ⊥
  /-- No `⊤` in the column where the objective function has `⊥`. -/
  hcA : ¬∃ j : J, (∃ i : I, A i j = ⊤) ∧ c j = ⊥
  /-- No `⊤` in the row where the right-hand-side vector has `⊤`. -/
  hAb : ¬∃ i : I, (∃ j : J, A i j = ⊤) ∧ b i = ⊤
  /-- No `⊥` in the column where the objective function has `⊤`. -/
  hAc : ¬∃ j : J, (∃ i : I, A i j = ⊥) ∧ c j = ⊤

open scoped Matrix

variable {I I_ J J' F : Type*} [LinearOrderedField F]

/-- A nonnegative vector `x` is a solution to a linear program `P` iff
    its multiplication by matrix `A` from the left yields a vector whose
    all entries are less or equal to corresponding entries of the vector `b`. -/
def GeneralizedELP.IsSolution [Fintype J] [Fintype J'] (P : GeneralizedELP I I_ J J' F) (x : J → F≥0) (x' : J' → F) : Prop :=
  P.A ₘ* x ≤ P.b ∧ toE ∘ (P.A' ₘ* x') ≤ P.b ∧ P.A_ *ᵥ (Subtype.val ∘ x) ≤ P.b_ ∧ P.A'_ *ᵥ x' ≤ P.b_

/-- Linear program `P` reaches objective value `r` iff there is a solution `x` such that,
    when its entries are elementwise multiplied by the the coefficients `c` and summed up,
    the result is the value `r`. -/
def GeneralizedELP.Reaches [Fintype J] [Fintype J'] (P : GeneralizedELP I I_ J J' F) (r : F∞) : Prop :=
  ∃ x : J → F≥0, ∃ x' : J' → F, P.IsSolution x x' ∧ P.c ᵥ⬝ x + P.c' ⬝ᵥ x' = r

/-- Linear program `P` is feasible iff `P` reaches a value that is not `⊤`. -/
def GeneralizedELP.IsFeasible [Fintype J] [Fintype J'] (P : GeneralizedELP I I_ J J' F) : Prop :=
  ∃ p : F∞, P.Reaches p ∧ p ≠ ⊤

/-- Linear program `P` is bounded by `r` iff every value reached by `P` is
    greater or equal to `r` (i.e., `P` is bounded by `r` from below). -/
def GeneralizedELP.IsBoundedBy [Fintype J] [Fintype J'] (P : GeneralizedELP I I_ J J' F) (r : F) : Prop :=
  ∀ p : F∞, P.Reaches p → r ≤ p

/-- Linear program `P` is unbounded iff values reached by `P` have no finite lower bound. -/
def GeneralizedELP.IsUnbounded [Fintype J] [Fintype J'] (P : GeneralizedELP I I_ J J' F) : Prop :=
  ¬∃ r : F, P.IsBoundedBy r

open scoped Classical in
/-- Extended notion of "optimum" of "minimization LP" (the less the better). -/
noncomputable def GeneralizedELP.optimum [Fintype J] [Fintype J'] (P : GeneralizedELP I I_ J J' F) : Option F∞ :=
  if ¬P.IsFeasible then
    some ⊤ -- infeasible means that the minimum is `⊤`
  else
    if P.IsUnbounded then
      some ⊥ -- unbounded means that the minimum is `⊥`
    else
      if hr : ∃ r : F, P.Reaches (toE r) ∧ P.IsBoundedBy r then
        some (toE hr.choose) -- the minimum is finite
      else
        none -- invalid finite value (infimum is not attained)

/-- Dualize an extended linear program in the standard form.
    The matrix gets transposed and its values flip signs.
    The original objective function becomes the new right-hand-side vector.
    The original right-hand-side vector becomes the new objective function.
    Both linear programs are intended to be minimized. -/
abbrev GeneralizedELP.dualize (P : GeneralizedELP I I_ J J' F) : GeneralizedELP J J' I I_ F :=
  ⟨-P.Aᵀ, -P.A_ᵀ, -P.A'ᵀ, -P.A'_ᵀ, P.c, P.c', P.b, P.b_⟩


lemma GeneralizedELP.dualize_dualize (P : GeneralizedELP I I_ J J' F) :
    P.dualize.dualize = P := by
  obtain ⟨_, _, _, _, _, _, _, _⟩ := P
  simp [GeneralizedELP.dualize, ←Matrix.ext_iff]

private def GeneralizedELP.toExtendedLP (P : GeneralizedELP I I_ J J' F) : ExtendedLP (I ⊕ I_ ⊕ I_) (J ⊕ J' ⊕ J') F :=
  ⟨Matrix.fromBlocks
    P.A ((Matrix.fromCols P.A' (-P.A')).map toE)
    ((Matrix.fromRows P.A_ (-P.A_)).map toE) ((Matrix.fromBlocks P.A'_ (-P.A'_) (-P.A'_) P.A'_).map toE),
   Sum.elim P.b (toE ∘ Sum.elim P.b_ (-P.b_)),
   Sum.elim P.c (toE ∘ Sum.elim P.c' (-P.c'))⟩

private lemma GeneralizedELP.dualize_toExtendedLP (P : GeneralizedELP I I_ J J' F) :
    P.dualize.toExtendedLP = P.toExtendedLP.dualize := by
  ext i j
  · rcases i with (_|_|_) <;> rcases j with (_|_|_) <;> rfl
  · rfl
  · rfl

abbrev partPos (f : F) : F≥0 := ⟨f⁺, posPart_nonneg f⟩
abbrev partNeg (f : F) : F≥0 := ⟨f⁻, negPart_nonneg f⟩

private lemma GeneralizedELP.isSolution_iff_toExtendedLP [Fintype J] [Fintype J']
    (P : GeneralizedELP I I_ J J' F) (x : J → F≥0) (x' : J' → F) :
    P.IsSolution x x' ↔ P.toExtendedLP.IsSolution (Sum.elim x (Sum.elim (partPos ∘ x') (partNeg ∘ x'))) := by
  sorry
