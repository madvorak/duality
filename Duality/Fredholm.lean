import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Have
import Duality.Common


private lemma impossible_index {m : ℕ} {i : Fin m.succ} (hi : ¬(i.val < m)) (i_neq_m : i ≠ ⟨m, m.lt_add_one⟩) : False := by
  push_neg at hi
  exact i_neq_m (eq_of_le_of_le (Fin.succ_le_succ_iff.→ i.isLt) hi)

private lemma filter_yielding_singleton_attach_sum {m : ℕ} {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (f : Fin m.succ → R) (v : V) :
    ∑ j ∈ (Finset.univ.filter (fun i : Fin m.succ => ¬(i.val < m))).attach, f j.val • v =
    f ⟨m, m.lt_add_one⟩ • v := by
  have singlet : Finset.univ.filter (fun i : Fin m.succ => ¬(i.val < m)) = {⟨m, m.lt_add_one⟩}
  · rw [Finset.ext_iff]
    intro i
    constructor <;> rw [Finset.mem_singleton, Finset.mem_filter] <;> intro hi
    · have him := hi.right
      push_neg at him
      exact eq_of_le_of_le (Nat.le_of_lt_succ i.isLt) him
    · refine ⟨Finset.mem_univ i, ?_⟩
      rw [hi]
      push_neg
      rfl
  rw [singlet, Finset.sum_attach _ (fun j : Fin m.succ => f j • v), Finset.sum_singleton]

private def withoutLastMap {m : ℕ} {R W : Type*} [Semiring R] [AddCommMonoid W] [Module R W]
    (A : W →ₗ[R] Fin m.succ → R) :
    W →ₗ[R] Fin m → R :=
  ⟨⟨
    fun w : W => fun i : Fin m => A w i.castSucc,
  by
    intros
    ext
    simp
  ⟩,
  by
    intros
    ext
    simp
  ⟩

prefix:max "▀" => withoutLastMap

private def auxLinMaps {m : ℕ} {R W : Type*} [Ring R] [AddCommMonoid W] [Module R W]
    (A : W →ₗ[R] Fin m.succ → R) (y : W) :
    W →ₗ[R] Fin m → R :=
  ⟨⟨
    ▀A - (A · ⟨m, m.lt_add_one⟩ • ▀A y),
  by
    intros
    ext
    simp only [withoutLastMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, map_add, smul_eq_mul, add_mul]
    abel
  ⟩,
  by
    intros
    ext
    simp [withoutLastMap, mul_sub, mul_assoc]
  ⟩

private def auxLinMap {m : ℕ} {R V W : Type*} [Semiring R] [AddCommGroup V] [Module R V] [AddCommMonoid W] [Module R W]
    (A : W →ₗ[R] Fin m.succ → R) (b : W →ₗ[R] V) (y : W) : W →ₗ[R] V :=
  ⟨⟨
    b - (A · ⟨m, m.lt_add_one⟩ • b y),
  by
    intros
    simp only [Pi.add_apply, Pi.sub_apply, map_add, add_smul]
    abel
  ⟩,
  by
    intros
    -- note that `simp` does not work here
    simp only [Pi.smul_apply, Pi.sub_apply, LinearMapClass.map_smul, RingHom.id_apply, smul_sub, IsScalarTower.smul_assoc]
  ⟩

private lemma finishing_piece {R V W : Type*} {m : ℕ} [Semiring R]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    {A : W →ₗ[R] Fin m.succ → R} {w : W} {x : Fin m → V} :
    ∑ i : Fin m, ▀A w i • x i =
    ∑ i : { j : Fin m.succ // j ∈ Finset.univ.filter (·.val < m) }, A w i.val • x ⟨i.val.val, by aesop⟩ := by
  apply
    Finset.sum_bij'
      (fun i : Fin m => ↓(⟨⟨i.val, by omega⟩, by aesop⟩ : { a : Fin m.succ // a ∈ Finset.univ.filter (·.val < m) }))
      (fun i' : { a : Fin m.succ // a ∈ Finset.univ.filter (·.val < m) } => ↓⟨i'.val.val, by aesop⟩)
      (by aesop)
      (by aesop)
      (by aesop)
      (by aesop)
  intros
  rfl

theorem finFredholm {R V W : Type*} {n : ℕ} [DivisionRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (A : W →ₗ[R] Fin n → R) (b : W →ₗ[R] V) :
    (∃ x : Fin n → V, ∀ w : W, ∑ j : Fin n, A w j • x j = b w) ≠ (∃ y : W, A y = 0 ∧ b y ≠ 0) := by
  apply neq_of_iff_neg
  push_neg
  refine ⟨fun ⟨x, hxb⟩ y hy => hxb y ▸ (by simp_all only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]), ?_⟩
  induction n generalizing b with -- note that `A` is "generalized" automatically
  | zero =>
    intro hAb
    refine ⟨0, fun w : W => ?_⟩
    symm
    apply hAb
    ext i
    exfalso
    exact Nat.not_succ_le_zero i.val i.isLt
  | succ m ih =>
    intro hAb
    if
      is_easy : ∀ y : W, ▀A y = 0 → b y = 0
    then
      obtain ⟨x, hxb⟩ := ih ▀A b is_easy
      use (fun i : Fin m.succ => if hi : i.val < m then x ⟨i.val, hi⟩ else 0)
      intro w
      simp_rw [smul_dite, smul_zero]
      rw [Finset.sum_dite, Finset.sum_const_zero, add_zero]
      convert hxb w using 1
      symm
      apply finishing_piece
    else
      push_neg at is_easy
      obtain ⟨y', hay', hby'⟩ := is_easy
      let M : Fin m.succ := ⟨m, lt_add_one m⟩ -- the last (new) index
      let y : W := (A y' M)⁻¹ • y' -- rescaled `y'`
      have hAy' : A y' M ≠ 0
      · by_contra! contr
        apply hby'
        apply hAb
        ext i
        if hi : i.val < m then
          exact congr_fun hay' ⟨i.val, hi⟩
        else if hiM : i = M then
          exact hiM ▸ contr
        else
          exfalso
          exact impossible_index hi hiM
      have hAy : A y M = 1
      · convert inv_mul_cancel₀ hAy'
        simp [y]
      have hAA : ∀ w : W, A (w - (A w M • y)) M = 0
      · intro w
        simp [hAy]
      have hbA : ∀ w : W, ▀A (w - (A w M • y)) = 0 → b (w - (A w M • y)) = 0
      · intro w hw
        apply hAb
        ext i
        if hi : i.val < m then
          exact congr_fun hw ⟨i.val, hi⟩
        else if hiM : i = M then
          rw [hiM, hAA, Pi.zero_apply]
        else
          exfalso
          exact impossible_index hi hiM
      have hbAb : ∀ w : W, (▀A - (A · M • ▀A y)) w = 0 → (b - (A · M • b y)) w = 0
      · simpa using hbA
      obtain ⟨x', hxb'⟩ := ih (auxLinMaps A y) (auxLinMap A b y) hbAb
      use (fun i : Fin m.succ => if hi : i.val < m then x' ⟨i.val, hi⟩ else b y - ∑ i : Fin m, ▀A y i • x' i)
      intro w
      have haAa : ∑ i : Fin m, (▀A w i - A w M * ▀A y i) • x' i = b w - A w M • b y
      · simpa using hxb' w
      rw [←add_eq_of_eq_sub haAa]
      simp_rw [smul_dite]
      rw [Finset.sum_dite]
      erw [filter_yielding_singleton_attach_sum]
      simp_rw [sub_smul]
      rw [Finset.sum_sub_distrib]
      simp_rw [←smul_smul, ←Finset.smul_sum]
      symm
      rw [smul_sub, finishing_piece]
      apply add_comm_sub

theorem fintypeFredholm {R V W J : Type*} [Fintype J] [DivisionRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (A : W →ₗ[R] J → R) (b : W →ₗ[R] V) :
    (∃ x : J → V, ∀ w : W, ∑ j : J, A w j • x j = b w) ≠ (∃ y : W, A y = 0 ∧ b y ≠ 0) := by
  convert
    finFredholm ⟨⟨(A · ∘ (Fintype.equivFin J).symm), by aesop⟩, by aesop⟩ b
      using 1
  · constructor <;> intro ⟨x, hA⟩
    · use x ∘ (Fintype.equivFin J).invFun
      intro w
      convert hA w
      apply Finset.sum_equiv (Fintype.equivFin J).symm <;>
      · intros
        simp
    · use x ∘ (Fintype.equivFin J).toFun
      intro w
      convert hA w
      apply Finset.sum_equiv (Fintype.equivFin J) <;>
      · intro
        simp
  · constructor <;> intro ⟨y, hAy, hby⟩ <;> refine ⟨y, ?_, hby⟩ <;> ext j
    · simpa using congr_fun hAy ((Fintype.equivFin J).invFun j)
    · simpa using congr_fun hAy ((Fintype.equivFin J).toFun j)

open scoped Matrix

theorem basicLinearAlgebra_stronger {I J F : Type*} [Fintype I] [Fintype J] [Field F]
    (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, A *ᵥ x = b) ≠ (∃ y : I → F, Aᵀ *ᵥ y = 0 ∧ b ⬝ᵥ y ≠ 0) := by
  convert
    fintypeFredholm Aᵀ.mulVecLin ⟨⟨(b ⬝ᵥ ·), dotProduct_add b⟩, (dotProduct_smul · b)⟩
      using 3
  constructor <;> intro hAx
  · simp
    rw [←hAx]
    intro
    unfold Matrix.mulVec Matrix.vecMul dotProduct
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    congr
    ext
    congr
    ext
    ring
  · simp at hAx
    apply dotProduct_eq
    intro w
    rw [←hAx w]
    unfold Matrix.mulVec Matrix.vecMul dotProduct
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    congr
    ext
    congr
    ext
    ring

#print axioms basicLinearAlgebra_stronger
