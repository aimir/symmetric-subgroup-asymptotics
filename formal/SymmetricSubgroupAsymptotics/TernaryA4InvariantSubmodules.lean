import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The actual four-coordinate ternary module for the natural A4 action

The invariant submodules are exactly zero, the diagonal, the augmentation
submodule, and the full module. The augmentation is a genuine additional
possibility even with full projections on each original coordinate.

A nonzero invariant functional on a retained invariant submodule removes
zero and augmentation. Consequently any invariant kernel containing that
retained submodule is diagonal or full. This is the precise local head
condition needed by the saturated 3-by-4 branch; no assertion is made here
that an arbitrary original normal-pair rank equality already supplies it.

Only four explicit coordinate vectors and the original Klein-four/three-
cycle permutations are used. The finite checked identities quantify over
at most the 81 vectors, never over subgroups or invariant subspaces.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.TernaryA4InvariantSubmodules

abbrev Scalar := ZMod 3
abbrev V := Fin 4 → Scalar
abbrev A4 := alternatingGroup (Fin 4)

/-- The natural left permutation action on the literal four coordinates. -/
def coordinateAction (g : Equiv.Perm (Fin 4)) : V →ₗ[Scalar] V where
  toFun v i := v (g.symm i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def Invariant (K : Submodule Scalar V) : Prop :=
  ∀ g ∈ A4, ∀ v ∈ K, coordinateAction g v ∈ K

def diagonal : Submodule Scalar V where
  carrier := {v | ∀ i, v i = v 0}
  zero_mem' := fun _ => rfl
  add_mem' := by
    intro v w hv hw i
    change v i + w i = v 0 + w 0
    rw [hv i,hw i]
  smul_mem' := by
    intro a v hv i
    change a * v i = a * v 0
    rw [hv i]

def augmentation : Submodule Scalar V where
  carrier := {v | ∑ i, v i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change Finset.univ.sum (fun i : Fin 4 => v i + w i) = 0
    rw [Finset.sum_add_distrib,hv,hw,add_zero]
  smul_mem' := by
    intro a v hv
    change Finset.univ.sum (fun i : Fin 4 => a * v i) = 0
    rw [← Finset.mul_sum,hv,mul_zero]

private def basisVector : Fin 4 → V :=
  ![![1,1,1,1], ![1,1,-1,-1], ![1,-1,1,-1], ![1,-1,-1,1]]

private def coefficient (v : V) (i : Fin 4) : Scalar :=
  ∑ j, basisVector i j * v j

private def klein : Fin 4 → Equiv.Perm (Fin 4) :=
  ![1, Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 0 3 * Equiv.swap 1 2]

private def rotate : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 2 3

private theorem klein_mem : ∀ j, klein j ∈ A4 := by
  change ∀ j, Equiv.Perm.sign (klein j) = 1
  decide +kernel
private theorem rotate_mem : rotate ∈ A4 := by
  change Equiv.Perm.sign rotate = 1
  decide +kernel

private theorem reconstruction : ∀ v : V,
    (∑ i : Fin 4, coefficient v i • basisVector i) = v := by decide +kernel

private theorem projection_identity : ∀ (v : V) (i : Fin 4),
    (∑ j : Fin 4, basisVector i j • coordinateAction (klein j) v) =
      coefficient v i • basisVector i := by decide +kernel

private theorem nontrivial_transport : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 →
    ∃ r : Fin 3, coordinateAction (rotate ^ r.val) (basisVector i) = basisVector j := by
  decide +kernel

private theorem nontrivial_negator : ∀ i : Fin 4, i ≠ 0 →
    ∃ j : Fin 4, coordinateAction (klein j) (basisVector i) = -basisVector i := by
  decide +kernel

private theorem diagonal_coefficients : ∀ v : V,
    (∀ j, v j = v 0) ↔ ∀ i : Fin 4, i ≠ 0 → coefficient v i = 0 := by
  decide +kernel

private theorem diagonal_scalars : ∀ v : V,
    (∀ j, v j = v 0) ↔ ∃ a : Scalar, v = a • basisVector 0 := by decide +kernel

private theorem augmentation_coefficient : ∀ v : V,
    (∑ j, v j = 0) ↔ coefficient v 0 = 0 := by decide +kernel

private theorem augmentation_reconstruction : ∀ v : V, (∑ j, v j = 0) →
    v = ∑ i : Fin 3, coefficient v i.succ • basisVector i.succ := by decide +kernel

private theorem augmentation_basis : ∀ i : Fin 3,
    (∑ j, basisVector i.succ j) = 0 := by decide +kernel

private theorem basis_zero_diagonal : basisVector 0 ∈ diagonal := by
  change ∀ i, basisVector 0 i = basisVector 0 0
  decide +kernel
private theorem basis_zero_ne : basisVector 0 ≠ 0 := by decide +kernel
private theorem basis_zero_not_augmentation : basisVector 0 ∉ augmentation := by
  change (∑ i, basisVector 0 i) ≠ 0
  decide +kernel
private theorem basis_one_augmentation : basisVector 1 ∈ augmentation := by
  change (∑ i, basisVector 1 i) = 0
  decide +kernel
private theorem basis_one_not_diagonal : basisVector 1 ∉ diagonal := by
  change ¬ ∀ i, basisVector 1 i = basisVector 1 0
  decide +kernel

private theorem basis_mem_of_coefficient_ne_zero (K : Submodule Scalar V)
    (hK : Invariant K) (v : V) (hv : v ∈ K) (i : Fin 4)
    (hi : coefficient v i ≠ 0) : basisVector i ∈ K := by
  have hp : coefficient v i • basisVector i ∈ K := by
    rw [← projection_identity]
    exact K.sum_mem (fun j _ => K.smul_mem _ (hK (klein j) (klein_mem j) v hv))
  have hm := K.smul_mem (coefficient v i)⁻¹ hp
  simpa only [smul_smul,inv_mul_cancel₀ hi,one_smul] using hm

private theorem nontrivial_basis_mem (K : Submodule Scalar V) (hK : Invariant K)
    {i j : Fin 4} (hi : i ≠ 0) (hj : j ≠ 0)
    (hb : basisVector i ∈ K) : basisVector j ∈ K := by
  obtain ⟨r,hr⟩ := nontrivial_transport i j hi hj
  rw [← hr]
  exact hK (rotate ^ r.val) (A4.pow_mem rotate_mem r.val) _ hb

private theorem mem_of_supported_coefficients (K : Submodule Scalar V) (v : V)
    (h : ∀ i, coefficient v i ≠ 0 → basisVector i ∈ K) : v ∈ K := by
  rw [← reconstruction v]
  apply K.sum_mem
  intro i _
  by_cases hi : coefficient v i = 0
  · simpa only [hi,zero_smul] using K.zero_mem
  · exact K.smul_mem _ (h i hi)

/-- Complete invariant-submodule classification for the actual natural
A4 action, without a list of invariant subspaces as a premise. -/
theorem classification (K : Submodule Scalar V) (hK : Invariant K) :
    K = ⊥ ∨ K = diagonal ∨ K = augmentation ∨ K = ⊤ := by
  by_cases h0 : basisVector 0 ∈ K
  · by_cases h1 : basisVector 1 ∈ K
    · right; right; right
      apply top_unique
      intro v _
      apply mem_of_supported_coefficients K v
      intro i _
      by_cases hi : i = 0
      · simpa only [hi] using h0
      · exact nontrivial_basis_mem K hK (by decide : (1 : Fin 4) ≠ 0) hi h1
    · right; left
      apply le_antisymm
      · intro v hv
        apply (diagonal_coefficients v).mpr
        intro i hi
        by_contra hc
        exact h1 (nontrivial_basis_mem K hK hi (by decide : (1 : Fin 4) ≠ 0)
          (basis_mem_of_coefficient_ne_zero K hK v hv i hc))
      · intro v hv
        obtain ⟨a,rfl⟩ := (diagonal_scalars v).mp hv
        exact K.smul_mem a h0
  · by_cases h1 : basisVector 1 ∈ K
    · right; right; left
      apply le_antisymm
      · intro v hv
        apply (augmentation_coefficient v).mpr
        by_contra hc
        exact h0 (basis_mem_of_coefficient_ne_zero K hK v hv 0 hc)
      · intro v hv
        apply mem_of_supported_coefficients K v
        intro i hi
        have hn : i ≠ 0 := by
          intro he
          subst i
          exact hi ((augmentation_coefficient v).mp hv)
        exact nontrivial_basis_mem K hK (by decide : (1 : Fin 4) ≠ 0) hn h1
    · left
      apply bot_unique
      intro v hv
      have hc : ∀ i, coefficient v i = 0 := by
        intro i
        by_contra hi
        have hb := basis_mem_of_coefficient_ne_zero K hK v hv i hi
        by_cases hz : i = 0
        · exact h0 (hz ▸ hb)
        · exact h1 (nontrivial_basis_mem K hK hz (by decide : (1 : Fin 4) ≠ 0) hb)
      change v = 0
      rw [← reconstruction v]
      simp only [hc,zero_smul,Finset.sum_const_zero]

/-- Invariance of a linear character on the same literal retained
submodule. Two subtype elements are used so no chosen action transport or
normality proof occurs in the definition. -/
def FunctionalInvariant (K : Submodule Scalar V) (f : K →ₗ[Scalar] Scalar) : Prop :=
  ∀ g ∈ A4, ∀ v w : K, coordinateAction g v.val = w.val → f w = f v

def HasInvariantHead (K : Submodule Scalar V) : Prop :=
  ∃ f : K →ₗ[Scalar] Scalar, f ≠ 0 ∧ FunctionalInvariant K f

private theorem neg_fixed_zero : ∀ a : Scalar, -a = a → a = 0 := by decide +kernel

/-- The augmentation has no retained invariant ternary character. -/
theorem augmentation_functional_eq_zero (f : augmentation →ₗ[Scalar] Scalar)
    (hf : FunctionalInvariant augmentation f) : f = 0 := by
  let b : Fin 3 → augmentation := fun i => ⟨basisVector i.succ,augmentation_basis i⟩
  have hb (i : Fin 3) : f (b i) = 0 := by
    obtain ⟨j,hj⟩ := nontrivial_negator i.succ (Fin.succ_ne_zero i)
    have ht := hf (klein j) (klein_mem j) (b i) (-(b i)) hj
    exact neg_fixed_zero _ (by simpa only [map_neg] using ht)
  apply LinearMap.ext
  intro v
  have hv : v = ∑ i : Fin 3, coefficient v.val i.succ • b i := by
    apply Subtype.ext
    change v.val = augmentation.subtype (∑ i : Fin 3, coefficient v.val i.succ • b i)
    rw [map_sum]
    simp only [map_smul]
    exact augmentation_reconstruction v.val v.property
  change f v = 0
  rw [hv,map_sum]
  simp only [map_smul,hb,smul_zero,Finset.sum_const_zero]

/-- A positive retained invariant head eliminates precisely the zero and
augmentation alternatives in the unconditional four-way classification. -/
theorem diagonal_or_full_of_head (K : Submodule Scalar V) (hK : Invariant K)
    (hhead : HasInvariantHead K) : K = diagonal ∨ K = ⊤ := by
  rcases classification K hK with h | h | h | h
  · subst K
    obtain ⟨f,hf,_⟩ := hhead
    apply False.elim
    apply hf
    apply LinearMap.ext
    intro v
    have hv : v = 0 := Subsingleton.elim _ _
    simp only [hv,map_zero]
  · exact Or.inl h
  · subst K
    obtain ⟨f,hf,hi⟩ := hhead
    exact False.elim (hf (augmentation_functional_eq_zero f hi))
  · exact Or.inr h

theorem diagonal_or_full_of_diagonal_le (K : Submodule Scalar V) (hK : Invariant K)
    (hD : diagonal ≤ K) : K = diagonal ∨ K = ⊤ := by
  rcases classification K hK with h | h | h | h
  · have hb := hD basis_zero_diagonal
    rw [h,Submodule.mem_bot] at hb
    exact False.elim (basis_zero_ne hb)
  · exact Or.inl h
  · have hb := hD basis_zero_diagonal
    rw [h] at hb
    exact False.elim (basis_zero_not_augmentation hb)
  · exact Or.inr h

/-- The retained kernel may be smaller than the whole block kernel. Its
nonzero invariant head is enough, provided both use the actual A4 action. -/
theorem diagonal_or_full_of_retained_head (K L : Submodule Scalar V)
    (hK : Invariant K) (hL : Invariant L) (hLK : L ≤ K)
    (hhead : HasInvariantHead L) : K = diagonal ∨ K = ⊤ := by
  rcases diagonal_or_full_of_head L hL hhead with h | h
  · exact diagonal_or_full_of_diagonal_le K hK (h ▸ hLK)
  · right
    exact top_unique (h ▸ hLK)

theorem augmentation_invariant : Invariant augmentation := by
  intro g _ v hv
  change (∑ i, v (g.symm i)) = 0
  rw [Equiv.sum_comp g.symm v]
  exact hv

/-- Even full projection on every original coordinate does not exclude
augmentation; a retained-head hypothesis is mathematically necessary. -/
theorem augmentation_coordinate_full (i : Fin 4) (a : Scalar) :
    ∃ v ∈ augmentation, v i = a := by
  have h : ∀ (i : Fin 4) (a : Scalar), ∃ v : V, (∑ j, v j) = 0 ∧ v i = a := by
    decide +kernel
  exact h i a

theorem augmentation_not_diagonal_or_full : augmentation ≠ diagonal ∧ augmentation ≠ ⊤ := by
  constructor
  · intro h
    exact basis_one_not_diagonal (h ▸ basis_one_augmentation)
  · intro h
    exact basis_zero_not_augmentation (h.symm ▸ (Submodule.mem_top : basisVector 0 ∈ (⊤ : Submodule Scalar V)))

/-- Every additive subgroup of this prime-field module carries its
unique compatible F3-submodule structure, with the same literal vectors. -/
theorem additive_classification (K : AddSubgroup V)
    (hK : ∀ g ∈ A4, ∀ v ∈ K, coordinateAction g v ∈ K) :
    K = ⊥ ∨ K = diagonal.toAddSubgroup ∨ K = augmentation.toAddSubgroup ∨ K = ⊤ := by
  let M : Submodule Scalar V := AddSubgroup.toZModSubmodule 3 K
  have hM : Invariant M := hK
  rcases classification M hM with h | h | h | h
  · left
    exact congrArg Submodule.toAddSubgroup h
  · right; left
    exact congrArg Submodule.toAddSubgroup h
  · right; right; left
    exact congrArg Submodule.toAddSubgroup h
  · right; right; right
    exact congrArg Submodule.toAddSubgroup h

end SymmetricSubgroupAsymptotics.TernaryA4InvariantSubmodules

end
