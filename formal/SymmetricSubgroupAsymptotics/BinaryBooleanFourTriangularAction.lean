import SymmetricSubgroupAsymptotics.BinaryBooleanFourPrefixFunctions
import SymmetricSubgroupAsymptotics.BinaryTriangularPointCoordinates

/-! The original central-pair tower is transported to the same sixteen
Boolean labels. Its actual point permutations preserve every lower-bit
prefix, with original higher-bit displacements still unrestricted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace BinaryBooleanFourPolynomialCoordinates

def bitPointEquiv : Fin 16 ≃ (Fin 4 → ZMod 2) :=
  Equiv.ofBijective (fun x i => bitValue i x) (by decide)

def IsTriangularPermutation (p : Equiv.Perm (Fin 16)) : Prop :=
  ∀ i : Fin 4, DependsOnPrefix (fun x => bitValue i (p x) - bitValue i x) i.val

def FixesLowerFlips (p : Equiv.Perm (Fin 16)) (i : Fin 4) : Prop :=
  ∀ x : Fin 16, (∀ j : Fin 4, j < i → bitValue j (p x) = bitValue j x) ∧
    bitValue i (p x) = bitValue i x + 1

theorem triangular_preserves_prefix (p : Equiv.Perm (Fin 16))
    (hp : IsTriangularPermutation p) (r : ℕ) (x y : Fin 16)
    (hxy : ∀ i : Fin 4, i.val < r → bitValue i x = bitValue i y) :
    ∀ i : Fin 4, i.val < r → bitValue i (p x) = bitValue i (p y) := by
  intro i hi
  have hd := hp i x y (fun j hj => hxy j (lt_trans hj hi))
  change bitValue i (p x) - bitValue i x = bitValue i (p y) - bitValue i y at hd
  rw [hxy i hi] at hd
  have he := congrArg (fun z : ZMod 2 => z + bitValue i y) hd
  simpa only [sub_add_cancel] using he

theorem prefix_comp_triangular {f : V} {r : ℕ} (hf : DependsOnPrefix f r)
    (p : Equiv.Perm (Fin 16)) (hp : IsTriangularPermutation p) :
    DependsOnPrefix (fun x => f (p x)) r := by
  intro x y hxy
  exact hf (p x) (p y) (triangular_preserves_prefix p hp r x y hxy)

theorem monomial_prefix_of_lt (a : Fin 16) (r : Fin 5) (ha : a.val < 2 ^ r.val) :
    DependsOnPrefix (monomial (BinaryElementaryPairMonomialWidth.support a)) r.val := by
  rw [← evaluate_basis]
  apply prefix_evaluate_of_coefficients_zero
  intro b hb
  have hne : b ≠ a := by
    intro he
    have hv := congrArg Fin.val he
    omega
  simp only [Pi.single_apply, if_neg hne]

end BinaryBooleanFourPolynomialCoordinates

namespace BinaryTriangularPointCoordinates
open BinaryBooleanFourPolynomialCoordinates
variable {G X : Type} [Group G] [MulAction G X]
    (T : BinaryTriangularPointCoordinates G X 4)

def booleanPointLabels : X ≃ Fin 16 := T.pointEquiv.trans bitPointEquiv.symm

@[simp] theorem booleanPointLabels_bit (x : X) (i : Fin 4) :
    bitValue i (T.booleanPointLabels x) = T.pointEquiv x i := by
  change bitPointEquiv (bitPointEquiv.symm (T.pointEquiv x)) i = _
  rw [Equiv.apply_symm_apply]

@[simp] theorem booleanPointLabels_symm_bit (x : Fin 16) (i : Fin 4) :
    T.pointEquiv (T.booleanPointLabels.symm x) i = bitValue i x := by
  have h := T.booleanPointLabels_bit (T.booleanPointLabels.symm x) i
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

def actualBooleanPermutation (g : G) : Equiv.Perm (Fin 16) :=
  T.booleanPointLabels.symm.trans ((MulAction.toPermHom G X g).trans T.booleanPointLabels)

@[simp] theorem actualBooleanPermutation_bit (g : G) (x : Fin 16) (i : Fin 4) :
    bitValue i (T.actualBooleanPermutation g x) =
      T.pointEquiv (g • T.booleanPointLabels.symm x) i := by
  exact T.booleanPointLabels_bit _ i

theorem actualBooleanPermutation_triangular (g : G) :
    IsTriangularPermutation (T.actualBooleanPermutation g) := by
  intro i x y hxy
  change bitValue i (T.actualBooleanPermutation g x) - bitValue i x =
    bitValue i (T.actualBooleanPermutation g y) - bitValue i y
  rw [actualBooleanPermutation_bit, actualBooleanPermutation_bit,
    ← booleanPointLabels_symm_bit T x i, ← booleanPointLabels_symm_bit T y i]
  apply T.displacement g i
  intro j hj
  simpa only [booleanPointLabels_symm_bit] using hxy j hj

theorem exists_actualBooleanPermutation_flip (i : Fin 4) :
    ∃ g : G, FixesLowerFlips (T.actualBooleanPermutation g) i := by
  obtain ⟨g, hg⟩ := T.flip i
  refine ⟨g, ?_⟩
  intro x
  constructor
  · intro j hj
    rw [actualBooleanPermutation_bit, ← booleanPointLabels_symm_bit T x j]
    exact (hg (T.booleanPointLabels.symm x)).1 j hj
  · rw [actualBooleanPermutation_bit, ← booleanPointLabels_symm_bit T x i]
    exact (hg (T.booleanPointLabels.symm x)).2

end BinaryTriangularPointCoordinates
end SymmetricSubgroupAsymptotics
