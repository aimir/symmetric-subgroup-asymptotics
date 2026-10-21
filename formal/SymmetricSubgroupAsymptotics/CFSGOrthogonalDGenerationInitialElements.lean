import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSignedPermutation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationForkTorus
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationMonomialAction

/-! The literal nonbinary D candidate pair, uniformly from rank four.
The first root is e1-e0, the star root is e1+e_last, and the torus has
equal positive weights at coordinates0/1. Every element is an actual
original D root word or an element of the proved natural SL subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationInitialElements
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDGenerationForkTorus CFSGOrthogonalDGenerationSignedPermutation
open CFSGTypeAMonomialMatrices
variable (K : Type) [Field K]

def second (s : ℕ) : Fin (s + 4) := ⟨1, by omega⟩

def starPermutation (s : ℕ) : Equiv.Perm (Fin (s + 4)) :=
  Equiv.swap (second s) (pen (s + 2))

def starTransport (s : ℕ) : elementaryRootGroup K (s + 4) :=
  signedPermutationElement K (s + 4) 0 (starPermutation s)

def initialShortRoot (s : ℕ) (a : K) : elementaryRootGroup K (s + 4) :=
  rootElement K (s + 4) true 0 a

def initialStarRoot (s : ℕ) (neg : Bool) (a : K) : elementaryRootGroup K (s + 4) :=
  starTransport K s * rootElement K (s + 4) neg (last (s + 2)) a * (starTransport K s)⁻¹

def torusPermutation (s : ℕ) : Equiv.Perm (Fin (s + 4)) :=
  Equiv.swap (0 : Fin (s + 4)) (pen (s + 2)) *
    Equiv.swap (second s) (last (s + 2))

def torusTransport (s : ℕ) : elementaryRootGroup K (s + 4) :=
  signedPermutationElement K (s + 4) 0 (torusPermutation s)

def initialTorus (s : ℕ) (g : Kˣ) : elementaryRootGroup K (s + 4) :=
  torusTransport K s * forkTorus K (s + 2) g * (torusTransport K s)⁻¹

def initialMixedWeyl (s : ℕ) : elementaryRootGroup K (s + 4) :=
  initialShortRoot K s 1 * initialStarRoot K s false 1 * coxeterWeyl K (s + 3)

@[simp] theorem initialShortRoot_zero (s : ℕ) : initialShortRoot K s 0 = 1 :=
  rootElement_zero K (s + 4) true 0

theorem initialShortRoot_add (s : ℕ) (a b : K) :
    initialShortRoot K s (a + b) = initialShortRoot K s a * initialShortRoot K s b :=
  rootElement_add K (s + 4) true 0 a b

@[simp] theorem initialStarRoot_zero (s : ℕ) (neg : Bool) : initialStarRoot K s neg 0 = 1 := by
  simp only [initialStarRoot, rootElement_zero, mul_one, mul_inv_cancel]

theorem initialStarRoot_add (s : ℕ) (neg : Bool) (a b : K) :
    initialStarRoot K s neg (a + b) = initialStarRoot K s neg a * initialStarRoot K s neg b := by
  simp only [initialStarRoot, rootElement_add, mul_assoc, inv_mul_cancel_left]

def initialTorusDiagonal (s : ℕ) (g : Kˣ) : Index (s + 4) → K :=
  forkDiagonal K (s + 2) g ∘ Equiv.sumCongr (torusPermutation s) (torusPermutation s)

theorem initialTorus_coe (s : ℕ) (g : Kˣ) :
    ((initialTorus K s g).val : Mat K (s + 4)) = Matrix.diagonal (initialTorusDiagonal K s g) := by
  change ((torusTransport K s).val : Mat K (s + 4)) *
    ((forkTorus K (s + 2) g).val : Mat K (s + 4)) *
      (↑((torusTransport K s).val⁻¹) : Mat K (s + 4)) = _
  rw [forkTorus_coe]
  exact CFSGMonomialUnitRootAction.monomial_conjugation_diagonal
    (torusTransport K s).val (Equiv.sumCongr (torusPermutation s) (torusPermutation s))
    (Sum.elim (weight K (0 : Fin (s + 4)) (torusPermutation s))
      (weight K (0 : Fin (s + 4)) (torusPermutation s)))
    (forkDiagonal K (s + 2) g) (signedPermutationElement_coe K (s + 4) 0 (torusPermutation s))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationInitialElements
