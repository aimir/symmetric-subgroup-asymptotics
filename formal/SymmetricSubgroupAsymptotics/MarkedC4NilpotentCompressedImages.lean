import SymmetricSubgroupAsymptotics.MarkedC4NilpotentPermutationGrid
import SymmetricSubgroupAsymptotics.MarkedC4ActiveFiberPermutation

/-! Actual compressed physical binary/odd permutation images of the
original nilpotent action. Images, prime-order properties and the shared
physical budget are constructed, never provided as capacity premises. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.NilpotentCompressedImages
open NilpotentSylowFactors NilpotentPermutationGrid
variable (G X : Type) [Group G] [Finite G] [Group.IsNilpotent G]
  [MulAction G X] [Finite X]
local instance : Fintype (OrbitIndex G X) := Fintype.ofFinite _

abbrev BinarySupport := ActiveFiberPermutation.Support (BinaryFiber G X)
abbrev OddSupport := ActiveFiberPermutation.Support (OddFiber G X)

def binaryAction : Binary G →* Equiv.Perm (BinarySupport G X) :=
  ActiveFiberPermutation.action (BinaryFiber G X)
def oddAction : OddFactor G →* Equiv.Perm (OddSupport G X) :=
  ActiveFiberPermutation.action (OddFiber G X)

abbrev BinaryImage := (binaryAction G X).range
abbrev OddImage := (oddAction G X).range

theorem binary_image_isPGroup : IsPGroup 2 (BinaryImage G X) :=
  (binary_isPGroup G).of_surjective (binaryAction G X).rangeRestrict
    (binaryAction G X).rangeRestrict_surjective

theorem odd_image_card_coprime_four : Nat.Coprime (Nat.card (OddImage G X)) 4 :=
  Nat.Coprime.of_dvd_left (Subgroup.card_range_dvd (oddAction G X))
    (odd_card_coprime_four G)

theorem binary_support_card : Nat.card (BinarySupport G X)=binaryDegree G X :=
  ActiveFiberPermutation.card_support (BinaryFiber G X)
theorem odd_support_card : Nat.card (OddSupport G X)=oddDegree G X :=
  ActiveFiberPermutation.card_support (OddFiber G X)

theorem physical_budget : Nat.card (BinarySupport G X)+Nat.card (OddSupport G X)≤Nat.card X := by
  rw [binary_support_card,odd_support_card]
  exact support_budget G X

/-- Kernel information remains exactly the action on every original
stabilizer-coset fiber, including the discarded singleton fibers. -/
theorem binary_kernel_iff (g : Binary G) : g∈(binaryAction G X).ker ↔
    ∀ ω (x : BinaryFiber G X ω), g • x=x :=
  ActiveFiberPermutation.ker_iff (BinaryFiber G X) g

theorem odd_kernel_iff (g : OddFactor G) : g∈(oddAction G X).ker ↔
    ∀ ω (x : OddFiber G X ω), g • x=x :=
  ActiveFiberPermutation.ker_iff (OddFiber G X) g
end SymmetricSubgroupAsymptotics.MarkedC4.NilpotentCompressedImages
