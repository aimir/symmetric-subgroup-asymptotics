import SymmetricSubgroupAsymptotics.MarkedC4NilpotentCompressedEquiv
import SymmetricSubgroupAsymptotics.MarkedC4PhysicalGridLabels

/-! Finite original-label codes for actual nilpotent permutation sources.
The label map is constructed from their original point grids and is
injective on original points. The alphabet has (b+1)^(3b) elements. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.NilpotentOriginalLabels
open NilpotentSylowFactors NilpotentPermutationGrid NilpotentCompressedImages

variable {b : ℕ} (K : Subgroup (PermutationGroup b)) [Group.IsNilpotent K]
local instance : Fintype (OrbitIndex K (Fin b)) := Fintype.ofFinite _
local instance (ω : OrbitIndex K (Fin b)) : Fintype (BinaryFiber K (Fin b) ω) := Fintype.ofFinite _
local instance (ω : OrbitIndex K (Fin b)) : Fintype (OddFiber K (Fin b) ω) := Fintype.ofFinite _
local instance : Fintype (PhysicalGridLabels.Active (BinaryFiber K (Fin b))) :=
  PhysicalGridLabels.instFintypeActive (BinaryFiber K (Fin b))
local instance : Fintype (PhysicalGridLabels.Active (OddFiber K (Fin b))) :=
  PhysicalGridLabels.instFintypeActive (OddFiber K (Fin b))

private theorem orbit_count_le : Fintype.card (OrbitIndex K (Fin b))≤b := by
  have h := Nat.card_le_card_of_injective
    (fun ω : OrbitIndex K (Fin b) => ω.out) Quotient.out_injective
  simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using h

private theorem binary_card_le :
    Fintype.card (PhysicalGridLabels.Active (BinaryFiber K (Fin b)))≤b := by
  have h := physical_budget K (Fin b)
  rw [Nat.card_fin] at h
  have ha : Nat.card (BinarySupport K (Fin b))≤b := (Nat.le_add_right _ _).trans h
  simpa only [Nat.card_eq_fintype_card] using ha

private theorem odd_card_le :
    Fintype.card (PhysicalGridLabels.Active (OddFiber K (Fin b)))≤b := by
  have h := physical_budget K (Fin b)
  rw [Nat.card_fin] at h
  have hd : Nat.card (OddSupport K (Fin b))≤b := (Nat.le_add_left _ _).trans h
  simpa only [Nat.card_eq_fintype_card] using hd

def code : PhysicalGridLabels.Code b := fun x =>
  PhysicalGridLabels.boundedLabels (BinaryFiber K (Fin b)) (OddFiber K (Fin b))
    (orbit_count_le K) (binary_card_le K) (odd_card_le K) (pointGrid K (Fin b) x)

/-- No original point is lost, even on entirely fixed orbits. -/
theorem code_injective : Function.Injective (code K) :=
  (PhysicalGridLabels.boundedLabels_injective (BinaryFiber K (Fin b)) (OddFiber K (Fin b))
    (orbit_count_le K) (binary_card_le K) (odd_card_le K)).comp
      (pointGrid K (Fin b)).injective

/-- All original-label maps belong to this one finite alphabet, independent
of the source K and its prime factorization or orbit multiplicities. -/
theorem alphabet_card : Fintype.card (PhysicalGridLabels.Code b)=(b+1)^(3*b) :=
  PhysicalGridLabels.card_code b

end SymmetricSubgroupAsymptotics.MarkedC4.NilpotentOriginalLabels
