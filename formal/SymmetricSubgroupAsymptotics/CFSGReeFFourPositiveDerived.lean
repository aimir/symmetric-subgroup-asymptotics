import SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveDerivedCoordinates
import SymmetricSubgroupAsymptotics.SubgroupFiltrationCoordinateDescent

/-! Full positive-subgroup membership in the commutator subgroup for the
original exceptional-fixed ReeF4 group when m>0. The proof descends the
actual ambient height filtration using genuine commutator representatives.
It makes no assertion for the Tits parameter m=0. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveDerived
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourPositiveHeightCoordinates
open CFSGReeFFourPositiveDerivedCoordinates CFSGNormTwoCoordinateExactHeightLayer
open CFSGNormTwoCoordinateRootHeightBound
local notation "A" => CartanMatrix.E₆
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

private def allCoordinateHom (m : ℕ) (h : ℤ) :
    tail m h→*Multiplicative (ExactHeightRoot A h→Field m) :=
  if hh : 0<h then coordinateHom m h hh else 1

theorem fixedPositive_le_commutator (m : ℕ) (hm : 0<m) :
    fixedPositive m≤commutator (originalModelFixed m) := by
  let S : Subgroup (fixedPositive m) :=
    (commutator (originalModelFixed m)).comap (fixedPositive m).subtype
  have hmem (u : fixedPositive m) : u∈S := by
    apply SubgroupFiltrationCoordinateDescent.mem_of_positive_coordinate_representatives
      S (tail m) (fun h=>Multiplicative (ExactHeightRoot A h→Field m))
      (allCoordinateHom m) (rootHeightBound A) (first_tail_eq_top m)
      (terminal_tail_eq_bot m) ?_ ?_ u
    · intro h hh
      simpa only [allCoordinateHom,dif_pos hh] using coordinateHom_kernel_le m h hh
    · intro h hh x
      obtain ⟨v,hv,he⟩ := exists_derived_same_coordinate m hm h hh x
      refine ⟨v,hv,?_⟩
      simpa only [allCoordinateHom,dif_pos hh] using he
  intro g hg
  exact hmem ⟨g,hg⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveDerived
