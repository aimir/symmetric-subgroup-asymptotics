import SymmetricSubgroupAsymptotics.BinaryPlaneKernelClassSignDescent
import SymmetricSubgroupAsymptotics.PrimeTwoKernelOrbitNormalGeneration
import SymmetricSubgroupAsymptotics.OddMarkerTernaryChart

/-! Literal cubic coordinates on the actual odd kernel. Two genuine
coordinate-kernel classes give jointly faithful coordinates in C3 squared;
an actual block transporter swaps those two kernels, so one normal seed
suffices in the SAME original ambient subgroup. No independent product
or externally chosen cubic action is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneTwoClassOddNormalGenerators
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel BinaryPlaneWreathNormalGenerators
open BinaryPlaneOddKernelMultiplicityUniform (localKernel)

variable {R I : Type} [Group R] [Finite R] [MulAction R I]
    [Fintype I] [DecidableEq I] (C : Subgroup (W (R := R) (I := I)))

private def localEven (i : I) : oddKernel C →* oddMarkerSign.ker where
  toFun u := ⟨toThree (localLinear C i u),local_even C i u⟩
  map_one' := Subtype.ext (by
    change toThree (localLinear C i 1) = 1
    rw [map_one,map_one])
  map_mul' u v := Subtype.ext (by
    change toThree (localLinear C i (u*v)) = toThree (localLinear C i u)*toThree (localLinear C i v)
    rw [map_mul,map_mul])

def coordinate (i : I) : oddKernel C →* Multiplicative (ZMod 3) :=
  OddMarkerTernaryChart.chart.symm.toMonoidHom.comp (localEven C i)

theorem coordinate_ker (i : I) : (coordinate C i).ker = localKernel C i := by
  ext u
  change OddMarkerTernaryChart.chart.symm (localEven C i u) = 1 ↔ localLinear C i u = 1
  constructor
  · intro h
    have he : localEven C i u = 1 :=
      OddMarkerTernaryChart.chart.symm.injective (h.trans (map_one _).symm)
    exact toThree_injective ((congrArg Subtype.val he).trans (map_one toThree).symm)
  · intro h
    have he : localEven C i u = 1 := Subtype.ext (by
      change toThree (localLinear C i u) = 1
      rw [h,map_one])
    rw [he,map_one]

theorem two_coordinates_injective (i j : I)
    (hcover : ∀ k : I, localKernel C k = localKernel C i ∨ localKernel C k = localKernel C j) :
    Function.Injective (fun u : oddKernel C => (coordinate C i u,coordinate C j u)) := by
  intro u v he
  have hfi : coordinate C i u = coordinate C i v := congrArg Prod.fst he
  have hgj : coordinate C j u = coordinate C j v := congrArg Prod.snd he
  have hi : u*v⁻¹ ∈ localKernel C i := by
    rw [←coordinate_ker C i]
    change coordinate C i (u*v⁻¹) = 1
    rw [map_mul,map_inv,hfi,mul_inv_cancel]
  have hj : u*v⁻¹ ∈ localKernel C j := by
    rw [←coordinate_ker C j]
    change coordinate C j (u*v⁻¹) = 1
    rw [map_mul,map_inv,hgj,mul_inv_cancel]
  have hz : u*v⁻¹ = 1 := by
    apply localLinear_joint C
    intro k
    have hk : u*v⁻¹ ∈ localKernel C k := by
      rcases hcover k with hk | hk
      · rw [hk]; exact hi
      · rw [hk]; exact hj
    have hk' : localLinear C k (u*v⁻¹) = 1 := hk
    exact hk'.trans (map_one (localLinear C k)).symm
  exact mul_inv_eq_one.mp hz

theorem normalGen_le_one_of_two_classes
    (htrans : ∀ i j : I, ∃ h : C, (h : W (R := R) (I := I)).right • i = j)
    (i j : I) (hne : localKernel C i ≠ localKernel C j)
    (hcover : ∀ k : I, localKernel C k = localKernel C i ∨ localKernel C k = localKernel C j) :
    MarkedC4.normalGen (oddKernel C) ≤ 1 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h,hh⟩ := htrans i j
  have hfg : (localKernel C i).map (MulAut.conjNormal h).toMonoidHom = localKernel C j := by
    simpa only [hh] using BinaryPlaneOddKernelMultiplicityUniform.kernel_map C h i
  have hgf : (localKernel C j).map (MulAut.conjNormal h).toMonoidHom = localKernel C i := by
    have hm := BinaryPlaneOddKernelMultiplicityUniform.kernel_map C h j
    rcases hcover ((h : W (R := R) (I := I)).right • j) with hk | hk
    · exact hm.trans hk
    · have he : localKernel C ((h : W (R := R) (I := I)).right • i) =
          localKernel C ((h : W (R := R) (I := I)).right • j) := by
        rw [hh,hk]
      exact (hne ((BinaryPlaneOddKernelMultiplicityUniform.kernel_covariance C h i j).mp he)).elim
  apply PrimeTwoKernelOrbitNormalGeneration.normalGen_le_one_of_two_kernel_orbit
    (oddKernel C) 3 (coordinate C i) (coordinate C j)
    (two_coordinates_injective C i j hcover) h
  · simpa only [coordinate_ker] using hne
  · simpa only [coordinate_ker] using hfg
  · simpa only [coordinate_ker] using hgf

end SymmetricSubgroupAsymptotics.BinaryPlaneTwoClassOddNormalGenerators
