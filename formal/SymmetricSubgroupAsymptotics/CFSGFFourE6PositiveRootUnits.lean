import SymmetricSubgroupAsymptotics.CFSGFFourIntegralRealization
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralRealization
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalRoots
import SymmetricSubgroupAsymptotics.CFSGQuadraticRootOrthogonalProduct

/-! The literal positive folded F4 root units are products of the
corresponding E6 root units. Mixed coefficients are proved over the
integers before base change, so the result includes bad characteristics. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveRootUnits
open CFSGFFourSerreMatrices CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGSerreQuadraticMatrix
open scoped Classical

abbrev e6Data := CFSGNormTwoGeckIntegralRealization.realizationData
  CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index

private theorem rational_mixed (i j : Fin 6)
    (hc : CartanMatrix.E₆ i j=0) (hc' : CartanMatrix.E₆ j i=0) :
    e6E i*e6Second j=0 ∧ e6Second i*e6E j=0 ∧ e6Second i*e6Second j=0 := by
  have heh := e6_mul_other_second i j hc'
  have hdf := CFSGQuadraticOrthogonalSum.second_mul_other
    (e6E i) (e6E j) (e6Second i)
    (e6_commute_of_cartan_zero i j hc) (e6_square i)
    (e6_mul_other_second j i hc)
  refine ⟨heh,hdf,?_⟩
  have hz : (2:ℚ) • (e6Second i*e6Second j)=0 := by
    calc
      (2:ℚ) • (e6Second i*e6Second j)=
          e6Second i*(e6Second j+e6Second j) := by
            rw [two_smul,mul_add]
      _=e6Second i*(e6E j*e6E j) := by rw [e6_square]
      _=0 := by rw [←mul_assoc,hdf,zero_mul]
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

private theorem integral_mixed (i j : Fin 6)
    (hc : CartanMatrix.E₆ i j=0) (hc' : CartanMatrix.E₆ j i=0) :
    e6EZ i*e6SecondZ j=0 ∧ e6SecondZ i*e6EZ j=0 ∧
      e6SecondZ i*e6SecondZ j=0 := by
  obtain ⟨hl,hr,hd⟩ := rational_mixed i j hc hc'
  refine ⟨?_,?_,?_⟩
  · apply CFSGSerreSquareZeroMatrix.integerCast_injective Index
    change (Int.castRingHom ℚ).mapMatrix (_*_)=(Int.castRingHom ℚ).mapMatrix 0
    simpa only [map_mul,map_zero,map_e6EZ,map_e6SecondZ] using hl
  · apply CFSGSerreSquareZeroMatrix.integerCast_injective Index
    change (Int.castRingHom ℚ).mapMatrix (_*_)=(Int.castRingHom ℚ).mapMatrix 0
    simpa only [map_mul,map_zero,map_e6EZ,map_e6SecondZ] using hr
  · apply CFSGSerreSquareZeroMatrix.integerCast_injective Index
    change (Int.castRingHom ℚ).mapMatrix (_*_)=(Int.castRingHom ℚ).mapMatrix 0
    simpa only [map_mul,map_zero,map_e6SecondZ] using hd

theorem positive_pair_product (K : Type*) [CommRing K] (i j : Fin 6)
    (hc : CartanMatrix.E₆ i j=0) (hc' : CartanMatrix.E₆ j i=0) (t : K) :
    (canonicalRoot e6Data K false i t : Matrix Index Index K)*
        (canonicalRoot e6Data K false j t : Matrix Index Index K)=
      1+t • (fieldRoot e6Data K false i+fieldRoot e6Data K false j)+
        t^2 • (fieldSecond e6Data K false i+fieldSecond e6Data K false j+
          fieldRoot e6Data K false i*fieldRoot e6Data K false j) := by
  obtain ⟨hl,hr,hd⟩ := integral_mixed i j hc hc'
  have mapped {x y : IntMat} (h : x*y=0) :
      (Int.castRingHom K).mapMatrix x*(Int.castRingHom K).mapMatrix y=0 := by
    rw [←map_mul,h,map_zero]
  rw [canonicalRoot_val,canonicalRoot_val]
  exact CFSGQuadraticRootOrthogonalProduct.polynomial_product _ _ _ _
    (mapped hl) (mapped hr) (mapped hd) t

theorem folded_positive_root (K : Type*) [CommRing K] (i : Fin 4) (t : K) :
    canonicalRoot realizationData K false i t=
      ![canonicalRoot e6Data K false 0 t*canonicalRoot e6Data K false 5 t,
        canonicalRoot e6Data K false 2 t*canonicalRoot e6Data K false 4 t,
        canonicalRoot e6Data K false 3 t,canonicalRoot e6Data K false 1 t] i := by
  apply Units.ext
  fin_cases i
  · change 1+t • (Int.castRingHom K).mapMatrix (e6EZ 0+e6EZ 5)+
        t^2 • (Int.castRingHom K).mapMatrix
          (e6SecondZ 0+e6SecondZ 5+e6EZ 0*e6EZ 5)=
      (canonicalRoot e6Data K false 0 t : Matrix Index Index K)*
        (canonicalRoot e6Data K false 5 t : Matrix Index Index K)
    rw [positive_pair_product K 0 5 (by decide) (by decide)]
    simp only [map_add,map_mul]
    rfl
  · change 1+t • (Int.castRingHom K).mapMatrix (e6EZ 2+e6EZ 4)+
        t^2 • (Int.castRingHom K).mapMatrix
          (e6SecondZ 2+e6SecondZ 4+e6EZ 2*e6EZ 4)=
      (canonicalRoot e6Data K false 2 t : Matrix Index Index K)*
        (canonicalRoot e6Data K false 4 t : Matrix Index Index K)
    rw [positive_pair_product K 2 4 (by decide) (by decide)]
    simp only [map_add,map_mul]
    rfl
  · rfl
  · rfl

end SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveRootUnits
