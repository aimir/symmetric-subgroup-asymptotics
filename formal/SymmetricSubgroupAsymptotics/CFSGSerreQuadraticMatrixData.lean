import SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroMatrixData
import SymmetricSubgroupAsymptotics.CFSGQuadraticRootDividedPowers

/-! Integral descent for actual rational Serre matrix realizations with
quadratic root exponentials. The fields below are concrete polynomial
identities, not an assumed divided-power intertwiner or image theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
open CFSG.Models.Chevalley
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (I : Type*) [Fintype I] [DecidableEq I]
abbrev IntMat := Matrix I I ℤ
abbrev RatMat := Matrix I I ℚ

structure Data where
  rational : RationalLie A→ₗ⁅ℚ⁆RatMat I
  integerGenerator : CartanMatrix.Generators (Fin n)→IntMat I
  integerSecond : Bool→Fin n→IntMat I
  generator_cast : ∀g,(Int.castRingHom ℚ).mapMatrix (integerGenerator g)=rational (generator A g)
  root_square : ∀neg i,
    integerGenerator (CFSGSerreSquareZeroMatrix.rootGenerator neg i)*
      integerGenerator (CFSGSerreSquareZeroMatrix.rootGenerator neg i)=integerSecond neg i+integerSecond neg i
  root_mul_second : ∀neg i,
    integerGenerator (CFSGSerreSquareZeroMatrix.rootGenerator neg i)*integerSecond neg i=0
  second_mul_root : ∀neg i,
    integerSecond neg i*integerGenerator (CFSGSerreSquareZeroMatrix.rootGenerator neg i)=0
  second_square : ∀neg i,integerSecond neg i*integerSecond neg i=0

variable {A I}
def integerRoot (D : Data A I) (neg : Bool) (i : Fin n) : IntMat I :=
  D.integerGenerator (CFSGSerreSquareZeroMatrix.rootGenerator neg i)
def fieldRoot (D : Data A I) (K : Type*) [CommRing K] (neg : Bool) (i : Fin n) : Matrix I I K :=
  (Int.castRingHom K).mapMatrix (integerRoot D neg i)
def fieldSecond (D : Data A I) (K : Type*) [CommRing K] (neg : Bool) (i : Fin n) : Matrix I I K :=
  (Int.castRingHom K).mapMatrix (D.integerSecond neg i)

theorem fieldRoot_square (D : Data A I) (K : Type*) [CommRing K] (neg : Bool) (i : Fin n) :
    fieldRoot D K neg i*fieldRoot D K neg i=fieldSecond D K neg i+fieldSecond D K neg i := by
  have hh := congrArg (Int.castRingHom K).mapMatrix (D.root_square neg i)
  simpa only [fieldRoot,integerRoot,fieldSecond,map_mul,map_add] using hh

theorem fieldRoot_mul_second (D : Data A I) (K : Type*) [CommRing K] (neg : Bool) (i : Fin n) :
    fieldRoot D K neg i*fieldSecond D K neg i=0 := by
  have hh := congrArg (Int.castRingHom K).mapMatrix (D.root_mul_second neg i)
  simpa only [fieldRoot,integerRoot,fieldSecond,map_mul,map_zero] using hh

theorem fieldSecond_mul_root (D : Data A I) (K : Type*) [CommRing K] (neg : Bool) (i : Fin n) :
    fieldSecond D K neg i*fieldRoot D K neg i=0 := by
  have hh := congrArg (Int.castRingHom K).mapMatrix (D.second_mul_root neg i)
  simpa only [fieldRoot,integerRoot,fieldSecond,map_mul,map_zero] using hh

theorem fieldSecond_square (D : Data A I) (K : Type*) [CommRing K] (neg : Bool) (i : Fin n) :
    fieldSecond D K neg i*fieldSecond D K neg i=0 := by
  have hh := congrArg (Int.castRingHom K).mapMatrix (D.second_square neg i)
  simpa only [fieldSecond,map_mul,map_zero] using hh

theorem rational_rootVector (D : Data A I) (neg : Bool) (i : Fin n) :
    D.rational (rootVector A neg i)=fieldRoot D ℚ neg i := by
  cases neg
  · exact (D.generator_cast (.E i)).symm
  · exact (D.generator_cast (.F i)).symm

private theorem operator_mem_subring {B : Type*} [Ring B] [Algebra ℚ B]
    (T : Subring B) (e d : B) (he : e∈T) (hd : d∈T) (k : ℕ) (x : B) (hx : x∈T) :
    CFSGIntegralQuadraticRootOperators.operator ℚ e d k x∈T := by
  by_cases hk : 5≤k
  · rw [CFSGIntegralQuadraticRootOperators.operator_large ℚ e d x k hk]
    exact T.zero_mem
  · have hlt : k<5 := by omega
    interval_cases k
    · simpa only [CFSGIntegralQuadraticRootOperators.operator_zero] using hx
    · rw [CFSGIntegralQuadraticRootOperators.operator_one]
      exact T.sub_mem (T.mul_mem he hx) (T.mul_mem hx he)
    · rw [CFSGIntegralQuadraticRootOperators.operator_two]
      exact T.sub_mem (T.add_mem (T.mul_mem hd hx) (T.mul_mem hx hd))
        (T.mul_mem (T.mul_mem he hx) he)
    · rw [CFSGIntegralQuadraticRootOperators.operator_three]
      exact T.sub_mem (T.mul_mem (T.mul_mem he hx) hd) (T.mul_mem (T.mul_mem hd hx) he)
    · rw [CFSGIntegralQuadraticRootOperators.operator_four]
      exact T.mul_mem (T.mul_mem hd hx) hd

theorem lattice_image_integral (D : Data A I) (x : RationalLie A) (hx : x∈integralLattice A) :
    D.rational x∈CFSGSerreSquareZeroMatrix.integerMatrices I := by
  let T := CFSGSerreSquareZeroMatrix.integerMatrices I
  let S : Submodule ℤ (RationalLie A) := T.toAddSubgroup.toIntSubmodule.comap
    (D.rational.toLinearMap.restrictScalars ℤ)
  have hgen : ∀g,generator A g∈S := by
    intro g
    exact ⟨D.integerGenerator g,D.generator_cast g⟩
  have hstable : ∀neg i k y,y∈S→dividedPower A neg i k y∈S := by
    intro neg i k y hy
    change D.rational y∈T at hy
    change D.rational (dividedPower A neg i k y)∈T
    rw [CFSGSerreIntegralRepresentation.dividedPower_intertwines,rational_rootVector,
      CFSGQuadraticRootDividedPowers.rational_operator _ _
        (fieldRoot_square D ℚ neg i) (fieldRoot_mul_second D ℚ neg i) (fieldSecond_mul_root D ℚ neg i)]
    exact operator_mem_subring T _ _ ⟨integerRoot D neg i,rfl⟩ ⟨D.integerSecond neg i,rfl⟩ k _ hy
  exact (show integralLattice A≤S from sInf_le ⟨hgen,hstable⟩) hx

def latticeRationalMap (D : Data A I) : integralLattice A→ₗ[ℤ]RatMat I :=
  (D.rational.toLinearMap.restrictScalars ℤ).domRestrict (integralLattice A)
def latticeIntegerRange (D : Data A I) :
    integralLattice A→ₗ[ℤ](CFSGSerreSquareZeroMatrix.integerCast I).range :=
  (latticeRationalMap D).codRestrict (CFSGSerreSquareZeroMatrix.integerCast I).range
    (fun x=>lattice_image_integral D x.val x.property)
def integralRepresentation (D : Data A I) : integralLattice A→ₗ[ℤ]IntMat I :=
  (LinearEquiv.ofInjective (CFSGSerreSquareZeroMatrix.integerCast I)
    (CFSGSerreSquareZeroMatrix.integerCast_injective I)).symm.toLinearMap.comp (latticeIntegerRange D)

theorem integralRepresentation_cast (D : Data A I) (x : integralLattice A) :
    CFSGSerreSquareZeroMatrix.integerCast I (integralRepresentation D x)=D.rational x.val := by
  have hh := (LinearEquiv.ofInjective (CFSGSerreSquareZeroMatrix.integerCast I)
    (CFSGSerreSquareZeroMatrix.integerCast_injective I)).apply_symm_apply (latticeIntegerRange D x)
  exact congrArg Subtype.val hh

theorem integralRepresentation_generator (D : Data A I) (g : CartanMatrix.Generators (Fin n)) :
    integralRepresentation D (CFSGSerreDiagram.latticeGenerator A g)=D.integerGenerator g := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective I
  rw [integralRepresentation_cast]
  change D.rational (generator A g)=(Int.castRingHom ℚ).mapMatrix (D.integerGenerator g)
  exact (D.generator_cast g).symm

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
