import SymmetricSubgroupAsymptotics.CFSGSerreIntegralRepresentation
import SymmetricSubgroupAsymptotics.CFSGSerreDiagramLattice
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Lie.Matrix

/-! Shared integral descent for an actual rational matrix realization
whose simple-root matrices have integral entries and square zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroMatrix
open CFSG.Models.Chevalley
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (I : Type*) [Fintype I] [DecidableEq I]
abbrev IntMat := Matrix I I ℤ
abbrev RatMat := Matrix I I ℚ

def rootGenerator (neg : Bool) (i : Fin n) : CartanMatrix.Generators (Fin n) :=
  if neg then .F i else .E i

structure Data where
  rational : RationalLie A→ₗ⁅ℚ⁆RatMat I
  integerGenerator : CartanMatrix.Generators (Fin n)→IntMat I
  generator_cast : ∀g,(Int.castRingHom ℚ).mapMatrix (integerGenerator g)=rational (generator A g)
  root_square_zero : ∀neg i,integerGenerator (rootGenerator neg i)^2=0

variable {A I}

def integerRoot (D : Data A I) (neg : Bool) (i : Fin n) : IntMat I :=
  D.integerGenerator (rootGenerator neg i)

def fieldRoot (D : Data A I) (K : Type*) [CommRing K] (neg : Bool) (i : Fin n) : Matrix I I K :=
  (Int.castRingHom K).mapMatrix (integerRoot D neg i)

theorem integerRoot_sq_zero (D : Data A I) (neg : Bool) (i : Fin n) : integerRoot D neg i^2=0 :=
  D.root_square_zero neg i

theorem fieldRoot_sq_zero (D : Data A I) (K : Type*) [CommRing K] (neg : Bool) (i : Fin n) :
    fieldRoot D K neg i*fieldRoot D K neg i=0 := by
  have hh := congrArg (Int.castRingHom K).mapMatrix (integerRoot_sq_zero D neg i)
  simpa only [fieldRoot,map_pow,map_zero,pow_two,map_mul] using hh

theorem rational_rootVector (D : Data A I) (neg : Bool) (i : Fin n) :
    D.rational (rootVector A neg i)=fieldRoot D ℚ neg i := by
  cases neg
  · exact (D.generator_cast (.E i)).symm
  · exact (D.generator_cast (.F i)).symm

def integerMatrices (I : Type*) [Fintype I] [DecidableEq I] : Subring (RatMat I) :=
  (Int.castRingHom ℚ).mapMatrix.range

theorem lattice_image_integral (D : Data A I) (x : RationalLie A) (hx : x∈integralLattice A) :
    D.rational x∈integerMatrices I := by
  apply CFSGSerreIntegralRepresentation.lattice_image_mem_subring A D.rational (integerMatrices I)
    ?_ ?_ x hx
  · intro g
    exact ⟨D.integerGenerator g,D.generator_cast g⟩
  · intro neg i
    rw [rational_rootVector]
    simpa only [pow_two] using fieldRoot_sq_zero D ℚ neg i

def integerCast (I : Type*) [Fintype I] [DecidableEq I] : IntMat I→ₗ[ℤ]RatMat I :=
  (Int.castRingHom ℚ).mapMatrix.toAddMonoidHom.toIntLinearMap

theorem integerCast_injective (I : Type*) [Fintype I] [DecidableEq I] :
    Function.Injective (integerCast I) := by
  intro X Y he
  ext i j
  apply (Int.cast_injective : Function.Injective (Int.cast : ℤ→ℚ))
  exact congrArg (fun Z : RatMat I => Z i j) he

def latticeRationalMap (D : Data A I) : integralLattice A→ₗ[ℤ]RatMat I :=
  (D.rational.toLinearMap.restrictScalars ℤ).domRestrict (integralLattice A)

def latticeIntegerRange (D : Data A I) : integralLattice A→ₗ[ℤ](integerCast I).range :=
  (latticeRationalMap D).codRestrict (integerCast I).range
    (fun x => lattice_image_integral D x.val x.property)

def integralRepresentation (D : Data A I) : integralLattice A→ₗ[ℤ]IntMat I :=
  (LinearEquiv.ofInjective (integerCast I) (integerCast_injective I)).symm.toLinearMap.comp
    (latticeIntegerRange D)

theorem integralRepresentation_cast (D : Data A I) (x : integralLattice A) :
    integerCast I (integralRepresentation D x)=D.rational x.val := by
  have hh := (LinearEquiv.ofInjective (integerCast I) (integerCast_injective I)).apply_symm_apply
    (latticeIntegerRange D x)
  exact congrArg Subtype.val hh

theorem integralRepresentation_generator (D : Data A I) (g : CartanMatrix.Generators (Fin n)) :
    integralRepresentation D (CFSGSerreDiagram.latticeGenerator A g)=D.integerGenerator g := by
  apply integerCast_injective I
  rw [integralRepresentation_cast]
  change D.rational (generator A g)=(Int.castRingHom ℚ).mapMatrix (D.integerGenerator g)
  exact (D.generator_cast g).symm

end SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroMatrix
