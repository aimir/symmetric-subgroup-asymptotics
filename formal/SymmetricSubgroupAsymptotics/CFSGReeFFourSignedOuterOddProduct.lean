import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryDerivedGeneration
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterSaving
import SymmetricSubgroupAsymptotics.CFSGReeFFourAmbientCentralQuotientAction
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterParabolicCardinality

/-! The actual outer signed involution pair has product order THREE,
including at the binary parameter, after the FULL derived-centre quotient.
Nontriviality is proved by central-kernel p-element separation and the
actual Weyl-not-in-Borel fact. No signed-block recognition, BN-pair,
known order or automorphism rigidity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourSignedOuterOddProduct
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourOriginalPositiveSylow
open CFSGReeFFourAllParameterDerivedPositive CFSGReeFFourBinaryDerivedGeneration
open CFSGReeFFourBinaryOuterSaving CFSGReeFFourOuterThreeWord
open CFSGReeFFourRelativePositiveSubgroups CFSGReeFFourRelativeWeylInvolutions
open CFSGReeFFourOuterParabolicCardinality CFSGReeFFourFixedBorelCardinality
open CFSGReeFFourOuterFixedRoot CFSGReeFFourOuterUnipotentGeneration
open CFSGReeFFourAmbientCentralQuotientAction CFSGReeFFourFixedPositiveFamilies
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def derivedOuterRoot (m : ℕ) : commutator (originalModelFixed m) :=
  ⟨outerInvolution m, outer_mem_derived m⟩

def derivedOuterWeyl (m : ℕ) : commutator (originalModelFixed m) :=
  ⟨outerFixedWeyl m, outer_weyl_mem_derived m (outer_mem_derived m)⟩

def originalOuterRoot (m : ℕ) : CFSG.Models.ReeF4 m :=
  derivedReeHom m (derivedOuterRoot m)

def originalOuterWeyl (m : ℕ) : CFSG.Models.ReeF4 m :=
  derivedReeHom m (derivedOuterWeyl m)

private theorem positive_injective (m : ℕ) : Function.Injective
    ((derivedReeHom m).comp (positiveSylow m : Subgroup (commutator (originalModelFixed m))).subtype) := by
  intro x y he
  apply CFSGDisjointSylowProjectiveCardinality.central_quotient_injective
    (positiveSylow m) (negativeSylow m) (opposite_inf m)
  exact (originalReeEquiv m).symm.injective he

private theorem source_root_square (m : ℕ) : (derivedOuterRoot m)^2 = 1 :=
  Subtype.ext (outerInvolution_square m)

private theorem source_weyl_square (m : ℕ) : (derivedOuterWeyl m)^2 = 1 := by
  apply Subtype.ext
  change (outerFixedWeyl m)^2 = 1
  have hi : (outerFixedWeyl m)⁻¹ = outerFixedWeyl m :=
    Subtype.ext (outerRelativeWeyl_inv m)
  calc
    _ = outerFixedWeyl m * outerFixedWeyl m := pow_two _
    _ = outerFixedWeyl m * (outerFixedWeyl m)⁻¹ :=
      congrArg (fun z => outerFixedWeyl m * z) hi.symm
    _ = 1 := mul_inv_cancel _

private theorem equal_images_of_product {G H : Type*} [Group G] [Group H]
    (f : G →* H) (w x : G) (hx : x^2=1) (h : f w*f x=1) : f w=f x := by
  have hs : (f x)^2=1 := (map_pow f x 2).symm.trans ((congrArg f hx).trans (map_one f))
  calc
    f w = f w*(f x)^2 := by rw [hs,mul_one]
    _ = (f w*f x)*f x := by rw [pow_two,mul_assoc]
    _ = f x := by rw [h,one_mul]

private theorem map_period {G H : Type*} [Group G] [Group H]
    (f : G →* H) (x : G) (n : ℕ) (h : x^n=1) : (f x)^n=1 :=
  (map_pow f x n).symm.trans ((congrArg f h).trans (map_one f))

theorem originalProduct_pow_three (m : ℕ) :
    (originalOuterWeyl m*originalOuterRoot m)^3=1 := by
  have h : (derivedOuterWeyl m*derivedOuterRoot m)^3=1 :=
    Subtype.ext (outerWeyl_product_cube m)
  simpa only [map_mul] using map_period (derivedReeHom m)
    (derivedOuterWeyl m*derivedOuterRoot m) 3 h

theorem originalProduct_ne_one (m : ℕ) :
    originalOuterWeyl m*originalOuterRoot m ≠ 1 := by
  intro h
  have he : derivedReeHom m (derivedOuterWeyl m) =
      derivedReeHom m (derivedOuterRoot m) :=
    equal_images_of_product (derivedReeHom m) (derivedOuterWeyl m)
      (derivedOuterRoot m) (source_root_square m) h
  have hs : derivedOuterWeyl m = derivedOuterRoot m :=
    CFSGCentralKernelPElements.eq_of_p_elements (derivedReeHom m) (positiveSylow m)
      (positive_injective m) (le_of_eq (derivedReeHom_ker m))
      (derivedOuterWeyl m) (derivedOuterRoot m)
      ⟨1, by simpa only [pow_one] using source_weyl_square m⟩
      ⟨1, by simpa only [pow_one] using source_root_square m⟩ he
  have hwx : outerFixedWeyl m=outerInvolution m := congrArg Subtype.val hs
  apply outerFixedWeyl_not_mem_borel m
  rw [hwx]
  exact positive_le_borel m (fixedOuterHom_range_le_fixedPositive m ⟨_,rfl⟩)

theorem originalProduct_order (m : ℕ) :
    orderOf (originalOuterWeyl m*originalOuterRoot m)=3 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact orderOf_eq_prime (originalProduct_pow_three m) (originalProduct_ne_one m)

def negativeOriginalOuterRoot (m : ℕ) : CFSG.Models.ReeF4 m :=
  originalOuterWeyl m*originalOuterRoot m*(originalOuterWeyl m)⁻¹

private theorem signed_product {G : Type*} [Group G] (w x : G) (hw : w^2=1) :
    (w*x*w⁻¹)*x=(w*x)^2 := by
  have hi : w⁻¹=w := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hw)
  simp only [hi,pow_two,mul_assoc]

theorem negative_mul_positive_order (m : ℕ) :
    orderOf (negativeOriginalOuterRoot m*originalOuterRoot m)=3 := by
  have hw : (originalOuterWeyl m)^2=1 :=
    map_period (derivedReeHom m) (derivedOuterWeyl m) 2 (source_weyl_square m)
  change orderOf ((originalOuterWeyl m*originalOuterRoot m*(originalOuterWeyl m)⁻¹)*
    originalOuterRoot m)=3
  rw [signed_product _ _ hw]
  have hc : (orderOf (originalOuterWeyl m*originalOuterRoot m)).Coprime 2 := by
    rw [originalProduct_order]
    decide
  exact hc.orderOf_pow.trans (originalProduct_order m)

end SymmetricSubgroupAsymptotics.CFSGReeFFourSignedOuterOddProduct
