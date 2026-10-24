import SymmetricSubgroupAsymptotics.CFSGE6GeckOuterTorusExponentCertificate
import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeWeylRawWords
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorusScalarCompatibility

/-! The literal outer relative Weyl element reflects the actual fixed
torus by (a,b) to (b/a,b). This is an original source-word identity from
the proved raw torus conjugation, not Weyl-word recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterTorusReflection
open CFSGE6GeckOuterTorusExponentCertificate CFSGE6GeckProductTorusWeylAction
open CFSGReeFFourRelativeWeylRawWords CFSGReeFFourRelativeSimpleWeyl
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFieldParameters
open CFSGFFourOriginalMiddleWords CFSGFFourOriginalProductTorus
open CFSGReeFFourFixedTorus CFSGReeFFourFixedTorusScalarCompatibility
open CFSGFFourE6ProductTorus CFSGFFourE6ScalarTuple
open CFSGIntegerMatrixPowerHom CFSGE6GeckProductTorus

private theorem outer_fixed_tuple (m : ℕ) (a b : (Field m)ˣ) :
    powerHom outerExponents (CFSGReeFFourFixedTorus.fixedTorusTuple m a b)=
      CFSGReeFFourFixedTorus.fixedTorusTuple m (b*a⁻¹) b := by
  rw [outer_exponents_value]
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · change alphaUnits m b*(alphaUnits m a)⁻¹=alphaUnits m (b*a⁻¹)
    rw [map_mul,map_inv]

def outerFixedReflection (m : ℕ) : originalModelFixed m :=
  ⟨outerRelativeWeyl m,outerRelativeWeyl_fixed m⟩

theorem model_outer_torus_reflection (m : ℕ) (a b : (Field m)ˣ) :
    outerRelativeWeyl m*(fixedTorus m a b).val*(outerRelativeWeyl m)⁻¹=
      (fixedTorus m (b*a⁻¹) b).val := by
  apply rawHom_injective (Field m)
  simp only [map_mul,map_inv,rawHom_outerRelativeWeyl,fixedTorus_val,rawHom_modelProductTorus]
  change _*rawProductTorus (Field m)
      (scalarTupleHom (CFSGReeFFourFixedTorus.fixedTorusTuple m a b))*_=
    rawProductTorus (Field m)
      (scalarTupleHom (CFSGReeFFourFixedTorus.fixedTorusTuple m (b*a⁻¹) b))
  rw [word_product_torus,outer_folded_tuple,outer_fixed_tuple]

theorem fixed_outer_torus_reflection (m : ℕ) (a b : (Field m)ˣ) :
    outerFixedReflection m*fixedTorus m a b*(outerFixedReflection m)⁻¹=
      fixedTorus m (b*a⁻¹) b :=
  Subtype.ext (model_outer_torus_reflection m a b)

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterTorusReflection
