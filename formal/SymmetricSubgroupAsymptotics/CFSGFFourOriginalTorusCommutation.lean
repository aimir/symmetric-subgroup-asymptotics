import SymmetricSubgroupAsymptotics.CFSGFFourOriginalProductTorus

/-! Each same-Model simple torus is a coordinate image of the actual
product torus homomorphism. Consequently all simple tori commute, without
identifying an enlarged normalizer with a torus. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalTorusCommutation
open CFSGFFourOriginalProductTorus CFSGFFourOriginalParameterizedTorus
open CFSGFFourOriginalMiddleWords

private theorem hom_images_commute {S T : Type*} [CommGroup S] [Group T]
    (f : S→*T) (s t : S) : Commute (f s) (f t) := by
  change f s*f t=f t*f s
  rw [←map_mul,←map_mul,mul_comm]

variable (K : Type) [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem parameterTorus_one (i : Fin 4) : parameterTorus K i 1=1 := by
  simp only [parameterTorus,parameterWeyl,Units.val_one,inv_one,weyl,mul_inv_cancel]

theorem modelProductTorus_single (i : Fin 4) (a : Kˣ) :
    modelProductTorusHom K (Pi.mulSingle i a)=parameterTorus K i a := by
  rw [modelProductTorus_word]
  fin_cases i <;> simp [parameterTorus_one,Fin.ext_iff]

theorem parameterTorus_commute (i j : Fin 4) (a b : Kˣ) :
    Commute (parameterTorus K i a) (parameterTorus K j b) := by
  rw [←modelProductTorus_single K i a,←modelProductTorus_single K j b]
  let x : Fin 4→Kˣ := Pi.mulSingle i a
  let y : Fin 4→Kˣ := Pi.mulSingle j b
  exact hom_images_commute (modelProductTorusHom K) x y

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalTorusCommutation
