import SymmetricSubgroupAsymptotics.CFSGGTwoNaturalBruhatFlag
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalBorel

/-! Actual original B6 values preserve the explicit native complete flag.
Two original Bruhat cells can have the same value only if their actual
monomial Weyl permutations agree. No ordinary simplicity, folded-model
recognition, or asserted Bruhat uniqueness is an input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalBruhatUniqueness
open CFSG.Models.Chevalley CFSGGTwoSerreMatrices CFSGGTwoNaturalBruhatFlag
open CFSGGTwoOriginalNaturalEquivalence CFSGGTwoOriginalPositiveRootWords
open CFSGGTwoOriginalRankTwoTorus CFSGGTwoPositiveWordSubgroup CFSGGTwoPositiveSixWord
open CFSGGTwoOriginalBorel
variable (K : Type) [Field K]
local notation "A" => CartanMatrix.G₂

def nativeHom : Model A K →* (Mat K)ˣ :=
  (naturalGroup K).subtype.comp (modelEquivNatural K).toMonoidHom

theorem nativeHom_positive (j : Fin 6) (a : K) :
    nativeHom K (positiveModel K j a)=CFSGGTwoPositiveDirections.positiveRoot K j a :=
  congrArg Subtype.val (positiveModel_native K j a)

theorem nativeHom_torus (t : Kˣ × Kˣ) :
    nativeHom K (torusPair K t)=(CFSGGTwoNaturalRankTwoTorus.torusPair K t).val :=
  congrArg Subtype.val (torusPair_native K t)

theorem nativeHom_injective : Function.Injective (nativeHom K) :=
  (naturalGroup K).subtype_injective.comp (modelEquivNatural K).injective

variable [CharP K 3]

theorem native_positive_upper (g : Model A K) (hg : g∈positiveWordGroup K) :
    nativeHom K g∈flagBorel K := by
  obtain ⟨x,rfl⟩ := hg
  have h (j : Fin 6) : nativeHom K (positiveModel K j (x j))∈flagBorel K := by
    rw [nativeHom_positive]
    exact positiveRoot_mem_flagBorel K j (x j)
  simp only [modelWord,map_mul]
  exact (flagBorel K).mul_mem ((flagBorel K).mul_mem ((flagBorel K).mul_mem
    ((flagBorel K).mul_mem ((flagBorel K).mul_mem (h 0) (h 1)) (h 2)) (h 3)) (h 4)) (h 5)

theorem native_positive_unipotent (g : Model A K) (hg : g∈positiveWordGroup K) :
    nativeHom K g∈CFSGMatrixFlagSubgroups.unipotentUnits coordinateOrder := by
  let U := CFSGMatrixFlagSubgroups.unipotentUnits (K := K) coordinateOrder
  obtain ⟨x,rfl⟩ := hg
  have h (j : Fin 6) : nativeHom K (positiveModel K j (x j))∈U := by
    rw [nativeHom_positive]
    exact positiveRoot_mem_flagUnipotent K j (x j)
  simp only [modelWord,map_mul]
  exact U.mul_mem (U.mul_mem (U.mul_mem (U.mul_mem (U.mul_mem
    (h 0) (h 1)) (h 2)) (h 3)) (h 4)) (h 5)

theorem native_borel_upper (g : Model A K) (hg : g∈borel K) :
    nativeHom K g∈flagBorel K := by
  obtain ⟨u,hu,t,ht,rfl⟩ := borel_factor K g hg
  rw [map_mul]
  apply (flagBorel K).mul_mem (native_positive_upper K u hu)
  obtain ⟨z,rfl⟩ := ht
  rw [torusHom_apply,nativeHom_torus]
  exact torusPair_mem_flagBorel K z

theorem original_cell_permutation_unique
    (b1 b2 w1 w2 : Model A K) (hb1 : b1∈borel K) (hb2 : b2∈borel K)
    (sigma1 sigma2 : Equiv.Perm Index) (d1 d2 : Index → K)
    (hW1 : (nativeHom K w1 : Mat K)=CFSGTypeAMonomialMatrices.monomial sigma1 d1)
    (hW2 : (nativeHom K w2 : Mat K)=CFSGTypeAMonomialMatrices.monomial sigma2 d2)
    (he : b1*w1*b2=w2) : sigma1=sigma2 := by
  apply monomial_permutation_unique K
    (nativeHom K b1) (nativeHom K b2) (nativeHom K w1) (nativeHom K w2)
    (native_borel_upper K b1 hb1) (native_borel_upper K b2 hb2)
    sigma1 sigma2 d1 d2 hW1 hW2
  simpa only [map_mul] using congrArg (nativeHom K) he

private theorem cell_rearrange {G : Type*} [Group G]
    (b1 b2 c1 c2 w1 w2 : G) (he : b1*w1*c1=b2*w2*c2) :
    (b2⁻¹*b1)*w1*(c1*c2⁻¹)=w2 := by
  calc
    _=b2⁻¹*(b1*w1*c1)*c2⁻¹ := by simp only [mul_assoc]
    _=b2⁻¹*(b2*w2*c2)*c2⁻¹ := by rw [he]
    _=w2 := by simp [mul_assoc]

theorem original_bruhat_cell_permutation_unique
    (b1 b2 c1 c2 w1 w2 : Model A K)
    (hb1 : b1∈borel K) (hb2 : b2∈borel K)
    (hc1 : c1∈borel K) (hc2 : c2∈borel K)
    (sigma1 sigma2 : Equiv.Perm Index) (d1 d2 : Index → K)
    (hW1 : (nativeHom K w1 : Mat K)=CFSGTypeAMonomialMatrices.monomial sigma1 d1)
    (hW2 : (nativeHom K w2 : Mat K)=CFSGTypeAMonomialMatrices.monomial sigma2 d2)
    (he : b1*w1*c1=b2*w2*c2) : sigma1=sigma2 :=
  original_cell_permutation_unique K (b2⁻¹*b1) (c1*c2⁻¹) w1 w2
    ((borel K).mul_mem ((borel K).inv_mem hb2) hb1)
    ((borel K).mul_mem hc1 ((borel K).inv_mem hc2))
    sigma1 sigma2 d1 d2 hW1 hW2 (cell_rearrange b1 b2 c1 c2 w1 w2 he)

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalBruhatUniqueness
