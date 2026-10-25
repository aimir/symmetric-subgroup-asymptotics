import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCentralJoin
import Mathlib.Algebra.Group.Subgroup.Finite

/-! The horizontal central plane is a genuine normal subgroup of the
actual source. Its invariance is checked on the literal normal radical,
short roots and short Weyl word, retaining original root parameters. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCentralPlane
open CFSG.Models.Chevalley CFSGGTwoOriginalNaturalEquivalence
open CFSGGTwoOriginalPositiveRootWords CFSGGTwoOriginalPositiveCollecting
open CFSGGTwoCharacteristicThreeMiddleCoordinateEquiv
open CFSGGTwoCharacteristicThreeMiddleCentralCoordinates
open CFSGGTwoCharacteristicThreeMiddleCentralWords
open CFSGGTwoCharacteristicThreeMiddleSource
variable (K : Type) [Field K] [Finite K] [CharP K 3]
local instance : Finite (Model CartanMatrix.G₂ K) :=
  Finite.of_injective (modelEquivNatural K) (modelEquivNatural K).injective

def horizontalCoordinates : Subgroup (Multiplicative (Fin 3 → K)) :=
  (LinearMap.proj (2 : Fin 3) : (Fin 3 → K) →ₗ[K] K).toAddMonoidHom.toMultiplicative.ker

def rawCentralHom : Multiplicative (Fin 3 → K) →* Model CartanMatrix.G₂ K :=
  (Middle K).subtype.comp (centralHom K)

theorem rawCentralHom_val (z : Multiplicative (Fin 3 → K)) :
    rawCentralHom K z = centralWord K z.toAdd := centralHom_val K z

def planeModel : Subgroup (Model CartanMatrix.G₂ K) :=
  (horizontalCoordinates K).map (rawCentralHom K)

theorem short_conjugate_central (a : K) (v : Fin 3 → K) :
    positiveModel K 0 a*centralWord K v*(positiveModel K 0 a)⁻¹ =
      centralWord K ![v 0,v 1+a*v 0,v 2] := by
  let w : Fin 3 → K := ![v 0,v 1+a*v 0,v 2]
  have h := centralWord_short_collect K w a
  have hv : ![w 0,w 1-a*w 0,w 2] = v := by
    funext i
    fin_cases i
    · rfl
    · change v 1+a*v 0-a*v 0 = v 1
      ring
    · rfl
  rw [hv] at h
  exact mul_inv_eq_iff_eq_mul.mpr h.symm

theorem planeModel_le_source : planeModel K ≤ source K := by
  rintro x ⟨z,hz,rfl⟩
  exact middle_le_source K (centralHom K z).property

theorem source_le_normalizer_plane : source K ≤
    Subgroup.normalizer (planeModel K : Set (Model CartanMatrix.G₂ K)) := by
  change Middle K ⊔ Subgroup.closure {g | (∃ a : K,g=positiveModel K 0 a) ∨ g=shortWord K} ≤ _
  apply sup_le
  · intro n hn
    apply Subgroup.mem_normalizer_fintype
    rintro x ⟨z,hz,rfl⟩
    have hcent : centralHom K z ∈ Subgroup.center (Middle K) := by
      rw [center_eq_endpointKer,←centralHom_range]
      exact ⟨z,rfl⟩
    have he : n*rawCentralHom K z = rawCentralHom K z*n :=
      congrArg (fun u : Middle K => u.val)
        (Subgroup.mem_center_iff.mp hcent (⟨n,hn⟩ : Middle K))
    rw [he,mul_assoc,mul_inv_cancel,mul_one]
    exact ⟨z,hz,rfl⟩
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with ⟨a,rfl⟩|rfl
    · apply Subgroup.mem_normalizer_fintype
      rintro x ⟨z,hz,rfl⟩
      refine ⟨Multiplicative.ofAdd ![z.toAdd 0,z.toAdd 1+a*z.toAdd 0,z.toAdd 2],?_,?_⟩
      · exact hz
      · rw [rawCentralHom_val,rawCentralHom_val]
        exact (short_conjugate_central K a z.toAdd).symm
    · apply Subgroup.mem_normalizer_fintype
      rintro x ⟨z,hz,rfl⟩
      refine ⟨Multiplicative.ofAdd ![-z.toAdd 1,z.toAdd 0,z.toAdd 2],?_,?_⟩
      · exact hz
      · rw [rawCentralHom_val,rawCentralHom_val]
        exact (shortWeyl_centralWord K z.toAdd).symm

def plane : Subgroup (source K) := (planeModel K).subgroupOf (source K)

theorem plane_normal : (plane K).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (planeModel_le_source K)).mpr
    (source_le_normalizer_plane K)

theorem third_root_mem_planeModel (a : K) : positiveModel K 3 a ∈ planeModel K := by
  refine ⟨Multiplicative.ofAdd ![0,a,0],rfl,?_⟩
  rw [rawCentralHom_val]
  change positiveModel K 2 0*positiveModel K 3 a*positiveModel K 4 0*
    positiveModel K 5 0 = positiveModel K 3 a
  simp only [positiveModel_zero,one_mul,mul_one]

end SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCentralPlane
