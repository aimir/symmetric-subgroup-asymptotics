import SymmetricSubgroupAsymptotics.PermutationalWreathQuotient
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Successive LOCAL quotient maps induce the same quotient of the original
correlated wreath source as their composite. The equivalence retains the
actual quotient classes of source elements; no independence of coordinates
or splitting of the original extension is inferred. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.WreathCompressionQuotientComposition
open PermutationalWreathProduct

variable {A D D' D'' Q I : Type}
    [Group A] [Group D] [Group D'] [Group D''] [Group Q] [MulAction Q I]
    (rho : A →* PermutationalWreathProduct D Q I)
    (phi : D →* D') (psi : D' →* D'')

/-- Local composition is coordinatewise composition with the SAME top. -/
theorem mapBase_comp :
    (mapBase (Q := Q) (I := I) psi).comp (mapBase phi) = mapBase (psi.comp phi) := by
  ext w i <;> rfl

/-- The second literal kernel pulls back to the original composite kernel. -/
theorem kernel_comap :
    (Compression.kernel (Compression.quotientEmbedding rho phi) psi).comap
        (QuotientGroup.mk' (Compression.kernel rho phi)) =
      Compression.kernel rho (psi.comp phi) := by
  ext a
  change (mapBase psi (Compression.quotientEmbedding rho phi
      (QuotientGroup.mk' (Compression.kernel rho phi) a)) = 1) ↔
    mapBase (psi.comp phi) (rho a) = 1
  rfl

/-- The image of the composite kernel is exactly the second kernel. -/
theorem kernel_map :
    (Compression.kernel rho (psi.comp phi)).map
        (QuotientGroup.mk' (Compression.kernel rho phi)) =
      Compression.kernel (Compression.quotientEmbedding rho phi) psi := by
  have hh := Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective (Compression.kernel rho phi))
    (Compression.kernel (Compression.quotientEmbedding rho phi) psi)
  rw [kernel_comap rho phi psi] at hh
  exact hh

/-- Canonical equivalence from the iterated actual quotient to the direct
actual quotient. Neither local surjectivity nor a faithful source is needed
for this quotient identity. -/
def quotientCompositionEquiv :
    ((A ⧸ Compression.kernel rho phi) ⧸
      Compression.kernel (Compression.quotientEmbedding rho phi) psi) ≃*
      A ⧸ Compression.kernel rho (psi.comp phi) := by
  have hle : Compression.kernel rho phi ≤ Compression.kernel rho (psi.comp phi) := by
    intro a ha
    have hh : Compression.map rho phi a = 1 := MonoidHom.mem_ker.mp ha
    change mapBase psi (Compression.map rho phi a) = 1
    rw [hh, map_one]
  exact (QuotientGroup.quotientMulEquivOfEq (kernel_map rho phi psi).symm).trans
    (QuotientGroup.quotientQuotientEquivQuotient
      (Compression.kernel rho phi) (Compression.kernel rho (psi.comp phi)) hle)

/-- The equivalence preserves the original source marking. -/
theorem quotientCompositionEquiv_mk (a : A) :
    quotientCompositionEquiv rho phi psi
      (QuotientGroup.mk'
        (Compression.kernel (Compression.quotientEmbedding rho phi) psi)
        (QuotientGroup.mk' (Compression.kernel rho phi) a)) =
      QuotientGroup.mk' (Compression.kernel rho (psi.comp phi)) a := by
  rfl

end SymmetricSubgroupAsymptotics.WreathCompressionQuotientComposition
