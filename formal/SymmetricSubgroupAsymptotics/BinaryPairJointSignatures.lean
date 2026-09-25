import SymmetricSubgroupAsymptotics.BinaryKernelNormalRegistry

/-! Pair cut certificates depend on the literal invariant kernel axis and
faithful top covers depend on the literal top normal. They may be checked
once and combined for every original normal with that joint signature.
The original normal, quotient, frame and physical width remain retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G I ι : Type*} [Group G]

/-- The kernel-side part of a pair certificate. `axis` is the actual
intersection with the original kernel, rather than a dimension label. -/
structure BinaryKernelCutCertificate (generators : ι → G)
    (top : G →* Equiv.Perm I) (axis : Subgroup G) where
  cut : Subgroup G
  cut_normal : cut.Normal
  cut_le_kernel : cut ≤ top.ker
  axis_le_cut : axis ≤ cut
  central : ∀ j, ∀ x : cut,
    (x:G)⁻¹*(generators j*(x:G)*(generators j)⁻¹) ∈ axis
  cutDimension : ℕ
  fixedDimension : ℕ
  cut_card : Nat.card cut = Nat.card axis*2^cutDimension
  fixed_card : letI := cut_normal
    Nat.card (binaryPairFixedSubgroup top.ker cut) = Nat.card cut*2^fixedDimension

/-- A faithful cover of the actual top quotient, retaining its exact map. -/
structure BinaryTopQuotientCover (top : G →* Equiv.Perm I)
    (T : Subgroup top.range) where
  degree : ℕ
  hom : top.range →* Equiv.Perm (Fin degree)
  kernel_eq : hom.ker = T

namespace BinaryKernelCutCertificate
variable {generators : ι → G} {top : G →* Equiv.Perm I} {axis : Subgroup G}
    (C : BinaryKernelCutCertificate generators top axis)

/-- A shared cut and a shared faithful top quotient recover a full local
certificate for each literal original normal. No splitting is assumed. -/
def install {T : Subgroup top.range} (E : BinaryTopQuotientCover top T)
    (N : Subgroup G) (hA : top.ker ⊓ N = axis)
    (hT : N.map top.rangeRestrict = T) (width : ℕ)
    (hgap : E.degree+2*C.cutDimension+4*C.fixedDimension < width) :
    BinaryPairLocalCertificate generators top N where
  cut := C.cut
  cut_normal := C.cut_normal
  cut_le_kernel := C.cut_le_kernel
  intersection_le_cut := hA.symm ▸ C.axis_le_cut
  central j x := by
    have h := C.central j x
    have hle : axis ≤ N := hA ▸ (inf_le_right : top.ker ⊓ N ≤ N)
    exact hle h
  cutDimension := C.cutDimension
  fixedDimension := C.fixedDimension
  cut_card := hA.symm ▸ C.cut_card
  fixed_card := C.fixed_card
  coverDegree := E.degree
  cover := E.hom.comp top.rangeRestrict
  cover_kernel := by
    change E.hom.ker.comap top.rangeRestrict=top.ker⊔N
    rw [E.kernel_eq,← hT,Subgroup.comap_map_eq,MonoidHom.ker_rangeRestrict,sup_comm]
  width := width
  gap := hgap

end BinaryKernelCutCertificate

namespace BinaryPairLocalCertificate
variable {generators : ι → G} {top : G →* Equiv.Perm I}
    {N₁ N₂ : Subgroup G} (C : BinaryPairLocalCertificate generators top N₁)

/-- Retargeting a certificate between original lifts preserves the cut,
cover, dimensions and width exactly. Only the equal literal joint
signature is used; no quotient action on the original kernel is invented. -/
def retarget (hA : top.ker ⊓ N₁ = top.ker ⊓ N₂)
    (hT : N₁.map top = N₂.map top) :
    BinaryPairLocalCertificate generators top N₂ where
  cut := C.cut
  cut_normal := C.cut_normal
  cut_le_kernel := C.cut_le_kernel
  intersection_le_cut := hA ▸ C.intersection_le_cut
  central j x := by
    have hx : (x:G)∈top.ker := C.cut_le_kernel x.property
    have hc : (x:G)⁻¹*(generators j*(x:G)*(generators j)⁻¹)∈top.ker := by
      change top ((x:G)⁻¹*(generators j*(x:G)*(generators j)⁻¹))=1
      have ht : top (x:G)=1 := hx
      simp only [map_mul,map_inv,ht,mul_one,inv_one,mul_inv_cancel]
    have hm : (x:G)⁻¹*(generators j*(x:G)*(generators j)⁻¹)∈top.ker⊓N₁ :=
      ⟨hc,C.central j x⟩
    rw [hA] at hm
    exact hm.2
  cutDimension := C.cutDimension
  fixedDimension := C.fixedDimension
  cut_card := hA ▸ C.cut_card
  fixed_card := C.fixed_card
  coverDegree := C.coverDegree
  cover := C.cover
  cover_kernel := C.cover_kernel.trans (binary_kernel_sup_eq_of_top_image_eq top N₁ N₂ hT)
  width := C.width
  gap := C.gap

end BinaryPairLocalCertificate
end SymmetricSubgroupAsymptotics
