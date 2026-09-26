import SymmetricSubgroupAsymptotics.BinaryPairCertificateCapacity

/-! A physical pair certificate retains its original permutation action,
normal subgroup, frame, generating tuple, cut and quotient cover. Its actual
representation capacity is a theorem, not an additional certificate field. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

structure BinaryPhysicalPairCertificate {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (N : Subgroup U) where
  pairCount : ℕ
  frame : BinaryPairFrame U (Fin pairCount)
  generatorCount : ℕ
  generators : Fin generatorCount → U
  generators_full : Subgroup.closure (Set.range generators)=⊤
  localCertificate : BinaryPairLocalCertificate generators frame.top N
  physical_width : localCertificate.width=Nat.card (Fin w)

namespace BinaryPhysicalPairCertificate
variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))} {N : Subgroup U} [N.Normal]
    (C : BinaryPhysicalPairCertificate U N)

def physicalCut := sectionSubgroupImage (p := 2)
  (V := C.frame.kernelSpace ⧸ C.frame.normalSpace N)
  (C.frame.sectionMap N) (C.localCertificate.kernelCut C.frame)

def physicalRepresentation := C.localCertificate.physicalRepresentation C.frame N
  C.generators C.generators_full

/-- The actual cut dimension and actual quotient capacity satisfy the
physical gap. No capacity bound is a certificate assumption. -/
theorem actual_gap (hU : IsPGroup 2 U) :
    (C.localCertificate.coverDegree:ℝ)+2*Module.finrank (ZMod 2) C.physicalCut+
      4*representationSchurCapacity C.physicalRepresentation<w := by
  rw [show Module.finrank (ZMod 2) C.physicalCut=C.localCertificate.cutDimension from
    C.localCertificate.cutDimension_eq C.frame N]
  have h := C.localCertificate.physical_gap C.frame N C.generators
    C.generators_full hU C.physical_width
  simpa only [Nat.card_fin] using h
end BinaryPhysicalPairCertificate

namespace BinaryPhysicalPairCertificate

/-- Package a checked local pair certificate with the actual physical frame
and an actual generating tuple. No new dimension or capacity premise enters. -/
def ofLocal {w k r : ℕ} {U : Subgroup (Equiv.Perm (Fin w))}
    {N : Subgroup U} (F : BinaryPairFrame U (Fin k))
    (generators : Fin r → U)
    (hgenerators : Subgroup.closure (Set.range generators)=⊤)
    (C : BinaryPairLocalCertificate generators F.top N)
    (hwidth : C.width=Nat.card (Fin w)) : BinaryPhysicalPairCertificate U N where
  pairCount := k
  frame := F
  generatorCount := r
  generators := generators
  generators_full := hgenerators
  localCertificate := C
  physical_width := hwidth

end BinaryPhysicalPairCertificate

end SymmetricSubgroupAsymptotics
