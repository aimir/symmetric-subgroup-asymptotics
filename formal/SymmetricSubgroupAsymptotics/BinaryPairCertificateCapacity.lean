import SymmetricSubgroupAsymptotics.BinaryPairCertificateTransport

/-! Install a finite pair certificate on its literal physical frame. The
cut dimension and fixed capacity follow from checked original subgroup
orders. The strict physical gap additionally requires the width binding. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem sectionSubgroupImage_card {p : ℕ} {K V : Type*} [Group K]
    [AddCommGroup V] [Module (ZMod p) V] (q : K→*Multiplicative V)
    (hq : Function.Surjective q) (L : Subgroup K) (hL : q.ker≤L) :
    Nat.card L=Nat.card q.ker*Nat.card (sectionSubgroupImage (p := p) q L) := by
  have he : sectionSubspacePreimage q (sectionSubgroupImage (p := p) q L)=L := by
    ext k
    exact sectionSubgroupImage_mem_iff (p := p) q L hL k
  have hc := sectionSubspacePreimage_card q hq (sectionSubgroupImage (p := p) q L)
  rwa [he] at hc

namespace BinaryPairLocalCertificate

variable {X I ι : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U) [N.Normal]
    (generators : ι→U) (hgen : Subgroup.closure (Set.range generators)=⊤)
    (C : BinaryPairLocalCertificate generators F.top N)

def kernelCut : Subgroup F.top.ker := C.cut.subgroupOf F.top.ker

omit [N.Normal] in
theorem sectionKernel_le : (F.sectionMap N).ker≤C.kernelCut F := by
  rw [F.sectionMap_ker]
  intro k hk
  exact C.intersection_le_cut ⟨k.property,hk⟩

omit [N.Normal] in
theorem original_commutators : ∀ j, ∀ k : C.kernelCut F,
    (k:F.top.ker)⁻¹*MulAut.conjNormal (generators j) (k:F.top.ker)∈
      (F.sectionMap N).ker := by
  intro j k
  rw [F.sectionMap_ker]
  exact C.central j ⟨((k:F.top.ker):U),k.property⟩

def physicalRepresentation := F.originalCutRepresentation N generators hgen
  (C.kernelCut F) (C.original_commutators F N generators)

omit [N.Normal] in
theorem cutDimension_eq [Finite X] [Finite I] :
    Module.finrank (ZMod 2) (sectionSubgroupImage (p := 2) (F.sectionMap N)
      (C.kernelCut F))=C.cutDimension := by
  letI : Finite (F.kernelSpace ⧸ F.normalSpace N) :=
    Finite.of_surjective (fun k => (F.sectionMap N k).toAdd)
      (Multiplicative.toAdd.surjective.comp (F.sectionMap_surjective N))
  have hc := sectionSubgroupImage_card (p := 2) (F.sectionMap N) (F.sectionMap_surjective N)
    (C.kernelCut F) (C.sectionKernel_le F N)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := sectionSubgroupImage (p := 2) (F.sectionMap N) (C.kernelCut F)),
    Nat.card_eq_fintype_card (α := ZMod 2),ZMod.card,F.sectionMap_ker] at hc
  have hk : Nat.card (N.subgroupOf F.top.ker)=Nat.card ↥(F.top.ker⊓N) := by
    rw [←Subgroup.inf_subgroupOf_left N F.top.ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hl : Nat.card (C.kernelCut F)=Nat.card C.cut :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe C.cut_le_kernel).toEquiv
  rw [hk,hl] at hc
  exact Nat.pow_right_injective (by decide : 1<2)
    (Nat.eq_of_mul_eq_mul_left Nat.card_pos (hc.symm.trans C.cut_card))

theorem fixed_preimage_eq : letI : C.cut.Normal := C.cut_normal
    F.originalCutFixedPreimage N generators hgen (C.kernelCut F)
      (C.original_commutators F N generators)=
    (binaryPairFixedSubgroup F.top.ker C.cut).subgroupOf F.top.ker := by
  letI : C.cut.Normal := C.cut_normal
  ext k
  rw [F.originalCutFixedPreimage_mem_iff N generators hgen (C.kernelCut F)
    (C.original_commutators F N generators) (C.sectionKernel_le F N)]
  change (∀ j, _) ↔ (k:U)∈binaryPairFixedSubgroup F.top.ker C.cut
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators hgen]
  exact (and_iff_right k.property).symm

theorem capacity_eq [Finite X] [Finite I] (hU : IsPGroup 2 U) :
    representationSchurCapacity (C.physicalRepresentation F N generators hgen)=
      (C.fixedDimension:ℝ) := by
  letI : C.cut.Normal := C.cut_normal
  apply F.originalCut_capacity_of_card N generators hgen (C.kernelCut F)
    (C.original_commutators F N generators) hU (C.sectionKernel_le F N)
  rw [C.fixed_preimage_eq F N generators hgen]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show binaryPairFixedSubgroup F.top.ker C.cut≤F.top.ker from inf_le_left)).toEquiv]
  change _=Nat.card (C.cut.subgroupOf F.top.ker)*_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe C.cut_le_kernel).toEquiv]
  exact C.fixed_card

/-- The arbitrary numerical width in a source certificate cannot be used
until it is identified with the degree of this actual physical action. -/
theorem physical_gap [Finite X] [Finite I] (hU : IsPGroup 2 U)
    (hwidth : C.width=Nat.card X) :
    (C.coverDegree:ℝ)+2*C.cutDimension+
      4*representationSchurCapacity (C.physicalRepresentation F N generators hgen)<
        Nat.card X := by
  rw [C.capacity_eq F N generators hgen hU,←hwidth]
  exact_mod_cast C.gap

end BinaryPairLocalCertificate
end SymmetricSubgroupAsymptotics
