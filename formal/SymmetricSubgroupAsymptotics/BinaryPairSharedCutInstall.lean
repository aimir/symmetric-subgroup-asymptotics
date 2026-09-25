import SymmetricSubgroupAsymptotics.BinaryPairCoordinateSubgroups

/-! Shared coordinate central cuts install on the actual original group.
The actual fixed preimage gives the original Schur-capacity certificate;
no normal-lift enumeration or declared capacity is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X ι : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem kernel_mem_coordinate_fixed (C : Subrepresentation F.coordinateTopAction)
    (k : F.top.ker) :
    (k:U)∈binaryPairFixedSubgroup F.top.ker (F.coordinateSubgroup C.toSubmodule) ↔
      ∀ t : F.top.range, F.coordinateTopAction t (F.bits k)-F.bits k∈C.toSubmodule := by
  rw [binaryPairFixedSubgroup_mem_iff F.top.ker (F.coordinateSubgroup C.toSubmodule)
    (fun u : U => u) (by simp) (k:U)]
  simp only [k.property,true_and]
  have he (u : U) : (k:U)⁻¹*(u*(k:U)*u⁻¹)∈F.coordinateSubgroup C.toSubmodule ↔
      F.coordinateTopAction (F.top.rangeRestrict u) (F.bits k)-F.bits k∈C.toSubmodule := by
    change ((k⁻¹*MulAut.conjNormal u k : F.top.ker):U)∈F.coordinateSubgroup C.toSubmodule ↔ _
    rw [F.kernel_mem_coordinateSubgroup,F.bits_commutator]
  constructor
  · intro h t
    obtain ⟨u,rfl⟩ := F.top.rangeRestrict_surjective t
    exact (he u).mp (h u)
  · exact fun h u => (he u).mpr (h (F.top.rangeRestrict u))

theorem coordinate_fixed_subgroup_eq
    (A C D : Subrepresentation F.coordinateTopAction)
    (h : BinaryCoordinateCutData F.coordinateTopAction F.kernelSubrepresentation A C D) :
    binaryPairFixedSubgroup F.top.ker (F.coordinateSubgroup C.toSubmodule)=
      F.coordinateSubgroup D.toSubmodule := by
  ext x
  constructor
  · intro hx
    let k : F.top.ker := ⟨x,hx.1⟩
    apply (F.kernel_mem_coordinateSubgroup D.toSubmodule k).mpr
    apply (h.fixed_iff (F.bits k)).mpr
    exact ⟨⟨Additive.ofMul k,rfl⟩,(F.kernel_mem_coordinate_fixed C k).mp hx⟩
  · intro hx
    obtain ⟨k,hk,rfl⟩ := (F.mem_coordinateSubgroup D.toSubmodule x).mp hx
    exact (F.kernel_mem_coordinate_fixed C k).mpr ((h.fixed_iff (F.bits k)).mp hk).2

/-- This inclusion follows from complete fixedness, independently of any
rank claimed by a finite dataset. -/
theorem coordinate_cut_le_fixed (A C D : Subrepresentation F.coordinateTopAction)
    (h : BinaryCoordinateCutData F.coordinateTopAction F.kernelSubrepresentation A C D) :
    C.toSubmodule≤D.toSubmodule := by
  intro v hv
  apply (h.fixed_iff v).mpr
  exact ⟨h.cut_le_kernel hv,fun t => C.toSubmodule.sub_mem
    (C.apply_mem_toSubmodule t hv) hv⟩

private theorem binary_subspace_card_ratio
    (A C : Submodule (ZMod 2) (Fin w → ZMod 2)) (h : A≤C) :
    Nat.card C=Nat.card A*2^(Module.finrank (ZMod 2) C-Module.finrank (ZMod 2) A) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := C),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := A),Nat.card_zmod,← pow_add]
  rw [Nat.add_sub_of_le (Submodule.finrank_mono h)]

/-- A shared cut becomes a literal original kernel certificate. The cut
and fixed dimensions are derived from actual vector-space dimensions. -/
def sharedKernelCut (A C D : Subrepresentation F.coordinateTopAction)
    (h : BinaryCoordinateCutData F.coordinateTopAction F.kernelSubrepresentation A C D)
    (generators : ι → U) :
    BinaryKernelCutCertificate generators F.top (F.coordinateSubgroup A.toSubmodule) where
  cut := F.coordinateSubgroup C.toSubmodule
  cut_normal := inferInstance
  cut_le_kernel := F.coordinateSubgroup_le_kernel C.toSubmodule
  axis_le_cut := F.coordinateSubgroup_mono h.axis_le_cut
  central j x := by
    obtain ⟨k,hk,hx⟩ := (F.mem_coordinateSubgroup C.toSubmodule (x:U)).mp x.property
    change (x:U)⁻¹*(generators j*(x:U)*(generators j)⁻¹)∈F.coordinateSubgroup A.toSubmodule
    rw [← hx]
    change ((k⁻¹*MulAut.conjNormal (generators j) k:F.top.ker):U)∈F.coordinateSubgroup A.toSubmodule
    rw [F.kernel_mem_coordinateSubgroup,F.bits_commutator]
    exact h.central (F.top.rangeRestrict (generators j)) (F.bits k) hk
  cutDimension := Module.finrank (ZMod 2) C.toSubmodule-Module.finrank (ZMod 2) A.toSubmodule
  fixedDimension := Module.finrank (ZMod 2) D.toSubmodule-Module.finrank (ZMod 2) C.toSubmodule
  cut_card := by
    rw [F.coordinateSubgroup_card C.toSubmodule h.cut_le_kernel,
      F.coordinateSubgroup_card A.toSubmodule (h.axis_le_cut.trans h.cut_le_kernel)]
    exact binary_subspace_card_ratio A.toSubmodule C.toSubmodule h.axis_le_cut
  fixed_card := by
    rw [F.coordinate_fixed_subgroup_eq A C D h,
      F.coordinateSubgroup_card C.toSubmodule h.cut_le_kernel,
      F.coordinateSubgroup_card D.toSubmodule (fun v hv => ((h.fixed_iff v).mp hv).1)]
    exact binary_subspace_card_ratio C.toSubmodule D.toSubmodule (F.coordinate_cut_le_fixed A C D h)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
