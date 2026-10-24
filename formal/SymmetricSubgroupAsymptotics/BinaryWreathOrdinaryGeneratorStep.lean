import SymmetricSubgroupAsymptotics.CentralBinaryCompressedKernelGenerators
import SymmetricSubgroupAsymptotics.AbelianKernelOrdinaryGeneration

/-! An actual correlated binary wreath subgroup costs at most one
half-block module charge above its actual block-top image. Only the
block labels are required to be transitive. The associated two-point
fibres may form an intransitive action; no split subgroup or whole base
is substituted for the original kernel. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryWreathOrdinaryGeneratorStep
open PermutationalWreathProduct

private def localKernelEquiv : Multiplicative (ZMod 2) ≃*
    (1 : Multiplicative (ZMod 2) →* PUnit.{1}).ker where
  toFun u := ⟨u, rfl⟩
  invFun u := u.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable {A Q I : Type} [Group A] [Finite A] [Group Q]
    [Fintype I] [Nonempty I] [MulAction Q I] [MulAction A I]
    (rho : A →* PermutationalWreathProduct (Multiplicative (ZMod 2)) Q I)

omit [Finite A] [Fintype I] [Nonempty I] [MulAction A I] in
theorem compression_kernel_eq_top_kernel :
    Compression.kernel rho (1 : Multiplicative (ZMod 2) →* PUnit.{1}) =
      (rightHom.comp rho).ker := by
  ext a
  change rho a ∈ (mapBase (1 : Multiplicative (ZMod 2) →* PUnit.{1})).ker ↔
    (rho a).right = 1
  rw [mem_mapBase_ker_iff]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, fun _ => rfl⟩

/-- The only ordinary extension step here has an actually abelian
kernel. Its normal-generator budget is therefore legitimate. -/
theorem genRank_le_top_add_half [Nontrivial I] [MulAction.IsPretransitive A I]
    (hrho : Function.Injective rho)
    (hact : ∀ (a : A) (i : I), (rho a).right • i = a • i) :
    MarkedC4.genRank A ≤ MarkedC4.genRank (rightHom.comp rho).range + Nat.card I / 2 := by
  let phi : Multiplicative (ZMod 2) →* PUnit.{1} := 1
  let e := localKernelEquiv
  let C := Compression.kernelElementaryChart (p := 2) rho phi e hrho
  have hker := compression_kernel_eq_top_kernel rho
  letI : IsMulCommutative (Compression.kernel rho phi) := IsMulCommutative.of_comm
    (fun u v => C.equiv.injective (by simp only [map_mul]; exact mul_comm _ _))
  let pi := rightHom.comp rho
  letI : IsMulCommutative pi.ker := by
    change IsMulCommutative (rightHom.comp rho).ker
    rw [← hker]
    infer_instance
  have hcentral : ∀ (d : Multiplicative (ZMod 2)) (u : phi.ker),
      MulAut.conjNormal d u = u := by
    intro d u
    apply Subtype.ext
    change d*u.val*d⁻¹ = u.val
    rw [mul_comm d u.val, mul_assoc, mul_inv_cancel, mul_one]
  have hk := CentralBinaryCompressedKernelGenerators.normalGen_le_half
    rho phi e hrho hcentral hact
  have hk' : MarkedC4.normalGen pi.ker ≤ Nat.card I / 2 := by
    change MarkedC4.normalGen (rightHom.comp rho).ker ≤ _
    rw [← hker]
    exact hk
  let piR : A →* pi.range := pi.rangeRestrict
  letI : Finite pi.range := Finite.of_surjective piR pi.rangeRestrict_surjective
  letI : IsMulCommutative piR.ker := by
    change IsMulCommutative pi.rangeRestrict.ker
    rw [MonoidHom.ker_rangeRestrict]
    infer_instance
  have hkR : MarkedC4.normalGen piR.ker ≤ Nat.card I / 2 := by
    change MarkedC4.normalGen pi.rangeRestrict.ker ≤ _
    rw [MonoidHom.ker_rangeRestrict]
    exact hk'
  exact (AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    piR pi.rangeRestrict_surjective).trans (Nat.add_le_add_left hkR _)

end SymmetricSubgroupAsymptotics.BinaryWreathOrdinaryGeneratorStep
