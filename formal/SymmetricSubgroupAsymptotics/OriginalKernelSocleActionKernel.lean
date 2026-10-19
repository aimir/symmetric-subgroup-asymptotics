import SymmetricSubgroupAsymptotics.OriginalKernelArbitraryNormalQuotient
import SymmetricSubgroupAsymptotics.AbelianNormalSocleCentralization

/-! The complete socle acts trivially on an actual abelian kernel, so its
image lies in the kernel of the original conjugation representation.
The retained version keeps the literal original normal denominator. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
variable {p : ℕ} {G B : Type} [Group G] [Group B]
  (pi : G →* B) (A : Rep.{0} (ZMod p) B) (E : OriginalKernelModuleChart pi A)

include E in
theorem socle_map_le_actionKernel :
    (finiteGroupSocle G).map pi≤A.ρ.asGroupHom.ker := by
  letI : IsMulCommutative pi.ker := IsMulCommutative.of_comm fun x y =>
    E.equiv.symm.injective (by rw [map_mul,map_mul,mul_comm])
  have hcentral := finiteGroupSocle_le_centralizer_of_abelian_normal pi.ker
  rintro b ⟨x,hx,rfl⟩
  change A.ρ.asGroupHom (pi x)=1
  apply Units.ext
  apply LinearMap.ext
  intro a
  change A.ρ (pi x) a=a
  apply Multiplicative.ofAdd.injective
  apply E.equiv.injective
  apply Subtype.ext
  rw [E.conjugate]
  let t := E.equiv (Multiplicative.ofAdd a)
  have ht : (t : G)*x=x*(t : G) :=
    Subgroup.mem_centralizer_iff.mp (hcentral hx) (t : G) t.property
  change x*(t : G)*x⁻¹=(t : G)
  rw [← ht,mul_assoc,mul_inv_cancel,mul_one]

/-- The actual G/N socle maps to the action kernel on the exact section
A/(N intersect ker pi), rather than on a replacement quotient module. -/
theorem retainedSocle_map_le_actionKernel (N : Subgroup G) [N.Normal] :
    (finiteGroupSocle (G ⧸ N)).map (base pi N)≤
      (E.sectionRepresentation pi A N).ρ.asGroupHom.ker :=
  (E.quotientChart pi A N).socle_map_le_actionKernel (base pi N)
    (E.sectionRepresentation pi A N)

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
