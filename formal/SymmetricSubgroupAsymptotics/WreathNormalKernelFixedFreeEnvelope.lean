import SymmetricSubgroupAsymptotics.WreathNormalBaseCoordinates
import SymmetricSubgroupAsymptotics.IrreducibleNormalFixedSpace
import SymmetricSubgroupAsymptotics.PermutationalWreathLinearRepresentation

/-! Actual full component forces fixed-freeness of the coordinate module
under every nontrivial ambient-normal subgroup of the block kernel.
This is proved from the original action, not supplied as a Clifford input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open PermutationalWreathProduct WreathNormalBaseCoordinates

 theorem wreath_normal_kernel_fixed_free
    {k G D Q I V : Type} [Field k] [Group G] [Group D] [Group Q]
    [MulAction Q I] [MulAction.IsPretransitive Q I]
    [AddCommGroup V] [Module k V]
    (rho : G →* PermutationalWreathProduct D Q I)
    (hrho : Function.Injective rho)
    (htop : Function.Surjective (rightHom.comp rho))
    (hfull : Compression.FullComponent rho)
    (beta : Representation k D V) [Representation.IsIrreducible beta]
    (hfaithful : Function.Injective beta)
    (L : Subgroup G) [L.Normal] (hL : L≤(rightHom.comp rho).ker) (hne : L≠⊥)
    (v : I → V)
    (hv : ∀ l : L,(functionRepresentation beta).comp rho l.val v=v) : v=0 := by
  funext i
  let f := coordinate rho L hL i
  let Li := f.range
  letI : Li.Normal := coordinate_range_normal rho L hL hfull i
  have hLi : Li≠⊥ := all_coordinate_nontrivial rho L hL hrho htop hne i
  apply irreducible_normal_fixed_eq_zero beta hfaithful Li hLi (v i)
  intro d
  obtain ⟨l,hl⟩ := d.property
  have hh := congrFun (hv l) i
  change beta ((rho l.val).left i) (v ((rho l.val).right⁻¹ • i))=v i at hh
  rw [show (rho l.val).right=1 from hL l.property,inv_one,one_smul] at hh
  change beta d.val (v i)=v i
  rw [←hl]
  exact hh

end SymmetricSubgroupAsymptotics
