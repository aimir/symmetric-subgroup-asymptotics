import SymmetricSubgroupAsymptotics.PermutationalWreathQuotient
import Mathlib.GroupTheory.PGroup

/-! A p-group compression kernel vanishes if its actual local kernel
has no normal p-subgroups. Exact-component fullness proves normality of
each literal coordinate image; faithfulness then kills the correlated
global kernel. No independent coordinate product is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.WreathCompressionNormalPTrivial
open PermutationalWreathProduct

variable {A D D' Q I : Type} [Group A] [Group D] [Group D'] [Group Q]
    [MulAction Q I] (rho : A →* PermutationalWreathProduct D Q I) (phi : D →* D')

theorem coordinate_range_eq_bot (p : ℕ) (hfull : Compression.FullComponent rho)
    (hlocal : ∀ N : Subgroup phi.ker, N.Normal → IsPGroup p N → N = ⊥)
    (hK : IsPGroup p (Compression.kernel rho phi)) (i : I) :
    (Compression.kernelCoordinate rho phi i).range = ⊥ := by
  let f := Compression.kernelCoordinate rho phi i
  have hn : f.range.Normal := Compression.kernelCoordinate_range_normal rho phi hfull i
  have hp : IsPGroup p f.range := hK.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  exact hlocal f.range hn hp

theorem kernel_eq_bot (p : ℕ) (hrho : Function.Injective rho)
    (hfull : Compression.FullComponent rho)
    (hlocal : ∀ N : Subgroup phi.ker, N.Normal → IsPGroup p N → N = ⊥)
    (hK : IsPGroup p (Compression.kernel rho phi)) :
    Compression.kernel rho phi = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro a ha
  have hu : (⟨a,ha⟩ : Compression.kernel rho phi) = 1 := by
    apply Compression.kernelCoordinate_joint_injective rho phi hrho
    funext i
    have hm : Compression.kernelCoordinate rho phi i ⟨a,ha⟩ ∈
        (Compression.kernelCoordinate rho phi i).range := ⟨⟨a,ha⟩,rfl⟩
    rw [coordinate_range_eq_bot rho phi p hfull hlocal hK i] at hm
    have heq : Compression.kernelCoordinate rho phi i ⟨a,ha⟩ = 1 := hm
    simpa only [map_one] using heq
  change a = 1
  exact congrArg Subtype.val hu

end SymmetricSubgroupAsymptotics.WreathCompressionNormalPTrivial
