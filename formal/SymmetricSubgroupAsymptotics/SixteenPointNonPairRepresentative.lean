import SymmetricSubgroupAsymptotics.Non2PreE7NonPairPhysicalFrontier
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport

/-! A literal nonbinary sixteen-point action with no physical pair system
has an actual PreE7 nonpair representative. The point relabelling is kept
explicit, so downstream original stabilizer and coinduced-frame transport
can use the same action conjugacy. This is proved type correspondence,
not an additional coverage or classification input. -/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

theorem sixteenPoint_nonpair_representative
    (T : Subgroup (Equiv.Perm (Fin 16)))
    (hnon2 : ¬ IsPGroup 2 T) (ht : MulAction.IsPretransitive T (Fin 16))
    (hpair : ¬Nonempty (BinaryPairFrame T (Fin 8))) :
    ∃ U : PreE7NonPairActionClass 16, ∃ c : Equiv.Perm (Fin 16),
      relabelSubgroup c T = preE7NonPairAction 16 U := by
  obtain ⟨i, c, hc⟩ := Non2TransitiveActionClass.representative_cover T hnon2 ht
  have hrel : relabelSubgroup c T = i.representative := by
    calc
      relabelSubgroup c T = MulAut.conj c • T := by
        change T.map c.permCongrHom.toMonoidHom = _
        rw [Subgroup.pointwise_smul_def]
        congr 1
      _ = i.representative := hc
  have hnone (n : ℕ) : ¬Nonempty (BinaryPairFrame i.representative (Fin n)) := by
    rintro ⟨F⟩
    have hback : relabelSubgroup c.symm i.representative = T := by
      rw [← hrel]
      exact relabelSubgroup_symm c T
    let F₀ : BinaryPairFrame T (Fin n) := hback ▸ F.relabelPoints c.symm
    have hn : Nat.card (Fin n) = 8 := by
      have hcard := F₀.card_points
      rw [Nat.card_fin] at hcard
      omega
    exact hpair ⟨F₀.reindex (Finite.equivFinOfCardEq hn)⟩
  let U₀ : PreE7ActionClass 16 := ⟨i, by
    intro d _
    exact hnone d.pairCount⟩
  let U : PreE7NonPairActionClass 16 := ⟨U₀, by
    intro d _
    exact hnone d.pairCount⟩
  exact ⟨U, c, hrel⟩

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
