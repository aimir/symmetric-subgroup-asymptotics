import SymmetricSubgroupAsymptotics.PrimitiveSixKernelSocleMaximum
import SymmetricSubgroupAsymptotics.CoprimeKernelQuotientSocles

/-! Exact epimorphisms feed the abelian/nonabelian socle maximum without
replacing their original source or imposing a split extension. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSixSocleMapBridge

variable {G T : Type} [Group G] [Group T]

private theorem image_commutative (f : G →* T) (L : Subgroup G)
    (hc : IsMulCommutative L) : IsMulCommutative (L.map f) := by
  apply IsMulCommutative.of_comm
  rintro ⟨x,hx⟩ ⟨y,hy⟩
  rcases hx with ⟨g,hg,rfl⟩
  rcases hy with ⟨h,hh,rfl⟩
  apply Subtype.ext
  change f g * f h=f h * f g
  rw [← map_mul,← map_mul]
  exact congrArg f (congrArg Subtype.val (hc.is_comm.comm (⟨g,hg⟩ : L) ⟨h,hh⟩))

theorem noAbelianNormal_of_equiv (e : G ≃* T)
    (htop : ∀ L : Subgroup T, L.Normal → IsMulCommutative L → L=⊥)
    (L : Subgroup G) (hL : L.Normal) (hc : IsMulCommutative L) : L=⊥ := by
  have hz := htop (L.map e.toMonoidHom) (hL.map _ e.surjective)
    (image_commutative e.toMonoidHom L hc)
  have hle := (Subgroup.map_eq_bot_iff (H := L)).mp hz
  have hk : e.toMonoidHom.ker=⊥ := (MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective
  exact le_antisymm (hle.trans hk.le) bot_le

theorem socle_le_max_of_map [Finite G] [Finite T]
    (f : G →* T) (hf : Function.Surjective f) (hc : IsMulCommutative f.ker)
    (t a : ℕ)
    (hkernel : ∀ L : Subgroup G, L.Normal → L ≤ f.ker → MarkedC4.normalGen L ≤ t)
    (hnoabelian : ∀ L : Subgroup T, L.Normal → IsMulCommutative L → L=⊥)
    (htop : ∀ L : Subgroup T, L.Normal → MarkedC4.normalGen L ≤ a) :
    SocleNormalGeneratorBound G (max t a) := by
  let e : G ⧸ f.ker ≃* T := QuotientGroup.quotientKerEquivOfSurjective f hf
  apply PrimitiveSixKernelSocleMaximum.socle_le_max f.ker hc t a hkernel
  · exact noAbelianNormal_of_equiv e hnoabelian
  · intro L hL
    letI := hL
    exact CoprimeKernelQuotientSocles.normalGen_image_bound
      e.symm.toMonoidHom e.symm.surjective a htop L

end SymmetricSubgroupAsymptotics.PrimitiveSixSocleMapBridge
