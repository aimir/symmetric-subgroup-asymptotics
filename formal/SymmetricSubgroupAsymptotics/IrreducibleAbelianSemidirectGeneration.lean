import SymmetricSubgroupAsymptotics.IrreducibleAbelianSemidirectNormalGenerators

/-! A subgroup containing the actual full complement and one nonidentity
translation contains an irreducible abelian semidirect product. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace IrreducibleAbelianSemidirect

open SemidirectProduct

variable {V R : Type} [CommGroup V] [Group R]
  (phi : R →* MulAut V)

theorem mem_of_complement_and_translation (hirr : Irreducible phi)
    (K : Subgroup (V ⋊[phi] R))
    (hcomplement : ∀ r : R, (inr r : V ⋊[phi] R) ∈ K)
    (v : V) (hv : v ≠ 1) (htranslation : (inl v : V ⋊[phi] R) ∈ K)
    (g : V ⋊[phi] R) : g ∈ K := by
  let S : Subgroup V := K.comap (inl : V →* V ⋊[phi] R)
  have hinv : ∀ r w, w ∈ S → phi r w ∈ S := by
    intro r w hw
    change (inl (phi r w) : V ⋊[phi] R) ∈ K
    rw [inl_aut]
    exact K.mul_mem (K.mul_mem (hcomplement r) hw)
      (by simpa only [map_inv] using K.inv_mem (hcomplement r))
  have hne : S ≠ ⊥ := by
    intro hb
    exact hv (Subgroup.mem_bot.mp (hb ▸ (show v ∈ S from htranslation)))
  have htop : S = ⊤ := (hirr S hinv).resolve_left hne
  have ht : (inl g.left : V ⋊[phi] R) ∈ K := by
    change g.left ∈ S
    rw [htop]
    trivial
  rw [← inl_left_mul_inr_right g]
  exact K.mul_mem ht (hcomplement g.right)

end IrreducibleAbelianSemidirect
end SymmetricSubgroupAsymptotics

end
