import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Transport an intrinsic subgroup-family permutation through an
actual opposition automorphism. Its square need not be the identity. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGOpposedFamilyPermutation
variable {G I : Type*} [Group G]

private theorem map_aut_mul (P : Subgroup G) (f g : MulAut G) :
    P.map (f * g).toMonoidHom = (P.map g.toMonoidHom).map f.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem map_aut_inverse (P Q : Subgroup G) (e : MulAut G)
    (he : P.map e.toMonoidHom = Q) : Q.map (e⁻¹).toMonoidHom = P := by
  rw [←he, Subgroup.map_map]
  have hi : (e⁻¹).toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    apply MonoidHom.ext
    intro x
    exact e.symm_apply_apply x
  rw [hi, Subgroup.map_id]

theorem exists_opposite_family_permutation
    (U V : Subgroup G) (R N : I → Subgroup G) (e : MulAut G)
    (hUV : U.map e.toMonoidHom = V) (hVU : V.map e.toMonoidHom = U)
    (hNR : ∀ i, (N i).map e.toMonoidHom = R i)
    (hperm : ∀ F : MulAut G, U.map F.toMonoidHom = U → V.map F.toMonoidHom = V →
      ∃ sigma : Equiv.Perm I, ∀ i, (N i).map F.toMonoidHom = N (sigma i))
    (f : MulAut G) (hU : U.map f.toMonoidHom = U) (hV : V.map f.toMonoidHom = V) :
    ∃ sigma : Equiv.Perm I, ∀ i, (R i).map f.toMonoidHom = R (sigma i) := by
  let F : MulAut G := e⁻¹ * f * e
  have hUVinv := map_aut_inverse U V e hUV
  have hVUinv := map_aut_inverse V U e hVU
  have hU' : U.map F.toMonoidHom = U := by
    change U.map (e⁻¹ * f * e).toMonoidHom = U
    rw [map_aut_mul, map_aut_mul, hUV, hV, hUVinv]
  have hV' : V.map F.toMonoidHom = V := by
    change V.map (e⁻¹ * f * e).toMonoidHom = V
    rw [map_aut_mul, map_aut_mul, hVU, hU, hVUinv]
  obtain ⟨sigma, hsigma⟩ := hperm F hU' hV'
  have heq : f.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp F.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change f (e x) = e (e.symm (f (e x)))
    exact (e.apply_symm_apply _).symm
  refine ⟨sigma, ?_⟩
  intro i
  calc
    (R i).map f.toMonoidHom = ((N i).map e.toMonoidHom).map f.toMonoidHom :=
      congrArg (fun P : Subgroup G => P.map f.toMonoidHom) (hNR i).symm
    _ = ((N i).map F.toMonoidHom).map e.toMonoidHom := by
      rw [Subgroup.map_map, heq, ←Subgroup.map_map]
    _ = (N (sigma i)).map e.toMonoidHom :=
      congrArg (fun P : Subgroup G => P.map e.toMonoidHom) (hsigma i)
    _ = R (sigma i) := hNR (sigma i)

end SymmetricSubgroupAsymptotics.CFSGOpposedFamilyPermutation
