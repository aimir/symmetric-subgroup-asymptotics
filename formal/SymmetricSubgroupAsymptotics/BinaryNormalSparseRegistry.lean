import SymmetricSubgroupAsymptotics.BinaryNormalParentSteps

/-! Sparse child slots retain complete central-row coverage without
duplicating a proof branch for every noncentral quotient element. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G ι I : Type*} [Group G] [Finite G]
    {generators : ι → G} (hgen : Subgroup.closure (Set.range generators)=⊤)

/-- Every listed slot is checked against its actual original child.
`covers` is a finite test on all quotient rows, not a normal-subgroup
enumeration or desired acceptance assumption. -/
structure BinaryNormalChildren (S : BinaryNormalState generators)
    (states : I → BinaryNormalState generators) where
  count : ℕ
  rows : Fin count → S.Row
  covers : ∀ z, S.centralRowTests hgen z → ∃ j, rows j=z
  child : Fin count → I
  generator_mem : ∀ i j, S.normalGenerators j ∈ (states (child i)).kernel
  lift_mem : ∀ i, S.cosets.representatives (rows i).index ∈ (states (child i)).kernel
  child_card : ∀ i, Nat.card (states (child i)).kernel=Nat.card S.kernel*2

structure BinaryNormalSparseRegistry (states : I → BinaryNormalState generators) where
  bottom : I
  bottom_kernel : (states bottom).kernel=⊥
  children : ∀ i, BinaryNormalChildren hgen (states i) states

namespace BinaryNormalSparseRegistry
variable {hgen} {states : I → BinaryNormalState generators}
    (C : BinaryNormalSparseRegistry hgen states)

include C

theorem complete (hG : IsPGroup 2 G) (N : Subgroup G) [N.Normal] :
    ∃ i, (states i).kernel=N := by
  apply pGroup_normal_registry_complete hG
    (Set.range (fun i => (states i).kernel))
    ⟨C.bottom,C.bottom_kernel⟩
    (by rintro _ ⟨i,rfl⟩; infer_instance) ?_ N
  rintro _ ⟨i,rfl⟩ _ z hzc hzo
  let S := states i
  letI := S.group hgen
  obtain ⟨r,hr⟩ := (S.quotientEquiv hgen).surjective z
  have hz : S.CentralInvolution hgen r :=
    (S.centralInvolution_iff hgen r).mpr (hr ▸ ⟨hzc,hzo⟩)
  obtain ⟨j,hj⟩ := (C.children i).covers r (S.centralInvolution_rowTests hgen r hz)
  refine ⟨(C.children i).child j,?_⟩
  rw [← hr]
  exact (S.child_eq hgen r hz (states ((C.children i).child j))
    ((C.children i).generator_mem j) (hj ▸ (C.children i).lift_mem j)
      ((C.children i).child_card j)).symm

theorem complete_map_of_equiv {H : Type*} [Group H]
    (hG : IsPGroup 2 G) (e : G ≃* H) (N : Subgroup H) [N.Normal] :
    ∃ i, (states i).kernel.map e.toMonoidHom=N := by
  obtain ⟨i,hi⟩ := C.complete hG (N.comap e.toMonoidHom)
  exact ⟨i,by rw [hi,Subgroup.map_comap_eq_self_of_surjective e.surjective]⟩

end BinaryNormalSparseRegistry
end SymmetricSubgroupAsymptotics
