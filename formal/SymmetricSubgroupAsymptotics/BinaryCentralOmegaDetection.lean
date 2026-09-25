import SymmetricSubgroupAsymptotics.BinaryNormalCharacterCriterion

/-! The actual central involution subgroup detects every nontrivial normal
subgroup of a finite binary group. Joint kernels faithful there are faithful
on the whole original group. This uses the already proved original-group
conjugation fixed-point theorem, not an abstract quotient action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G]

def binaryCentralOmegaEmbedding : binaryCentralOmega G →* G :=
  (Subgroup.center G).subtype.comp (binaryCentralOmega G).subtype

theorem binaryCentralOmegaEmbedding_injective :
    Function.Injective (binaryCentralOmegaEmbedding (G := G)) := by
  intro x y h
  exact Subtype.ext (Subtype.ext h)

/-- Every nontrivial original normal contains an actual nonidentity
central involution; the original subgroup and original embedding remain. -/
theorem binaryCentralOmega_meets_normal [Finite G] (hG : IsPGroup 2 G)
    (N : Subgroup G) [N.Normal] (hN : N≠⊥) :
    ∃ z : binaryCentralOmega G,
      binaryCentralOmegaEmbedding z∈N ∧ z≠1 := by
  obtain ⟨z,hzN,hzc,hzo⟩ := pGroup_normal_contains_central_prime hG N hN
  have hz2 : z^2=1 := by rw [←hzo]; exact pow_orderOf_eq_one z
  let x : binaryCentralOmega G := ⟨⟨z,hzc⟩,by
    change (⟨z,hzc⟩ : Subgroup.center G)^2=1
    exact Subtype.ext hz2⟩
  refine ⟨x,hzN,?_⟩
  intro he
  have hz1 : z=1 := congrArg (binaryCentralOmegaEmbedding (G := G)) he
  rw [hz1,orderOf_one] at hzo
  exact (by decide : (1:ℕ)≠2) hzo

theorem binaryCentralOmega_normal_eq_bot [Finite G] (hG : IsPGroup 2 G)
    (N : Subgroup G) [N.Normal]
    (hfaithful : ∀ z : binaryCentralOmega G,
      binaryCentralOmegaEmbedding z∈N → z=1) : N=⊥ := by
  by_contra hn
  obtain ⟨z,hz,hne⟩ := binaryCentralOmega_meets_normal hG N hn
  exact hne (hfaithful z hz)

/-- A family of actual homomorphisms, in particular representations, is
jointly faithful once it is jointly faithful on the actual central omega.
The family is arbitrary; no independent-source assumption is present. -/
theorem binaryCentralOmega_joint_kernel_detection [Finite G]
    (hG : IsPGroup 2 G) {ι : Type*} {T : ι→Type*} [∀ i,Monoid (T i)]
    (f : ∀ i,G→*T i)
    (hfaithful : ∀ z : binaryCentralOmega G,
      (∀ i,f i (binaryCentralOmegaEmbedding z)=1) → z=1) :
    ∀ g : G, (∀ i, f i g = 1) → g = 1 := by
  let N : Subgroup G := ⨅ i,(f i).ker
  letI : N.Normal := Subgroup.normal_iInf_normal (fun i => inferInstance)
  have hN : N=⊥ := binaryCentralOmega_normal_eq_bot hG N (by
    intro z hz
    apply hfaithful z
    simpa only [N,Subgroup.mem_iInf,MonoidHom.mem_ker] using hz)
  intro g hg
  have hm : g∈N := by
    simpa only [N,Subgroup.mem_iInf,MonoidHom.mem_ker] using hg
  simpa only [hN,Subgroup.mem_bot] using hm

end SymmetricSubgroupAsymptotics
