import SymmetricSubgroupAsymptotics.BinaryMarkedInvariantsCongr
import SymmetricSubgroupAsymptotics.BinaryRankHotDefinition

/-! Hot complete sources with an actual bounded finite top are counted by
the SAME hot kernel and finitely many original permutations. This includes
index-six S3 kernels without choosing an index-three surrogate. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
variable (T : Type) [Group T] [Finite T]

def FiniteTopKernelRankHot (a : ℝ) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) : Prop :=
  ∃ theta : J →* T, Function.Surjective theta ∧
    a*b < binaryCharacterRank theta.ker

/-- All actual coset representatives are retained; no kernel multiplicity
is divided out. -/
theorem eq_closure_kernel_section {G : Type} [Group G] (J : Subgroup G)
    (theta : J →* T) (s : T → J) (hs : ∀ t, theta (s t)=t) :
    J=Subgroup.closure ((theta.ker.map J.subtype : Set G) ∪
      Set.range (fun t => (s t : G))) := by
  apply le_antisymm
  · intro g hg
    let u : J := ⟨g,hg⟩
    let t := theta u
    have hm : (s t)⁻¹*u ∈ theta.ker := by
      rw [MonoidHom.mem_ker,map_mul,map_inv,hs]
      exact inv_mul_cancel t
    have hk : (((s t)⁻¹*u : J) : G) ∈ Subgroup.closure
        ((theta.ker.map J.subtype : Set G) ∪ Set.range (fun t => (s t : G))) :=
      Subgroup.subset_closure (Or.inl ⟨_,hm,rfl⟩)
    have ht : (s t : G) ∈ Subgroup.closure
        ((theta.ker.map J.subtype : Set G) ∪ Set.range (fun t => (s t : G))) :=
      Subgroup.subset_closure (Or.inr ⟨t,rfl⟩)
    have he : g=(s t : G)*(((s t)⁻¹*u : J) : G) := by simp [u]
    rw [he]
    exact Subgroup.mul_mem _ ht hk
  · rw [Subgroup.closure_le]
    rintro g (⟨k,_,rfl⟩ | ⟨t,rfl⟩)
    · exact k.property
    · exact (s t).property

/-- The finite top costs only a fixed factorial power in the hot count. -/
theorem hot_card_le (a : ℝ) (b : ℕ) :
    Nat.card {J : Subgroup (Equiv.Perm (Fin b)) // FiniteTopKernelRankHot T a J} ≤
      Nat.factorial b ^ Nat.card T *
        Nat.card {F : Subgroup (Equiv.Perm (Fin b)) // BinaryRankHot a F} := by
  let HJ := {J : Subgroup (Equiv.Perm (Fin b)) // FiniteTopKernelRankHot T a J}
  let HF := {F : Subgroup (Equiv.Perm (Fin b)) // BinaryRankHot a F}
  have hw : ∀ J : HJ, ∃ theta : J.val →* T, ∃ s : T → J.val,
      (∀ t, theta (s t)=t) ∧ a*b < binaryCharacterRank theta.ker := by
    intro J
    obtain ⟨theta,htheta,hhot⟩ := J.property
    choose s hs using htheta
    exact ⟨theta,s,hs,hhot⟩
  choose theta s hs hhot using hw
  let enc : HJ → HF × (T → Equiv.Perm (Fin b)) := fun J =>
    (⟨(theta J).ker.map J.val.subtype,by
      unfold BinaryRankHot
      rw [← binaryCharacterRank_congr (Subgroup.equivMapOfInjective (theta J).ker
        J.val.subtype Subtype.val_injective)]
      exact hhot J⟩,fun t => (s J t : Equiv.Perm (Fin b)))
  have hi : Function.Injective enc := by
    intro J K h
    have hk := congrArg (fun z : HF × (T → Equiv.Perm (Fin b)) => z.1.val) h
    have he := congrArg (fun z : HF × (T → Equiv.Perm (Fin b)) => z.2) h
    dsimp only [enc] at hk he
    apply Subtype.ext
    rw [eq_closure_kernel_section T J.val (theta J) (s J) (hs J),
      eq_closure_kernel_section T K.val (theta K) (s K) (hs K),hk,he]
  have h := Nat.card_le_card_of_injective enc hi
  rw [Nat.card_prod,Nat.card_fun,Nat.card_perm,Nat.card_fin] at h
  exact h.trans_eq (Nat.mul_comm _ _)
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
