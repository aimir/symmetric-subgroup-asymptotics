import SymmetricSubgroupAsymptotics.TernaryFourScalarDiagonalQuotient

/-! Minimality of the two actual translation kernels in the full scalar
four-block model. Every normal translation subgroup is classified using
the already proved original A4 invariant-subspace lattice. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.TernaryFourScalarTranslationKernels

open SemidirectProduct TernaryFourScalarDiagonalQuotient
open TernaryFourAugmentationRepresentation

variable {H : Type} [Group H] (b : H →* Equiv.Perm (Fin 4))

abbrev augmentationMap := TernaryFourScalarFullProjection.toAugmentation
  (blocks b) (scalars (H := H))

def translationSpace (N : Subgroup (Model b)) : AddSubgroup FullVector where
  carrier := {v | (inl (Multiplicative.ofAdd v) : Model b) ∈ N}
  zero_mem' := by
    change (inl (Multiplicative.ofAdd (0 : FullVector)) : Model b) ∈ N
    rw [ofAdd_zero,map_one]
    exact N.one_mem
  add_mem' := by
    intro v w hv hw
    change (inl (Multiplicative.ofAdd (v+w)) : Model b) ∈ N
    rw [ofAdd_add,map_mul]
    exact N.mul_mem hv hw
  neg_mem' := by
    intro v hv
    change (inl (Multiplicative.ofAdd (-v)) : Model b) ∈ N
    rw [ofAdd_neg,map_inv]
    exact N.inv_mem hv

theorem eq_inl_of_right_one (g : Model b) (hg : g.right = 1) :
    g = inl g.left := SemidirectProduct.ext rfl hg

theorem le_of_space_le (N M : Subgroup (Model b))
    (hright : ∀ g ∈ N, g.right = 1)
    (hle : translationSpace b N ≤ translationSpace b M) : N ≤ M := by
  intro g hg
  have he := eq_inl_of_right_one b g (hright g hg)
  have hspace : g.left.toAdd ∈ translationSpace b N := by
    change (inl g.left : Model b) ∈ N
    rwa [← he]
  have hm := hle hspace
  change (inl g.left : Model b) ∈ M at hm
  rwa [← he] at hm

theorem eq_bot_of_space_bot (N : Subgroup (Model b))
    (hright : ∀ g ∈ N, g.right = 1) (hspace : translationSpace b N = ⊥) : N = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  have he := eq_inl_of_right_one b g (hright g hg)
  have hm : g.left.toAdd ∈ translationSpace b N := by
    change (inl g.left : Model b) ∈ N
    rwa [← he]
  rw [hspace,AddSubgroup.mem_bot] at hm
  apply Subgroup.mem_bot.mpr
  rw [he]
  have hl : g.left = 1 := Multiplicative.toAdd.injective hm
  rw [hl,map_one]

theorem space_invariant
    (heven : ∀ g : alternatingGroup (Fin 4), ∃ h : H, b h = g.1)
    (N : Subgroup (Model b)) (hN : N.Normal) :
    ∀ g ∈ alternatingGroup (Fin 4), ∀ v ∈ translationSpace b N,
      TernaryA4InvariantSubmodules.coordinateAction g v ∈ translationSpace b N := by
  intro g hg v hv
  obtain ⟨h,hh⟩ := heven ⟨g,hg⟩
  change b h = g at hh
  have ha : TernaryMonomialSemidirect.linearAction (blocks b) (scalars (H := H))
      (h,1) v = TernaryA4InvariantSubmodules.coordinateAction g v := by
    funext i
    change (bitScalar 1 : ZMod 3) * v (b h⁻¹ i) = v (g.symm i)
    rw [map_one,Units.val_one,one_mul,b.map_inv,hh]
    rfl
  have hc := hN.conj_mem (inl (Multiplicative.ofAdd v)) hv (inr (h,1))
  change (inl (Multiplicative.ofAdd
    (TernaryA4InvariantSubmodules.coordinateAction g v)) : Model b) ∈ N
  rw [← ha]
  have hi := inl_aut (φ := LinearSemidirectCoprimeSocleBounds.linearAction
    (TernaryMonomialSemidirect.linearAction (blocks b) (scalars (H := H))))
      (h,1) (Multiplicative.ofAdd v)
  change (inl (Multiplicative.ofAdd
    (TernaryMonomialSemidirect.linearAction (blocks b) (scalars (H := H)) (h,1) v)) :
    Model b) = inr (h,1)*inl (Multiplicative.ofAdd v)*inr (h,1)⁻¹ at hi
  rw [hi]
  simpa only [map_inv] using hc

theorem augmentationMap_kernel_membership (g : Model b) :
    g ∈ (augmentationMap b).ker ↔
      g.right = 1 ∧ ∀ i, g.left.toAdd i = g.left.toAdd 0 := by
  constructor
  · intro hg
    exact ⟨TernaryFourScalarFullProjection.kernel_right _ _ ⟨g,hg⟩,
      TernaryFourScalarFullProjection.kernel_diagonal _ _ ⟨g,hg⟩⟩
  · rintro ⟨hright,hdiag⟩
    apply MonoidHom.mem_ker.mpr
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      exact (TernaryFourScalarFullProjection.projection_eq_zero_iff g.left.toAdd).mpr hdiag
    · exact hright

theorem diagonal_kernel_space :
    translationSpace b (augmentationMap b).ker =
      TernaryA4InvariantSubmodules.diagonal.toAddSubgroup := by
  ext v
  change (inl (Multiplicative.ofAdd v) : Model b) ∈ (augmentationMap b).ker ↔ _
  rw [augmentationMap_kernel_membership]
  change (1 = (1 : H × C2) ∧ ∀ i, v i = v 0) ↔ ∀ i, v i = v 0
  exact and_iff_right rfl

theorem augmentation_kernel_space :
    translationSpace b (toDiagonal b).ker =
      TernaryA4InvariantSubmodules.augmentation.toAddSubgroup := by
  ext v
  change (inl (Multiplicative.ofAdd v) : Model b) ∈ (toDiagonal b).ker ↔ _
  rw [mem_toDiagonal_ker]
  change (1 = (1 : H × C2) ∧ ∑ i, v i = 0) ↔ ∑ i, v i = 0
  exact and_iff_right rfl

theorem augmentation_kernel_minimal
    (heven : ∀ g : alternatingGroup (Fin 4), ∃ h : H, b h = g.1) :
    IsMinimalNormalSubgroup (toDiagonal b).ker := by
  have hright (g : Model b) (hg : g ∈ (toDiagonal b).ker) : g.right = 1 :=
    ((mem_toDiagonal_ker b g).mp hg).1
  have hne : (toDiagonal b).ker ≠ ⊥ := by
    intro hb
    have hs := augmentation_kernel_space b
    have hm : encode (Pi.single 0 1) ∈ translationSpace b (toDiagonal b).ker := by
      rw [hs]
      exact encode_sum _
    change (inl (Multiplicative.ofAdd (encode (Pi.single 0 1))) : Model b) ∈
      (toDiagonal b).ker at hm
    rw [hb] at hm
    have he := congrArg (fun g : Model b => g.left.toAdd 0) (Subgroup.mem_bot.mp hm)
    exact (by decide : (1 : ZMod 3) ≠ 0) he
  refine ⟨inferInstance,hne,?_⟩
  intro N hN hNb hNA
  have hNR : ∀ g ∈ N, g.right = 1 := fun g hg => hright g (hNA hg)
  have hspace : translationSpace b N ≤ TernaryA4InvariantSubmodules.augmentation.toAddSubgroup := by
    intro v hv
    exact ((mem_toDiagonal_ker b _).mp (hNA hv)).2
  rcases TernaryA4InvariantSubmodules.additive_classification (translationSpace b N)
      (space_invariant b heven N hN) with hb | hd | ha | ht
  · exact (hNb (eq_bot_of_space_bot b N hNR hb)).elim
  · have hc : (fun _ : Fin 4 => (1 : ZMod 3)) ∈ translationSpace b N := by
      rw [hd]
      exact fun _ => rfl
    have hsum := hspace hc
    exact ((show (∑ _ : Fin 4, (1 : ZMod 3)) ≠ 0 by decide +kernel) hsum).elim
  · apply le_antisymm hNA
    apply le_of_space_le b _ _ hright
    rw [augmentation_kernel_space,ha]
  · have hc : Pi.single (0 : Fin 4) (1 : ZMod 3) ∈ translationSpace b N := by
      rw [ht]
      exact AddSubgroup.mem_top _
    have hsum := hspace hc
    exact ((show (∑ i : Fin 4, Pi.single 0 (1 : ZMod 3) i) ≠ 0 by decide +kernel) hsum).elim

theorem diagonal_kernel_minimal
    (heven : ∀ g : alternatingGroup (Fin 4), ∃ h : H, b h = g.1) :
    IsMinimalNormalSubgroup (augmentationMap b).ker := by
  have hright (g : Model b) (hg : g ∈ (augmentationMap b).ker) : g.right = 1 :=
    ((augmentationMap_kernel_membership b g).mp hg).1
  have hne : (augmentationMap b).ker ≠ ⊥ := by
    intro hb
    have hm : (inl (Multiplicative.ofAdd (fun _ : Fin 4 => (1 : ZMod 3))) : Model b) ∈
        (augmentationMap b).ker :=
      (augmentationMap_kernel_membership b _).mpr ⟨rfl,fun _ => rfl⟩
    rw [hb] at hm
    have he := congrArg (fun g : Model b => g.left.toAdd 0) (Subgroup.mem_bot.mp hm)
    exact (by decide : (1 : ZMod 3) ≠ 0) he
  refine ⟨inferInstance,hne,?_⟩
  intro N hN hNb hNB
  have hNR : ∀ g ∈ N, g.right = 1 := fun g hg => hright g (hNB hg)
  have hspace : translationSpace b N ≤ TernaryA4InvariantSubmodules.diagonal.toAddSubgroup := by
    intro v hv
    exact ((augmentationMap_kernel_membership b _).mp (hNB hv)).2
  rcases TernaryA4InvariantSubmodules.additive_classification (translationSpace b N)
      (space_invariant b heven N hN) with hb | hd | ha | ht
  · exact (hNb (eq_bot_of_space_bot b N hNR hb)).elim
  · apply le_antisymm hNB
    apply le_of_space_le b _ _ hright
    rw [diagonal_kernel_space,hd]
  · have hc : encode (Pi.single 0 1) ∈ translationSpace b N := by
      rw [ha]
      exact encode_sum _
    have he := hspace hc (1 : Fin 4)
    change (0 : ZMod 3) = 1 at he
    exact ((by decide : (0 : ZMod 3) ≠ 1) he).elim
  · have hc : Pi.single (0 : Fin 4) (1 : ZMod 3) ∈ translationSpace b N := by
      rw [ht]
      exact AddSubgroup.mem_top _
    have he := hspace hc (1 : Fin 4)
    change (0 : ZMod 3) = 1 at he
    exact ((by decide : (0 : ZMod 3) ≠ 1) he).elim

end SymmetricSubgroupAsymptotics.TernaryFourScalarTranslationKernels

end
