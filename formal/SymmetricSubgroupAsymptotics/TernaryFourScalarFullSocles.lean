import SymmetricSubgroupAsymptotics.TernaryFourScalarTranslationKernels
import SymmetricSubgroupAsymptotics.TernaryFourBlockPermutationGenerators

/-! Full scalar four-block quotient socles from two actual smaller maps.
The scalar-one subgroup acts fully on augmentation and centralizes the
diagonal line. The augmentation quotient has a faithful irreducible
translation core, so the intrinsic separated-axis theorem applies. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics.TernaryFourScalarFullSocles

open SemidirectProduct TernaryFourScalarDiagonalQuotient
open TernaryFourScalarTranslationKernels TernaryFourAugmentationRepresentation

variable {H : Type} [Group H] (b : H →* Equiv.Perm (Fin 4))

def signProjection : Model b →* C2 :=
  (MonoidHom.snd H C2).comp rightHom

abbrev scalarOne := (signProjection b).ker

theorem separating (hb : Function.Injective b) :
    Function.Injective (fun g : H × C2 => (scalars g,blocks b g)) := by
  intro g h he
  apply Prod.ext
  · apply hb
    exact congrArg (fun z : (ZMod 3)ˣ × Equiv.Perm (Fin 4) => z.2) he
  · have hi : Function.Injective bitScalar := by decide +kernel
    apply hi
    exact congrArg (fun z : (ZMod 3)ˣ × Equiv.Perm (Fin 4) => z.1) he

theorem even_lifts
    (heven : ∀ g : alternatingGroup (Fin 4), ∃ h : H, b h = g.1) :
    ∀ g : alternatingGroup (Fin 4), ∃ r : H × C2,
      blocks b r = g.1 ∧ scalars r = 1 := by
  intro g
  obtain ⟨h,hh⟩ := heven g
  exact ⟨(h,1),hh,map_one bitScalar⟩

theorem irreducible
    (heven : ∀ g : alternatingGroup (Fin 4), ∃ h : H, b h = g.1) :
    AffineModel.Irreducible (TernaryFourScalarAugmentation.linearGroup (blocks b) scalars) :=
  TernaryFourScalarAugmentation.irreducible_of_even_lifts _ _ (even_lifts b heven)

theorem augmentation_commutator_full
    (heven : ∀ g : alternatingGroup (Fin 4), ∃ h : H, b h = g.1) :
    ⁅scalarOne b,(toDiagonal b).ker⁆ = (toDiagonal b).ker := by
  apply (augmentation_kernel_minimal b heven).2.2 _ inferInstance _
    (Subgroup.commutator_le_right _ _)
  intro hzero
  obtain ⟨h,hh⟩ := heven
    ⟨TernaryFourBlockPermutationGenerators.a,TernaryFourBlockPermutationGenerators.a_even⟩
  change b h = TernaryFourBlockPermutationGenerators.a at hh
  let v : FullVector := encode (Pi.single 0 1)
  let c : Model b := inr (h,1)
  let t : Model b := inl (Multiplicative.ofAdd v)
  have hc : c ∈ scalarOne b := rfl
  have ht : t ∈ (toDiagonal b).ker :=
    (mem_toDiagonal_ker b t).mpr ⟨rfl,encode_sum _⟩
  have hm := Subgroup.commutator_mem_commutator hc ht
  rw [hzero] at hm
  have hcomm := commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hm)
  have he := congrArg (fun g : Model b => g.left.toAdd) hcomm
  change 0 + TernaryMonomialSemidirect.linearAction (blocks b) scalars (h,1) v =
    v + TernaryMonomialSemidirect.linearAction (blocks b) scalars 1 0 at he
  simp only [zero_add,map_zero,add_zero] at he
  have hi := congrFun he 0
  change (bitScalar 1 : ZMod 3) * v (b h⁻¹ 0) = v 0 at hi
  rw [map_one,Units.val_one,one_mul,b.map_inv,hh] at hi
  exact (show v (TernaryFourBlockPermutationGenerators.a.symm 0) ≠ v 0 by
    decide +kernel) hi

theorem diagonal_centralizes_scalarOne :
    (augmentationMap b).ker ≤ Subgroup.centralizer (scalarOne b : Set (Model b)) := by
  intro z hz
  obtain ⟨hzright,hzdiag⟩ := (augmentationMap_kernel_membership b z).mp hz
  apply Subgroup.mem_centralizer_iff.mpr
  intro g hg
  have hgsign : g.right.2 = 1 := MonoidHom.mem_ker.mp hg
  have hact : TernaryMonomialSemidirect.linearAction (blocks b) scalars
      g.right z.left.toAdd = z.left.toAdd := by
    funext i
    change (bitScalar g.right.2 : ZMod 3) * z.left.toAdd (b g.right.1⁻¹ i) = z.left.toAdd i
    rw [hgsign,map_one,Units.val_one,one_mul]
    exact (hzdiag _).trans (hzdiag i).symm
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    change g.left.toAdd + TernaryMonomialSemidirect.linearAction (blocks b) scalars
        g.right z.left.toAdd =
      z.left.toAdd + TernaryMonomialSemidirect.linearAction (blocks b) scalars
        z.right g.left.toAdd
    rw [hact,hzright,map_one]
    exact add_comm _ _
  · change g.right*z.right = z.right*g.right
    simp only [hzright,mul_one,one_mul]

theorem augmentation_image_cover (hb : Function.Injective b)
    (heven : ∀ g : alternatingGroup (Fin 4), ∃ h : H, b h = g.1)
    (N : Subgroup (TernaryFourScalarAugmentation.Model (blocks b) scalars))
    (hN : N.Normal) (hNb : N ≠ ⊥) :
    (toDiagonal b).ker.map (augmentationMap b) ≤ N := by
  let R := TernaryFourScalarAugmentation.linearGroup (blocks b) scalars
  let e := TernaryFourScalarAugmentation.affineEquiv (blocks b) scalars (separating b hb)
  have hM : (N.map e.toMonoidHom).Normal := hN.map e.toMonoidHom e.surjective
  letI := hM
  have hMb : N.map e.toMonoidHom ≠ ⊥ := by
    intro h
    apply hNb
    apply le_antisymm _ bot_le
    intro n hn
    have hm : e n ∈ N.map e.toMonoidHom := ⟨n,hn,rfl⟩
    rw [h] at hm
    apply Subgroup.mem_bot.mpr
    apply e.injective
    exact (Subgroup.mem_bot.mp hm).trans e.map_one.symm
  have hV := AffineModel.Vsub_le_normal (irreducible b heven) (N.map e.toMonoidHom) hMb
  rintro _ ⟨g,hg,rfl⟩
  have hright := ((mem_toDiagonal_ker b g).mp hg).1
  have hv : e (augmentationMap b g) ∈ AffineModel.Vsub R := by
    apply (AffineModel.mem_Vsub R _).mpr
    change TernaryFourScalarAugmentation.complementEquiv (blocks b) scalars
      (separating b hb) g.right = 1
    rw [hright,map_one]
  obtain ⟨n,hn,he⟩ := hV hv
  have hng : n = augmentationMap b g := e.injective he
  rwa [← hng]

theorem socle_of_surjective [Finite H]
    (hb : Function.Injective b)
    (heven : ∀ g : alternatingGroup (Fin 4), ∃ h : H, b h = g.1)
    {t : ℕ} (ht : 1 ≤ t)
    (hcomplement : ∀ N : Subgroup (H × C2), ∀ _ : N.Normal,
      SocleNormalGeneratorBound ((H × C2) ⧸ N) t)
    (hdiagonal : ∀ N : Subgroup (H × D3), ∀ _ : N.Normal,
      SocleNormalGeneratorBound ((H × D3) ⧸ N) t)
    {X : Type} [Group X] (rho : Model b →* X) (hrho : Function.Surjective rho) :
    SocleNormalGeneratorBound X t := by
  have hq := TernaryFourScalarFullProjection.toAugmentation_surjective
    (blocks b) (scalars (H := H))
  have haxes : ∀ N : Subgroup (Model b), N.Normal →
      (toDiagonal b).ker ≤ N ∨ N ≤ (augmentationMap b).ker :=
    SeparatedNormalAxesQuotientSocles.normal_contains_or_le_kernel
      (augmentationMap b) hq (scalarOne b) (toDiagonal b).ker
      (augmentation_commutator_full b heven) (diagonal_centralizes_scalarOne b)
      (augmentation_image_cover b hb heven)
  have hsep : NoCommonNormalQuotient (toDiagonal b).ker (augmentationMap b).ker :=
    noCommonNormalQuotient_of_commutator_full_central (scalarOne b) _ _
      (augmentation_commutator_full b heven) (diagonal_centralizes_scalarOne b)
  apply SeparatedNormalAxesQuotientSocles.socle_of_surjective
    (toDiagonal b) (toDiagonal_surjective b) (augmentationMap b) hq
    (augmentation_kernel_minimal b heven) (diagonal_kernel_minimal b heven)
    haxes hsep ht hdiagonal _ rho hrho
  intro N hN
  letI := hN
  apply TernaryFourScalarAugmentation.socle_of_surjective (blocks b) scalars
    (separating b hb) (irreducible b heven) (Pi.single 0 1) _ ht hcomplement
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  intro hv
  have he := congrFun hv 0
  exact (by decide : (1 : ZMod 3) ≠ 0) he

end SymmetricSubgroupAsymptotics.TernaryFourScalarFullSocles

end
