import SymmetricSubgroupAsymptotics.NaturalSymmetricTopOrdinaryClassBound
import SymmetricSubgroupAsymptotics.OriginalBinaryBlockSubnormalClassGap
import SymmetricSubgroupAsymptotics.OriginalTernaryBlockSubnormalClassGap
import SymmetricSubgroupAsymptotics.PermutationalWreathTransport

/-! The all-degree natural symmetric-top ordinary bound on the original block action.
Only the coordinates of the actual wreath embedding are relabelled. Its
source subgroup and projected range remain the same, and no transitivity
of the subnormal subgroup is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.OriginalNaturalSymmetricTopOrdinaryClassBound
open OriginalBlockClassBound WreathHomProjectionRange

section CoordinateTransport
variable {A C I : Type} [Group A] [Finite A] [Finite C] [Finite I]

theorem binary_class_cube_le_of_subnormal_top_range [CommGroup C]
    (hC : Nat.card C=2) (hn : 5≤Nat.card I)
    (f : A →* PermutationalWreathProduct C (Equiv.Perm I) I)
    (hf : Function.Injective f) (hR : (topProjection f).range.IsSubnormal) :
    Nat.card (ConjClasses A)^3≤5^(2*Nat.card I-1) := by
  let c : I ≃ Fin (Nat.card I) := Finite.equivFinOfCardEq rfl
  let e : Equiv.Perm I ≃* Equiv.Perm (Fin (Nat.card I)) := c.permCongrHom
  have hc : ∀ (q : Equiv.Perm I) (i : I), c (q • i)=e q • c i := by
    intro q i
    change c (q i)=c.permCongr q (c i)
    simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
  let w := PermutationalWreathProduct.transport (D := C) e c hc
  let f' := w.toMonoidHom.comp f
  have hf' : Function.Injective f' := w.injective.comp hf
  have hp : topProjection f'=e.toMonoidHom.comp (topProjection f) := by ext a; rfl
  have hR' : (topProjection f').range.IsSubnormal := by
    rw [hp,MonoidHom.range_comp]
    exact Subgroup.IsSubnormal.map e.surjective hR
  exact NaturalSymmetricTopOrdinaryClassBound.binary_class_cube_le_of_subnormal_top_range
    (Nat.card I) hn hC f' hf' hR'

theorem ternary_class_cube_le_of_subnormal_top_range [Group C]
    (horder : Nat.card C≤6) (hC : Nat.card (ConjClasses C)≤3)
    (hn : 5≤Nat.card I)
    (f : A →* PermutationalWreathProduct C (Equiv.Perm I) I)
    (hf : Function.Injective f) (hR : (topProjection f).range.IsSubnormal) :
    Nat.card (ConjClasses A)^3≤5^(3*Nat.card I-1) := by
  let c : I ≃ Fin (Nat.card I) := Finite.equivFinOfCardEq rfl
  let e : Equiv.Perm I ≃* Equiv.Perm (Fin (Nat.card I)) := c.permCongrHom
  have hc : ∀ (q : Equiv.Perm I) (i : I), c (q • i)=e q • c i := by
    intro q i
    change c (q i)=c.permCongr q (c i)
    simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
  let w := PermutationalWreathProduct.transport (D := C) e c hc
  let f' := w.toMonoidHom.comp f
  have hf' : Function.Injective f' := w.injective.comp hf
  have hp : topProjection f'=e.toMonoidHom.comp (topProjection f) := by ext a; rfl
  have hR' : (topProjection f').range.IsSubnormal := by
    rw [hp,MonoidHom.range_comp]
    exact Subgroup.IsSubnormal.map e.surjective hR
  exact NaturalSymmetricTopOrdinaryClassBound.ternary_class_cube_le_of_subnormal_top_range
    (Nat.card I) hn horder hC f' hf' hR'
end CoordinateTransport

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω] [MulAction.IsPretransitive A X]

theorem subnormal_class_cube_le_at_original_degree
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω), b (g • ω)=g • b ω)
    (x₀ : X) (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : Nat.card (originalBlockFibre b x₀)=c)
    (hn : 5≤Nat.card X)
    (hTop : (Top (A := A) (X := X)).IsSubnormal)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-1) := by
  let f := (OriginalBinaryBlockSubnormalClassGap.ambientEmbedding b hb x₀).comp H.subtype
  have hf : Function.Injective f :=
    (OriginalBinaryBlockSubnormalClassGap.ambientEmbedding_injective b hb x₀).comp
      Subtype.val_injective
  have hrange : (topProjection f).range.IsSubnormal := by
    have h := SubnormalImageOfSubnormalRange.restricted_range_isSubnormal
      (topMap (A := A) (X := X)) hTop H hH
    have he : topProjection f=(topMap (A := A) (X := X)).comp H.subtype := by ext a; rfl
    rw [he]
    exact h
  have hd : c*Nat.card X=Nat.card Ω := by
    have hh := Nat.card_congr (ActualBlockWreathEmbedding.productEquiv b hb x₀)
    rw [Nat.card_prod,hsize] at hh
    exact hh
  rcases hc with rfl|rfl
  · letI : IsMulCommutative (Equiv.Perm (originalBlockFibre b x₀)) :=
      Equiv.Perm.isMulCommutative_iff_card_le_two.mpr hsize.le
    letI : CommGroup (Equiv.Perm (originalBlockFibre b x₀)) := inferInstance
    have hC : Nat.card (Equiv.Perm (originalBlockFibre b x₀))=2 := by
      rw [Nat.card_perm,hsize]
      rfl
    have h := binary_class_cube_le_of_subnormal_top_range hC hn f hf hrange
    simpa only [hd] using h
  · let C := Equiv.Perm (originalBlockFibre b x₀)
    have horder : Nat.card C≤6 := by
      change Nat.card (Equiv.Perm (originalBlockFibre b x₀))≤6
      rw [Nat.card_perm,hsize]
      decide
    have hclass : Nat.card (ConjClasses C)≤3 := by
      have htop : Nat.card (ConjClasses (⊤ : Subgroup C))≤3 :=
        SmallPermutationClassBudgets.subgroup_class_card_le_three hsize.le ⊤
      have hle : Nat.card (ConjClasses C)≤Nat.card (ConjClasses (⊤ : Subgroup C)) :=
        Nat.card_le_card_of_surjective
          (ConjClasses.map (Subgroup.topEquiv : (⊤ : Subgroup C) ≃* C).toMonoidHom)
          (ConjClasses.map_surjective Subgroup.topEquiv.surjective)
      exact hle.trans htop
    have h := ternary_class_cube_le_of_subnormal_top_range horder hclass hn f hf hrange
    simpa only [hd] using h

theorem subnormal_class_cube_le_of_single_factor_natural_degree
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω),b (g • ω)=g • b ω)
    (x₀ : X) (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : Nat.card (originalBlockFibre b x₀)=c)
    (D : PrimitiveSocleRawStructure.NonaffineData (Top (A:=A) (X:=X)) X)
    (m : ℕ) (hm : 5 ≤ m) (e : D.Simple ≃* alternatingGroup (Fin m))
    (hk : D.factorCount=1) (hdegree : Nat.card X=m)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-1) := by
  letI : Fintype X := Fintype.ofFinite X
  letI : DecidableEq X := Classical.decEq X
  have hnatural := PrimitiveAlternatingNaturalDegreeRecognition.alternating_or_top_of_single_factor_natural_degree
    (Top (A:=A) (X:=X)) D m hm e hk hdegree
  have htop : (Top (A:=A) (X:=X)).IsSubnormal := by
    rcases hnatural with h|h
    · rw [h]; exact Subgroup.Normal.isSubnormal inferInstance
    · rw [h]; exact Subgroup.IsSubnormal.top
  exact subnormal_class_cube_le_at_original_degree b hb x₀ c hc hsize
    (by omega) htop H hH

end SymmetricSubgroupAsymptotics.OriginalNaturalSymmetricTopOrdinaryClassBound
