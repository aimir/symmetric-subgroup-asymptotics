import SymmetricSubgroupAsymptotics.CFSGSuzukiPairTorusImage

/-! Exact cardinality and faithful inner action of the original model's
diagonal torus. Its inner automorphisms preserve the actual opposite pair,
so the same q-1 factor is charged before passing to Out. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiPairRestriction
open CFSGSuzukiFieldParameters CFSGSuzukiTorus CFSGSuzukiUnipotent
open CFSGSuzukiSylowOfNormalizer CFSGSuzukiGoodSylow CFSGSuzukiBorelIntersection
open CFSGSuzukiAlignedAutomorphisms

def modelNormalizedTorusHom (m : ℕ) : (Field m)ˣ→*ActualGroup m where
  toFun c := ⟨normalizedTorusElement m c,normalizedTorusElement_mem_model m c⟩
  map_one' := Subtype.ext (normalizedTorus_one m)
  map_mul' c d := Subtype.ext (normalizedTorus_mul m c d)

theorem modelNormalizedTorusHom_injective (m : ℕ) : Function.Injective (modelNormalizedTorusHom m) := by
  intro c d he
  apply Units.ext
  have hh := congrArg (fun g : ActualGroup m => (g.val : CFSG.Models.SuzukiConstruction.Mat m) 0 0) he
  change (normalizedTorusElement m c : CFSG.Models.SuzukiConstruction.Mat m) 0 0=
    (normalizedTorusElement m d : CFSG.Models.SuzukiConstruction.Mat m) 0 0 at hh
  rw [normalizedTorusElement_coe,normalizedTorusElement_coe] at hh
  exact hh

theorem modelNormalizedTorusHom_range (m : ℕ) : (modelNormalizedTorusHom m).range=modelTorus m := by
  ext t
  constructor
  · rintro ⟨c,rfl⟩
    exact ⟨c,rfl⟩
  · rintro ⟨c,hc⟩
    exact ⟨c,Subtype.ext hc⟩

theorem modelTorus_card (m : ℕ) : Nat.card (modelTorus m)=2^(2*m+1)-1 := by
  rw [←modelNormalizedTorusHom_range]
  have he := Nat.card_congr (MonoidHom.ofInjective (modelNormalizedTorusHom_injective m)).toEquiv.symm
  rw [he,Nat.card_units,field_card]

theorem inner_modelTorus_injective (m : ℕ) :
    Function.Injective (fun t : modelTorus m => MulAut.conj (t : ActualGroup m)) := by
  intro t u he
  obtain ⟨c,hc⟩ := modelTorus_original_parameter m t.val t.property
  obtain ⟨d,hd⟩ := modelTorus_original_parameter m u.val u.property
  let v : ActualGroup m := ⟨unipotentElement m 1 0,unipotentElement_mem_model m 1 0⟩
  have hh := congrArg (fun A : MulAut (ActualGroup m) => (A v).val) he
  change t.val.val*unipotentElement m 1 0*(t.val.val)⁻¹=
    u.val.val*unipotentElement m 1 0*(u.val.val)⁻¹ at hh
  rw [hc,hd,original_torus_conjugation,original_torus_conjugation] at hh
  have hfirst := congrArg (fun g : CFSGSuzukiTorus.Ambient m =>
    (g : CFSG.Models.SuzukiConstruction.Mat m) 1 0) hh
  change (c : Field m)⁻¹*1=(d : Field m)⁻¹*1 at hfirst
  simp only [mul_one] at hfirst
  have hcd : c=d := Units.ext (inv_injective hfirst)
  apply Subtype.ext
  apply Subtype.ext
  rw [hc,hd,hcd]

theorem modelTorus_conj_mem_pair (m : ℕ) (t : modelTorus m) :
    MulAut.conj (t : ActualGroup m)∈pairStabilizer m := by
  have ht := (pair_normalizer_eq_torus m).ge t.property
  constructor
  · exact SetLike.coe_injective (Subgroup.mem_normalizer_iff_conj_image_eq.mp ht.1)
  · exact SetLike.coe_injective (Subgroup.mem_normalizer_iff_conj_image_eq.mp ht.2)

end SymmetricSubgroupAsymptotics.CFSGSuzukiPairRestriction
