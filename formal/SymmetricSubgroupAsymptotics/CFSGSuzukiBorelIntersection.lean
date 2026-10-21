import SymmetricSubgroupAsymptotics.CFSGSuzukiSylowAlignment
import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentProductCoordinates
import SymmetricSubgroupAsymptotics.CFSGSuzukiFixedLine
import SymmetricSubgroupAsymptotics.CFSGSuzukiWeylTorus

/-! The intersection of the two original opposite Suzuki Borels is
exactly the original normalized diagonal torus. The proof reads two
original matrix entries, without assuming an abstract BN-pair. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiBorelIntersection
open CFSGSuzukiUnipotent CFSGSuzukiTorus CFSGSuzukiFieldParameters
open CFSGSuzukiSylowOfNormalizer CFSGSuzukiGoodSylow CFSGSuzukiSylowAlignment

theorem reversed_entry23 (m : ℕ) (g : CFSGSuzukiUnipotent.Ambient m) :
    (((weylElement m)⁻¹*g*weylElement m : CFSGSuzukiUnipotent.Ambient m) :
      CFSG.Models.SuzukiConstruction.Mat m) 2 3=
        (g : CFSG.Models.SuzukiConstruction.Mat m) 1 0 := by
  rw [weylElement_inv]
  simp [weylElement_coe,CFSG.Models.SuzukiConstruction.weyl,
    Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]

theorem reversed_entry13 (m : ℕ) (g : CFSGSuzukiUnipotent.Ambient m) :
    (((weylElement m)⁻¹*g*weylElement m : CFSGSuzukiUnipotent.Ambient m) :
      CFSG.Models.SuzukiConstruction.Mat m) 1 3=
        (g : CFSG.Models.SuzukiConstruction.Mat m) 2 0 := by
  rw [weylElement_inv]
  simp [weylElement_coe,CFSG.Models.SuzukiConstruction.weyl,
    Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]

theorem borel_inf_opposite_borel (m : ℕ) :
    borelEnvelope m ⊓ (borelEnvelope m).map (MulAut.conj (weylElement m)).toMonoidHom=
      (normalizedTorusHom m).range := by
  apply le_antisymm
  · rintro g ⟨hg,v,hv,he⟩
    have hr : (weylElement m)⁻¹*g*weylElement m∈borelEnvelope m := by
      have he' : (weylElement m)⁻¹*g*weylElement m=v := by
        rw [←he]
        change (weylElement m)⁻¹*(weylElement m*v*(weylElement m)⁻¹)*weylElement m=v
        group
      rw [he']
      exact hv
    have hz := normalizer_last_column m _ (borelEnvelope_le_normalizer m hr)
    rw [reversed_entry13,reversed_entry23] at hz
    obtain ⟨a,b,c,hg⟩ := borelEnvelope_factor m g hg
    have hc := product_firstColumn m a b c
    have ha : a=0 := (mul_eq_zero.mp (hc.2.1.symm.trans (hg ▸ hz.2.2))).resolve_right
      (Units.ne_zero c)
    have hb : b=0 := (mul_eq_zero.mp (hc.2.2.symm.trans (hg ▸ hz.2.1))).resolve_right
      (Units.ne_zero c)
    refine ⟨c,?_⟩
    rw [hg,ha,hb,unipotentElement_zero,one_mul]
    rfl
  · rintro g ⟨c,rfl⟩
    refine ⟨normalizedTorus_mem_borelEnvelope m c,?_⟩
    refine ⟨normalizedTorusElement m c⁻¹,normalizedTorus_mem_borelEnvelope m c⁻¹,?_⟩
    change weylElement m*normalizedTorusElement m c⁻¹*(weylElement m)⁻¹=
      normalizedTorusElement m c
    rw [weyl_normalizedTorus_conjugation,inv_inv]

def modelTorus (m : ℕ) : Subgroup (ActualGroup m) :=
  ((normalizedTorusHom m).range).subgroupOf (CFSG.Models.SuzukiConstruction.subgroup m)

theorem modelTorus_le_borel (m : ℕ) : modelTorus m≤modelBorel m := by
  rintro g ⟨c,he⟩
  change g.val∈borelEnvelope m
  change normalizedTorusElement m c=g.val at he
  rw [←he]
  exact normalizedTorus_mem_borelEnvelope m c

theorem modelBorel_inf_opposite_borel (m : ℕ) :
    modelBorel m ⊓ (modelBorel m).map (MulAut.conj (modelWeyl m)).toMonoidHom=
      modelTorus m := by
  apply le_antisymm
  · rintro g ⟨hg,v,hv,he⟩
    have hh : g.val∈borelEnvelope m ⊓ (borelEnvelope m).map
        (MulAut.conj (weylElement m)).toMonoidHom := by
      refine ⟨hg,v.val,hv,?_⟩
      exact congrArg (fun z : ActualGroup m => z.val) he
    rw [borel_inf_opposite_borel] at hh
    exact hh
  · intro g hg
    have hh : g.val∈borelEnvelope m ⊓ (borelEnvelope m).map
        (MulAut.conj (weylElement m)).toMonoidHom := by
      rw [borel_inf_opposite_borel]
      exact hg
    refine ⟨hh.1,?_⟩
    obtain ⟨v,hv,he⟩ := hh.2
    refine ⟨⟨v,borelEnvelope_le_model m hv⟩,hv,?_⟩
    exact Subtype.ext he

end SymmetricSubgroupAsymptotics.CFSGSuzukiBorelIntersection
