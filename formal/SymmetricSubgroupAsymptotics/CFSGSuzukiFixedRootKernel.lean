import SymmetricSubgroupAsymptotics.CFSGSuzukiAlignedAutomorphisms
import SymmetricSubgroupAsymptotics.CFSGSuzukiWeylWordRigidity

/-! An actual model automorphism fixing U pointwise and whose Weyl image
differs from W by the actual pair-normalizer torus is the identity. The
Weyl parameter is killed by the original constant word, and U/W generate
the original model. No simplicity or abstract model identification occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiFixedRootKernel
open CFSGSuzukiFieldParameters CFSGSuzukiTorus CFSGSuzukiUnipotent CFSGSuzukiBruhat
open CFSGSuzukiSylowOfNormalizer CFSGSuzukiGoodSylow CFSGSuzukiBorelIntersection

theorem eq_one_of_fixed_unipotent_and_weyl_coset (m : ℕ)
    (f : MulAut (ActualGroup m))
    (hfix : ∀ u : modelUnipotent m,f u.val=u.val)
    (hY : f (modelWeyl m)*(modelWeyl m)⁻¹∈modelTorus m) : f=1 := by
  let u (a b : Field m) : ActualGroup m :=
    ⟨unipotentElement m a b,unipotentElement_mem_model m a b⟩
  have hfu : ∀ a b : Field m,f (u a b)=u a b := by
    intro a b
    exact hfix ⟨u a b,⟨a,b,rfl⟩⟩
  have hword : modelWeyl m=u 0 1*(modelWeyl m*u 1 0*modelWeyl m)*u 1 1 :=
    Subtype.ext (weylElement_word m)
  have hwordf := congrArg f hword
  simp only [map_mul,hfu] at hwordf
  obtain ⟨c,hc⟩ := hY
  have hfc : (f (modelWeyl m)).val=normalizedTorusElement m c*weylElement m := by
    have hc' : normalizedTorusElement m c=(f (modelWeyl m)).val*(weylElement m)⁻¹ := hc
    calc
      (f (modelWeyl m)).val=((f (modelWeyl m)).val*(weylElement m)⁻¹)*weylElement m := by group
      _=normalizedTorusElement m c*weylElement m := by rw [←hc']
  have hmove : normalizedTorusElement m c*weylElement m=
      weylElement m*normalizedTorusElement m c⁻¹ := by
    calc
      _=(weylElement m*normalizedTorusElement m c⁻¹*(weylElement m)⁻¹)*weylElement m := by
        rw [weyl_normalizedTorus_conjugation,inv_inv]
      _=weylElement m*normalizedTorusElement m c⁻¹ := by group
  rw [hmove] at hfc
  have hwinv : (modelWeyl m)⁻¹=modelWeyl m := Subtype.ext (weylElement_inv m)
  have hyinv : ((f (modelWeyl m)).val)⁻¹=(f (modelWeyl m)).val := by
    have hh : (f (modelWeyl m))⁻¹=f (modelWeyl m) := by rw [←map_inv,hwinv]
    exact congrArg (fun g : ActualGroup m => g.val) hh
  have he := congrArg (fun g : ActualGroup m => g.val) hwordf
  change (f (modelWeyl m)).val=unipotentElement m 0 1*
    ((f (modelWeyl m)).val*unipotentElement m 1 0*(f (modelWeyl m)).val)*unipotentElement m 1 1 at he
  have he' : weylElement m*normalizedTorusElement m c⁻¹=unipotentElement m 0 1*
      ((weylElement m*normalizedTorusElement m c⁻¹)*unipotentElement m 1 0*
        (weylElement m*normalizedTorusElement m c⁻¹)⁻¹)*unipotentElement m 1 1 := by
    rw [←hfc,hyinv]
    exact he
  have hc1 : c⁻¹=1 := weyl_torus_word_rigidity m c⁻¹ he'
  have hfw : f (modelWeyl m)=modelWeyl m := by
    apply Subtype.ext
    rw [hfc,hc1]
    have hn : normalizedTorusElement m 1=1 := by
      apply Units.ext
      rw [normalizedTorusElement_coe]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diagonalTorus]
    rw [hn,mul_one]
    rfl
  let K := f.toMonoidHom.eqLocus (MonoidHom.id (ActualGroup m))
  let ι := (CFSG.Models.SuzukiConstruction.subgroup m).subtype
  have hU : unipotentSubgroup m≤K.map ι := by
    intro g hg
    let v : ActualGroup m := ⟨g,unipotentSubgroup_le_model m hg⟩
    refine ⟨v,?_,rfl⟩
    exact hfix ⟨v,hg⟩
  have hW : weylElement m∈K.map ι := ⟨modelWeyl m,hfw,rfl⟩
  have hle := model_le_of_unipotent_weyl m (K.map ι) hU hW
  apply MulEquiv.ext
  intro g
  obtain ⟨v,hv,hvg⟩ := hle g.property
  have heq : v=g := Subtype.ext hvg
  rw [←heq]
  exact hv

end SymmetricSubgroupAsymptotics.CFSGSuzukiFixedRootKernel
