import SymmetricSubgroupAsymptotics.CFSGFFourOriginalDiagonalTorus
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalProductTorusInjective
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedBruhatCover
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorus

/-! Actual exceptional fixedness of the original product torus forces
its two opposite coordinate pairs. Combined with proved original diagonal
realization, every retained fixed diagonal factor is the constructed
two-unit fixed torus word. No ordinary F4 simplicity is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedDiagonalTorus
open CFSGReeFFourFieldParameters CFSGReeFFourOriginalAutomorphism
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourParameterizedTorusCovariance
open CFSGFFourOriginalProductTorus CFSGFFourOriginalParameterizedTorus
open CFSGFFourOriginalTorusCommutation CFSGFFourOriginalProductTorusInjective
open CFSGFFourOriginalDiagonalTorus CFSGReeFFourFixedTorus CFSGReeFFourFixedBruhatCover

/-- The actual exceptional action on all four product-torus coordinates. -/
def twistTorusTuple (m : ℕ) (x : Fin 4→(Field m)ˣ) : Fin 4→(Field m)ˣ :=
  ![unitPower m 3 (x 3),unitPower m 2 (x 2),unitPower m 1 (x 1),unitPower m 0 (x 0)]

theorem ree_modelProductTorus (m : ℕ) (x : Fin 4→(Field m)ˣ) :
    reeAutomorphism m (modelProductTorusHom (Field m) x)=
      modelProductTorusHom (Field m) (twistTorusTuple m x) := by
  simp only [modelProductTorus_word,map_mul,ree_parameterTorus]
  change parameterTorus (Field m) 3 (unitPower m 0 (x 0))*
      (parameterTorus (Field m) 2 (unitPower m 1 (x 1))*
        (parameterTorus (Field m) 0 (unitPower m 3 (x 3))*
          parameterTorus (Field m) 1 (unitPower m 2 (x 2))))=
    parameterTorus (Field m) 0 (unitPower m 3 (x 3))*
      (parameterTorus (Field m) 1 (unitPower m 2 (x 2))*
        (parameterTorus (Field m) 3 (unitPower m 0 (x 0))*
          parameterTorus (Field m) 2 (unitPower m 1 (x 1))))
  have hZ := (parameterTorus_commute (Field m) 3 0 (unitPower m 0 (x 0))
    (unitPower m 3 (x 3))).mul_right
      (parameterTorus_commute (Field m) 3 1 (unitPower m 0 (x 0)) (unitPower m 2 (x 2)))
  have hW := (parameterTorus_commute (Field m) 2 0 (unitPower m 1 (x 1))
    (unitPower m 3 (x 3))).mul_right
      (parameterTorus_commute (Field m) 2 1 (unitPower m 1 (x 1)) (unitPower m 2 (x 2)))
  simpa only [mul_assoc] using (hZ.mul_left hW).eq

theorem fixed_product_torus_tuple (m : ℕ) (x : Fin 4→(Field m)ˣ)
    (hfix : reeAutomorphism m (modelProductTorusHom (Field m) x)=
      modelProductTorusHom (Field m) x) : x=fixedTorusTuple m (x 0) (x 1) := by
  have he : twistTorusTuple m x=x :=
    modelProductTorusHom_injective (Field m) ((ree_modelProductTorus m x).symm.trans hfix)
  have h2 := congrArg (fun z : Fin 4→(Field m)ˣ=>z 2) he
  have h3 := congrArg (fun z : Fin 4→(Field m)ˣ=>z 3) he
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact h2.symm
  · exact h3.symm

theorem exists_fixedDiagonal_torus (m : ℕ) (d : originalModelFixed m)
    (hdD : d∈fixedDiagonal m) : ∃a b : (Field m)ˣ,d=fixedTorus m a b := by
  obtain ⟨x,hx⟩ := exists_model_diagonal_torus (Field m) d.val hdD
  have hfix : reeAutomorphism m (modelProductTorusHom (Field m) x)=
      modelProductTorusHom (Field m) x := by
    rw [←hx]
    exact d.property
  have ht := fixed_product_torus_tuple m x hfix
  refine ⟨x 0,x 1,?_⟩
  apply Subtype.ext
  change d.val=modelProductTorusHom (Field m) (fixedTorusTuple m (x 0) (x 1))
  exact hx.trans (congrArg (modelProductTorusHom (Field m)) ht)

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedDiagonalTorus
