import SymmetricSubgroupAsymptotics.Row67OriginalKernelChart
import SymmetricSubgroupAsymptotics.BinaryThreeQuartetCornerUniform
import SymmetricSubgroupAsymptotics.RepresentationOperatorContainmentUniform
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.Row67OriginalNaturalThree
open Row67OriginalQuartetFrame
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
abbrev Bit := ZMod 2
private theorem bit_two : (2 : Bit)=0 := by decide +kernel
private theorem bit_three : (3 : Bit)=1 := by decide +kernel
private theorem bit_four : (4 : Bit)=0 := by decide +kernel
abbrev BlockSpace := Fin 3 → Fin 4 → Bit
abbrev Corner := BinaryThreeQuartetCornerUniform.Space
private def pointCoordinates : (Fin 12 → Bit) ≃ₗ[Bit] BlockSpace where
  toFun f i j := f (points (i,j))
  invFun f x := f (points.symm x).1 (points.symm x).2
  left_inv f := by funext x; exact congrArg f (points.apply_symm_apply x)
  right_inv f := by funext i j; change f (points.symm (points (i,j))).1 (points.symm (points (i,j))).2=f i j; rw [points.symm_apply_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private def split : BlockSpace ≃ₗ[Bit] Corner where
  toFun v := (v 0+v 1+v 2,![v 0+(v 0+v 1+v 2),v 1+(v 0+v 1+v 2)])
  invFun x := ![x.1+x.2 0,x.1+x.2 1,x.1+x.2 0+x.2 1]
  left_inv v := by funext i j; fin_cases i <;> simp <;> ring_nf <;> simp only [bit_two,bit_three,bit_four,mul_zero,mul_one,zero_add,add_zero]
  right_inv x := by
    apply Prod.ext
    · funext j; simp; ring_nf; simp only [bit_two,bit_three,mul_zero,mul_one,add_zero]
    · funext i j; fin_cases i <;> simp <;> ring_nf <;> simp only [bit_two,bit_three,bit_four,mul_zero,mul_one,zero_add,add_zero]
  map_add' v w := by
    apply Prod.ext
    · funext j; simp; abel
    · funext i j; fin_cases i <;> simp <;> abel
  map_smul' z v := by
    apply Prod.ext
    · funext j; simp
    · funext i j; fin_cases i <;> simp
 def flat : (Fin 12 → Bit) ≃ₗ[Bit] Corner := pointCoordinates.trans split
private def natural := permutationFunctionRepresentation Bit Row67Top (Fin 12)
private def transformed : Representation Bit Row67Top Corner := flat.conjRingEquiv.toMonoidHom.comp natural
private def pointAction (g : Row67Top) (v : Corner) : Corner :=
  flat (fun x => flat.symm v ((g⁻¹ : Row67Top).val x))
private theorem transformed_apply (g : Row67Top) (v : Corner) :
    transformed g v=pointAction g v := rfl
private theorem corner_apply (h : BinaryThreeQuartetCornerUniform.H) (v : Corner) :
    BinaryThreeQuartetCornerUniform.rho h v=
      ((if h.1=1 then v.1 else v.1+BinaryFourSumOperatorUniform.operator v.1),
        BinarySymmetricThreeFourColumnUniform.operator h.2 v.2) := by
  have hb : h.1=1 ∨ h.1=(Multiplicative.ofAdd 1 : BinaryFourSumCornerRepresentation.Binary) := by
    have hall : ∀ b : BinaryFourSumCornerRepresentation.Binary,
        b=1 ∨ b=Multiplicative.ofAdd 1 := by decide +kernel
    exact hall h.1
  apply Prod.ext
  · change BinaryFourSumCornerRepresentation.rho h.1 v.1=
      (if h.1=1 then v.1 else v.1+BinaryFourSumOperatorUniform.operator v.1)
    rcases hb with hb | hb
    · simp only [hb]
      rfl
    · rw [hb]
      simp only [show (Multiplicative.ofAdd 1 : BinaryFourSumCornerRepresentation.Binary)≠1 by decide +kernel,if_false]
      rfl
  · rfl
private def cubicAverage : Bit[Row67Top] :=
  1+MonoidAlgebra.single (original 2) 1+(MonoidAlgebra.single (original 2) 1)^2
private def independentTranslation : Row67Top :=
  (Row67OriginalKernelChart.kernelMap (Multiplicative.ofAdd ![![1,0],![0,1]])).val
private def sumOperator : Bit[Row67Top] :=
  cubicAverage*MonoidAlgebra.single independentTranslation 1*cubicAverage+cubicAverage
private def actualOperator (h : BinaryThreeQuartetCornerUniform.H) : Bit[Row67Top] :=
  MonoidAlgebra.single (Row67OriginalKernelCertificate.liftSection h.2) 1*
    (if h.1=1 then 1 else 1+sumOperator)
private def evaluatedAverage : Module.End Bit Corner :=
  1+transformed (original 2)+(transformed (original 2))^2
private def evaluatedOperator (h : BinaryThreeQuartetCornerUniform.H) : Module.End Bit Corner :=
  transformed (Row67OriginalKernelCertificate.liftSection h.2)*
    (if h.1=1 then 1 else 1+
      (evaluatedAverage*transformed independentTranslation*evaluatedAverage+evaluatedAverage))
private def averageAction (v : Corner) : Corner :=
  v+transformed (original 2) v+transformed (original 2) (transformed (original 2) v)
set_option maxHeartbeats 1000000 in
private theorem evaluatedOperator_apply (h : BinaryThreeQuartetCornerUniform.H) (v : Corner) :
    evaluatedOperator h v=transformed (Row67OriginalKernelCertificate.liftSection h.2)
      (if h.1=1 then v else v+
        (averageAction (transformed independentTranslation (averageAction v))+averageAction v)) := by
  have ha (w : Corner) : evaluatedAverage w=averageAction w := rfl
  unfold evaluatedOperator
  rw [Module.End.mul_apply]
  split_ifs <;>
    simp only [Module.End.one_apply,Module.End.mul_apply,LinearMap.add_apply,ha]
private theorem actualOperator_evaluation (h : BinaryThreeQuartetCornerUniform.H) :
    transformed.asAlgebraHom (actualOperator h)=evaluatedOperator h := by
  unfold actualOperator evaluatedOperator
  split_ifs <;> simp [sumOperator,cubicAverage,evaluatedAverage,map_add,map_mul,map_pow]
private def plainCorner (h : BinaryThreeQuartetCornerUniform.H) (v : Corner) : Corner :=
  ((if h.1=1 then v.1 else v.1+BinaryFourSumOperatorUniform.operator v.1),
    BinarySymmetricThreeFourColumnUniform.operator h.2 v.2)
private def plainAverage (v : Corner) : Corner :=
  v+pointAction (original 2) v+pointAction (original 2) (pointAction (original 2) v)
private def plainOperator (h : BinaryThreeQuartetCornerUniform.H) (v : Corner) : Corner :=
  pointAction (Row67OriginalKernelCertificate.liftSection h.2)
    (if h.1=1 then v else v+
      (plainAverage (pointAction independentTranslation (plainAverage v))+plainAverage v))
private def blockAction (f : Fin 3 × Fin 4 → Fin 3 × Fin 4) (v : Corner) : Corner :=
  split (fun i j => split.symm v (f (i,j)).1 (f (i,j)).2)
private theorem pointAction_block (g : Row67Top) (v : Corner) :
    pointAction g v=blockAction (fun x => points.symm ((g⁻¹).val (points x))) v := rfl
private def blockPermutation (p : Equiv.Perm (Fin 3)) (x : Fin 3 × Fin 4) := (p⁻¹ x.1,x.2)
private def localTranslation (x : Fin 3 × Fin 4) : Fin 3 × Fin 4 :=
  (x.1,(![![1,0,3,2],![2,3,0,1],![3,2,1,0]] : Fin 3 → Fin 4 → Fin 4) x.1 x.2)
private theorem section_coordinates : ∀ p : Equiv.Perm (Fin 3),
    (fun x => points.symm (((Row67OriginalKernelCertificate.liftSection p)⁻¹).val (points x)))=
      blockPermutation p := by decide +kernel
private theorem cycle_coordinates :
    (fun x => points.symm (((original 2)⁻¹).val (points x)))=blockPermutation (finRotate 3) := by
  decide +kernel
private theorem translation_coordinates :
    (fun x => points.symm ((independentTranslation⁻¹).val (points x)))=localTranslation := by
  decide +kernel
private theorem section_action (p : Equiv.Perm (Fin 3)) (v : Corner) :
    pointAction (Row67OriginalKernelCertificate.liftSection p) v=blockAction (blockPermutation p) v := by
  rw [pointAction_block,section_coordinates]
private theorem cycle_action (v : Corner) :
    pointAction (original 2) v=blockAction (blockPermutation (finRotate 3)) v := by
  rw [pointAction_block,cycle_coordinates]
private theorem translation_action (v : Corner) :
    pointAction independentTranslation v=blockAction localTranslation v := by
  rw [pointAction_block,translation_coordinates]
private def compactAverage (v : Corner) : Corner :=
  v+blockAction (blockPermutation (finRotate 3)) v+
    blockAction (blockPermutation (finRotate 3)) (blockAction (blockPermutation (finRotate 3)) v)
private def compactOperator (h : BinaryThreeQuartetCornerUniform.H) (v : Corner) : Corner :=
  blockAction (blockPermutation h.2)
    (if h.1=1 then v else v+
      (compactAverage (blockAction localTranslation (compactAverage v))+compactAverage v))
set_option backward.isDefEq.respectTransparency true in
private theorem plain_compact (h : BinaryThreeQuartetCornerUniform.H) (v : Corner) :
    plainOperator h v=compactOperator h v := by
  have ha (w : Corner) : plainAverage w=compactAverage w := by
    unfold plainAverage compactAverage
    rw [cycle_action,cycle_action]
  have ht : plainAverage (pointAction independentTranslation (plainAverage v))=
      compactAverage (blockAction localTranslation (compactAverage v)) := by
    rw [ha,translation_action,ha]
  unfold plainOperator compactOperator
  rw [ht,ha]
  exact section_action h.2 _
private def scalarSection (p : Equiv.Perm (Fin 3)) (z a b : Bit) : Bit × (Fin 2 → Bit) :=
  let t := fun i => (![z+a,z+b,z+a+b] : Fin 3 → Bit) (p⁻¹ i)
  let s := t 0+t 1+t 2
  (s,![t 0+s,t 1+s])
private theorem scalar_section : ∀ (p : Equiv.Perm (Fin 3)) (z a b : Bit),
    scalarSection p z a b=
      (z,fun i : Fin 2 => (![a,b,-a-b] : Fin 3 → Bit) (p⁻¹ i.castSucc)) := by
  decide +kernel
private def scalarSplit (t : Fin 3 → Bit) : Bit × (Fin 2 → Bit) :=
  (t 0+t 1+t 2,![t 0+(t 0+t 1+t 2),t 1+(t 0+t 1+t 2)])
private theorem split_column (w : BlockSpace) (j : Fin 4) :
    ((split w).1 j,fun i => (split w).2 i j)=scalarSplit (fun k => w k j) := by
  apply Prod.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
private theorem scalarSection_eq (p : Equiv.Perm (Fin 3)) (z a b : Bit) :
    scalarSection p z a b=scalarSplit
      (fun k => (![z+a,z+b,z+a+b] : Fin 3 → Bit) (p⁻¹ k)) := rfl
private theorem inverse_column (v : Corner) (k : Fin 3) (j : Fin 4) :
    split.symm v k j=(![v.1 j+v.2 0 j,v.1 j+v.2 1 j,v.1 j+v.2 0 j+v.2 1 j] : Fin 3 → Bit) k := by
  fin_cases k <;> rfl
private theorem active_column (p : Equiv.Perm (Fin 3)) (v : Fin 2 → Fin 4 → Bit)
    (i : Fin 2) (j : Fin 4) :
    BinarySymmetricThreeFourColumnUniform.operator p v i j=
      (![v 0 j,v 1 j,-v 0 j-v 1 j] : Fin 3 → Bit) (p⁻¹ i.castSucc) := by
  change BinarySymmetricThreeFourColumnUniform.full v (p⁻¹ i.castSucc) j=_
  generalize p⁻¹ i.castSucc=k
  fin_cases k <;> rfl
private theorem block_section (p : Equiv.Perm (Fin 3)) (v : Corner) :
    blockAction (blockPermutation p) v=
      (v.1,BinarySymmetricThreeFourColumnUniform.operator p v.2) := by
  have hc (j : Fin 4) :
      ((blockAction (blockPermutation p) v).1 j,fun i => (blockAction (blockPermutation p) v).2 i j)=
        (v.1 j,fun i => BinarySymmetricThreeFourColumnUniform.operator p v.2 i j) := by
    calc
      _ = scalarSplit (fun k => split.symm v (p⁻¹ k) j) :=
        split_column (fun k t => split.symm v (p⁻¹ k) t) j
      _ = scalarSection p (v.1 j) (v.2 0 j) (v.2 1 j) := by
        rw [scalarSection_eq]
        exact congrArg scalarSplit (funext (fun k => inverse_column v (p⁻¹ k) j))
      _ = _ := by simpa only [active_column] using scalar_section p (v.1 j) (v.2 0 j) (v.2 1 j)
  apply Prod.ext
  · funext j
    exact congrArg Prod.fst (hc j)
  · funext i j
    exact congrArg (fun x : Bit × (Fin 2 → Bit) => x.2 i) (hc j)
private theorem compactAverage_eq (v : Corner) : compactAverage v=(v.1,0) := by
  unfold compactAverage
  rw [block_section,block_section]
  apply Prod.ext
  · funext j
    change v.1 j+v.1 j+v.1 j=v.1 j
    have h : ∀ z : Bit,z+z+z=z := by decide +kernel
    exact h _
  · funext i j
    fin_cases i
    · change v.2 0 j+(-v.2 0 j-v.2 1 j)+(-(-v.2 0 j-v.2 1 j)-v.2 0 j)=0
      abel
    · change v.2 1 j+v.2 0 j+(-v.2 0 j-v.2 1 j)=0
      abel
private theorem translation_average (z : BinaryFourSumOperatorUniform.Space) :
    compactAverage (blockAction localTranslation (z,0))=
      (z+BinaryFourSumOperatorUniform.operator z,0) := by
  rw [compactAverage_eq]
  apply Prod.ext
  · funext j
    fin_cases j <;>
      simp [blockAction,localTranslation,split,BinaryFourSumOperatorUniform.operator,Fin.sum_univ_succ] <;>
      ring_nf <;> (try simp only [bit_two,mul_zero,add_zero])
  · rfl
private theorem compact_operator (h : BinaryThreeQuartetCornerUniform.H) (v : Corner) :
    plainCorner h v=compactOperator h v := by
  have ht : compactAverage (blockAction localTranslation (compactAverage v))=
      (v.1+BinaryFourSumOperatorUniform.operator v.1,0) := by
    rw [compactAverage_eq v]
    exact translation_average v.1
  unfold compactOperator
  rw [ht,compactAverage_eq v]
  rw [block_section]
  by_cases hb : h.1=1
  · simp [hb,plainCorner]
  · simp [hb,plainCorner]
    funext j
    change BinaryFourSumOperatorUniform.operator v.1 j=
      v.1 j+BinaryFourSumOperatorUniform.operator v.1 j+v.1 j
    ring_nf
    simp only [bit_two,mul_zero,zero_add]
set_option backward.isDefEq.respectTransparency true in
private theorem average_point (v : Corner) : averageAction v=plainAverage v := by
  exact congrArg₂ (fun a b : Corner => v+a+b)
    (transformed_apply (original 2) v)
    ((transformed_apply (original 2) (transformed (original 2) v)).trans
      (congrArg (pointAction (original 2)) (transformed_apply (original 2) v)))
set_option backward.isDefEq.respectTransparency true in
private theorem evaluated_plain (h : BinaryThreeQuartetCornerUniform.H) (v : Corner) :
    evaluatedOperator h v=plainOperator h v := by
  have ht : averageAction (transformed independentTranslation (averageAction v))=
      plainAverage (pointAction independentTranslation (plainAverage v)) :=
    (average_point _).trans (congrArg plainAverage
      ((transformed_apply independentTranslation (averageAction v)).trans
        (congrArg (pointAction independentTranslation) (average_point v))))
  rw [evaluatedOperator_apply]
  unfold plainOperator
  rw [ht,average_point v]
  exact transformed_apply (Row67OriginalKernelCertificate.liftSection h.2) _
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2048 in
private theorem actual_operator : ∀ h : BinaryThreeQuartetCornerUniform.H,
    BinaryThreeQuartetCornerUniform.rho h=transformed.asAlgebraHom (actualOperator h) := by
  intro h
  apply LinearMap.ext
  intro v
  calc
    BinaryThreeQuartetCornerUniform.rho h v=plainCorner h v := corner_apply h v
    _ = compactOperator h v := compact_operator h v
    _ = plainOperator h v := (plain_compact h v).symm
    _ = evaluatedOperator h v := (evaluated_plain h v).symm
    _ = transformed.asAlgebraHom (actualOperator h) v :=
      congrArg (fun f : Module.End Bit Corner => f v) (actualOperator_evaluation h).symm
 theorem natural_three : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation Bit row67Interface.top (Fin 12)) 3 := by
  have ht : UniformSubrepresentationGeneratorBound transformed 3 :=
    UniformSubrepresentationGeneratorBound.of_operator_containment transformed
      BinaryThreeQuartetCornerUniform.rho (fun h => ⟨actualOperator h,actual_operator h⟩)
      BinaryThreeQuartetCornerUniform.uniform_three
  let j : Representation.IntertwiningMap natural transformed := {
    toLinearMap := flat.toLinearMap
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      change flat (natural g v)=flat (natural g (flat.symm (flat v)))
      rw [flat.symm_apply_apply] }
  exact ht.of_injective j flat.injective
end SymmetricSubgroupAsymptotics.Row67OriginalNaturalThree
