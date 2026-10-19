import SymmetricSubgroupAsymptotics.BinaryFourSumCornerRepresentation
import SymmetricSubgroupAsymptotics.BinarySymmetricThreeFourColumnUniform
import SymmetricSubgroupAsymptotics.ModuleGeneratorUniformProjection
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.BinaryThreeQuartetCornerUniform
abbrev Bit := ZMod 2
abbrev Fixed := BinaryFourSumOperatorUniform.Space
abbrev Active := BinarySymmetricThreeFourColumnUniform.Space
abbrev H := BinaryFourSumCornerRepresentation.Binary × Equiv.Perm (Fin 3)
abbrev Space := Fixed × Active
 def left : Representation Bit H Fixed :=
  BinaryFourSumCornerRepresentation.rho.comp (MonoidHom.fst _ _)
 def right : Representation Bit H Active :=
  BinarySymmetricThreeFourColumnUniform.rho.comp (MonoidHom.snd _ _)
 def rho : Representation Bit H Space := left.prod right
private def iLeft : left.IntertwiningMap rho where
  toLinearMap := LinearMap.inl Bit Fixed Active
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change (left g v,0)=(left g v,right g 0)
    rw [map_zero]
private def iRight : right.IntertwiningMap rho where
  toLinearMap := LinearMap.inr Bit Fixed Active
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change (0,right g v)=(left g 0,right g v)
    rw [map_zero]
private def lmap := Representation.IntertwiningMap.equivLinearMapAsModule left rho iLeft
private def rmap := Representation.IntertwiningMap.equivLinearMapAsModule right rho iRight
private def P : Submodule Bit[H] rho.asModule := lmap.range
private def Q : Submodule Bit[H] rho.asModule := rmap.range
 def projector : Bit[H] :=
  MonoidAlgebra.single (1,1) 1+MonoidAlgebra.single (1,finRotate 3) 1+
    MonoidAlgebra.single (1,(finRotate 3)^2) 1
private theorem projector_apply (x : Space) : rho.asAlgebraHom projector x=(x.1,0) := by
  have hfixed : ∀ z : Fixed,z+z+z=z := by decide +kernel
  have hactive (v : Active) : v+BinarySymmetricThreeFourColumnUniform.rho (finRotate 3) v+
      BinarySymmetricThreeFourColumnUniform.rho ((finRotate 3)^2) v=0 := by
    funext i j
    fin_cases i
    · change v 0 j+(-v 0 j-v 1 j)+v 1 j=0
      abel
    · change v 1 j+v 0 j+(-v 0 j-v 1 j)=0
      abel
  have hp (g : H) (v : Space) : rho g v=(left g v.1,right g v.2) := rfl
  have hl (p : Equiv.Perm (Fin 3)) (v : Fixed) : left (1,p) v=v := by
    change BinaryFourSumCornerRepresentation.rho 1 v=v
    rw [map_one]
    rfl
  have hr (p : Equiv.Perm (Fin 3)) (v : Active) :
      right (1,p) v=BinarySymmetricThreeFourColumnUniform.rho p v := rfl
  simp only [projector,map_add,Representation.asAlgebraHom_single_one,LinearMap.add_apply,hp]
  apply Prod.ext
  · change left (1,1) x.1+left (1,finRotate 3) x.1+left (1,(finRotate 3)^2) x.1=x.1
    rw [hl,hl,hl]
    exact hfixed x.1
  · change right (1,1) x.2+right (1,finRotate 3) x.2+right (1,(finRotate 3)^2) x.2=0
    rw [hr,hr,hr]
    rw [map_one]
    exact hactive x.2
 theorem uniform_three : UniformSubrepresentationGeneratorBound rho 3 := by
  apply (uniformSubrepresentationGeneratorBound_iff_submodule rho 3).mpr
  intro W
  have hl : UniformSubrepresentationGeneratorBound left 3 :=
    UniformSubrepresentationGeneratorBound.comp_of_surjective BinaryFourSumCornerRepresentation.rho
      (MonoidHom.fst BinaryFourSumCornerRepresentation.Binary (Equiv.Perm (Fin 3)))
      (fun x => ⟨(x,1),rfl⟩) BinaryFourSumCornerRepresentation.uniform_three
  have hr : UniformSubrepresentationGeneratorBound right 3 :=
    (UniformSubrepresentationGeneratorBound.comp_of_surjective BinarySymmetricThreeFourColumnUniform.rho
      (MonoidHom.snd BinaryFourSumCornerRepresentation.Binary (Equiv.Perm (Fin 3)))
      (fun x => ⟨(1,x),rfl⟩) BinarySymmetricThreeFourColumnUniform.uniform_two).mono (by decide)
  let eP : @LinearEquiv Bit[H] Bit[H]
      (inferInstance : Ring Bit[H]).toSemiring (inferInstance : Ring Bit[H]).toSemiring
      (RingHom.id Bit[H]) (RingHom.id Bit[H]) inferInstance inferInstance
      left.asModule P
      (inferInstance : AddCommGroup left.asModule).toAddCommMonoid
      (inferInstance : AddCommGroup P).toAddCommMonoid
      inferInstance inferInstance := {
    toFun := fun x => ⟨(x,0),x,rfl⟩
    invFun := fun y => y.val.1
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨x,y,hy⟩
      apply Subtype.ext
      change (x.1,0)=x
      rw [← hy]
      rfl
    map_add' := fun _ _ => rfl
    map_smul' := by
      intro a x
      apply Subtype.ext
      change lmap (a • x)=a • lmap x
      exact lmap.map_smul a x }
  let eQ : @LinearEquiv Bit[H] Bit[H]
      (inferInstance : Ring Bit[H]).toSemiring (inferInstance : Ring Bit[H]).toSemiring
      (RingHom.id Bit[H]) (RingHom.id Bit[H]) inferInstance inferInstance
      right.asModule Q
      (inferInstance : AddCommGroup right.asModule).toAddCommMonoid
      (inferInstance : AddCommGroup Q).toAddCommMonoid
      inferInstance inferInstance := {
    toFun := fun x => ⟨(0,x),x,rfl⟩
    invFun := fun y => y.val.2
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨x,y,hy⟩
      apply Subtype.ext
      change (0,x.2)=x
      rw [← hy]
      rfl
    map_add' := fun _ _ => rfl
    map_smul' := by
      intro a x
      apply Subtype.ext
      change rmap (a • x)=a • rmap x
      exact rmap.map_smul a x }
  apply ModuleGeneratedBy.uniform_of_projected_submodules P Q projector ?_ ?_ ?_ 3 ?_ ?_ W
  · rintro ⟨x,y,hy⟩
    change rho.asAlgebraHom projector x=x
    rw [projector_apply]
    rw [← hy]
    rfl
  · rintro ⟨x,y,hy⟩
    change rho.asAlgebraHom projector x=0
    rw [projector_apply]
    rw [← hy]
    rfl
  · apply top_unique
    intro x _
    exact Submodule.mem_sup.mpr ⟨(x.1,0),⟨x.1,rfl⟩,(0,x.2),⟨x.2,rfl⟩,by
      change ((x.1,0)+(0,x.2) : Space)=x
      apply Prod.ext <;> simp⟩
  · exact ModuleGeneratedBy.uniform_congr eP
      ((uniformSubrepresentationGeneratorBound_iff_submodule left 3).mp hl)
  · exact ModuleGeneratedBy.uniform_congr eQ
      ((uniformSubrepresentationGeneratorBound_iff_submodule right 3).mp hr)
end SymmetricSubgroupAsymptotics.BinaryThreeQuartetCornerUniform
