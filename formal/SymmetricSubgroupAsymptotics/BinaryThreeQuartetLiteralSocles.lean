import SymmetricSubgroupAsymptotics.BinaryPlanePermutationWreathCoordinates
import SymmetricSubgroupAsymptotics.GeneratedLiteralImage
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords

/-! Literal twelve-point consumers of the binary-plane wreath bounds.
The actual generated affine subgroup and its projected image are retained,
and every target quotient is reached by its original quotient map. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryThreeQuartetLiteralSocles

open SemidirectProduct BinaryPlanePermutationAffineEquiv
open BinaryPlaneWreathIrreducible

def planeLabel : Plane ≃ Fin 4 where
  toFun v := if v 0 = 0 then (if v 1 = 0 then 0 else 2) else (if v 1 = 0 then 1 else 3)
  invFun i := ![![0,0],![1,0],![0,1],![1,1]] i
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pointChart : Plane × Fin 3 ≃ Fin 12 :=
  (Equiv.prodCongr planeLabel (Equiv.refl (Fin 3))).trans finProdFinEquiv

variable {R : Type} [Group R] [Finite R] [MulAction R (Fin 3)] [FaithfulSMul R (Fin 3)]

abbrev Model := BinaryPlanePermutationWreathCoordinates.Model (R := R) (I := Fin 3)

def action : Model (R := R) →* Equiv.Perm (Fin 12) :=
  pointChart.permCongrHom.toMonoidHom.comp BinaryPlanePermutationWreathCoordinates.pointAction

theorem quotientSocle {n : ℕ} (lifted : Fin n → Model (R := R))
    (target : Fin n → Equiv.Perm (Fin 12))
    (hbinding : ∀ i, action (lifted i) = target i)
    (hfull : Subgroup.closure (Set.range (fun i => (lifted i).right.right)) = ⊤)
    (hlocal : ∀ j : Fin 3, localEmbedding j singer ∈
      Subgroup.closure (Set.range (fun i => (lifted i).right)))
    (htrans : ∀ i j : Fin 3, ∃ g : R, g • i = j)
    (c : R) (i : Fin 3) (hcycle : ∀ j : Fin 3, ∃ m : ℕ, c^m • i = j)
    (a : ℕ) (ha : ∀ N : Subgroup R, N.Normal → MarkedC4.normalGen N ≤ a)
    (N : Subgroup (Subgroup.closure (Set.range target))) [N.Normal] :
    SocleNormalGeneratorBound (Subgroup.closure (Set.range target) ⧸ N) (2+a) := by
  let K := Subgroup.closure (Set.range lifted)
  let C := BinaryPlaneWreathNormalGenerators.actualImage K
  have hC : Subgroup.closure (Set.range (fun i => (lifted i).right)) ≤ C := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact ⟨closureGenerators lifted j,rfl⟩
  let beta : C →* R := PermutationalWreathProduct.rightHom.comp C.subtype
  have hbeta : Function.Surjective beta := by
    have htop : (⊤ : Subgroup R) ≤ beta.range := by
      rw [← hfull]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨j,rfl⟩
      exact ⟨⟨(lifted j).right,hC (Subgroup.subset_closure (Set.mem_range_self j))⟩,rfl⟩
    intro r
    exact htop (Subgroup.mem_top r)
  have hmove : ∀ i j : Fin 3, ∃ g : C,
      (g : W (R := R) (I := Fin 3)).right • i = j := by
    intro i j
    obtain ⟨r,hr⟩ := htrans i j
    obtain ⟨g,hg⟩ := hbeta r
    exact ⟨g,by change beta g • i = j; rw [hg,hr]⟩
  have htuples := BinaryPlaneWreathNormalGenerators.affine_normal_generating_tuples
    K (fun j => hC (hlocal j)) hmove hbeta c i hcycle a ha
  let f : K →* Equiv.Perm (Fin 12) := action.comp K.subtype
  let pi := GeneratedLiteralImage.toTop f (closureGenerators lifted) target (Equiv.refl _)
    (closureGenerators_full lifted) hbinding
  have hpi : Function.Surjective pi :=
    GeneratedLiteralImage.toTop_surjective f (closureGenerators lifted) target (Equiv.refl _)
      (closureGenerators_full lifted) hbinding
  exact normal_generating_tuples_of_surjective ((QuotientGroup.mk' N).comp pi)
    ((QuotientGroup.mk'_surjective N).comp hpi) htuples
    (finiteGroupSocle _) inferInstance

end SymmetricSubgroupAsymptotics.BinaryThreeQuartetLiteralSocles

end
