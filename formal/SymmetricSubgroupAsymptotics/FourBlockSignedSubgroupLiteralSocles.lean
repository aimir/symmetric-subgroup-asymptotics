import SymmetricSubgroupAsymptotics.BinarySignTernarySubgroupSocles
import SymmetricSubgroupAsymptotics.FourBlockBinarySignSpaces
import SymmetricSubgroupAsymptotics.GeneratedLiteralImage
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords

/-! Literal consumers for arbitrary signed affine subgroups with C4 or
D8 block image. Only the block image is generated symbolically. The sign
kernel and the ternary translation kernel remain the actual retained
subspaces; neither full translation generation nor a splitting is needed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.FourBlockSignedSubgroupLiteralSocles

open SemidirectProduct BinarySignTernaryLinear FourBlockBinarySignSpaces

variable {R : Type} [Group R] [Finite R] [MulAction R (Fin 4)]

abbrev fullSpace := space (R := R) false
abbrev Model := BinarySignTernaryAffineSocles.Model (fullSpace (R := R))

def lift (v : Vector) (z : BinaryVector) (r : R) : Model (R := R) :=
  inl (Multiplicative.ofAdd v) *
    inr (inl (Multiplicative.ofAdd ⟨z,Submodule.mem_top⟩) * inr r)

def action (pointRelabel : Equiv.Perm (Fin 4)) : Model (R := R) →* Equiv.Perm (Fin 12) :=
  ((Equiv.prodCongr pointRelabel (Equiv.refl (ZMod 3))).trans
    TernaryFourAugmentationAffineImage.pointEquiv.symm).permCongrHom.toMonoidHom.comp
      (BinarySignTernaryPointAction.pointAction (fullSpace (R := R)))

theorem quotientSocle {n : ℕ}
    (pointRelabel : Equiv.Perm (Fin 4)) (lifted : Fin n → Model (R := R))
    (target : Fin n → Equiv.Perm (Fin 12))
    (hbinding : ∀ i, action pointRelabel (lifted i) = target i)
    (hfull : Subgroup.closure (Set.range (fun i => (lifted i).right.right)) = ⊤)
    (htrans : ∀ i : Fin 4, ∃ r : R, r • 0 = i)
    (hcop : Nat.Coprime 3 (Nat.card R)) (u a : ℕ)
    (hu : UniformSubrepresentationGeneratorBound
      (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation (R := R) (X := Fin 4)) u)
    (ha : ∀ L : Subgroup R, L.Normal → MarkedC4.normalGen L ≤ a)
    (N : Subgroup (Subgroup.closure (Set.range target))) [N.Normal] :
    SocleNormalGeneratorBound (Subgroup.closure (Set.range target) ⧸ N) (max 1 (u+a)) := by
  let K := Subgroup.closure (Set.range lifted)
  let beta : K →* R := (rightHom : SignModel (fullSpace (R := R)) →* R).comp
    ((rightHom : Model (R := R) →* SignModel (fullSpace (R := R))).comp K.subtype)
  have hbeta : Function.Surjective beta := by
    have htop : (⊤ : Subgroup R) ≤ beta.range := by
      rw [← hfull]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨i,rfl⟩
      exact ⟨closureGenerators lifted i,rfl⟩
    intro r
    exact htop (Subgroup.mem_top r)
  let f : K →* Equiv.Perm (Fin 12) := (action pointRelabel).comp K.subtype
  let pi := GeneratedLiteralImage.toTop f (closureGenerators lifted) target (Equiv.refl _)
    (closureGenerators_full lifted) hbinding
  have hpi : Function.Surjective pi :=
    GeneratedLiteralImage.toTop_surjective f (closureGenerators lifted) target (Equiv.refl _)
      (closureGenerators_full lifted) hbinding
  apply BinarySignTernarySubgroupSocles.socle_of_surjective (fullSpace (R := R)) K
    ?_ htrans hcop u a hu ha ((QuotientGroup.mk' N).comp pi)
    ((QuotientGroup.mk'_surjective N).comp hpi)
  intro r
  obtain ⟨g,hg⟩ := hbeta r
  exact ⟨(LinearSemidirectSubgroupKernelChart.projection
    (linearHom (fullSpace (R := R))) K).rangeRestrict g,hg⟩

theorem cyclic_coprime : Nat.Coprime 3 (Nat.card Cyclic) := by
  apply (by decide : Nat.Coprime 3 4).of_dvd_right
  rw [Nat.card_zpowers]
  exact orderOf_dvd_of_pow_eq_one (by decide +kernel : TernaryFourBlockPermutationGenerators.c^4=1)

theorem dihedral_coprime : Nat.Coprime 3 (Nat.card Dihedral) := by
  have hsource : Nat.Coprime 3 (Nat.card (DihedralGroup 4)) := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  exact hsource.of_dvd_right
    (Subgroup.card_dvd_of_surjective dihedralMap.rangeRestrict dihedralMap.rangeRestrict_surjective)

theorem cyclic_uniform : UniformSubrepresentationGeneratorBound
    (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation (R := Cyclic) (X := Fin 4)) 1 := by
  apply permutationFunctionRepresentation_uniform_of_polynomial_orbitCover
    cyclicGenerator (fun _ : Fin 1 => (0 : Fin 4))
  intro i
  obtain ⟨n,hn⟩ := cyclic_orbit i
  exact ⟨0,n,hn⟩

theorem dihedral_uniform : UniformSubrepresentationGeneratorBound
    (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation (R := Dihedral) (X := Fin 4)) 1 := by
  apply permutationFunctionRepresentation_uniform_of_polynomial_orbitCover
    dihedralRotation (fun _ : Fin 1 => (0 : Fin 4))
  intro i
  obtain ⟨n,hn⟩ := dihedral_orbit i
  exact ⟨0,n,hn⟩

end SymmetricSubgroupAsymptotics.FourBlockSignedSubgroupLiteralSocles

end
