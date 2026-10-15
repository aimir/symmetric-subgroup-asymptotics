import SymmetricSubgroupAsymptotics.FourBlockSignedSubgroupLiteralSocles
import SymmetricSubgroupAsymptotics.BinarySignTernaryIrreducibleSubgroupSocles

/-! Exact literal-image transfer for the irreducible retained-sign
criterion. The two even flips are proved inside the generated sign image;
all translation correlations and the original quotient kernel are kept. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.FourBlockIrreducibleSignedSubgroupLiteralSocles

open SemidirectProduct BinarySignTernaryLinear FourBlockBinarySignSpaces
open FourBlockSignedSubgroupLiteralSocles

variable {R : Type} [Group R] [Finite R] [MulAction R (Fin 4)]
  [FaithfulSMul R (Fin 4)]

def evenFlip (i j : Fin 4) : SignModel (fullSpace (R := R)) :=
  inl (Multiplicative.ofAdd ⟨pair i j,Submodule.mem_top⟩)

theorem quotientSocle {n : ℕ}
    (pointRelabel : Equiv.Perm (Fin 4)) (lifted : Fin n → Model (R := R))
    (target : Fin n → Equiv.Perm (Fin 12))
    (hbinding : ∀ i, action pointRelabel (lifted i) = target i)
    (hfull : Subgroup.closure (Set.range (fun i => (lifted i).right.right)) = ⊤)
    (htrans : ∀ i : Fin 4, ∃ r : R, r • 0 = i)
    (h01 : evenFlip (R := R) 0 1 ∈ Subgroup.closure (Set.range (fun i => (lifted i).right)))
    (h02 : evenFlip (R := R) 0 2 ∈ Subgroup.closure (Set.range (fun i => (lifted i).right)))
    (u a : ℕ) (hpos : 0 < u+a)
    (hu : UniformSubrepresentationGeneratorBound
      (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation (R := R) (X := Fin 4)) u)
    (ha : ∀ L : Subgroup R, L.Normal → MarkedC4.normalGen L ≤ a)
    (N : Subgroup (Subgroup.closure (Set.range target))) [N.Normal] :
    SocleNormalGeneratorBound (Subgroup.closure (Set.range target) ⧸ N) (u+a) := by
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
  have hsign : Subgroup.closure (Set.range (fun i => (lifted i).right)) ≤
      BinarySignTernarySubgroupSocles.signImage (fullSpace (R := R)) K := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨closureGenerators lifted i,rfl⟩
  let f : K →* Equiv.Perm (Fin 12) := (action pointRelabel).comp K.subtype
  let pi := GeneratedLiteralImage.toTop f (closureGenerators lifted) target (Equiv.refl _)
    (closureGenerators_full lifted) hbinding
  have hpi : Function.Surjective pi :=
    GeneratedLiteralImage.toTop_surjective f (closureGenerators lifted) target (Equiv.refl _)
      (closureGenerators_full lifted) hbinding
  apply BinarySignTernaryIrreducibleSubgroupSocles.socle_of_surjective
    (fullSpace (R := R)) K ?_ htrans (Submodule.mem_top) (Submodule.mem_top)
    (hsign h01) (hsign h02) u a hpos hu ha ((QuotientGroup.mk' N).comp pi)
    ((QuotientGroup.mk'_surjective N).comp hpi)
  intro r
  obtain ⟨g,hg⟩ := hbeta r
  exact ⟨(LinearSemidirectSubgroupKernelChart.projection
    (linearHom (fullSpace (R := R))) K).rangeRestrict g,hg⟩

theorem symmetric_uniform : UniformSubrepresentationGeneratorBound
    (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation
      (R := Equiv.Perm (Fin 4)) (X := Fin 4)) 1 := by
  apply permutationFunctionRepresentation_uniform_of_polynomial_orbitCover
    TernaryFourBlockPermutationGenerators.c (fun _ : Fin 1 => (0 : Fin 4))
  intro i
  obtain ⟨n,hn⟩ := symmetric_orbit i
  exact ⟨0,n,hn⟩

end SymmetricSubgroupAsymptotics.FourBlockIrreducibleSignedSubgroupLiteralSocles

end
