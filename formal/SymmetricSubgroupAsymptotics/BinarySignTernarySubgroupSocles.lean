import SymmetricSubgroupAsymptotics.LinearSemidirectSubgroupFullProjection
import SymmetricSubgroupAsymptotics.BinarySignTernaryAffineSocles

/-! Arbitrary retained subgroups of the signed ternary affine model.
The two projection images are kept literally. A transitive block image
makes the ternary monomial module cyclic; a uniform binary module bound
controls the actual sign-image subgroup, including sign-carrying lifts. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.BinarySignTernarySubgroupSocles

open SemidirectProduct BinarySignTernaryLinear

variable {R : Type} [Group R] [MulAction R (Fin 4)]
  (E : Subrepresentation
    (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation (R := R) (X := Fin 4)))

theorem coefficient_ne_zero (z : ZMod 2) : coefficient z ≠ 0 :=
  Units.ne_zero (TernaryFourScalarDiagonalQuotient.bitScalar (Multiplicative.ofAdd z))

theorem linearHom_single (g : SignModel E) (i : Fin 4) (a : ZMod 3) :
    linearHom E g (Pi.single i a) =
      Pi.single (g.right • i) (coefficient (g.left.toAdd.1 (g.right • i))*a) := by
  funext j
  change coefficient (g.left.toAdd.1 j) * (Pi.single i a : Vector) (g.right⁻¹ • j) =
    (Pi.single (g.right • i) (coefficient (g.left.toAdd.1 (g.right • i))*a) : Vector) j
  by_cases hj : j = g.right • i
  · subst j
    rw [← mul_smul,inv_mul_cancel,one_smul]
    simp only [Pi.single_eq_same]
  · have hn : g.right⁻¹ • j ≠ i := by
      intro hi
      apply hj
      calc
        j = g.right • (g.right⁻¹ • j) := (smul_inv_smul g.right j).symm
        _ = g.right • i := congrArg (fun z => g.right • z) hi
    simp only [Pi.single_eq_of_ne hj,Pi.single_eq_of_ne hn,mul_zero]

theorem generated_subgroup (S : Subgroup (SignModel E))
    (htrans : ∀ i : Fin 4, ∃ g : S, (g : SignModel E).right • 0 = i) :
    RepresentationGeneratedBy
      ((LinearSemidirectCoprimeSocleBounds.linearRepresentation (linearHom E)).comp S.subtype) 1 := by
  let rho : Representation (ZMod 3) S Vector :=
    (LinearSemidirectCoprimeSocleBounds.linearRepresentation (linearHom E)).comp S.subtype
  let code : Fin 1 → rho.asModule := fun _ => rho.asModuleEquiv.symm (Pi.single 0 1)
  let P : Submodule (ZMod 3)[S] rho.asModule :=
    Submodule.span (ZMod 3)[S] (Set.range code)
  let W : Subrepresentation rho := Subrepresentation.ofSubmodule' P
  have hzero : (Pi.single 0 1 : Vector) ∈ W := by
    change code 0 ∈ P
    exact Submodule.subset_span (Set.mem_range_self 0)
  have hdelta (i : Fin 4) : (Pi.single i 1 : Vector) ∈ W := by
    obtain ⟨g,hg⟩ := htrans i
    have h := W.apply_mem_toSubmodule g hzero
    change linearHom E g (Pi.single 0 1) ∈ W at h
    rw [linearHom_single,hg,mul_one] at h
    have hs := W.toSubmodule.smul_mem
      (coefficient ((g : SignModel E).left.toAdd.1 i))⁻¹ h
    have he : (coefficient ((g : SignModel E).left.toAdd.1 i))⁻¹ •
        (Pi.single i (coefficient ((g : SignModel E).left.toAdd.1 i)) : Vector) =
      Pi.single i 1 := by
      rw [← Pi.single_smul,smul_eq_mul,inv_mul_cancel₀ (coefficient_ne_zero _)]
    rwa [he] at hs
  have hall (v : Vector) : v ∈ W := by
    have he : (∑ i : Fin 4, v i • (Pi.single i 1 : Vector)) = v := by
      calc
        _ = ∑ i, Pi.single i (v i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Pi.single_smul]
          simp
        _ = v := LinearMap.sum_single_apply (fun _ : Fin 4 => ZMod 3) v
    rw [← he]
    exact W.toSubmodule.sum_mem fun i _ => W.toSubmodule.smul_mem _ (hdelta i)
  refine ⟨code,top_unique ?_⟩
  intro v _
  exact hall v

variable [Finite R]
  (K : Subgroup (BinarySignTernaryAffineSocles.Model E))

abbrev signImage := LinearSemidirectSubgroupKernelChart.Image (linearHom E) K

def blocks : signImage E K →* R :=
  LinearSemidirectSubgroupKernelChart.projection
    (CyclicOrbitBinarySignNormalGenerators.linearAction E) (signImage E K)

theorem socle_of_surjective
    (hblocks : Function.Surjective (blocks E K))
    (htrans : ∀ i : Fin 4, ∃ r : R, r • 0 = i)
    (hcop : Nat.Coprime 3 (Nat.card R)) (u a : ℕ)
    (hu : UniformSubrepresentationGeneratorBound
      (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation (R := R) (X := Fin 4)) u)
    (ha : ∀ L : Subgroup R, L.Normal → MarkedC4.normalGen L ≤ a)
    {Q : Type} [Group Q] (pi : K →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q (max 1 (u+a)) := by
  have hsignCoprime : Nat.Coprime 3 (Nat.card (SignModel E)) := by
    rw [Nat.card_congr SemidirectProduct.equivProd,Nat.card_prod,
      Nat.card_congr Multiplicative.toAdd,Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod]
    exact Nat.coprime_mul_iff_right.mpr
      ⟨(by decide : Nat.Coprime 3 2).pow_right _,hcop⟩
  have hsignUniform : UniformSubrepresentationGeneratorBound
      (LinearSemidirectCoprimeSocleBounds.linearRepresentation
        (CyclicOrbitBinarySignNormalGenerators.linearAction E)) u := by
    let inclusion : E.toRepresentation.IntertwiningMap
        (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation
          (R := R) (X := Fin 4)) :=
      { toLinearMap := E.toSubmodule.subtype
        isIntertwining' _ := rfl }
    change UniformSubrepresentationGeneratorBound E.toRepresentation u
    exact hu.of_injective inclusion (fun _ _ h => Subtype.ext h)
  apply LinearSemidirectSubgroupSocles.coprime_socle_of_surjective
    (linearHom E) K ?_ 1 (u+a) ?_ ?_ pi hpi
  · exact hsignCoprime.of_dvd_right
      (Subgroup.card_subgroup_dvd_card (signImage E K))
  · apply generated_subgroup E (signImage E K)
    intro i
    obtain ⟨r,hr⟩ := htrans i
    obtain ⟨g,hg⟩ := hblocks r
    exact ⟨g,by change (blocks E K g) • 0 = i; rw [hg,hr]⟩
  · intro L hL
    letI := hL
    exact LinearSemidirectSubgroupFullProjection.normalGen_le
      (CyclicOrbitBinarySignNormalGenerators.linearAction E) (signImage E K)
      hblocks u a hsignUniform ha L

end SymmetricSubgroupAsymptotics.BinarySignTernarySubgroupSocles

end
