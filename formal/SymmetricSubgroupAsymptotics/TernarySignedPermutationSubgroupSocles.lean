import SymmetricSubgroupAsymptotics.TernaryMonomialOrbitUniform
import SymmetricSubgroupAsymptotics.LinearSemidirectSubgroupFullProjection
import SymmetricSubgroupAsymptotics.BinarySignTernaryLinear

/-! Uniform normal bounds on actual signed ternary affine subgroups over
a cyclic point orbit. The binary sign kernel and ternary translation
kernel each contribute at most one generator. Both projected subgroups
are literal images; block lifts can carry signs and translations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.TernarySignedPermutationSubgroupSocles

open SemidirectProduct

variable {R X : Type} [Group R] [MulAction R X] [Fintype X] [DecidableEq X]
  (E : Subrepresentation
    (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation (R := R) (X := X)))

abbrev SignModel := CyclicOrbitBinarySignNormalGenerators.Model E

def blockPermutation : SignModel E →* Equiv.Perm X :=
  (MulAction.toPermHom R X).comp (rightHom : SignModel E →* R)

def coefficient (g : SignModel E) (i : X) : ZMod 3 :=
  BinarySignTernaryLinear.coefficient (g.left.toAdd.val i)

theorem coefficient_one (i : X) : coefficient E 1 i = 1 := rfl

theorem coefficient_mul (g h : SignModel E) (i : X) :
    coefficient E (g*h) i = coefficient E g i * coefficient E h (blockPermutation E g⁻¹ i) :=
  BinarySignTernaryLinear.coefficient_add _ _

abbrev linearAction := TernaryMonomialCocycle.linearAction
  (blockPermutation E) (coefficient E) (coefficient_one E) (coefficient_mul E)

abbrev Model := LinearSemidirectCoprimeSocleBounds.Model (linearAction E)

variable [Finite R] (K : Subgroup (Model E))

abbrev Image := LinearSemidirectSubgroupKernelChart.Image (linearAction E) K

def blocks : Image E K →* R :=
  LinearSemidirectSubgroupKernelChart.projection
    (CyclicOrbitBinarySignNormalGenerators.linearAction E) (Image E K)

theorem uniform_image (c : R) (x : X)
    (hcycle : ∀ y : X, ∃ n : ℕ, c^n • x = y)
    (hsurj : Function.Surjective (blocks E K)) :
    UniformSubrepresentationGeneratorBound
      (LinearSemidirectSubgroupKernelChart.imageRepresentation (linearAction E) K) 1 := by
  let S := Image E K
  let b : S →* Equiv.Perm X := (blockPermutation E).comp S.subtype
  let d : S → X → ZMod 3 := fun g => coefficient E g
  have h1 : ∀ i, d 1 i = 1 := coefficient_one E
  have hm : ∀ g h i, d (g*h) i = d g i * d h (b g⁻¹ i) :=
    fun g h i => coefficient_mul E g h i
  obtain ⟨g,hg⟩ := hsurj c
  change UniformSubrepresentationGeneratorBound
    (TernaryMonomialOrbitUniform.representation b d h1 hm) 1
  apply TernaryMonomialOrbitUniform.uniform b d h1 hm g (fun _ : Fin 1 => x)
  intro y
  obtain ⟨n,hn⟩ := hcycle y
  refine ⟨0,n,?_⟩
  have hb : b g = MulAction.toPermHom R X c := by
    change MulAction.toPermHom R X (blocks E K g) = _
    rw [hg]
  rw [hb,← map_pow]
  exact hn

theorem image_normalGen_le (c : R) (x : X)
    (hcycle : ∀ y : X, ∃ n : ℕ, c^n • x = y)
    (hsurj : Function.Surjective (blocks E K)) (a : ℕ)
    (ha : ∀ L : Subgroup R, L.Normal → MarkedC4.normalGen L ≤ a)
    (N : Subgroup (Image E K)) [N.Normal] : MarkedC4.normalGen N ≤ 1+a :=
  LinearSemidirectSubgroupFullProjection.normalGen_le
    (CyclicOrbitBinarySignNormalGenerators.linearAction E) (Image E K)
    hsurj 1 a (CyclicOrbitBinarySignNormalGenerators.uniform E c x hcycle) ha N

theorem normalGen_le (c : R) (x : X)
    (hcycle : ∀ y : X, ∃ n : ℕ, c^n • x = y)
    (hsurj : Function.Surjective (blocks E K)) (a : ℕ)
    (ha : ∀ L : Subgroup R, L.Normal → MarkedC4.normalGen L ≤ a)
    (N : Subgroup K) [N.Normal] : MarkedC4.normalGen N ≤ 2+a := by
  have h := LinearSemidirectSubgroupSocles.normalGen_le (linearAction E) K 1 (1+a)
    (uniform_image E K c x hcycle hsurj)
    (fun L hL => by letI := hL; exact image_normalGen_le E K c x hcycle hsurj a ha L) N
  simpa only [← Nat.add_assoc] using h

theorem normal_generating_tuples (c : R) (x : X)
    (hcycle : ∀ y : X, ∃ n : ℕ, c^n • x = y)
    (hsurj : Function.Surjective (blocks E K)) (a : ℕ)
    (ha : ∀ L : Subgroup R, L.Normal → MarkedC4.normalGen L ≤ a)
    (N : Subgroup K) (hN : N.Normal) :
    ∃ g : Fin (2+a) → K, Subgroup.normalClosure (Set.range g) = N := by
  letI := hN
  exact exists_normal_generating_tuple_of_normalGen_le N
    (normalGen_le E K c x hcycle hsurj a ha N)

theorem socle_of_surjective (c : R) (x : X)
    (hcycle : ∀ y : X, ∃ n : ℕ, c^n • x = y)
    (hsurj : Function.Surjective (blocks E K)) (a : ℕ)
    (ha : ∀ L : Subgroup R, L.Normal → MarkedC4.normalGen L ≤ a)
    {Q : Type} [Group Q] (pi : K →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q (2+a) :=
  normal_generating_tuples_of_surjective pi hpi
    (normal_generating_tuples E K c x hcycle hsurj a ha) (finiteGroupSocle Q) inferInstance

end SymmetricSubgroupAsymptotics.TernarySignedPermutationSubgroupSocles

end
