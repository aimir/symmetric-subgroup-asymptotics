import SymmetricSubgroupAsymptotics.BinaryPlaneWreathActualOddKernelStructure
import SymmetricSubgroupAsymptotics.BinaryCubicKernelMultiplicityGenerators
import SymmetricSubgroupAsymptotics.TransitiveKernelClassMultiplicity

/-! Actual correlated odd kernels with several transported kernel classes
have uniform half-degree translation generation. The zero odd image and
the single-class case remain explicit separate branches. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneOddKernelMultiplicityUniform
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel BinaryPlaneWreathNormalGenerators

variable {R I : Type} [Group R] [Finite R] [MulAction R I]
    [Fintype I] [DecidableEq I]
    (C : Subgroup (W (R := R) (I := I)))

abbrev localKernel (i : I) : Subgroup (oddKernel C) := (localLinear C i).ker

private theorem conjugate_mem_iff (h : C) (g : oddKernel C) (i : I) :
    (MulAut.conjNormal h : MulAut (oddKernel C)) g ∈
      localKernel C ((h : W (R := R) (I := I)).right • i) ↔ g ∈ localKernel C i := by
  change localLinear C ((h : W (R := R) (I := I)).right • i)
    ((MulAut.conjNormal h : MulAut (oddKernel C)) g) = 1 ↔ localLinear C i g = 1
  rw [localLinear_conjugate]
  constructor
  · intro he
    have hc := congrArg (fun z =>
      ((h : W (R := R) (I := I)).left ((h : W (R := R) (I := I)).right • i))⁻¹ * z *
      (h : W (R := R) (I := I)).left ((h : W (R := R) (I := I)).right • i)) he
    simpa [mul_assoc] using hc
  · intro he
    rw [he,mul_one,mul_inv_cancel]

/-- The literal kernel is transported by the actual odd-layer conjugation. -/
theorem kernel_map (h : C) (i : I) :
    (localKernel C i).map (MulAut.conjNormal h : MulAut (oddKernel C)).toMonoidHom =
      localKernel C ((h : W (R := R) (I := I)).right • i) := by
  ext g
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (conjugate_mem_iff C h x i).mpr hx
  · intro hg
    let a : MulAut (oddKernel C) := MulAut.conjNormal h
    have hx : a.symm g ∈ localKernel C i :=
      (conjugate_mem_iff C h (a.symm g) i).mp (by
        change a (a.symm g) ∈ localKernel C ((h : W (R := R) (I := I)).right • i)
        rw [a.apply_symm_apply]
        exact hg)
    exact ⟨a.symm g,hx,a.apply_symm_apply g⟩

/-- Equality of actual kernels is invariant under actual block transport. -/
theorem kernel_covariance (h : C) (i j : I) :
    localKernel C ((h : W (R := R) (I := I)).right • i) =
      localKernel C ((h : W (R := R) (I := I)).right • j) ↔
      localKernel C i = localKernel C j := by
  rw [←kernel_map C h i,←kernel_map C h j]
  exact (Subgroup.map_injective (MulAut.conjNormal h).injective).eq_iff

variable (htrans : ∀ i j : I, ∃ h : C,
    (h : W (R := R) (I := I)).right • i = j)

include htrans in
theorem kernel_card_eq (i j : I) : Nat.card (localKernel C i) = Nat.card (localKernel C j) := by
  obtain ⟨h,hh⟩ := htrans i j
  have hm := kernel_map C h i
  rw [hh] at hm
  rw [←hm]
  exact Nat.card_congr ((MulAut.conjNormal h).subgroupMap (localKernel C i)).toEquiv

include htrans in
/-- At least two actual kernel classes force every multiplicity below half. -/
theorem class_card_le_half (htwo : ∃ i j : I, localKernel C i ≠ localKernel C j)
    (K : Subgroup (oddKernel C)) :
    Nat.card {i : I // localKernel C i = K} ≤ Nat.card I / 2 := by
  apply TransitiveKernelClassMultiplicity.all_fibres_card_le_half
    (localKernel C) ?_ htwo K
  intro i j
  obtain ⟨h,hh⟩ := htrans i j
  refine ⟨(MulAction.toPerm (h : W (R := R) (I := I)).right : Equiv.Perm I),hh,?_⟩
  intro x y
  exact kernel_covariance C h x y

include htrans in
/-- Bounded actual class multiplicity supplies a uniform generator bound
on the original correlated wreath subgroup's translation representation. -/
theorem uniform_of_bound (hO : oddKernel C ≠ ⊥) (m : ℕ)
    (hbound : ∀ K : Subgroup (oddKernel C), Nat.card {i : I // localKernel C i = K} ≤ m) :
    UniformSubrepresentationGeneratorBound (BinaryPlaneCyclicWreathUniform.representation C) m := by
  let rho := BinaryPlaneCyclicWreathUniform.representation C
  let L : I → oddKernel C →* Linear := localLinear C
  have happly : ∀ g : oddKernel C, ∀ v i, rho (g : C) v i = L i g (v i) := by
    intro g v i
    change localLinear C i g (v (((g : C) : W (R := R) (I := I)).right⁻¹ • i)) = L i g (v i)
    rw [top_one C g,inv_one,one_smul]
  exact BinaryCubicKernelMultiplicityGenerators.uniform_of_restrict L rho
    (oddKernel C).subtype happly (isPGroup_three C) (local_cubic C)
    (all_local_nontrivial C hO htrans) (kernel_card_eq C htrans) m hbound

include htrans in
/-- This closes precisely the nonzero, at-least-two-class branch. It makes
no assertion for a zero odd image or a single isotypic kernel class. -/
theorem uniform_of_two_classes (hO : oddKernel C ≠ ⊥)
    (htwo : ∃ i j : I, localKernel C i ≠ localKernel C j) :
    UniformSubrepresentationGeneratorBound (BinaryPlaneCyclicWreathUniform.representation C)
      (Nat.card I / 2) :=
  uniform_of_bound C htrans hO (Nat.card I / 2) (class_card_le_half C htrans htwo)

end SymmetricSubgroupAsymptotics.BinaryPlaneOddKernelMultiplicityUniform
