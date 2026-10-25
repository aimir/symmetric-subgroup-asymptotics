import SymmetricSubgroupAsymptotics.BinaryPlaneActualSignKernelCoordinates
import SymmetricSubgroupAsymptotics.PrimeCoordinateNormalGeneration

/-! The actual top kernel of the actual sign image has one ambient normal
seed when the literal odd-coordinate kernels have two classes. Both sign
coordinates are inherited from the same original wreath subgroup. They
need not be surjective or have distinct kernels. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneTwoClassSignNormalGenerators
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel BinaryPlaneWreathNormalGenerators
open BinaryPlaneOddKernelMultiplicityUniform (localKernel)
open BinaryPlaneActualSignKernelCoordinates

variable {R I : Type} [Group R] [Finite R] [MulAction R I]
    [Fintype I] [DecidableEq I] (C : Subgroup (W (R := R) (I := I)))

theorem coordinate_eq_of_class
    (htrans : ∀ i j : I, ∃ h : C, (h : W (R := R) (I := I)).right • i = j)
    (hO : oddKernel C ≠ ⊥) (i j : I) (hij : localKernel C i = localKernel C j)
    (u : Kernel C) : coordinate C i u = coordinate C j u := by
  obtain ⟨h,hh⟩ := (u : Image C).property
  have he : (((u : Image C) : Sign (R := R) (I := I))) = signProjection C h := hh.symm
  have ht : (h : W (R := R) (I := I)).right = 1 := by
    have hr := congrArg (fun z : Sign (R := R) (I := I) => z.right) he
    exact hr.symm.trans u.property
  rw [coordinate_of_actual_lift C u h he i,coordinate_of_actual_lift C u h he j]
  exact BinaryPlaneKernelClassSignDescent.sign_eq_of_top_one_of_localKernel_eq
    C h ht i j hij (all_local_nontrivial C hO htrans i)

theorem two_coordinates_injective
    (htrans : ∀ i j : I, ∃ h : C, (h : W (R := R) (I := I)).right • i = j)
    (hO : oddKernel C ≠ ⊥) (i j : I)
    (hcover : ∀ k : I, localKernel C k = localKernel C i ∨ localKernel C k = localKernel C j) :
    Function.Injective (fun u : Kernel C => (coordinate C i u,coordinate C j u)) := by
  intro u v he
  have hi : coordinate C i u = coordinate C i v := congrArg Prod.fst he
  have hj : coordinate C j u = coordinate C j v := congrArg Prod.snd he
  apply coordinate_joint_injective C
  funext k
  rcases hcover k with hk | hk
  · exact (coordinate_eq_of_class C htrans hO k i hk u).trans
      (hi.trans (coordinate_eq_of_class C htrans hO k i hk v).symm)
  · exact (coordinate_eq_of_class C htrans hO k j hk u).trans
      (hj.trans (coordinate_eq_of_class C htrans hO k j hk v).symm)

private theorem coordinate_kernel_map (h : C) (i : I) :
    (coordinate C i).ker.map
      (MulAut.conjNormal (⟨signProjection C h,⟨h,rfl⟩⟩ : Image C)).toMonoidHom =
      (coordinate C ((h : W (R := R) (I := I)).right • i)).ker := by
  let q : Image C := ⟨signProjection C h,⟨h,rfl⟩⟩
  let a : MulAut (Kernel C) := MulAut.conjNormal q
  have hc (u : Kernel C) :
      coordinate C ((h : W (R := R) (I := I)).right • i) (a u) = coordinate C i u := by
    have hh := coordinate_conjugation C q u ((h : W (R := R) (I := I)).right • i)
    change coordinate C ((h : W (R := R) (I := I)).right • i) (a u) =
      coordinate C ((h : W (R := R) (I := I)).right⁻¹ •
        ((h : W (R := R) (I := I)).right • i)) u at hh
    simpa only [inv_smul_smul] using hh
  change (coordinate C i).ker.map a.toMonoidHom = _
  apply le_antisymm
  · intro u hu
    obtain ⟨v,hv,rfl⟩ := hu
    change coordinate C ((h : W (R := R) (I := I)).right • i) (a v) = 1
    rw [hc]
    exact hv
  · intro u hu
    refine ⟨a.symm u,?_,a.apply_symm_apply u⟩
    change coordinate C i (a.symm u) = 1
    rw [←hc,a.apply_symm_apply]
    exact hu

theorem normalGen_le_one_of_two_classes
    (htrans : ∀ i j : I, ∃ h : C, (h : W (R := R) (I := I)).right • i = j)
    (hO : oddKernel C ≠ ⊥) (i j : I) (hne : localKernel C i ≠ localKernel C j)
    (hcover : ∀ k : I, localKernel C k = localKernel C i ∨ localKernel C k = localKernel C j) :
    MarkedC4.normalGen (Kernel C) ≤ 1 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h,hh⟩ := htrans i j
  let q : Image C := ⟨signProjection C h,⟨h,rfl⟩⟩
  have hswap : localKernel C ((h : W (R := R) (I := I)).right • j) = localKernel C i := by
    rcases hcover ((h : W (R := R) (I := I)).right • j) with hk | hk
    · exact hk
    · have he : localKernel C ((h : W (R := R) (I := I)).right • i) =
          localKernel C ((h : W (R := R) (I := I)).right • j) := by rw [hh,hk]
      exact (hne ((BinaryPlaneOddKernelMultiplicityUniform.kernel_covariance C h i j).mp he)).elim
  have hmapswap : (coordinate C ((h : W (R := R) (I := I)).right • j)).ker =
      (coordinate C i).ker := by
    ext u
    change coordinate C ((h : W (R := R) (I := I)).right • j) u = 1 ↔ coordinate C i u = 1
    rw [coordinate_eq_of_class C htrans hO _ i hswap u]
  apply PrimeCoordinateNormalGeneration.normalGen_le_one_of_two_coordinate_kernel_orbit
    (Kernel C) 2 (coordinate C i) (coordinate C j)
    (two_coordinates_injective C htrans hO i j hcover) q
  · simpa only [hh] using coordinate_kernel_map C h i
  · exact (coordinate_kernel_map C h j).trans hmapswap

end SymmetricSubgroupAsymptotics.BinaryPlaneTwoClassSignNormalGenerators
