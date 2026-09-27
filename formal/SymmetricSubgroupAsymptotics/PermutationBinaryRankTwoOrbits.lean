import SymmetricSubgroupAsymptotics.RepresentationBinaryRankTwoResidual
import SymmetricSubgroupAsymptotics.PermutationBinaryTrivialSection
import SymmetricSubgroupAsymptotics.NormalSubgroupOrbitIndex

/-! The common-character kernel has two original four-point orbits.
The section is an actual quotient of an original permutation
subrepresentation, and the action kernel remains a subgroup of the
original acting group. No block action or labelled block chart is
supplied. In particular, a purported single orbit is excluded by the
proved original binary permutation-head bound.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G X A : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [MulAction.IsPretransitive G X]
    [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]

/-- A four-dimensional actual section with action kernel of index two
has exactly two original kernel orbits, both of cardinality four. -/
theorem permutationBinary_section_kernel_two_orbits
    (hG : IsPGroup 2 G) (x : X) (hX : Nat.card X=8)
    (ρ : Representation (ZMod 2) G A)
    (M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))
    (q : M.toRepresentation.IntertwiningMap ρ) (hq : Function.Surjective q)
    (hA : 4≤Module.finrank (ZMod 2) A) (hindex : ρ.ker.index=2) :
    Nat.card (MulAction.orbitRel.Quotient ρ.ker X)=2 ∧
      ∀ o : MulAction.orbitRel.Quotient ρ.ker X, Nat.card o.orbit=4 := by
  letI : Nonempty X := ⟨x⟩
  letI : Nonempty (MulAction.orbitRel.Quotient ρ.ker X) := ⟨Quotient.mk'' x⟩
  have hpos : 0<Nat.card (MulAction.orbitRel.Quotient ρ.ker X) := Nat.card_pos
  have hle : Nat.card (MulAction.orbitRel.Quotient ρ.ker X)≤2 := by
    rw [normal_orbit_classes_card_eq_index ρ.ker x]
    exact (Subgroup.index_antitone
      (show ρ.ker≤ρ.ker⊔MulAction.stabilizer G x from le_sup_left)).trans hindex.le
  have hne : Nat.card (MulAction.orbitRel.Quotient ρ.ker X)≠1 := by
    intro hone
    letI : Subsingleton (MulAction.orbitRel.Quotient ρ.ker X) :=
      (Nat.card_eq_one_iff_unique.mp hone).1
    letI : MulAction.IsPretransitive ρ.ker X :=
      (MulAction.pretransitive_iff_subsingleton_quotient ρ.ker X).mpr inferInstance
    let MK : Subrepresentation (permutationFunctionRepresentation (ZMod 2) ρ.ker X) := {
      toSubmodule := M.toSubmodule
      apply_mem_toSubmodule := fun g _ hm => M.apply_mem_toSubmodule (g:G) hm }
    have htrivial : ∀ (g : ρ.ker) (m : MK.toSubmodule),
        q (MK.toRepresentation g m)=q m := by
      intro g m
      change q (M.toRepresentation (g:G) m)=q m
      rw [Representation.IntertwiningMap.isIntertwining _ _ q]
      have hg : ρ (g:G)=1 := g.property
      rw [hg]
      rfl
    have hb := twoGroup_permutation_trivial_quotient_finrank_le
      (hG.to_subgroup ρ.ker) 3 (by simpa using hX) x MK q.toLinearMap hq htrivial
    norm_num at hb
    omega
  have hclasses : Nat.card (MulAction.orbitRel.Quotient ρ.ker X)=2 := by omega
  have hsize : Nat.card (MulAction.orbit ρ.ker x)=4 := by
    have hm := normal_orbit_card_mul_classes ρ.ker x
    rw [hclasses,hX] at hm
    omega
  exact ⟨hclasses,fun o => (normal_orbit_card_eq ρ.ker x o).trans hsize⟩

/-- The common-character branch supplies the original index internally. -/
theorem permutationBinary_twoBlockCharacter_orbits
    (hG : IsPGroup 2 G) (x : X) (hX : Nat.card X=8)
    (ρ : Representation (ZMod 2) G A)
    (M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))
    (q : M.toRepresentation.IntertwiningMap ρ) (hq : Function.Surjective q)
    (hA : Module.finrank (ZMod 2) A=4)
    (data : RepresentationBinaryCommonCharacter.TwoBlockCharacter ρ) :
    Nat.card (MulAction.orbitRel.Quotient ρ.ker X)=2 ∧
      ∀ o : MulAction.orbitRel.Quotient ρ.ker X, Nat.card o.orbit=4 :=
  permutationBinary_section_kernel_two_orbits hG x hX ρ M q hq hA.ge data.kernel_index

end SymmetricSubgroupAsymptotics
