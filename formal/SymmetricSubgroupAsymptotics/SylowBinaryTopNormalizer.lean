import Mathlib.GroupTheory.Sylow

/-! A Sylow-three normalizer supplements the kernel of an actual binary
quotient. In a faithful transitive binary quotient action, it therefore
contains an element moving every block. All maps are the original maps. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.SylowBinaryTopNormalizer

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {G T : Type} [Group G] [Finite G] [Group T]
    (beta : G →* T) (hbeta : Function.Surjective beta)
    (hT : IsPGroup 2 T) (P : Sylow 3 G)

include hT in
theorem sylow_le_kernel : (P : Subgroup G) ≤ beta.ker := by
  let S : Subgroup T := (P : Subgroup G).map beta
  have hS3 : IsPGroup 3 S := P.isPGroup'.map beta
  have hS2 : IsPGroup 2 S := hT.to_subgroup S
  have hbot : S = ⊥ := disjoint_self.mp
    (IsPGroup.disjoint_of_ne 2 3 (by decide) S S hS2 hS3)
  intro x hx
  have hi : beta x ∈ S := ⟨x, hx, rfl⟩
  rw [hbot] at hi
  exact hi

include hbeta hT in
theorem normalizer_surjective : Function.Surjective
    (beta.comp (Subgroup.normalizer (P : Set G)).subtype) := by
  apply MonoidHom.range_eq_top.mp
  rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [(Subgroup.map_eq_range_iff).mpr
    (show Codisjoint (Subgroup.normalizer (P : Set G)) beta.ker from
      codisjoint_iff.mpr (P.normalizer_sup_eq_top' (sylow_le_kernel beta hT P)))]
  exact MonoidHom.range_eq_top.mpr hbeta

variable {I : Type} [MulAction T I] [MulAction.IsPretransitive T I]
    [FaithfulSMul T I] [Nontrivial I]

include hbeta hT in
/-- Centrality and transitivity turn a nonidentity central top element
into a fixed-point-free block permutation, and Frattini lifts that very
element inside the original Sylow normalizer. -/
theorem exists_moving_normalizer : ∃ g : G,
    g ∈ Subgroup.normalizer (P : Set G) ∧ ∀ i : I, beta g • i ≠ i := by
  letI : Finite T := Finite.of_surjective beta hbeta
  letI : Nontrivial T := by
    obtain ⟨i, j, hij⟩ := exists_pair_ne I
    obtain ⟨t, ht⟩ := MulAction.exists_smul_eq T i j
    refine ⟨⟨t, 1, ?_⟩⟩
    intro he
    have : i = j := by simpa only [he, one_smul] using ht
    exact hij this
  letI : Nontrivial (Subgroup.center T) := hT.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center T)
  have hzne : (z : T) ≠ 1 := fun h => hz (Subtype.ext h)
  have hmove : ∀ i : I, (z : T) • i ≠ i := by
    intro i hi
    apply hzne
    apply eq_of_smul_eq_smul (α := I)
    intro j
    obtain ⟨t, rfl⟩ := MulAction.exists_smul_eq T i j
    have hc : (z : T) * t = t * (z : T) :=
      (Subgroup.mem_center_iff.mp z.2 t).symm
    simpa only [one_smul] using
      (calc
        (z : T) • (t • i) = ((z : T) * t) • i := (mul_smul _ _ _).symm
        _ = (t * (z : T)) • i := congrArg (fun a : T => a • i) hc
        _ = t • ((z : T) • i) := mul_smul _ _ _
        _ = t • i := congrArg (fun a : I => t • a) hi)
  obtain ⟨g, hg⟩ := normalizer_surjective beta hbeta hT P (z : T)
  refine ⟨g, g.2, ?_⟩
  intro i
  change beta g.1 • i ≠ i
  change beta g.1 = (z : T) at hg
  rw [hg]
  exact hmove i

end SymmetricSubgroupAsymptotics.SylowBinaryTopNormalizer

end
