import SymmetricSubgroupAsymptotics.PermutationBinaryFourRegular

/-! The extremal fixed-quotient conclusion for a possibly nonfaithful
original action. The complete displacement evaluation kernel equals
the literal original permutation-action kernel. Consequently it is the
actual permutation image, rather than a replacement acting group, that
has the physical degree's cardinality.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.PermutationBinaryFourRegular

variable {G X : Type} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] [Finite G] [Finite X]

local notation "ρ" => permutationFunctionRepresentation (ZMod 2) G X

/-- Without faithfulness, the same singleton-orbit argument identifies
the complete character kernel with the original action kernel exactly. -/
theorem displacementEvaluation_ker_eq_permutation_ker_of_maximal_fixed_quotient
    (x : X) (a : ℕ) (hcard : Nat.card X=2^a)
    (hdim : Module.finrank (ZMod 2)
      (centralQuotientRepresentation ρ (ρ).invariants le_rfl).invariants=a) :
    (displacementEvaluation (G := G) x).ker=(MulAction.toPermHom G X).ker := by
  apply le_antisymm
  · intro g hg
    change MulAction.toPermHom G X g=1
    apply Equiv.ext
    intro y
    change g • y=y
    let o : MulAction.orbitRel.Quotient (displacementEvaluation (G := G) x).ker X :=
      Quotient.mk'' y
    have ho := retainedCharacterKernel_orbit_card 2 (displacementCharactersAt x) x
      (displacementCharactersAt_injective x) a hcard o
    rw [retainedStabilizerVanishing_eq_top,finrank_top,
      displacementSlice_invariants_finrank,hdim,Nat.sub_self,pow_zero] at ho
    have hy : Fintype.card (MulAction.orbit (displacementEvaluation (G := G) x).ker y)=1 := by
      simpa only [Fintype.card_eq_nat_card] using ho
    have hfixed := MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mpr hy
    exact MulAction.mem_fixedPoints.mp hfixed ⟨g,hg⟩
  · intro g hg
    apply (mem_retainedCharacterEvaluation_ker_iff 2 (displacementCharactersAt x) g).mpr
    intro f
    apply displacementCharactersAt_stabilizer x f g
    apply MulAction.mem_stabilizer_iff.mpr
    have he : MulAction.toPermHom G X g=1 := hg
    exact congrArg (fun e : Equiv.Perm X => e x) he

/-- Original-image order from the unchanged action and its original
permutation quotient. The acting group itself may have a nontrivial kernel. -/
theorem image_card_eq_degree_of_maximal_fixed_quotient
    (x : X) (a : ℕ) (hcard : Nat.card X=2^a)
    (hdim : Module.finrank (ZMod 2)
      (centralQuotientRepresentation ρ (ρ).invariants le_rfl).invariants=a) :
    Nat.card (MulAction.toPermHom G X).range=2^a := by
  calc
    Nat.card (MulAction.toPermHom G X).range =
        Nat.card (G ⧸ (MulAction.toPermHom G X).ker) :=
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange
        (MulAction.toPermHom G X)).toEquiv).symm
    _ = Nat.card (G ⧸ (displacementEvaluation x).ker) := by
      rw [displacementEvaluation_ker_eq_permutation_ker_of_maximal_fixed_quotient
        x a hcard hdim]
    _ = Nat.card (Multiplicative (Module.Dual (ZMod 2)
        (displacementSlice ρ (ρ).invariants))) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
        (displacementEvaluation x) (displacementEvaluation_surjective x)).toEquiv
    _ = 2^a := by
      change Nat.card (Module.Dual (ZMod 2) (displacementSlice ρ (ρ).invariants))=2^a
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
        Subspace.dual_finrank_eq,displacementSlice_invariants_finrank,hdim]

end SymmetricSubgroupAsymptotics.PermutationBinaryFourRegular
