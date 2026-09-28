import SymmetricSubgroupAsymptotics.RepresentationJointDisplacement
import SymmetricSubgroupAsymptotics.PermutationOrbitHeadSection
import SymmetricSubgroupAsymptotics.RepresentationGeneratorHead
import SymmetricSubgroupAsymptotics.TerminalContraction

/-!
# The exact two-step unipotent section

The preimage of the invariants after quotienting by all original invariants
has dimension `t + ell`.  Its action has exponent two in characteristic two,
so the literal binary residual fixes it pointwise.  Pulling it back through
the original permutation section reduces its `3/8` budget to local head caps
on the actual residual orbits.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics

variable {G A : Type} [Group G] [Finite G]
    [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]

/-- The literal preimage of the fixed space of `A/A^G`, as an original
`G`-subrepresentation. -/
def fixedDisplacementPreimageSubrepresentation
    (ρ : Representation (ZMod 2) G A) : Subrepresentation ρ where
  toSubmodule := displacementPreimage ρ ρ.invariants
  apply_mem_toSubmodule g v hv := by
    apply (centralQuotient_mem_invariants_iff ρ ρ.invariants le_rfl _).mp
    have hvQ :=
      (centralQuotient_mem_invariants_iff ρ ρ.invariants le_rfl v).mpr hv
    change (centralQuotientRepresentation ρ ρ.invariants le_rfl) g
      (ρ.invariants.mkQ v) ∈
        (centralQuotientRepresentation ρ ρ.invariants le_rfl).invariants
    rw [hvQ g]
    exact hvQ

/-- Its dimension is exactly the fixed dimension plus the full retained
displacement dimension. -/
theorem fixedDisplacementPreimage_finrank
    (ρ : Representation (ZMod 2) G A) :
    Module.finrank (ZMod 2)
        (fixedDisplacementPreimageSubrepresentation ρ).toSubmodule =
      Module.finrank (ZMod 2) ρ.invariants +
        Module.finrank (ZMod 2) (displacementSlice ρ ρ.invariants) := by
  have hd := (displacementToSlice ρ ρ.invariants).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr
      (displacementToSlice_surjective ρ ρ.invariants),
    finrank_top, displacementToSlice_ker,
    (Submodule.comapSubtypeEquivOfLe
      (invariants_le_displacementPreimage ρ ρ.invariants)).finrank_eq] at hd
  exact hd.symm.trans (Nat.add_comm _ _)

/-- Every element acts with square one on the exact two-step preimage. -/
theorem fixedDisplacementPreimage_action_sq
    (ρ : Representation (ZMod 2) G A) (g : G)
    (v : (fixedDisplacementPreimageSubrepresentation ρ).toSubmodule) :
    (fixedDisplacementPreimageSubrepresentation ρ).toRepresentation (g ^ 2) v = v := by
  apply Subtype.ext
  change ρ (g ^ 2) (v : A) = v
  rw [pow_two, map_mul, Module.End.mul_apply]
  have hd : ρ g (v : A) - v ∈ ρ.invariants := v.property g
  have hfix := hd g
  have hneg (w : A) : -w = w := by
    calc
      -w = (-(1 : ZMod 2)) • w := by simp only [neg_smul, one_smul]
      _ = w := by rw [ZMod.neg_eq_self_mod_two, one_smul]
  have hadd (w : A) : w + w = 0 := by
    simpa only [two_nsmul] using ZModModule.char_nsmul_eq_zero 2 w
  change ρ g (ρ g (v : A)) = v
  calc
    ρ g (ρ g (v : A)) = ρ g ((v : A) + (ρ g (v : A) - v)) := by
      congr 1
      symm
      rw [sub_eq_add_neg, hneg]
      calc
        (v : A) + (ρ g (v : A) + v) = ρ g (v : A) + (v + v) := by abel
        _ = ρ g (v : A) := by rw [hadd, add_zero]
    _ = ρ g (v : A) + ρ g (ρ g (v : A) - v) := map_add _ _ _
    _ = ρ g (v : A) + (ρ g (v : A) - v) := by rw [hfix]
    _ = v := by
      rw [sub_eq_add_neg, hneg]
      calc
        ρ g (v : A) + (ρ g (v : A) + v) =
            (ρ g (v : A) + ρ g (v : A)) + v := by abel
        _ = v := by rw [hadd, zero_add]

/-- The action quotient on the exact preimage is a `2`-group. -/
theorem fixedDisplacementPreimage_action_quotient_isPGroup
    (ρ : Representation (ZMod 2) G A) :
    IsPGroup 2 (G ⧸
      (representationGroupAction
        (fixedDisplacementPreimageSubrepresentation ρ).toRepresentation).ker) := by
  intro z
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (representationGroupAction
      (fixedDisplacementPreimageSubrepresentation ρ).toRepresentation).ker z
  refine ⟨1, ?_⟩
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  change representationGroupAction
    (fixedDisplacementPreimageSubrepresentation ρ).toRepresentation
      (g ^ (2 ^ 1)) = 1
  apply MulEquiv.ext
  intro v
  apply Multiplicative.toAdd.injective
  change (fixedDisplacementPreimageSubrepresentation ρ).toRepresentation
      (g ^ (2 ^ 1)) v.toAdd = v.toAdd
  simpa using fixedDisplacementPreimage_action_sq ρ g v.toAdd

/-- The literal binary residual `O²(G)` fixes the whole exact two-step
preimage pointwise. -/
theorem terminalTwoResidual_fixedDisplacementPreimage_fixed
    (ρ : Representation (ZMod 2) G A)
    (g : terminalTwoResidual G)
    (v : (fixedDisplacementPreimageSubrepresentation ρ).toSubmodule) :
    (fixedDisplacementPreimageSubrepresentation ρ).toRepresentation
      (g : G) v = v := by
  let τ := (fixedDisplacementPreimageSubrepresentation ρ).toRepresentation
  let f := representationGroupAction τ
  have hker : terminalTwoResidual G ≤ f.ker :=
    terminalTwoResidual_le G f.ker
      (fixedDisplacementPreimage_action_quotient_isPGroup ρ)
  have hg : f (g : G) = 1 := hker g.property
  have hv := congrArg (fun e : MulAut (Multiplicative
      (fixedDisplacementPreimageSubrepresentation ρ).toSubmodule) =>
    e (Multiplicative.ofAdd v)) hg
  exact congrArg Multiplicative.toAdd hv

variable {X : Type} [Finite X] [MulAction G X]

/-- Local head caps on all actual orbits of any subgroup fixing the exact
two-step preimage give the corresponding weighted global budget. -/
theorem permutationSection_fixedDisplacementPreimage_weighted_le_orbit_caps
    (ρ : Representation (ZMod 2) G A)
    (M : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) G X))
    (q : M.toRepresentation.IntertwiningMap ρ)
    (hq : Function.Surjective q)
    (K : Subgroup G)
    (hKfixed : ∀ (g : K)
      (v : (fixedDisplacementPreimageSubrepresentation ρ).toSubmodule),
      (fixedDisplacementPreimageSubrepresentation ρ).toRepresentation
        (g : G) v = v)
    (a b : ℕ)
    (cap : MulAction.orbitRel.Quotient K X → ℕ)
    (hcap : ∀ (o : MulAction.orbitRel.Quotient K X)
      (S : Subrepresentation
        (permutationFunctionRepresentation (ZMod 2) K o.orbit)),
      Module.finrank (ZMod 2) (S.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) K (ZMod 2))) ≤ cap o)
    (hweight : ∀ o : MulAction.orbitRel.Quotient K X,
      b * cap o ≤ a * Nat.card o.orbit) :
    b * (Module.finrank (ZMod 2) ρ.invariants +
      Module.finrank (ZMod 2) (displacementSlice ρ ρ.invariants)) ≤
        a * Nat.card X := by
  let W := (fixedDisplacementPreimageSubrepresentation ρ).toSubmodule
  let P : Submodule (ZMod 2) M.toSubmodule := W.comap q.toLinearMap
  have hfixed (g : K) (v : M.toSubmodule) (hv : v ∈ P) :
      q (M.toRepresentation (g : G) v) = q v :=
    (Representation.IntertwiningMap.isIntertwining _ _ q (g : G) v).trans
      (congrArg Subtype.val (hKfixed g ⟨q v, hv⟩))
  let M' : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) K X) := {
    toSubmodule := P.map M.toSubmodule.subtype
    apply_mem_toSubmodule := by
      intro g v hv
      obtain ⟨v, hv, rfl⟩ := hv
      refine ⟨M.toRepresentation (g : G) v, ?_, rfl⟩
      change q (M.toRepresentation (g : G) v) ∈ W
      rw [hfixed g v hv]
      exact hv }
  let e : P ≃ₗ[ZMod 2] M'.toSubmodule :=
    M.toSubmodule.equivSubtypeMap P
  let qP : P →ₗ[ZMod 2] W :=
    (q.toLinearMap.comp P.subtype).codRestrict W (fun v => v.property)
  have hqP : Function.Surjective qP := by
    intro w
    obtain ⟨v, hv⟩ := hq (w : A)
    have hvP : v ∈ P := by
      change q v ∈ W
      rw [hv]
      exact w.property
    exact ⟨⟨v, hvP⟩, Subtype.ext hv⟩
  let qM : M'.toSubmodule →ₗ[ZMod 2] W := qP.comp e.symm.toLinearMap
  have hqM : Function.Surjective qM := hqP.comp e.symm.surjective
  have htrivial : ∀ (g : K) (m : M'.toSubmodule),
      qM (M'.toRepresentation g m) = qM m := by
    intro g m
    apply Subtype.ext
    change q (e.symm (M'.toRepresentation g m) : M.toSubmodule) =
      q (e.symm m : M.toSubmodule)
    have he : (e.symm (M'.toRepresentation g m) : M.toSubmodule) =
        M.toRepresentation (g : G) (e.symm m : M.toSubmodule) := by
      apply Subtype.ext
      rfl
    rw [he]
    exact hfixed g (e.symm m : M.toSubmodule) (e.symm m).property
  have hb := permutation_trivial_quotient_weighted_finrank_le
    a b cap hcap hweight M' qM hqM htrivial
  change b * Module.finrank (ZMod 2) W ≤ a * Nat.card X at hb
  rw [fixedDisplacementPreimage_finrank] at hb
  exact hb

/-- Specialization to the literal binary residual and the `3/8` local
orbit budget. -/
theorem binary_permutationSection_unipotent_of_residual_orbit_caps
    (ρ : Representation (ZMod 2) G A)
    (M : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) G X))
    (q : M.toRepresentation.IntertwiningMap ρ)
    (hq : Function.Surjective q)
    (cap : MulAction.orbitRel.Quotient (terminalTwoResidual G) X → ℕ)
    (hcap : ∀ (o : MulAction.orbitRel.Quotient (terminalTwoResidual G) X)
      (S : Subrepresentation
        (permutationFunctionRepresentation (ZMod 2)
          (terminalTwoResidual G) o.orbit)),
      Module.finrank (ZMod 2) (S.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2)
          (terminalTwoResidual G) (ZMod 2))) ≤ cap o)
    (hweight : ∀ o : MulAction.orbitRel.Quotient (terminalTwoResidual G) X,
      8 * cap o ≤ 3 * Nat.card o.orbit) :
    8 * (Module.finrank (ZMod 2) ρ.invariants +
      Module.finrank (ZMod 2) (displacementSlice ρ ρ.invariants)) ≤
        3 * Nat.card X := by
  exact permutationSection_fixedDisplacementPreimage_weighted_le_orbit_caps
    ρ M q hq (terminalTwoResidual G)
    (terminalTwoResidual_fixedDisplacementPreimage_fixed ρ)
    3 8 cap hcap hweight

end SymmetricSubgroupAsymptotics

end
