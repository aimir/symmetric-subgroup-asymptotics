import SymmetricSubgroupAsymptotics.CFSGTwistedAEndpointDerivedWords
import SymmetricSubgroupAsymptotics.CFSGTypeAPrimitiveUnitSquare
import SymmetricSubgroupAsymptotics.CFSGSimpleProjectiveDescent

/-! Nontriviality of the original twisted-A derived project's actual
natural action image, for every rank >=3. Source simplicity is used ONLY
in the final descent and is the original twisted model's own instance.
Rank two, with adjacent reversed nodes, is not included. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
open CFSGTwistedAFirstBlock CFSGTwistedASLTwoDerivedWitness

theorem endpoint_delta_commutator_not_scalar (s : ℕ) (q : CFSG.PrimePower)
    (a : q.Extension 2) (ha : a ≠ 0) (hsquare : a ^ 2 ≠ 1) :
    ¬ ∃ c : q.Extension 2,
      ((⁅endpointDelta s q 1, endpointDelta s q a⁆).val : Mat (q.Extension 2) (s + 3)) =
        c • (1 : Mat (q.Extension 2) (s + 3)) := by
  rintro ⟨c, hc⟩
  apply delta_commutator_not_scalar a ha hsquare
  change ((⁅endpointDeltaRow s q 1, endpointDeltaRow s q a⁆).val :
    Mat (q.Extension 2) (s + 3)) = c • 1 at hc
  have hb := congrArg (block (q.Extension 2) s) hc
  change (blockHom (q.Extension 2) s
    ⁅endpointDeltaRow s q 1, endpointDeltaRow s q a⁆ :
      Matrix (Fin 2) (Fin 2) (q.Extension 2)) = block (q.Extension 2) s (c • 1) at hb
  rw [map_commutatorElement, endpointDeltaRow_block, endpointDeltaRow_block, block_scalar] at hb
  exact ⟨c, hb⟩

theorem endpoint_derived_image_not_center (s : ℕ) (q : CFSG.PrimePower) :
    (twistedDerivedAction (s + 3) q).rangeRestrict (endpointDerivedWord s q 1) ∉
      Subgroup.center (twistedDerivedAction (s + 3) q).range := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hcard : 4 ≤ Nat.card (q.Extension 2) := by
    rw [extension_two_card]
    exact Nat.pow_le_pow_left hq 2
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := (q.Extension 2)ˣ)
  have hsquare : (a : q.Extension 2) ^ 2 ≠ 1 :=
    CFSGTypeAPrimitiveUnitSquare.square_ne_one hcard a ha
  intro hc
  have hh := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hc)
    ((twistedDerivedAction (s + 3) q).rangeRestrict (endpointDerivedWord s q a)))
  change twistedDerivedAction (s + 3) q (endpointDerivedWord s q a) *
      twistedDerivedAction (s + 3) q (endpointDerivedWord s q 1) =
    twistedDerivedAction (s + 3) q (endpointDerivedWord s q 1) *
      twistedDerivedAction (s + 3) q (endpointDerivedWord s q a) at hh
  rw [endpointDerivedWord_image, endpointDerivedWord_image] at hh
  have hcomm : ⁅naturalElementaryAction (q.Extension 2) (s + 3) (endpointDelta s q 1),
      naturalElementaryAction (q.Extension 2) (s + 3) (endpointDelta s q a)⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr hh.symm
  have hk : ⁅endpointDelta s q 1, endpointDelta s q a⁆ ∈
      (naturalElementaryAction (q.Extension 2) (s + 3)).ker := by
    change naturalElementaryAction (q.Extension 2) (s + 3) _ = 1
    rw [map_commutatorElement]
    exact hcomm
  rw [naturalElementaryAction_ker (q.Extension 2) (s + 3) (by omega)] at hk
  exact endpoint_delta_commutator_not_scalar s q a (Units.ne_zero a) hsquare
    ((naturalElementary_center_iff_scalar (q.Extension 2) (s + 3) (by omega) _).mp hk)

theorem derived_natural_projective_nontrivial (s : ℕ) (q : CFSG.PrimePower) :
    Nontrivial ((twistedDerivedAction (s + 3) q).range ⧸
      Subgroup.center (twistedDerivedAction (s + 3) q).range) := by
  let f := twistedDerivedAction (s + 3) q
  let π := QuotientGroup.mk' (Subgroup.center f.range)
  have hn : π (f.rangeRestrict (endpointDerivedWord s q 1)) ≠ 1 := by
    intro h
    exact endpoint_derived_image_not_center s q ((QuotientGroup.eq_one_iff _).mp h)
  exact ⟨⟨π (f.rangeRestrict (endpointDerivedWord s q 1)), 1, hn⟩⟩

def twistedA_natural_projective_equiv (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedA (s + 3) q)] :
    CFSG.Models.TwistedA (s + 3) q ≃*
      ((twistedDerivedAction (s + 3) q).range ⧸
        Subgroup.center (twistedDerivedAction (s + 3) q).range) := by
  letI := derived_natural_projective_nontrivial s q
  exact CFSGSimpleProjectiveDescent.projectiveEquivOfSimple
    (twistedDerivedAction (s + 3) q).rangeRestrict
      (twistedDerivedAction (s + 3) q).rangeRestrict_surjective

theorem twistedA_natural_projective_map_injective (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedA (s + 3) q)] :
    Function.Injective (CFSGSimpleProjectiveDescent.projectiveMap
      (twistedDerivedAction (s + 3) q).rangeRestrict
        (twistedDerivedAction (s + 3) q).rangeRestrict_surjective) := by
  letI := derived_natural_projective_nontrivial s q
  exact CFSGSimpleProjectiveDescent.projectiveMap_injective _ _

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
