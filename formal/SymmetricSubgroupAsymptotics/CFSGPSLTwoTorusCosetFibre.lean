import SymmetricSubgroupAsymptotics.CFSGPSLTwoBorelCardinality
import SymmetricSubgroupAsymptotics.CFSGPSLTwoFixedRootKernel

/-! Actual torus transport on the Borel cover. No independent action on
cover fibres and no global kernel-normality hypothesis are used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoTorusCosetFibre
open CFSGPSLTwoGeometry CFSGPSLTwoRootCoordinates
variable {F : Type*} [Field F]

/-- The actual torus covers B/H whenever H contains the upper root group. -/
theorem exists_torus_coset_rep (H : Subgroup (PSL (F:=F)))
    (hroot : projectiveRoot (F:=F) ≤ H) (b : projectiveBorel (F:=F)) :
    ∃ t : pairTorus (F:=F),
      (QuotientGroup.mk b.val : PSL (F:=F) ⧸ H) = QuotientGroup.mk t.val := by
  obtain ⟨⟨t,u⟩,htu⟩ := borelProduct_surjective b
  have hv : t.val*u.val=b.val := congrArg Subtype.val htu
  refine ⟨t, QuotientGroup.eq.mpr ?_⟩
  change b.val⁻¹*t.val ∈ H
  rw [←hv]
  simpa only [mul_inv_rev,mul_assoc,inv_mul_cancel,mul_one] using
    H.inv_mem (hroot u.property)

/-- A normalizing Weyl representative transports those same actual torus
representatives to the complete fibre over gB. -/
theorem exists_torus_move_over_representative
    (H : Subgroup (PSL (F:=F))) (hroot : projectiveRoot (F:=F) ≤ H)
    (g : PSL (F:=F))
    (hconj : ∀ t : pairTorus (F:=F), g*t.val*g⁻¹ ∈ pairTorus (F:=F))
    (b : projectiveBorel (F:=F)) :
    ∃ n : pairTorus (F:=F),
      n.val • (QuotientGroup.mk g : PSL (F:=F) ⧸ H) = QuotientGroup.mk (g*b.val) := by
  obtain ⟨t,ht⟩ := exists_torus_coset_rep H hroot b
  let n : pairTorus (F:=F) := ⟨g*t.val*g⁻¹,hconj t⟩
  refine ⟨n, ?_⟩
  have hleft := congrArg (fun q : PSL (F:=F) ⧸ H => g • q) ht
  change (QuotientGroup.mk (g*b.val) : PSL (F:=F) ⧸ H) =
    QuotientGroup.mk (g*t.val) at hleft
  change (QuotientGroup.mk ((g*t.val*g⁻¹)*g) : PSL (F:=F) ⧸ H) = _
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hleft.symm

/-- Literal Weyl conjugation preserves the original torus. -/
theorem weyl_conjugates_torus (t : pairTorus (F:=F)) :
    projectiveWeyl*t.val*(projectiveWeyl (F:=F))⁻¹ ∈ pairTorus (F:=F) := by
  obtain ⟨c,hc⟩ := t.property
  rw [←hc]
  change projectiveWeyl*projectiveTorus c*(projectiveWeyl (F:=F))⁻¹ ∈ pairTorus (F:=F)
  rw [projective_weyl_torus]
  exact ⟨c⁻¹,rfl⟩

/-- Complete actual fibre transport at the nonidentity Bruhat representative. -/
theorem exists_torus_move_over_weyl
    (H : Subgroup (PSL (F:=F))) (hroot : projectiveRoot (F:=F) ≤ H)
    (b : projectiveBorel (F:=F)) :
    ∃ n : pairTorus (F:=F),
      n.val • (QuotientGroup.mk (projectiveWeyl (F:=F)) : PSL (F:=F) ⧸ H) =
        QuotientGroup.mk (projectiveWeyl*b.val) :=
  exists_torus_move_over_representative H hroot projectiveWeyl weyl_conjugates_torus b

end SymmetricSubgroupAsymptotics.CFSGPSLTwoTorusCosetFibre
