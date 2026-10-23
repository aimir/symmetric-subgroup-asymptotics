import SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicBlockMembership
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeChainLift

/-! The same literal smaller split-D block belongs to the independently
retained relative-root subgroup. Every generator has an explicit chain
or paired-Weyl conjugate witness; the original Derived preimage is not
used as a substitute for this stronger word membership. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeBlockMembership
open CFSGOrthogonalDSerreMatrices CFSGTwistedDHyperbolicBlockMatrices
open CFSGTwistedDHyperbolicBlockRootCoordinates CFSGTwistedDHyperbolicBlockMembership
open CFSGOrthogonalDMatrixScalarExtension CFSGTwistedA2FixedField
open CFSGTwistedDPairedWeyl CFSGTwistedDRelativeChainLift CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDA2MatrixWitness CFSGOrthogonalDGenerationForkTorus

theorem root_has_relative_lift (s : ℕ) (q : CFSG.PrimePower)
    (neg : Bool) (i : Fin (s + 3)) (a : fixedField q) :
    ∃ g : elementaryRootGroup (q.Extension 2) (s + 4),
      g ∈ relativePreimage s q ∧
      g.val = scalarBlockHom s q (rootTransvection (fixedField q) (s + 3) neg i a) := by
  by_cases hi : i.val + 1 < s + 3
  · let j : Fin (s + 3) := ⟨i.val + 1, hi⟩
    have hij : i ≠ j := by
      intro h
      have hh := congrArg Fin.val h
      change i.val = i.val + 1 at hh
      omega
    cases neg
    · refine ⟨chain (q.Extension 2) (s + 4) i.castSucc j.castSucc
        ((Fin.castSucc_injective (s + 3)).ne hij) (a : q.Extension 2),
        CFSGTwistedDRelativeChainLift.chain_mem s q i j hij a, ?_⟩
      apply Units.ext
      change ((chain (q.Extension 2) (s + 4) i.castSucc j.castSucc _
        (a : q.Extension 2)).val : Mat (q.Extension 2) (s + 4)) =
        (blockUnitHom (q.Extension 2) (s + 3)
          (scalarUnitHom (fixedField q).subtype (s + 3)
            (rootTransvection (fixedField q) (s + 3) false i a)) : Mat (q.Extension 2) (s + 4))
      rw [scalarUnitHom_root, block_chain_positive (q.Extension 2) (s + 3) i hi, CFSGTwistedDRetainedForkRoots.chain_val]
      rfl
    · refine ⟨chain (q.Extension 2) (s + 4) j.castSucc i.castSucc
        ((Fin.castSucc_injective (s + 3)).ne (Ne.symm hij)) (a : q.Extension 2),
        CFSGTwistedDRelativeChainLift.chain_mem s q j i (Ne.symm hij) a, ?_⟩
      apply Units.ext
      change ((chain (q.Extension 2) (s + 4) j.castSucc i.castSucc _
        (a : q.Extension 2)).val : Mat (q.Extension 2) (s + 4)) =
        (blockUnitHom (q.Extension 2) (s + 3)
          (scalarUnitHom (fixedField q).subtype (s + 3)
            (rootTransvection (fixedField q) (s + 3) true i a)) : Mat (q.Extension 2) (s + 4))
      rw [scalarUnitHom_root, block_chain_negative (q.Extension 2) (s + 3) i hi, CFSGTwistedDRetainedForkRoots.chain_val]
      rfl
  · have hilast : i = Fin.last (s + 2) := by
      apply Fin.ext
      have := i.isLt
      simp only [Fin.val_last]
      omega
    subst i
    have hij := beforeLast_ne_last s
    have hp : (beforeLast s).castSucc ≠ pen (s + 2) := by
      change (beforeLast s).castSucc ≠ (Fin.last (s + 2)).castSucc
      exact (Fin.castSucc_injective (s + 3)).ne hij
    have hl : (beforeLast s).castSucc ≠ last (s + 2) := by
      exact Fin.castSucc_ne_last _
    have hpen : (Fin.last (s + 2)).castSucc = pen (s + 2) := rfl
    cases neg
    · let g := pairedWeyl s q *
        chain (q.Extension 2) (s + 4) (beforeLast s).castSucc (Fin.last (s + 2)).castSucc
          ((Fin.castSucc_injective (s + 3)).ne hij) ((-a : fixedField q) : q.Extension 2) *
        (pairedWeyl s q)⁻¹
      refine ⟨g, CFSGTwistedDRelativeChainLift.conjugate_chain_mem s q (beforeLast s) (Fin.last (s + 2)) hij (-a), ?_⟩
      apply Units.ext
      change (g.val : Mat (q.Extension 2) (s + 4)) =
        (blockUnitHom (q.Extension 2) (s + 3)
          (scalarUnitHom (fixedField q).subtype (s + 3)
            (rootTransvection (fixedField q) (s + 3) false (Fin.last (s + 2)) a)) :
              Mat (q.Extension 2) (s + 4))
      rw [scalarUnitHom_root, block_fork_positive]
      simpa only [g, hpen] using
        CFSGTwistedDRetainedForkRoots.conjugation_positive s q (beforeLast s).castSucc hp hl (a : q.Extension 2)
    · let g := pairedWeyl s q *
        chain (q.Extension 2) (s + 4) (Fin.last (s + 2)).castSucc (beforeLast s).castSucc
          ((Fin.castSucc_injective (s + 3)).ne (Ne.symm hij))
          ((-a : fixedField q) : q.Extension 2) * (pairedWeyl s q)⁻¹
      refine ⟨g, CFSGTwistedDRelativeChainLift.conjugate_chain_mem s q (Fin.last (s + 2)) (beforeLast s) (Ne.symm hij) (-a), ?_⟩
      apply Units.ext
      change (g.val : Mat (q.Extension 2) (s + 4)) =
        (blockUnitHom (q.Extension 2) (s + 3)
          (scalarUnitHom (fixedField q).subtype (s + 3)
            (rootTransvection (fixedField q) (s + 3) true (Fin.last (s + 2)) a)) :
              Mat (q.Extension 2) (s + 4))
      rw [scalarUnitHom_root, block_fork_negative]
      simpa only [g, hpen] using
        CFSGTwistedDRetainedForkRoots.conjugation_negative s q (beforeLast s).castSucc hp hl (a : q.Extension 2)

theorem scalarBlockHom_maps_relative (s : ℕ) (q : CFSG.PrimePower) :
    elementaryRootGroup (fixedField q) (s + 3) ≤
      (relativeRootGroup (s + 2) q).comap (scalarBlockHom s q) := by
  apply (Subgroup.closure_le _).mpr
  rintro u ⟨neg, i, a, rfl⟩
  obtain ⟨g, hg, he⟩ := root_has_relative_lift s q neg i a
  change scalarBlockHom s q (rootTransvection (fixedField q) (s + 3) neg i a) ∈
    relativeRootGroup (s + 2) q
  rw [← he]
  exact hg

theorem exists_relative_lift (s : ℕ) (q : CFSG.PrimePower)
    (g : elementaryRootGroup (fixedField q) (s + 3)) :
    ∃ u : relativePreimage s q, u.val.val = scalarBlockHom s q g.val := by
  have hr := scalarBlockHom_maps_relative s q g.property
  have he := relativeRootGroup_le_elementary (s + 2) q hr
  exact ⟨⟨⟨scalarBlockHom s q g.val, he⟩, hr⟩, rfl⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeBlockMembership
