import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankBlockRootCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankConjugateFork
import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankChainLift
import SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicBlockRootCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDMatrixScalarExtension

/-! The entire smaller split-D group over the actual fixed field has a
literal relative-root block embedding, already D2 into relative rank3.
Terminal generators have explicit paired-Weyl conjugate witnesses. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankBlockMembership
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDHyperbolicBlockMatrices CFSGOrthogonalDMatrixScalarExtension
open CFSGTwistedDAllRankBlockRootCoordinates CFSGTwistedDHyperbolicBlockRootCoordinates
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDAllRankPairedWeyl
open CFSGTwistedDA2MatrixWitness CFSGTwistedA2FixedField

def scalarBlockHom (n : ℕ) (q : CFSG.PrimePower) :
    (Mat (fixedField q) (n + 2))ˣ →* (Mat (q.Extension 2) (n + 3))ˣ :=
  (blockUnitHom (q.Extension 2) (n + 2)).comp
    (scalarUnitHom (fixedField q).subtype (n + 2))

theorem root_mem (n : ℕ) (q : CFSG.PrimePower)
    (neg : Bool) (i : Fin (n + 2)) (a : fixedField q) :
    scalarBlockHom n q (rootTransvection (fixedField q) (n + 2) neg i a) ∈
      relativeRootGroup (n + 1) q := by
  by_cases hi : i.val + 1 < n + 2
  · let j : Fin (n + 2) := ⟨i.val + 1, hi⟩
    have hij : i ≠ j := by
      intro h
      have hh := congrArg Fin.val h
      change i.val = i.val + 1 at hh
      omega
    cases neg
    · have he : scalarBlockHom n q (rootTransvection (fixedField q) (n + 2) false i a) =
          (chain (q.Extension 2) (n + 3) i.castSucc j.castSucc
            ((Fin.castSucc_injective (n + 2)).ne hij) (a : q.Extension 2)).val := by
        apply Units.ext
        change (blockUnitHom (q.Extension 2) (n + 2)
          (scalarUnitHom (fixedField q).subtype (n + 2)
            (rootTransvection (fixedField q) (n + 2) false i a)) : Mat (q.Extension 2) (n + 3)) = _
        rw [scalarUnitHom_root, block_chain_positive _ _ i hi,
          CFSGTwistedDRetainedForkRoots.chain_val]
        rfl
      rw [he]
      exact CFSGTwistedDAllRankChainLift.chain_mem (n + 1) q i j hij a
    · have he : scalarBlockHom n q (rootTransvection (fixedField q) (n + 2) true i a) =
          (chain (q.Extension 2) (n + 3) j.castSucc i.castSucc
            ((Fin.castSucc_injective (n + 2)).ne (Ne.symm hij)) (a : q.Extension 2)).val := by
        apply Units.ext
        change (blockUnitHom (q.Extension 2) (n + 2)
          (scalarUnitHom (fixedField q).subtype (n + 2)
            (rootTransvection (fixedField q) (n + 2) true i a)) : Mat (q.Extension 2) (n + 3)) = _
        rw [scalarUnitHom_root, block_chain_negative _ _ i hi,
          CFSGTwistedDRetainedForkRoots.chain_val]
        rfl
      rw [he]
      exact CFSGTwistedDAllRankChainLift.chain_mem (n + 1) q j i (Ne.symm hij) a
  · have he : i = last n := by
      apply Fin.ext
      have hb := i.isLt
      change i.val = n + 1
      omega
    subst i
    have hj : (last n).castSucc = pen (n + 1) := Fin.ext rfl
    have hneg : ((-a : fixedField q) : q.Extension 2) = -(a : q.Extension 2) := rfl
    have hp : (pen n).castSucc ≠ pen (n + 1) := by
      change (pen n).castSucc ≠ (last n).castSucc
      exact (Fin.castSucc_injective (n + 2)).ne (pen_ne_last n)
    have hl : (pen n).castSucc ≠ last (n + 1) := Fin.castSucc_ne_last (pen n)
    have hc (x : fixedField q) :
        (chain (q.Extension 2) (n + 3) (pen n).castSucc (last n).castSucc
          ((Fin.castSucc_injective (n + 2)).ne (pen_ne_last n)) (x : q.Extension 2)).val ∈
            relativeRootGroup (n + 1) q :=
      CFSGTwistedDAllRankChainLift.chain_mem (n + 1) q (pen n) (last n) (pen_ne_last n) x
    cases neg
    · let g := (weyl (n + 1) q).val *
        (chain (q.Extension 2) (n + 3) (pen n).castSucc (last n).castSucc
          ((Fin.castSucc_injective (n + 2)).ne (pen_ne_last n)) ((-a : fixedField q) : q.Extension 2)).val *
        (weyl (n + 1) q).val⁻¹
      have hg : g ∈ relativeRootGroup (n + 1) q :=
        (relativeRootGroup (n + 1) q).mul_mem
          ((relativeRootGroup (n + 1) q).mul_mem (weyl (n + 1) q).property (hc (-a)))
          ((relativeRootGroup (n + 1) q).inv_mem (weyl (n + 1) q).property)
      have hge : g = scalarBlockHom n q
          (rootTransvection (fixedField q) (n + 2) false (last n) a) := by
        apply Units.ext
        have hm := CFSGTwistedDAllRankConjugateFork.conjugation_positive
          (n + 1) q (pen n).castSucc hp hl (a : q.Extension 2)
        calc
          (g : Mat (q.Extension 2) (n + 3)) =
              1 + Matrix.single (Sum.inl (pen n).castSucc) (Sum.inr (last n).castSucc) (a : q.Extension 2) -
                Matrix.single (Sum.inl (last n).castSucc) (Sum.inr (pen n).castSucc) (a : q.Extension 2) := by
            simpa only [g, hj, hneg] using hm
          _ = _ := by
            change _ = (blockUnitHom (q.Extension 2) (n + 2)
              (scalarUnitHom (fixedField q).subtype (n + 2)
                (rootTransvection (fixedField q) (n + 2) false (last n) a)) : Mat (q.Extension 2) (n + 3))
            rw [scalarUnitHom_root, block_terminal_positive]
            rfl
      exact hge ▸ hg
    · let g := (weyl (n + 1) q).val *
        (chain (q.Extension 2) (n + 3) (last n).castSucc (pen n).castSucc
          ((Fin.castSucc_injective (n + 2)).ne (Ne.symm (pen_ne_last n)))
          ((-a : fixedField q) : q.Extension 2)).val * (weyl (n + 1) q).val⁻¹
      have hrev : (chain (q.Extension 2) (n + 3) (last n).castSucc (pen n).castSucc
          ((Fin.castSucc_injective (n + 2)).ne (Ne.symm (pen_ne_last n)))
          ((-a : fixedField q) : q.Extension 2)).val ∈ relativeRootGroup (n + 1) q :=
        CFSGTwistedDAllRankChainLift.chain_mem (n + 1) q (last n) (pen n) (Ne.symm (pen_ne_last n)) (-a)
      have hg : g ∈ relativeRootGroup (n + 1) q :=
        (relativeRootGroup (n + 1) q).mul_mem
          ((relativeRootGroup (n + 1) q).mul_mem (weyl (n + 1) q).property hrev)
          ((relativeRootGroup (n + 1) q).inv_mem (weyl (n + 1) q).property)
      have hge : g = scalarBlockHom n q
          (rootTransvection (fixedField q) (n + 2) true (last n) a) := by
        apply Units.ext
        have hm := CFSGTwistedDAllRankConjugateFork.conjugation_negative
          (n + 1) q (pen n).castSucc hp hl (a : q.Extension 2)
        calc
          (g : Mat (q.Extension 2) (n + 3)) =
              1 + Matrix.single (Sum.inr (last n).castSucc) (Sum.inl (pen n).castSucc) (a : q.Extension 2) -
                Matrix.single (Sum.inr (pen n).castSucc) (Sum.inl (last n).castSucc) (a : q.Extension 2) := by
            simpa only [g, hj, hneg] using hm
          _ = _ := by
            change _ = (blockUnitHom (q.Extension 2) (n + 2)
              (scalarUnitHom (fixedField q).subtype (n + 2)
                (rootTransvection (fixedField q) (n + 2) true (last n) a)) : Mat (q.Extension 2) (n + 3))
            rw [scalarUnitHom_root, block_terminal_negative]
            rfl
      exact hge ▸ hg

theorem scalarBlockHom_maps_relative (n : ℕ) (q : CFSG.PrimePower) :
    elementaryRootGroup (fixedField q) (n + 2) ≤
      (relativeRootGroup (n + 1) q).comap (scalarBlockHom n q) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨neg, i, a, rfl⟩
  exact root_mem n q neg i a

def blockRelativeHom (n : ℕ) (q : CFSG.PrimePower) :
    elementaryRootGroup (fixedField q) (n + 2) →* relativeRootGroup (n + 1) q where
  toFun g := ⟨scalarBlockHom n q g.val, scalarBlockHom_maps_relative n q g.property⟩
  map_one' := Subtype.ext ((scalarBlockHom n q).map_one)
  map_mul' g h := Subtype.ext ((scalarBlockHom n q).map_mul g.val h.val)

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankBlockMembership
