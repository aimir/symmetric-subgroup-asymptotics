import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeElementaryGroup
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailVectorAction

/-! The literal relative-root group in rank n+2 embeds in rank n+3
by adjoining a fixed FIRST hyperbolic pair. Every generator is sent to
its actual successor-index generator with the same field parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeTailEmbedding
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDRelativeElementaryGroup CFSGOrthogonalDIndexTailCoordinates
open CFSGTwistedDSingularPrefix

theorem pen_succ (n : ℕ) : (pen n).succ = pen (n + 1) := Fin.ext rfl

theorem last_succ (n : ℕ) : (last n).succ = last (n + 1) := Fin.ext rfl

theorem chainNode_succ (n : ℕ) (i : Fin n) :
    (chainNode n i).succ = chainNode (n + 1) i.succ := Fin.ext rfl

theorem tail_paired (n : ℕ) (q : CFSG.PrimePower) (neg : Bool) (a : q.Extension 2) :
    tailUnitHom (q.Extension 2) (n + 2) (pairedRoot n q neg a) =
      pairedRoot (n + 1) q neg a := by
  rw [pairedRoot, map_mul, tailUnitHom_rootTransvection _ _ (by omega),
    tailUnitHom_rootTransvection _ _ (by omega), pen_succ, last_succ]
  rfl

theorem tail_maps_relative (n : ℕ) (q : CFSG.PrimePower) :
    relativeRootGroup n q ≤ (relativeRootGroup (n + 1) q).comap
      (tailUnitHom (q.Extension 2) (n + 2)) := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with ⟨neg, i, a, rfl⟩ | ⟨neg, a, rfl⟩
  · change tailUnitHom (q.Extension 2) (n + 2)
      (rootTransvection (q.Extension 2) (n + 2) neg (chainNode n i) (a : q.Extension 2)) ∈ relativeRootGroup (n + 1) q
    rw [tailUnitHom_rootTransvection _ _ (by omega), chainNode_succ]
    exact chain_mem (n + 1) q neg i.succ a
  · change tailUnitHom (q.Extension 2) (n + 2) (pairedRoot n q neg a) ∈ relativeRootGroup (n + 1) q
    rw [tail_paired]
    exact paired_mem (n + 1) q neg a

def tailRelativeHom (n : ℕ) (q : CFSG.PrimePower) :
    relativeRootGroup n q →* relativeRootGroup (n + 1) q where
  toFun g := ⟨tailUnitHom (q.Extension 2) (n + 2) g.val, tail_maps_relative n q g.property⟩
  map_one' := Subtype.ext ((tailUnitHom (q.Extension 2) (n + 2)).map_one)
  map_mul' g h := Subtype.ext ((tailUnitHom (q.Extension 2) (n + 2)).map_mul g.val h.val)

theorem tailRelativeHom_injective (n : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (tailRelativeHom n q) := by
  intro g h he
  apply Subtype.ext
  apply tailUnitHom_injective (q.Extension 2) (n + 2)
  exact congrArg Subtype.val he

theorem tail_action (n : ℕ) (q : CFSG.PrimePower) (g : relativeRootGroup n q)
    (v : Index (n + 3) → q.Extension 2) :
    tailRestriction (q.Extension 2) (n + 2)
      (((tailRelativeHom n q g).val : Mat (q.Extension 2) (n + 3)) *ᵥ v) =
      (g.val : Mat (q.Extension 2) (n + 2)) *ᵥ tailRestriction (q.Extension 2) (n + 2) v :=
  tailElementaryHom_tail_action (q.Extension 2) (n + 2) (by omega)
    ⟨g.val, relativeRootGroup_le_elementary n q g.property⟩ v

theorem head_positive (n : ℕ) (q : CFSG.PrimePower) (g : relativeRootGroup n q)
    (v : Index (n + 3) → q.Extension 2) :
    (((tailRelativeHom n q g).val : Mat (q.Extension 2) (n + 3)) *ᵥ v) (Sum.inl 0) =
      v (Sum.inl 0) :=
  tailElementaryHom_head_positive (q.Extension 2) (n + 2) (by omega)
    ⟨g.val, relativeRootGroup_le_elementary n q g.property⟩ v

theorem head_negative (n : ℕ) (q : CFSG.PrimePower) (g : relativeRootGroup n q)
    (v : Index (n + 3) → q.Extension 2) :
    (((tailRelativeHom n q g).val : Mat (q.Extension 2) (n + 3)) *ᵥ v) (Sum.inr 0) =
      v (Sum.inr 0) :=
  tailElementaryHom_head_negative (q.Extension 2) (n + 2) (by omega)
    ⟨g.val, relativeRootGroup_le_elementary n q g.property⟩ v

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeTailEmbedding
