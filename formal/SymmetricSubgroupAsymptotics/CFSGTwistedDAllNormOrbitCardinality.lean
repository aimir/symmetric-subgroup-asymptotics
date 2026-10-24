import SymmetricSubgroupAsymptotics.CFSGTwistedDAllNormVectorOrbit
import SymmetricSubgroupAsymptotics.CFSGTwistedDLinearParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedDAnisotropicNormForm
import SymmetricSubgroupAsymptotics.HyperbolicNormLevelSliceCardinality

/-! Every nonzero actual twisted-D natural orbit contains a whole norm
slice. The literal anisotropic quadratic-extension coordinate contributes
q squared, with no characteristic-prime factor or abstract model change. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllNormOrbitCardinality

open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDAllNormVectorOrbit CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDLinearParameters CFSGTwistedDAnisotropicNormForm
open CFSGTwistedA2FixedField HyperbolicNormLevelSliceCardinality CFSGParabolicQuadricCount

def vectorOrbit (n : ℕ) (q : CFSG.PrimePower) (v : fixedSpace (n + 1) q) :
    Set (fixedSpace (n + 1) q) :=
  {w | ∃ g : relativeRootGroup (n + 1) q, fixedLinearHom (n + 1) q g v = w}

theorem norm_slice_le_vectorOrbit (n : ℕ) (q : CFSG.PrimePower)
    (v : fixedSpace (n + 1) q) (hv : v ≠ 0) :
    (q.order ^ (n + 2) - 1) * q.order ^ (n + 3) ≤ Nat.card (vectorOrbit n q v) := by
  let E := linearParameters (n + 1) q
  let S := LevelSlice (I := Fin (n + 2)) (normForm q) (fixedQuadraticForm (n + 1) q v)
  let e : S → vectorOrbit n q v := fun p => by
    let w := E.symm (p.val.1.1, (p.val.2, p.val.1.2))
    have hw : w ≠ 0 := by
      intro hz
      have hh := congrArg E hz
      change E (E.symm (p.val.1.1, (p.val.2, p.val.1.2))) = E 0 at hh
      rw [E.apply_symm_apply, map_zero] at hh
      exact p.property.1 (congrArg Prod.fst hh)
    have hQ : fixedQuadraticForm (n + 1) q w = fixedQuadraticForm (n + 1) q v := by
      calc
        fixedQuadraticForm (n + 1) q w =
            (∑ i : Fin (n + 2), p.val.1.1 i * p.val.2 i) +
              Algebra.norm (fixedField q) p.val.1.2 := quadratic_parameters (n + 1) q _
        _ = dotDual p.val.1.1 p.val.2 + normForm q p.val.1.2 := by
          rw [normForm_apply]
          rfl
        _ = _ := p.property.2
    refine ⟨w, ?_⟩
    exact exists_map_of_same_norm n q v w hv hw hQ.symm
  have he : Function.Injective e := by
    intro p t h
    have hh := congrArg (fun w : vectorOrbit n q v => w.val) h
    have hc := congrArg E hh
    change E (E.symm (p.val.1.1, (p.val.2, p.val.1.2))) =
      E (E.symm (t.val.1.1, (t.val.2, t.val.1.2))) at hc
    rw [E.apply_symm_apply, E.apply_symm_apply] at hc
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg (fun x : (Fin (n + 2) → fixedField q) ×
          ((Fin (n + 2) → fixedField q) × q.Extension 2) => x.1) hc
      · exact congrArg (fun x : (Fin (n + 2) → fixedField q) ×
          ((Fin (n + 2) → fixedField q) × q.Extension 2) => x.2.2) hc
    · exact congrArg (fun x : (Fin (n + 2) → fixedField q) ×
        ((Fin (n + 2) → fixedField q) × q.Extension 2) => x.2.1) hc
  have hc : Nat.card S = (q.order ^ (n + 2) - 1) * q.order ^ (n + 3) := by
    have hh := card_levelSlice (I := Fin (n + 2)) (normForm q) (fixedQuadraticForm (n + 1) q v)
    have hn : n + 2 - 1 = n + 1 := by omega
    calc
      Nat.card S = (q.order ^ (n + 2) - 1) * q.order ^ 2 * q.order ^ (n + 1) := by
        simpa only [fixedField_card, CFSGTwistedANaturalMatrices.extension_two_card,
          Fintype.card_fin, hn] using hh
      _ = (q.order ^ (n + 2) - 1) * (q.order ^ 2 * q.order ^ (n + 1)) := by ac_rfl
      _ = (q.order ^ (n + 2) - 1) * q.order ^ (2 + (n + 1)) :=
        congrArg (fun a : ℕ => (q.order ^ (n + 2) - 1) * a)
          (pow_add q.order 2 (n + 1)).symm
      _ = _ := by congr 2 <;> omega
  rw [← hc]
  exact Nat.card_le_card_of_injective e he

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllNormOrbitCardinality
