import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarPoints
import SymmetricSubgroupAsymptotics.CFSGTwistedAQuadraticTrace
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

/-! Literal singular vectors span the entire three-dimensional natural
unitary residue, even at q=2. Two endpoint axes and a vector with middle
coordinate one suffice; its endpoint coefficient solves the actual trace
equation. No unital point census or group recognition is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters
open CFSGTwistedAQuadraticTrace

theorem unitary_rankTwo_singular_span_eq_top (q : CFSG.PrimePower) :
    Submodule.span (q.Extension 2)
      {v : Fin 3 → q.Extension 2 | unitaryNaturalPair q 2 v v = 0} = ⊤ := by
  classical
  let sig := definingFieldAutomorphism q 2
  let H : Mat (q.Extension 2) 2 := signedReversalUnit (q.Extension 2) 2
  let e₀ : Fin 3 → q.Extension 2 := Pi.single 0 1
  let e₁ : Fin 3 → q.Extension 2 := Pi.single 1 1
  let e₂ : Fin 3 → q.Extension 2 := Pi.single 2 1
  let S := Submodule.span (q.Extension 2)
    {v : Fin 3 → q.Extension 2 | unitaryNaturalPair q 2 v v = 0}
  have he₀ : e₀ ∈ S := by
    apply Submodule.subset_span
    change unitaryNaturalPair q 2 (Pi.single (0 : Fin 3) 1) (Pi.single 0 1) = 0
    rw [unitaryNaturalPair_basis]
    norm_num [signWeight, Fin.rev, Pi.single_apply, Fin.ext_iff]
  have he₂ : e₂ ∈ S := by
    apply Submodule.subset_span
    change unitaryNaturalPair q 2 (Pi.single (2 : Fin 3) 1) (Pi.single 2 1) = 0
    rw [unitaryNaturalPair_basis]
    norm_num [signWeight, Fin.rev, Pi.single_apply, Fin.ext_iff]
  obtain ⟨b, hb⟩ := exists_trace_eq_fixed q (1 : q.Extension 2) (map_one sig)
  let w : Fin 3 → q.Extension 2 := ![b,1,1]
  have hwdec : w = (b • e₀ + e₁) + e₂ := by
    ext i
    fin_cases i <;> norm_num [w, e₀, e₁, e₂, Pi.single_apply, Fin.ext_iff]
  have hwnorm : unitaryNaturalPair q 2 w w = 0 := by
    calc
      _ = unitaryNaturalPair q 2 ((b • e₀ + e₁) + e₂) w :=
        congrArg (fun v => unitaryNaturalPair q 2 v w) hwdec
      _ = 0 := by
        change hermitianPair sig H ((b • e₀ + e₁) + e₂) w = 0
        rw [hermitianPair_add_left, hermitianPair_add_left]
        have hs := hermitianPair_smul sig H b 1 e₀ w
        simp only [one_smul, mul_one] at hs
        rw [hs]
        change sig b * unitaryNaturalPair q 2 e₀ w + unitaryNaturalPair q 2 e₁ w +
          unitaryNaturalPair q 2 e₂ w = 0
        rw [unitaryNaturalPair_basis, unitaryNaturalPair_basis, unitaryNaturalPair_basis]
        norm_num [w, signWeight, Fin.rev]
        change definingFieldAutomorphism q 2 b + (-1) + b = 0
        linear_combination hb
  have hw : w ∈ S := Submodule.subset_span hwnorm
  have he₁ : e₁ ∈ S := by
    have hh := S.sub_mem (S.sub_mem hw (S.smul_mem b he₀)) he₂
    have he : w - b • e₀ - e₂ = e₁ := by rw [hwdec]; module
    rwa [he] at hh
  apply top_unique
  intro v _
  have hv : v = (v 0 • e₀ + v 1 • e₁) + v 2 • e₂ := by
    ext i
    fin_cases i <;> norm_num [e₀, e₁, e₂, Pi.single_apply, Fin.ext_iff] <;> rfl
  rw [hv]
  exact S.add_mem (S.add_mem (S.smul_mem _ he₀) (S.smul_mem _ he₁)) (S.smul_mem _ he₂)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
