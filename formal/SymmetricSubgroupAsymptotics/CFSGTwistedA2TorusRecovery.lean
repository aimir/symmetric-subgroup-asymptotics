import SymmetricSubgroupAsymptotics.CFSGTwistedA2NaturalRootJoin
import SymmetricSubgroupAsymptotics.CFSGTwistedA2OppositeArrays
import SymmetricSubgroupAsymptotics.CFSGTwistedA2ColumnAction
import SymmetricSubgroupAsymptotics.CFSGTwistedA2UpperIsometricFactor
import SymmetricSubgroupAsymptotics.CFSGTwistedA2NormSurjectivity

/-! The TWO actual unipotent subgroups generate every literal torus
word. Norm surjectivity and explicit first-column elimination construct
the word; no torus-generation or Bruhat premise is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedA2DiagonalTorus

theorem torusNatural_mem_rootGenerated (q : CFSG.PrimePower) (t : q.Extension 2)
    (ht0 : t ≠ 0) (ht : t ^ q.order = -t) (z : q.Extension 2) (hz : z ≠ 0) :
    torusNatural (q.Extension 2) (definingFieldAutomorphism q 2) z ∈ naturalRootGenerated q t := by
  let σ := definingFieldAutomorphism q 2
  let H := naturalRootGenerated q t
  let b := -t * z
  obtain ⟨a, hab⟩ := exists_first_parameter q b
  let L := oppositeNatural (q.Extension 2) σ t a b
  have hL : L ∈ H :=
    (show (naturalUnipotent q).map (MulAut.conj (weylNatural (q.Extension 2) t)).toMonoidHom ≤ H
      from le_sup_right) ⟨upperNatural (q.Extension 2) σ a b, ⟨a, b, hab, rfl⟩, rfl⟩
  have hL20 : (L.val : Mat (q.Extension 2) 2) 2 0 = -b / t ^ 2 := by
    change ((oppositeNatural (q.Extension 2) σ t a b).val : Mat (q.Extension 2) 2) 2 0 = _
    rw [oppositeNatural_array _ σ t ht0 a b]
    simp [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have hpivot : t * (L.val : Mat (q.Extension 2) 2) 2 0 = z := by
    rw [hL20]
    dsimp only [b]
    field_simp [ht0] <;> ring
  have hL20ne : (L.val : Mat (q.Extension 2) 2) 2 0 ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hpivot
    exact hz hpivot.symm
  have hLform := fixed_unit_isometric (q.Extension 2) 2 σ.toRingHom L.val
    (naturalRootGenerated_fixed q t ht L hL)
  obtain ⟨ac, bc, hcb, hc⟩ := upper_clear_column (q.Extension 2) σ
    (fun x => extension_two_pow_twice q x) (L.val : Mat (q.Extension 2) 2) hLform hL20ne
  let C := upperNatural (q.Extension 2) σ ac bc
  have hC : C ∈ H :=
    (show naturalUnipotent q ≤ H from le_sup_left) ⟨ac, bc, hcb, rfl⟩
  let N := weylNatural (q.Extension 2) t * C * L
  have hN : N ∈ H := H.mul_mem
    (H.mul_mem (weylNatural_mem_rootGenerated q t ht0 ht) hC) hL
  have hNcol : firstColumn (q.Extension 2) (N.val : Mat (q.Extension 2) 2) =
      z • (![1, 0, 0] : Fin 3 → q.Extension 2) := by
    have hh := weyl_after_column_clear (q.Extension 2) σ t ht0
      (L.val : Mat (q.Extension 2) 2) ac bc hc
    rw [hpivot] at hh
    exact hh
  have hN00 : (N.val : Mat (q.Extension 2) 2) 0 0 = z := by
    simpa [firstColumn, Pi.smul_apply, smul_eq_mul] using congrArg (fun v => v 0) hNcol
  have hN20 : (N.val : Mat (q.Extension 2) 2) 2 0 = 0 := by
    simpa [firstColumn, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail] using congrArg (fun v => v 2) hNcol
  have hNform := fixed_unit_isometric (q.Extension 2) 2 σ.toRingHom N.val
    (naturalRootGenerated_fixed q t ht N hN)
  have hNu := isometric_upper_of_lower_pivot_zero σ N.val hNform hN20
  obtain ⟨z', hz', af, bf, hfb, hfac⟩ := upper_isometric_factor (q.Extension 2) σ
    (fun x => extension_two_pow_twice q x) N.val hNu (naturalElementary_det _ _ N) hNform
  have hparam : z' = z := by
    have he := congrArg (fun A : Mat (q.Extension 2) 2 => A 0 0) hfac
    change (N.val : Mat (q.Extension 2) 2) 0 0 =
      (Matrix.diagonal (torusWeights (q.Extension 2) σ z') * upperArray σ af bf) 0 0 at he
    rw [Matrix.diagonal_mul] at he
    change (N.val : Mat (q.Extension 2) 2) 0 0 = z' * 1 at he
    rw [mul_one] at he
    exact he.symm.trans hN00
  subst z'
  have hNat : N = torusNatural (q.Extension 2) σ z * upperNatural (q.Extension 2) σ af bf := by
    apply Subtype.ext
    apply Units.ext
    change (N.val : Mat (q.Extension 2) 2) =
      ((torusNatural (q.Extension 2) σ z).val : Mat (q.Extension 2) 2) *
        ((upperNatural (q.Extension 2) σ af bf).val : Mat (q.Extension 2) 2)
    rw [torusNatural_unit _ σ z hz', upperNatural_val]
    exact hfac
  have hUf : upperNatural (q.Extension 2) σ af bf ∈ H :=
    (show naturalUnipotent q ≤ H from le_sup_left) ⟨af, bf, hfb, rfl⟩
  have hm := H.mul_mem hN (H.inv_mem hUf)
  rwa [hNat, mul_assoc, mul_inv_cancel, mul_one] at hm

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
