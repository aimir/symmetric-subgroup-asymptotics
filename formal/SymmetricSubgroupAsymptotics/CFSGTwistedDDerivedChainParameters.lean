import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedChainParameters
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDChainDoubleCommutators

/-! Full positive and negative relative chain lines lie in the SAME
original Derived action image. Natural double commutators retain every
field-fixed parameter; original source relations are not postulated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedChainParameters
open CFSGOrthogonalDSerreMatrices CFSGTwistedDSingularPrefix
open CFSGTwistedDFixedChainRoots CFSGTwistedDFixedChainParameters
open CFSGTwistedDFixedCentralCocycle CFSGTwistedDDerivedPairedRoots
open CFSGTwistedDImageCommutators CFSGOrthogonalDChainDoubleCommutators

private theorem comm_mem_fixed (s : ℕ) (q : CFSG.PrimePower)
    (x y : elementaryRootGroup (q.Extension 2) (s + 4))
    (hx : x ∈ naturalFixedPreimage s q) (hy : y ∈ naturalFixedPreimage s q) :
    ⁅x, y⁆ ∈ naturalFixedPreimage s q := by
  rw [commutatorElement_def]
  exact (naturalFixedPreimage s q).mul_mem
    ((naturalFixedPreimage s q).mul_mem ((naturalFixedPreimage s q).mul_mem hx hy)
      ((naturalFixedPreimage s q).inv_mem hx)) ((naturalFixedPreimage s q).inv_mem hy)

theorem parameter_mem_derived_preimage (s : ℕ) (q : CFSG.PrimePower) (neg : Bool)
    (i : Fin (s + 2)) (t : q.Extension 2)
    (ht : CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2 t = t) :
    CFSGTwistedDPairedRootImages.naturalRoot s q neg (chainNode (s + 2) i) t ∈
      naturalDerivedPreimage s q := by
  let R : Bool → Fin (s + 2) → q.Extension 2 → elementaryRootGroup (q.Extension 2) (s + 4) :=
    fun e j a => CFSGTwistedDPairedRootImages.naturalRoot s q e (chainNode (s + 2) j) a
  have hfixed (e : Bool) (j : Fin (s + 2)) (a : q.Extension 2)
      (ha : CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2 a = a) :
      R e j a ∈ naturalFixedPreimage s q := parameter_mem_fixed_preimage s q e j a ha
  have hone : CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2 1 = 1 := map_one _
  by_cases hi : i.val + 1 < s + 2
  · let j : Fin (s + 2) := ⟨i.val + 1, hi⟩
    have he : CFSGTwistedDFixedChainRoots.nextCoordinate s i = chainNode (s + 2) j := Fin.ext rfl
    have hij : chainNode (s + 2) i ≠ chainNode (s + 2) j := by
      intro h
      have hv := congrArg Fin.val h
      change i.val = i.val + 1 at hv
      omega
    have hik : chainNode (s + 2) i ≠ CFSGTwistedDFixedChainRoots.nextCoordinate s j := by
      intro h
      have hv := congrArg Fin.val h
      change i.val = i.val + 1 + 1 at hv
      omega
    cases neg
    · have hm := commutator_mem_derived_preimage s q ⁅R false i t, R false j 1⁆ (R true j 1)
        (comm_mem_fixed s q _ _ (hfixed false i t ht) (hfixed false j 1 hone))
        (hfixed true j 1 hone)
      have heq : ⁅⁅R false i t, R false j 1⁆, R true j 1⁆ = R false i t := by
        dsimp only [R]
        rw [positive_parameter, positive_parameter, negative_parameter]
        simpa only [he] using
          (first_edge (q.Extension 2) (s + 4) _ _ _ hij (chainNode_ne_next s j) hik t)
      simpa only [heq] using hm
    · have hm := commutator_mem_derived_preimage s q (R false j 1) ⁅R true j 1, R true i t⁆
        (hfixed false j 1 hone)
        (comm_mem_fixed s q _ _ (hfixed true j 1 hone) (hfixed true i t ht))
      have heq : ⁅R false j 1, ⁅R true j 1, R true i t⁆⁆ = R true i t := by
        dsimp only [R]
        rw [positive_parameter, negative_parameter, negative_parameter]
        simpa only [he] using
          (second_edge (q.Extension 2) (s + 4) _ _ _ (Ne.symm (chainNode_ne_next s j))
            (Ne.symm hij) (Ne.symm hik) t)
      simpa only [heq] using hm
  · have hi0 : 0 < i.val := by have := i.isLt; omega
    let j : Fin (s + 2) := ⟨i.val - 1, by have := i.isLt; omega⟩
    have he : CFSGTwistedDFixedChainRoots.nextCoordinate s j = chainNode (s + 2) i := by
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      omega
    have hji : chainNode (s + 2) j ≠ chainNode (s + 2) i := by
      intro h
      have hv := congrArg Fin.val h
      change i.val - 1 = i.val at hv
      omega
    have hjk : chainNode (s + 2) j ≠ CFSGTwistedDFixedChainRoots.nextCoordinate s i := by
      intro h
      have hv := congrArg Fin.val h
      change i.val - 1 = i.val + 1 at hv
      omega
    cases neg
    · have hm := commutator_mem_derived_preimage s q (R true j 1) ⁅R false j 1, R false i t⁆
        (hfixed true j 1 hone)
        (comm_mem_fixed s q _ _ (hfixed false j 1 hone) (hfixed false i t ht))
      have heq : ⁅R true j 1, ⁅R false j 1, R false i t⁆⁆ = R false i t := by
        dsimp only [R]
        rw [negative_parameter, positive_parameter, positive_parameter]
        simpa only [he] using
          (second_edge (q.Extension 2) (s + 4) _ _ _ hji (chainNode_ne_next s i) hjk t)
      simpa only [heq] using hm
    · have hm := commutator_mem_derived_preimage s q ⁅R true i t, R true j 1⁆ (R false j 1)
        (comm_mem_fixed s q _ _ (hfixed true i t ht) (hfixed true j 1 hone))
        (hfixed false j 1 hone)
      have heq : ⁅⁅R true i t, R true j 1⁆, R false j 1⁆ = R true i t := by
        dsimp only [R]
        rw [negative_parameter, negative_parameter, positive_parameter]
        simpa only [he] using
          (first_edge (q.Extension 2) (s + 4) _ _ _ (Ne.symm (chainNode_ne_next s i))
            (Ne.symm hji) (Ne.symm hjk) t)
      simpa only [heq] using hm

end SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedChainParameters
