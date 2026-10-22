import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOriginalGeneration
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOriginalSylow
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNormalizerSoluble
import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrime

/-! Good Sylow data on the SAME original derived fixed source, all
ranks at least three and all fields. Its Sylow is the proved original U;
its conjugator is the proved original signed reversal. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGReduction

theorem originalDerived_goodSylowPrime (q : CFSG.PrimePower) (s : ℕ) :
    GoodSylowPrime (commutator (Fixed (s + 3) q)) q.prime := by
  letI : Finite (Fixed (s + 3) q) := originalFixed_finite q (s + 3) (by omega)
  let D := commutator (Fixed (s + 3) q)
  let U := originalUnipotent (s + 3) q
  let V := originalOppositeUnipotent q (s + 3)
  have hUD : U ≤ D := originalUnipotent_le_derived q s
  have hVD : V ≤ D := by
    intro x hx
    exact original_join_le_derived q s
      ((show V ≤ originalUpperOppositeJoin q (s + 3) from le_sup_right) hx)
  let UH := U.subgroupOf D
  let VH := V.subgroupOf D
  have hjoin : U ⊔ V = D := originalUpperOppositeJoin_eq_derived q s
  have hgen : UH ⊔ VH = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hUD hVD, hjoin, Subgroup.subgroupOf_self]
  let P : Sylow q.prime D :=
    (originalSylow q (s + 3) (by omega)).subtype (originalSylow_le_derived q s)
  let w : D := ⟨originalReversal q (s + 3), originalReversal_mem_derived q s⟩
  have hVeq : VH = UH.map (MulAut.conj w).toMonoidHom := by
    ext x
    constructor
    · intro hx
      change x.val ∈ originalOppositeUnipotent q (s + 3) at hx
      obtain ⟨u, hu, he⟩ := hx
      refine ⟨⟨u, hUD hu⟩, hu, ?_⟩
      exact Subtype.ext he
    · rintro ⟨u, hu, he⟩
      change x.val ∈ originalOppositeUnipotent q (s + 3)
      exact ⟨u.val, hu, congrArg (fun y : D => y.val) he⟩
  have hUmap : UH.map D.subtype = U := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hUD]
  let NI := Subgroup.normalizer (UH : Set D)
  let NO := Subgroup.normalizer (U : Set (Fixed (s + 3) q))
  have hnormal : NI.map D.subtype ≤ NO := by
    have hh := UH.le_normalizer_map D.subtype
    rw [hUmap] at hh
    exact hh
  letI : IsSolvable NO := originalUnipotent_normalizer_soluble q (s + 3) (by omega)
  let f : NI →* NO :=
    { toFun := fun x => ⟨x.val.val, hnormal ⟨x.val, x.property, rfl⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : NO => z.val) he
  refine ⟨q.prime_isPrime, P, w, ?_, ?_⟩
  · change IsSolvable NI
    exact solvable_of_solvable_injective (f := f) hf
  · change Subgroup.closure ((UH : Set D) ∪ UH.map (MulAut.conj w).toMonoidHom) = ⊤
    rw [← Subgroup.sup_eq_closure, ← hVeq]
    exact hgen

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
