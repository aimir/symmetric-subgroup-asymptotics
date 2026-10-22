import SymmetricSubgroupAsymptotics.CFSGTwistedA2OriginalDerivedGeneration
import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrime

/-! Good Sylow data in the SAME original fixed-source derived group.
The checked original U is restricted to that group, and the conjugator
is the displayed originalWeyl word, not a replacement witness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices CFSGTwistedA2FieldWitness CFSGReduction

theorem originalDerived_goodSylowPrime (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    GoodSylowPrime (commutator (OriginalFixedA 2 q)) q.prime := by
  letI : Finite (fixedNaturalPullback 2 q) :=
    Finite.of_injective (pullbackMatrix 2 q) (pullbackMatrix_two_injective q)
  letI : Finite (OriginalFixedA 2 q) :=
    Finite.of_surjective (pullbackSource 2 q) (pullbackSource_surjective 2 (by decide) q)
  obtain ⟨t, _, ht0, ht, _, _, _⟩ := exists_skew_and_fixed_scalar q hq
  let D := commutator (OriginalFixedA 2 q)
  let U := originalUnipotent q
  let V := oppositeOriginalUnipotent q t ht
  have hUD : U ≤ D := originalUnipotent_le_commutator q hq
  have hVD : V ≤ D := by
    intro x hx
    exact rootGenerated_le_commutator q hq t ht
      ((show V ≤ rootGenerated q t ht from le_sup_right) hx)
  let UH := U.subgroupOf D
  let VH := V.subgroupOf D
  have hjoin : U ⊔ V = D := rootGenerated_eq_commutator q hq t ht0 ht
  have hgen : UH ⊔ VH = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hUD hVD, hjoin, Subgroup.subgroupOf_self]
  let P : Sylow q.prime D := (originalSylow q hq).subtype (originalSylow_le_commutator q hq)
  have hWD : originalWeyl q t ht ∈ D :=
    rootGenerated_le_commutator q hq t ht (originalWeyl_mem_rootGenerated q t ht0 ht)
  let w : D := ⟨originalWeyl q t ht, hWD⟩
  have hVeq : VH = UH.map (MulAut.conj w).toMonoidHom := by
    ext x
    constructor
    · intro hx
      change x.val ∈ oppositeOriginalUnipotent q t ht at hx
      obtain ⟨u, hu, he⟩ := hx
      refine ⟨⟨u, hUD hu⟩, hu, ?_⟩
      exact Subtype.ext he
    · rintro ⟨u, hu, he⟩
      change x.val ∈ oppositeOriginalUnipotent q t ht
      refine ⟨u.val, hu, ?_⟩
      exact congrArg (fun y : D => y.val) he
  have hUmap : UH.map D.subtype = U := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hUD]
  let NI := Subgroup.normalizer (UH : Set D)
  let NO := Subgroup.normalizer (U : Set (OriginalFixedA 2 q))
  have hnormal : NI.map D.subtype ≤ NO := by
    have hh := UH.le_normalizer_map D.subtype
    rw [hUmap] at hh
    exact hh
  letI : IsSolvable NO := originalUnipotent_normalizer_soluble q hq
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

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
