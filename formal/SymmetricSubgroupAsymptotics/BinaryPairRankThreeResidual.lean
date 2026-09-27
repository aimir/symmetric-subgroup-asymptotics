import SymmetricSubgroupAsymptotics.BinaryPairResidualTop
import SymmetricSubgroupAsymptotics.PermutationBinaryRankThreeOrder

/-! The rank-three residual of an original eight-pair frame.
The ambient denominator is the literal image of normalSpace in the
original pair permutation module. Its actual quotient is intertwined
with the original section, retaining the whole original N. The
nonfaithful branch bounds the original source by 256 and the unchanged
quotient U/N by 128; no assertion N=ker(top) intersect N is used.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U) [N.Normal]

/-- The original lower space as a stable subspace of the original pair
permutation module, with every correlation retained. -/
def normalTopPermutationSubrepresentation :
    Subrepresentation (permutationFunctionRepresentation (ZMod 2) F.top.range I) where
  toSubmodule := (F.normalSpace N).map F.kernelSpace.subtype
  apply_mem_toSubmodule t v hv := by
    obtain ⟨m,hm,rfl⟩ := hv
    refine ⟨F.kernelTopPermutationSubrepresentation.toRepresentation t m,?_,rfl⟩
    apply (Submodule.Quotient.mk_eq_zero (F.normalSpace N)).mp
    have h := Representation.IntertwiningMap.isIntertwining _ _
      (F.sectionTopIntertwiner N) t m
    change (F.normalSpace N).mkQ
      (F.kernelTopPermutationSubrepresentation.toRepresentation t m)=
        F.sectionTopRepresentation N t ((F.normalSpace N).mkQ m) at h
    have hz : (F.normalSpace N).mkQ m=0 :=
      (Submodule.Quotient.mk_eq_zero (F.normalSpace N)).mpr hm
    rw [hz,map_zero] at h
    exact h

theorem normalTop_le_kernelTop :
    (F.normalTopPermutationSubrepresentation N).toSubmodule≤
      F.kernelTopPermutationSubrepresentation.toSubmodule := by
  rintro _ ⟨m,_,rfl⟩
  exact m.property

theorem normalTop_comap_eq :
    (F.normalTopPermutationSubrepresentation N).toSubmodule.comap F.kernelSpace.subtype=
      F.normalSpace N :=
  Submodule.comap_map_eq_of_injective (f := F.kernelSpace.subtype)
    Subtype.val_injective (F.normalSpace N)

/-- The quotient equivalence is induced by identity on the original
correlated flip vectors. -/
def originalTopSectionLinearEquiv :
    (F.kernelTopPermutationSubrepresentation.toSubmodule ⧸
      (F.normalTopPermutationSubrepresentation N).toSubmodule.comap
        F.kernelTopPermutationSubrepresentation.toSubmodule.subtype) ≃ₗ[ZMod 2]
      F.kernelSpace ⧸ F.normalSpace N :=
  Submodule.quotEquivOfEq _ _ (F.normalTop_comap_eq N)

@[simp] theorem originalTopSectionLinearEquiv_mk (m : F.kernelSpace) :
    F.originalTopSectionLinearEquiv N
      (((F.normalTopPermutationSubrepresentation N).toSubmodule.comap
        F.kernelSpace.subtype).mkQ m)=(F.normalSpace N).mkQ m := rfl

def originalTopSectionEquiv :
    (originalPermutationSection F.kernelTopPermutationSubrepresentation
      (F.normalTopPermutationSubrepresentation N)).Equiv (F.sectionTopRepresentation N) where
  toLinearEquiv := F.originalTopSectionLinearEquiv N
  isIntertwining' t := by
    apply LinearMap.ext
    intro a
    obtain ⟨m,rfl⟩ := ((F.normalTopPermutationSubrepresentation N).toSubmodule.comap
      F.kernelSpace.subtype).mkQ_surjective a
    change F.originalTopSectionLinearEquiv N
      (((F.normalTopPermutationSubrepresentation N).toSubmodule.comap F.kernelSpace.subtype).mkQ
        (F.kernelTopPermutationSubrepresentation.toRepresentation t m))=
      F.sectionTopRepresentation N t
        (F.originalTopSectionLinearEquiv N
          (((F.normalTopPermutationSubrepresentation N).toSubmodule.comap F.kernelSpace.subtype).mkQ m))
    rw [F.originalTopSectionLinearEquiv_mk,F.originalTopSectionLinearEquiv_mk]
    exact Representation.IntertwiningMap.isIntertwining _ _ (F.sectionTopIntertwiner N) t m

def originalTopSectionFixedEquiv :
    (originalPermutationSection F.kernelTopPermutationSubrepresentation
      (F.normalTopPermutationSubrepresentation N)).invariants ≃ₗ[ZMod 2]
        (F.sectionTopRepresentation N).invariants where
  toFun a := ⟨F.originalTopSectionEquiv N a.1,fun t =>
    (Representation.IntertwiningMap.isIntertwining _ _
      (F.originalTopSectionEquiv N).toIntertwiningMap t a.1).symm.trans
      (congrArg (F.originalTopSectionEquiv N) (a.property t))⟩
  invFun a := ⟨(F.originalTopSectionEquiv N).symm a.1,fun t =>
    (Representation.IntertwiningMap.isIntertwining _ _
      (F.originalTopSectionEquiv N).symm.toIntertwiningMap t a.1).symm.trans
      (congrArg (F.originalTopSectionEquiv N).symm (a.property t))⟩
  left_inv a := Subtype.ext ((F.originalTopSectionEquiv N).symm_apply_apply a.1)
  right_inv a := Subtype.ext ((F.originalTopSectionEquiv N).apply_symm_apply a.1)
  map_add' a b := Subtype.ext (map_add (F.originalTopSectionEquiv N) a.1 b.1)
  map_smul' c a := Subtype.ext (map_smul (F.originalTopSectionEquiv N) c a.1)

/-- The original top and original correlated kernel are bounded before
any ambient group cardinality is inferred. -/
theorem eight_rank_three_nonfaithful_top_bound [Finite X] [Finite I]
    [MulAction.IsPretransitive F.top.range I] (hU : IsPGroup 2 U)
    (hI : Nat.card I=8)
    (hd : Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)=4)
    (ht : Module.finrank (ZMod 2) (F.sectionRepresentation N).invariants=3)
    (hne : ¬Function.Injective (F.sectionTopRepresentation N)) :
    Nat.card F.top.range≤8 ∧ Module.finrank (ZMod 2) F.kernelSpace=5 := by
  have hnonempty : Nonempty I := (Nat.card_pos_iff.mp (by rw [hI]; decide)).1
  let i : I := Classical.choice hnonempty
  have htTop : Module.finrank (ZMod 2) (F.sectionTopRepresentation N).invariants=3 := by
    rw [F.sectionTop_invariants_eq,ht]
  have hne' : ¬Function.Injective
      (originalPermutationSection F.kernelTopPermutationSubrepresentation
        (F.normalTopPermutationSubrepresentation N)) := by
    intro hi
    apply hne
    intro t s hts
    apply hi
    apply LinearMap.ext
    intro a
    apply (F.originalTopSectionEquiv N).toLinearEquiv.injective
    have ht' := Representation.IntertwiningMap.isIntertwining _ _
      (F.originalTopSectionEquiv N).toIntertwiningMap t a
    have hs' := Representation.IntertwiningMap.isIntertwining _ _
      (F.originalTopSectionEquiv N).toIntertwiningMap s a
    exact ht'.trans ((DFunLike.congr_fun hts _).trans hs'.symm)
  exact permutationBinary_rankThree_nonfaithful_order
    F.kernelTopPermutationSubrepresentation (F.normalTopPermutationSubrepresentation N)
    (F.top_isPGroup hU) i hI (F.normalTop_le_kernelTop N)
    ((F.originalTopSectionLinearEquiv N).finrank_eq.trans hd)
    ((F.originalTopSectionFixedEquiv N).finrank_eq.trans htTop) hne'

/-- These are bounds on the actual original source and original normal
quotient. The full image of N is allowed in the original base quotient. -/
theorem eight_rank_three_nonfaithful_orders [Finite X] [Finite I]
    [MulAction.IsPretransitive F.top.range I] (hU : IsPGroup 2 U)
    (hI : Nat.card I=8)
    (hd : Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)=4)
    (ht : Module.finrank (ZMod 2) (F.sectionRepresentation N).invariants=3)
    (hne : ¬Function.Injective (F.sectionTopRepresentation N)) :
    Nat.card U≤256 ∧ Nat.card (U ⧸ N)≤128 := by
  obtain ⟨htop,hM⟩ := F.eight_rank_three_nonfaithful_top_bound N hU hI hd ht hne
  have hker : Nat.card F.top.ker=32 := by
    calc
      Nat.card F.top.ker = Nat.card F.kernelSpace :=
        (Nat.card_congr F.kernelChart.toEquiv).trans (Nat.card_congr Multiplicative.toAdd)
      _ = 2^Module.finrank (ZMod 2) F.kernelSpace := by
        simpa only [Nat.card_zmod] using
          (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.kernelSpace))
      _ = 32 := by rw [hM]; norm_num
  have hsource := F.top.ker.card_mul_index
  rw [Subgroup.index_ker,hker] at hsource
  have hbase : Nat.card (U ⧸ (F.top.ker⊔N))≤8 :=
    (Nat.card_le_card_of_surjective (F.sectionTopQuotient N)
      (F.sectionTopQuotient_surjective N)).trans htop
  have hA : Nat.card (F.zeroCutBase N).ker=16 := by
    calc
      Nat.card (F.zeroCutBase N).ker = Nat.card (F.kernelSpace ⧸ F.normalSpace N) :=
        (Nat.card_congr (F.sectionKernelEquiv N).symm.toEquiv).trans
          (Nat.card_congr Multiplicative.toAdd)
      _ = 2^Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N) := by
        simpa only [Nat.card_zmod] using
          (Module.natCard_eq_pow_finrank (K := ZMod 2)
            (V := F.kernelSpace ⧸ F.normalSpace N))
      _ = 16 := by rw [hd]; norm_num
  have hindex : (F.zeroCutBase N).ker.index=Nat.card (U ⧸ (F.top.ker⊔N)) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (F.zeroCutBase N)
      (F.zeroCutBase_surjective N)).toEquiv
  have htarget := (F.zeroCutBase N).ker.card_mul_index
  rw [hA,hindex] at htarget
  constructor <;> omega

/-- All original rank-three dimension-four axes pass an actual order
bound or the original seven-character test. -/
theorem eight_rank_three_order_or_character [Finite X] [Finite I]
    [MulAction.IsPretransitive F.top.range I] (hU : IsPGroup 2 U)
    (hI : Nat.card I=8)
    (hd : Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)=4)
    (ht : Module.finrank (ZMod 2) (F.sectionRepresentation N).invariants=3) :
    (Nat.card U≤256 ∧ Nat.card (U ⧸ N)≤128) ∨
      Nonempty (BinarySevenCharacterCriterion (U ⧸ N) (Nat.card X)) := by
  classical
  by_cases hfaithful : Function.Injective (F.sectionTopRepresentation N)
  · exact Or.inr ⟨F.faithfulSectionTopSevenCriterion_of_eight N hU hI hfaithful⟩
  · exact Or.inl (F.eight_rank_three_nonfaithful_orders N hU hI hd ht hfaithful)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
