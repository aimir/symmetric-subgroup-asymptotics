import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingFactor
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticRootSubgroup

/-! The actual first-height coordinate homomorphism on the original U.
Its additive simple-root generators have exactly the standard independent
coordinates. Generation is proved for the SAME subgroup U. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingHom
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckColumns
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckPositiveFirstLayer
open CFSGNormTwoGeckSimpleRootCoordinates CFSGNormTwoCoordinateLeadingFactor
open CFSGGradedMatrixGroupFirstLayer CFSGNormTwoCoordinateHeight
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
local notation "w" => weight A hs hp b₀ coordinateHeight

theorem leadingCoordinates_one (K : Type) [Field K] :
    leadingCoordinates A hd hs hp ho K 1=0 := by
  funext i
  change (1 : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)
    (Sum.inl (s₀ i)) (Sum.inr (negativeIndex A hs hp (s₀ i)))=0
  simp only [Matrix.one_apply,Sum.inl_ne_inr,if_false]

theorem leadingCoordinates_mul (K : Type) [Field K] (u v : rootGroup A hs hp b₀ s₀ K false) :
    leadingCoordinates A hd hs hp ho K (u.val*v.val)=
      leadingCoordinates A hd hs hp ho K u.val+leadingCoordinates A hd hs hp ho K v.val := by
  funext i
  have hu := (positive_firstLayer_mem_span A hs hp b₀ s₀ coordinateHeight
    (simple_height A hd hs hp ho) K u.val u.property).1
  have hv := (positive_firstLayer_mem_span A hs hp b₀ s₀ coordinateHeight
    (simple_height A hd hs hp ho) K v.val v.property).1
  have hh := congrArg (fun M : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K=>
    M (Sum.inl (s₀ i)) (Sum.inr (negativeIndex A hs hp (s₀ i))))
      (firstLayer_mul w u.val v.val hu hv)
  dsimp only at hh
  rw [firstLayer_entry,Matrix.add_apply,firstLayer_entry,firstLayer_entry] at hh
  exact hh

def leadingHom (K : Type) [Field K] :
    rootGroup A hs hp b₀ s₀ K false→*Multiplicative (Fin r→K) where
  toFun u := Multiplicative.ofAdd (leadingCoordinates A hd hs hp ho K u.val)
  map_one' := by
    change leadingCoordinates A hd hs hp ho K 1=0
    exact leadingCoordinates_one A hd hs hp ho K
  map_mul' := by
    intro u v
    change leadingCoordinates A hd hs hp ho K (u.val*v.val)=
      leadingCoordinates A hd hs hp ho K u.val+leadingCoordinates A hd hs hp ho K v.val
    exact leadingCoordinates_mul A hd hs hp ho K u v

def positiveRoot (K : Type) [Field K] (i : Fin r) (a : K) : rootGroup A hs hp b₀ s₀ K false :=
  ⟨canonicalRoot D K false i a,Subgroup.subset_closure ⟨(i,a),rfl⟩⟩

theorem positiveRoot_zero (K : Type) [Field K] (i : Fin r) :
    positiveRoot A hd hs hp ho K i 0=1 := by
  apply Subtype.ext
  exact canonicalRoot_zero D K false i

theorem positiveRoot_add (K : Type) [Field K] (i : Fin r) (a b : K) :
    positiveRoot A hd hs hp ho K i (a+b)=
      positiveRoot A hd hs hp ho K i a*positiveRoot A hd hs hp ho K i b := by
  apply Subtype.ext
  exact (canonicalRoot_add D K false i a b).symm

theorem leadingHom_positiveRoot (K : Type) [Field K] (j : Fin r) (a : K) :
    leadingHom A hd hs hp ho K (positiveRoot A hd hs hp ho K j a)=
      Multiplicative.ofAdd (Pi.single j a : Fin r→K) := by
  change leadingCoordinates A hd hs hp ho K (canonicalRoot D K false j a)=Pi.single j a
  funext i
  rw [←firstLayer_entry,simple_firstLayer A hs hp b₀ s₀ coordinateHeight (simple_height A hd hs hp ho)]
  rw [Matrix.smul_apply,field_E_coordinate_entry A hs hp b₀ s₀ K i j]
  by_cases hij : i=j <;> simp [Pi.single_apply,hij,eq_comm]

theorem positiveRoot_generates (K : Type) [Field K] :
    Subgroup.closure (Set.range (fun z : Fin r×K=>positiveRoot A hd hs hp ho K z.1 z.2))=⊤ := by
  apply Subgroup.map_injective (rootGroup A hs hp b₀ s₀ K false).subtype_injective
  rw [MonoidHom.map_closure,←MonoidHom.range_eq_map,Subgroup.range_subtype]
  have himage : (rootGroup A hs hp b₀ s₀ K false).subtype ''
      Set.range (fun z : Fin r×K=>positiveRoot A hd hs hp ho K z.1 z.2)=
        Set.range (fun z : Fin r×K=>canonicalRoot D K false z.1 z.2) := by
    ext x
    constructor
    · rintro ⟨y,⟨z,rfl⟩,rfl⟩
      exact ⟨z,rfl⟩
    · rintro ⟨z,rfl⟩
      exact ⟨positiveRoot A hd hs hp ho K z.1 z.2,⟨z,rfl⟩,rfl⟩
  rw [himage]
  rfl

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingHom
