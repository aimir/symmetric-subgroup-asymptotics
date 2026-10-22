import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOpposedSpaces

/-! In the original split quadratic space, negative dilation is an actual
similitude for EVERY nonzero scalar. There is no anisotropic middle
coordinate or square obstruction. Linear pieces fixing both coordinate
halves therefore give this SAME dilation on every original singular ray. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDNegativeDilation
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexPositiveGraph CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDOpposedSpaces
open CFSGOrthogonalDIndexQuadraticSubspacePoints
variable (K : Type) [Field K]

def map (r : ℕ) (t : K) : (Index r→K)→ₗ[K](Index r→K) where
  toFun v := Sum.elim (fun i=>v (Sum.inl i)) (fun i=>t*v (Sum.inr i))
  map_add' v w := by
    funext i
    cases i <;> simp [mul_add]
  map_smul' a v := by
    funext i
    cases i <;> simp [mul_left_comm]

theorem map_decompose (r : ℕ) (t : K) (v : Index r→K) :
    map K r t v=positiveEmbedding K r (leftPart K v)+t•negativeEmbedding K r (rightPart K v) := by
  funext i
  cases i <;> simp [map,positiveEmbedding,positiveEquiv,negativeEmbedding,negativeEquiv,
    leftPart,rightPart]

theorem map_quadratic (r : ℕ) (t : K) (v : Index r→K) :
    splitQuadraticForm K r (map K r t v)=t*splitQuadraticForm K r v := by
  rw [splitQuadraticForm_apply,splitQuadraticForm_apply]
  change leftPart K v ⬝ᵥ (t•rightPart K v)=t*(leftPart K v ⬝ᵥ rightPart K v)
  rw [dotProduct_smul]
  rfl

def equiv (r : ℕ) (t : K) (ht : t≠0) : (Index r→K)≃ₗ[K](Index r→K) where
  __ := map K r t
  invFun := map K r t⁻¹
  left_inv v := by
    funext i
    cases i <;> simp [map,ht]
  right_inv v := by
    funext i
    cases i <;> simp [map,ht]

theorem exists_dilation (s : ℕ)
    (f : Points (splitQuadraticForm K (s+3))≃Points (splitQuadraticForm K (s+3)))
    (hlinear : ∀W : Subspaces (splitQuadraticForm K (s+3)),Module.finrank K W.val=s+3 →
      Nonempty (SemilinearPiece (splitQuadraticForm K (s+3)) f W (RingEquiv.refl K)))
    (hfixP : ∀R : Points (splitQuadraticForm K (s+3)),R.val≤positiveSpace K (s+3) → f R=R)
    (hfixZ : ∀R : Points (splitQuadraticForm K (s+3)),R.val≤negativeSpace K (s+3) → f R=R) :
    ∃t : K,t≠0 ∧ ∀(v : Index (s+3)→K) (hv0 : v≠0)
      (hv : splitQuadraticForm K (s+3) v=0),
        (f (ray (splitQuadraticForm K (s+3)) v hv0 hv)).val=
          Submodule.span K {map K (s+3) t v} := by
  obtain ⟨t,ht,htr⟩ := exists_common_ratio K s f hlinear hfixP hfixZ
  refine ⟨t,ht,?_⟩
  intro v hv0 hv
  let q := splitQuadraticForm K (s+3)
  let x := positiveEmbedding K (s+3) (leftPart K v)
  let y := negativeEmbedding K (s+3) (rightPart K v)
  have hx : x∈positiveSpace K (s+3) := (positiveEquiv K (s+3) (leftPart K v)).property
  have hy : y∈negativeSpace K (s+3) := (negativeEquiv K (s+3) (rightPart K v)).property
  have he : v=x+y := decompose K (s+3) v
  have hemap : map K (s+3) t v=x+t•y := map_decompose K (s+3) t v
  let R := ray q v hv0 hv
  by_cases hx0 : x=0
  · have hvy : v=y := by simpa only [hx0,zero_add] using he
    have hRy : R.val≤negativeSpace K (s+3) := by
      apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      rw [hvy]
      exact hy
    rw [hfixZ R hRy]
    change Submodule.span K {v}=Submodule.span K {map K (s+3) t v}
    rw [hemap,hx0,zero_add,←hvy]
    exact (Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ht) v).symm
  by_cases hy0 : y=0
  · have hvx : v=x := by simpa only [hy0,add_zero] using he
    have hRx : R.val≤positiveSpace K (s+3) :=
      (Submodule.span_singleton_le_iff_mem _ _).mpr (hvx ▸ hx)
    rw [hfixP R hRx]
    change Submodule.span K {v}=Submodule.span K {map K (s+3) t v}
    rw [hemap,hy0,smul_zero,add_zero,←hvx]
  have hxy : q.polarBilin y x=0 := by
    have heQ : q (x+y)=0 := he ▸ hv
    rw [QuadraticMap.map_add q x y] at heQ
    change q x+q y+q.polarBilin x y=0 at heQ
    rw [positiveSpace_singular K (s+3) ⟨x,hx⟩,
      negativeSpace_singular K (s+3) y hy,zero_add,zero_add] at heQ
    exact (QuadraticMap.polar_comm q y x).trans heQ
  have hsum0 : x+y≠0 := fun h=>hv0 (he.trans h)
  have hsum : q (x+y)=0 := he ▸ hv
  have hr : ray q (x+y) hsum0 hsum=R := by
    apply Subtype.ext
    exact congrArg (fun z=>Submodule.span K {z}) he.symm
  have h := htr x y hx hx0 hy hy0 hxy hsum0 hsum
  rw [hr] at h
  rw [hemap]
  exact h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDNegativeDilation
