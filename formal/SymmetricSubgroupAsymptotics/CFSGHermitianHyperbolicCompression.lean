import SymmetricSubgroupAsymptotics.CFSGHermitianPairTransport
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperIsometry

/-! Compression of an actual isotropic subspace containing the first
hyperbolic axis. The middle space is a literal linear preimage, and the
displayed decomposition retains the first coordinate. No extension or
transitivity theorem for a classical group is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGHermitianHyperbolicCompression
open CFSGTwistedAUnitaryUpperArrays CFSGTwistedAUnitaryParameters
variable {K J : Type*} [Field K] [Fintype J]

def headVector : Index J → K
  | .inl _ => 1
  | .inr _ => 0

def middleVector : (J → K) →ₗ[K] (Index J → K) where
  toFun v := fun p => match p with
    | .inl _ => 0
    | .inr (.inl i) => v i
    | .inr (.inr _) => 0
  map_add' v w := by ext (u | (i | u)) <;> simp
  map_smul' a v := by ext (u | (i | u)) <;> simp

def middleProjection : (Index J → K) →ₗ[K] (J → K) where
  toFun x := fun i => x (.inr (.inl i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem middleProjection_middleVector (v : J → K) :
    middleProjection (middleVector v) = v := rfl

theorem middleVector_injective : Function.Injective (middleVector (K := K) (J := J)) := by
  intro v w h
  exact congrArg (middleProjection (K := K) (J := J)) h

theorem vector_decomposition (x : Index J → K) (hx : x (.inr (.inr ())) = 0) :
    x = x (.inl ()) • headVector + middleVector (middleProjection x) := by
  ext (u | (i | u))
  · cases u
    simp [headVector, middleVector]
  · simp [headVector, middleVector, middleProjection]
  · cases u
    simpa [headVector, middleVector] using hx

theorem block_pair (sigma : K ≃+* K) (eps : K) (H : Matrix J J K)
    (x y : Index J → K) :
    hermitianPair sigma (blockForm eps H) x y =
      sigma (x (.inl ())) * y (.inr (.inr ())) +
        hermitianPair sigma H (middleProjection x) (middleProjection y) +
        eps * sigma (x (.inr (.inr ()))) * y (.inl ()) := by
  simp [hermitianPair, middleProjection, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, blockForm, Function.comp_apply, mul_add,
    add_assoc, mul_assoc, mul_comm eps]

theorem head_pair (sigma : K ≃+* K) (eps : K) (H : Matrix J J K)
    (x : Index J → K) :
    hermitianPair sigma (blockForm eps H) headVector x = x (.inr (.inr ())) := by
  rw [block_pair]
  have hzero : sigma ∘ (0 : J → K) = 0 := by
    ext i
    exact map_zero sigma
  change sigma 1 * x (.inr (.inr ())) +
    dotProduct (sigma ∘ (0 : J → K)) (H *ᵥ middleProjection x) +
    eps * sigma 0 * x (.inl ()) = x (.inr (.inr ()))
  rw [hzero, zero_dotProduct]
  simp only [map_one, map_zero, one_mul, mul_zero, zero_mul, add_zero]

theorem middle_pair (sigma : K ≃+* K) (eps : K) (H : Matrix J J K)
    (v w : J → K) :
    hermitianPair sigma (blockForm eps H) (middleVector v) (middleVector w) =
      hermitianPair sigma H v w := by
  rw [block_pair]
  simp [middleVector, middleProjection]

def compressedSpace (S : Submodule K (Index J → K)) : Submodule K (J → K) :=
  S.comap middleVector

theorem last_zero_of_pair_zero (sigma : K ≃+* K) (eps : K) (H : Matrix J J K)
    (S : Submodule K (Index J → K)) (he : headVector ∈ S)
    (hS : ∀ x ∈ S, ∀ y ∈ S, hermitianPair sigma (blockForm eps H) x y = 0)
    (x : Index J → K) (hx : x ∈ S) : x (.inr (.inr ())) = 0 := by
  simpa only [head_pair] using hS headVector he x hx

theorem middleProjection_mem (S : Submodule K (Index J → K))
    (he : headVector ∈ S) (hz : ∀ x ∈ S, x (.inr (.inr ())) = 0)
    (x : Index J → K) (hx : x ∈ S) : middleProjection x ∈ compressedSpace S := by
  change middleVector (middleProjection x) ∈ S
  have h := S.sub_mem hx (S.smul_mem (x (.inl ())) he)
  have heq : x - x (.inl ()) • headVector = middleVector (middleProjection x) :=
    sub_eq_iff_eq_add.mpr ((vector_decomposition x (hz x hx)).trans (add_comm _ _))
  exact heq ▸ h

theorem compressed_pair_zero (sigma : K ≃+* K) (eps : K) (H : Matrix J J K)
    (S : Submodule K (Index J → K))
    (hS : ∀ x ∈ S, ∀ y ∈ S, hermitianPair sigma (blockForm eps H) x y = 0) :
    ∀ v ∈ compressedSpace S, ∀ w ∈ compressedSpace S,
      hermitianPair sigma H v w = 0 := by
  intro v hv w hw
  simpa only [middle_pair] using hS (middleVector v) hv (middleVector w) hw

def compressionEquiv (S : Submodule K (Index J → K))
    (he : headVector ∈ S) (hz : ∀ x ∈ S, x (.inr (.inr ())) = 0) :
    S ≃ₗ[K] K × compressedSpace S where
  toFun x := (x.val (.inl ()), ⟨middleProjection x.val, middleProjection_mem S he hz _ x.property⟩)
  invFun p := ⟨p.1 • headVector + middleVector p.2.val,
    S.add_mem (S.smul_mem p.1 he) p.2.property⟩
  left_inv x := by
    apply Subtype.ext
    exact (vector_decomposition x.val (hz x.val x.property)).symm
  right_inv p := by
    apply Prod.ext
    · simp [headVector, middleVector]
    · apply Subtype.ext
      ext i
      simp [headVector, middleVector, middleProjection]
  map_add' x y := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl
  map_smul' a x := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl

end SymmetricSubgroupAsymptotics.CFSGHermitianHyperbolicCompression
