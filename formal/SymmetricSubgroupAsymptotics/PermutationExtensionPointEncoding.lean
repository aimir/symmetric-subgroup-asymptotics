import Mathlib.Algebra.Group.End
import Mathlib.Logic.Equiv.Fin.Basic

/-! A raw point map extends by fixing every new point. Its genuine typed
shadow is the permutation homomorphism extendDomainHom. This transports
already checked packed rows without producing any new permutation table. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.PermutationExtensionPointEncoding

def rawExtension (m : ℕ) (raw : ℕ → ℕ) (p : ℕ) : ℕ :=
  if p < m then raw p else p

theorem rawExtension_point_eq {m n : ℕ} (hmn : m ≤ n)
    (g : Equiv.Perm (Fin m)) (raw : ℕ → ℕ)
    (hraw : ∀ p : Fin m, raw p.val = (g p).val) (p : Fin n) :
    rawExtension m raw p.val =
      ((Equiv.Perm.extendDomainHom (Fin.castLEquiv hmn) g) p).val := by
  by_cases hp : p.val < m
  · let q : Fin m := ⟨p.val,hp⟩
    have he : p = q.castLE hmn := Fin.ext rfl
    have hc : (Equiv.Perm.extendDomainHom (Fin.castLEquiv hmn) g)
        (q.castLE hmn) = (g q).castLE hmn :=
      Equiv.Perm.extendDomain_apply_image g (Fin.castLEquiv hmn) q
    rw [he,hc]
    change (if q.val < m then raw q.val else q.val) = (g q).val
    rw [if_pos q.isLt]
    exact hraw q
  · have hf : (Equiv.Perm.extendDomainHom (Fin.castLEquiv hmn) g) p = p :=
      Equiv.Perm.extendDomain_apply_not_subtype g (Fin.castLEquiv hmn) hp
    simp only [rawExtension,if_neg hp,hf]

end SymmetricSubgroupAsymptotics.PermutationExtensionPointEncoding
