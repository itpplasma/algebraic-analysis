/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Algebra.Polynomial.Laurent

/-!
# Diagonal regrading of iterated Laurent polynomials

This file supplies the finite-support change of exponents
`(ell, q) ↦ (ell - q - A, B + q)`. The unshifted part is a ring
homomorphism; the affine offsets are applied by a separate monomial.
-/

noncomputable section

namespace LaurentPolynomial

variable {R : Type*} [CommRing R]

/-- Laurent polynomials in an outer variable with Laurent-polynomial coefficients. -/
abbrev Iterated (R : Type*) [CommRing R] :=
  _root_.LaurentPolynomial (_root_.LaurentPolynomial R)

/-- The canonical unit whose value is the Laurent monomial `T n`. -/
def monomialUnit {A : Type*} [CommRing A] (n : ℤ) :
    (_root_.LaurentPolynomial A)ˣ :=
  Units.mkOfMulEqOne (T n : _root_.LaurentPolynomial A) (T (-n)) (by
    rw [← T_add, add_neg_cancel, T_zero])

@[simp] theorem monomialUnit_coe {A : Type*} [CommRing A] (n : ℤ) :
    ((monomialUnit n : (_root_.LaurentPolynomial A)ˣ) :
      _root_.LaurentPolynomial A) = T n := rfl

@[simp] theorem monomialUnit_inv_coe {A : Type*} [CommRing A] (n : ℤ) :
    ((((monomialUnit n : (_root_.LaurentPolynomial A)ˣ)⁻¹ :
      (_root_.LaurentPolynomial A)ˣ)) : _root_.LaurentPolynomial A) =
      T (-n) := rfl

/-- Integer powers of Laurent monomial units multiply their exponents. -/
theorem monomialUnit_zpow_coe {A : Type*} [CommRing A] (m n : ℤ) :
    (((monomialUnit m : (_root_.LaurentPolynomial A)ˣ) ^ n :
      (_root_.LaurentPolynomial A)ˣ) : _root_.LaurentPolynomial A) =
      T (n * m) := by
  cases n with
  | ofNat n =>
      simp [zpow_natCast, Units.val_pow_eq_pow_val, T_pow]
  | negSucc n =>
      simp [zpow_negSucc, T_pow]
      congr 1
      simp only [Int.negSucc_eq]
      ring

/-- On the coefficient Laurent variable, send `T q` to `T (-q) * C (T q)`. -/
def innerDiagonalMap :
    _root_.LaurentPolynomial R →+* Iterated R :=
  eval₂ (algebraMap R (Iterated R))
    ((monomialUnit (-1) : (Iterated R)ˣ) *
      Units.map
        (algebraMap (_root_.LaurentPolynomial R) (Iterated R)).toMonoidHom
        (monomialUnit 1 : (_root_.LaurentPolynomial R)ˣ))

/-- The unshifted diagonal regrading `(ell, q) ↦ (ell - q, q)`. -/
def diagonalMap : Iterated R →+* Iterated R :=
  eval₂ innerDiagonalMap (monomialUnit 1)

/-- Diagonal regrading followed by the affine shift `(-A, B)`. -/
def affineDiagonal (A B : ℤ) (p : Iterated R) : Iterated R :=
  T (-A) * C (T B) * diagonalMap p

/-- Exact action of the affine diagonal regrading on a Laurent monomial. -/
theorem affineDiagonal_monomial (A B ell q : ℤ) :
    affineDiagonal A B
        ((C (T q) : Iterated R) * (T ell : Iterated R)) =
      (T (ell - q - A) : Iterated R) *
        (C (T (B + q)) : Iterated R) := by
  let u : (Iterated R)ˣ :=
    (monomialUnit (-1) : (Iterated R)ˣ) *
      Units.map
        (algebraMap (_root_.LaurentPolynomial R) (Iterated R)).toMonoidHom
        (monomialUnit 1 : (_root_.LaurentPolynomial R)ˣ)
  have hpow (q : ℤ) :
      (((u ^ q : (Iterated R)ˣ) : Iterated R)) =
        T (-q) * C (T q : _root_.LaurentPolynomial R) := by
    rw [show u ^ q = (monomialUnit (-1) : (Iterated R)ˣ) ^ q *
        (Units.map
          (algebraMap (_root_.LaurentPolynomial R) (Iterated R)).toMonoidHom
          (monomialUnit 1 : (_root_.LaurentPolynomial R)ˣ)) ^ q by
            dsimp [u]
            exact mul_zpow (α := (Iterated R)ˣ)
              (monomialUnit (-1) : (Iterated R)ˣ)
              (Units.map
                (algebraMap (_root_.LaurentPolynomial R)
                  (Iterated R)).toMonoidHom
                (monomialUnit 1 : (_root_.LaurentPolynomial R)ˣ)) q]
    rw [← map_zpow
      (Units.map
        (algebraMap (_root_.LaurentPolynomial R) (Iterated R)).toMonoidHom)
      (monomialUnit 1 : (_root_.LaurentPolynomial R)ˣ) q]
    simp only [Units.val_mul, Units.coe_map, monomialUnit_zpow_coe]
    change T (q * -1) * C (T (q * 1) : _root_.LaurentPolynomial R) =
      T (-q) * C (T q : _root_.LaurentPolynomial R)
    simp
  simp [affineDiagonal, diagonalMap, innerDiagonalMap,
    LaurentPolynomial.eval₂_C_mul_T]
  change C (T B) * T (-A) *
      (((u ^ q : (Iterated R)ˣ) : Iterated R) *
        ((((monomialUnit 1 : (Iterated R)ˣ) ^ ell :
          (Iterated R)ˣ) : Iterated R))) =
    C (T (B + q)) * T (ell - q - A)
  rw [hpow q, monomialUnit_zpow_coe]
  calc
    (C (T B) : Iterated R) * T (-A) *
        (T (-q) * (C (T q) : Iterated R) * T (ell * 1)) =
        (C (T B) : Iterated R) * (C (T q) : Iterated R) *
          (T (-A) * T (-q) * T (ell * 1)) := by ac_rfl
    _ = (C (T (B + q)) : Iterated R) * T ((-A + -q) + (ell * 1)) := by
      rw [← map_mul C, ← T_add, ← T_add, ← T_add]
    _ = (C (T (B + q)) : Iterated R) * T (ell - q - A) := by
      congr 2
      ring

end LaurentPolynomial
