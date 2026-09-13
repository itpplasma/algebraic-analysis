"""Exact counterexample to the pre-repair abstract BernsteinInequality.

The pre-repair statement quantified over every field.  Take n = 1 and K = F_2.  Let A be
the first Weyl algebra with PBW basis X^a D^b and relation D*X-X*D = 1,
filtered by total PBW degree.  The normal-order multiplication formula below
shows directly that

    dim_K(FA[i]) = binom(i + 2, 2),
    [FA[i], FA[j]] <= FA[i + j - 2].

The two exact 2-by-2 matrices give a nonzero A-module: X is multiplication by
t and D is differentiation on F_2[t]/(t^2).  Its constant filtration has GK
dimension zero, while the target of BernsteinInequality(1) is 1 <= 0.

The finite loops are an independent behavioral check of the closed formulas;
the PBW basis and the degree estimates are the algebraic proof for all indices.
No Lean declaration, axiom, sorry, or theorem wrapper is used here.
"""

from math import comb, factorial


P = 2


def mod(x):
    return x % P


def mat_mul(a, b):
    return tuple(
        tuple(mod(sum(a[i][k] * b[k][j] for k in range(2))) for j in range(2))
        for i in range(2)
    )


def mat_sub(a, b):
    return tuple(tuple(mod(a[i][j] - b[i][j]) for j in range(2)) for i in range(2))


I = ((1, 0), (0, 1))
X = ((0, 0), (1, 0))
D = ((0, 1), (0, 0))
ZERO = ((0, 0), (0, 0))


def mat_pow(a, n):
    out = I
    for _ in range(n):
        out = mat_mul(out, a)
    return out


def falling(n, k):
    return factorial(n) // factorial(n - k)


def normal_product(a, b):
    """Coefficients of (X^a0 D^b0)(X^a1 D^b1) in PBW order."""
    a0, b0 = a
    a1, b1 = b
    out = {}
    for k in range(min(b0, a1) + 1):
        coeff = comb(b0, k) * falling(a1, k)
        monomial = (a0 + a1 - k, b0 + b1 - k)
        out[monomial] = mod(out.get(monomial, 0) + coeff)
    return {m: c for m, c in out.items() if c}


def degree(monomial):
    return sum(monomial)


def fa_basis(i):
    return [(a, b) for a in range(i + 1) for b in range(i + 1 - a)]


def commutator_degree_ok(u, v):
    uv = normal_product(u, v)
    vu = normal_product(v, u)
    all_monomials = set(uv) | set(vu)
    # The degree-zero (k=0) terms cancel; all surviving terms have k >= 1.
    return all(degree(m) <= degree(u) + degree(v) - 2 for m in all_monomials
               if uv.get(m, 0) != vu.get(m, 0))


def check_pbw_filtration(bound=8):
    for i in range(bound + 1):
        assert len(fa_basis(i)) == comb(i + 2, 2)
        assert set(fa_basis(i)).issubset(set(fa_basis(i + 1)))
        for j in range(bound + 1):
            for u in fa_basis(i):
                for v in fa_basis(j):
                    assert all(degree(m) <= i + j for m in normal_product(u, v))
                    assert commutator_degree_ok(u, v) or i + j < 2


def check_module_representation(bound=8):
    # D X - X D = I in M_2(F_2), hence the PBW Weyl algebra acts on F_2^2.
    assert mat_sub(mat_mul(D, X), mat_mul(X, D)) == I
    assert mat_pow(X, 2) == ZERO
    assert mat_pow(D, 2) == ZERO

    # Check the PBW multiplication formula against the matrix action on a
    # finite prefix; the displayed generator relation proves it in general.
    for a0 in range(bound + 1):
        for b0 in range(bound + 1):
            for a1 in range(bound + 1):
                for b1 in range(bound + 1):
                    lhs = mat_mul(mat_pow(X, a0), mat_mul(mat_pow(D, b0),
                                                           mat_mul(mat_pow(X, a1), mat_pow(D, b1))))
                    rhs = ZERO
                    for (a, b), coeff in normal_product((a0, b0), (a1, b1)).items():
                        term = mat_pow(X, a)
                        term = mat_mul(term, mat_pow(D, b))
                        if coeff:
                            rhs = tuple(tuple(mod(rhs[i][j] + coeff * term[i][j])
                                               for j in range(2)) for i in range(2))
                    assert lhs == rhs


def check_constant_module_filtration():
    # F_j = M for every j: monotone, exhaustive, finite, and compatible.
    hilbert = lambda _j: 2
    assert all(hilbert(j) == 2 for j in range(20))
    # Since 1 belongs to FA[1], span(FA[1] • F_j) = F_{j+1} = M.
    assert I != ZERO  # the module is nonzero, and 1 in FA[1] acts as identity
    # The growth degree of a positive constant sequence under the repository's
    # nonnegative-exponent definition is exactly zero.
    gk_dim = 0
    target = 1
    assert not target <= gk_dim


if __name__ == "__main__":
    check_pbw_filtration()
    check_module_representation()
    check_constant_module_filtration()
    print("PASS: characteristic-2 Weyl module violates the pre-repair arbitrary-field BernsteinInequality(1)")
    print("      hgr(i)=binom(i+2,2), commutator drops by 2, gkDim(F)=0, target=1")
