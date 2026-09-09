#!/usr/bin/env python3
"""Numerical checks for the Kanade--Russell identities and auxiliary identities.

Checks use truncated integer power series and Python's standard library.
They guard against transcription errors in exponents, signs, and
normalizations, but are not proofs.

Conventions follow Y. Mizuno, The three Kanade--Russell identities modulo
nine (2026). Series in q are coefficient lists truncated at degree N.
Series in t with q = t^4 are truncated at degree 4N. Bivariate series in
(q, x) are lists of lists truncated at q-degree N and x-degree M.

Run: python check_statements.py [--order N] [--xorder M]
"""

import argparse
import sys

# --------------------------------------------------------------------------
# Truncated univariate integer series
# --------------------------------------------------------------------------


class S:
    """Truncated power series with integer coefficients, degree <= N."""

    def __init__(self, coeffs, N):
        self.N = N
        c = list(coeffs)[: N + 1]
        c += [0] * (N + 1 - len(c))
        self.c = c

    @staticmethod
    def const(a, N):
        return S([a], N)

    @staticmethod
    def mono(k, N, a=1):
        if k < 0:
            raise ValueError("negative exponent %d" % k)
        c = [0] * (N + 1)
        if k <= N:
            c[k] = a
        return S(c, N)

    def __add__(self, o):
        o = _lift(o, self.N)
        return S([a + b for a, b in zip(self.c, o.c)], self.N)

    def __sub__(self, o):
        o = _lift(o, self.N)
        return S([a - b for a, b in zip(self.c, o.c)], self.N)

    def __neg__(self):
        return S([-a for a in self.c], self.N)

    def __mul__(self, o):
        o = _lift(o, self.N)
        N = self.N
        out = [0] * (N + 1)
        for i, a in enumerate(self.c):
            if a == 0:
                continue
            oc = o.c
            for j in range(N + 1 - i):
                b = oc[j]
                if b:
                    out[i + j] += a * b
        return S(out, N)

    __radd__ = __add__
    __rmul__ = __mul__

    def __rsub__(self, o):
        return _lift(o, self.N) - self

    def shift(self, k):
        """Multiply by q^k (k >= 0)."""
        if k < 0:
            raise ValueError("negative shift %d" % k)
        return S([0] * k + self.c, self.N)

    def inv(self):
        if self.c[0] not in (1, -1):
            raise ValueError("not a unit: constant term %d" % self.c[0])
        N = self.N
        u = self.c[0]
        out = [0] * (N + 1)
        out[0] = u
        for n in range(1, N + 1):
            s = 0
            for k in range(1, n + 1):
                s += self.c[k] * out[n - k]
            out[n] = -u * s
        return S(out, N)

    def __eq__(self, o):
        o = _lift(o, self.N)
        return self.c == o.c

    def is_zero(self):
        return all(a == 0 for a in self.c)

    def subs_pow(self, d):
        """f(q) -> f(q^d), same truncation degree."""
        out = [0] * (self.N + 1)
        for i, a in enumerate(self.c):
            if i * d <= self.N:
                out[i * d] = a
        return S(out, self.N)

    def lift4(self, NT):
        """f(q) -> f(t^4) as a t-series truncated at degree NT (NT <= 4N+3)."""
        assert NT <= 4 * self.N + 3
        return S([self.c[i // 4] if i % 4 == 0 else 0 for i in range(NT + 1)], NT)

    def neg_var(self):
        """f(t) -> f(-t)."""
        return S([a * (1 if i % 2 == 0 else -1) for i, a in enumerate(self.c)], self.N)

    def even_part(self):
        return S([a if i % 2 == 0 else 0 for i, a in enumerate(self.c)], self.N)

    def odd_part_div(self):
        """(f(t) - f(-t)) / (2 t)."""
        return S([self.c[i + 1] if i % 2 == 0 else 0 for i in range(self.N)], self.N)

    def truncate(self, D):
        return S(self.c[: D + 1], D)


def _lift(o, N):
    if isinstance(o, S):
        assert o.N == N, "mixed truncation orders"
        return o
    return S.const(o, N)


def poch_inf(a_exp, q_exp, N):
    """(q^a; q^b)_infinity, a >= 1, b >= 1."""
    out = S.const(1, N)
    k = a_exp
    while k <= N:
        out = out * (S.const(1, N) - S.mono(k, N))
        k += q_exp
    return out


def poch_inv_table(q_exp, N, up_to):
    """bInv (q^b; q^b)_n for n = 0..up_to."""
    tab = []
    cur = S.const(1, N)
    for n in range(up_to + 1):
        tab.append(cur.inv())
        cur = cur * (S.const(1, N) - S.mono(q_exp * (n + 1), N))
    return tab


# --------------------------------------------------------------------------
# Bivariate truncated series in (q, x): c[i][j] is the coefficient of q^i x^j
# --------------------------------------------------------------------------


class B:
    def __init__(self, N, M, rows=None):
        self.N, self.M = N, M
        if rows is None:
            rows = [[0] * (M + 1) for _ in range(N + 1)]
        self.c = rows

    @staticmethod
    def const(a, N, M):
        b = B(N, M)
        b.c[0][0] = a
        return b

    @staticmethod
    def mono(i, j, N, M, a=1):
        b = B(N, M)
        if 0 <= i <= N and 0 <= j <= M:
            b.c[i][j] = a
        return b

    def add_xterm(self, s, j):
        """In place: add s(q) * x^j."""
        if j <= self.M:
            col = self.c
            for i in range(self.N + 1):
                a = s.c[i]
                if a:
                    col[i][j] += a

    def __add__(self, o):
        o = _liftB(o, self.N, self.M)
        return B(self.N, self.M, [[a + b for a, b in zip(r1, r2)] for r1, r2 in zip(self.c, o.c)])

    def __sub__(self, o):
        o = _liftB(o, self.N, self.M)
        return B(self.N, self.M, [[a - b for a, b in zip(r1, r2)] for r1, r2 in zip(self.c, o.c)])

    def __neg__(self):
        return B(self.N, self.M, [[-a for a in r] for r in self.c])

    def __mul__(self, o):
        o = _liftB(o, self.N, self.M)
        N, M = self.N, self.M
        out = [[0] * (M + 1) for _ in range(N + 1)]
        for i in range(N + 1):
            for j in range(M + 1):
                a = self.c[i][j]
                if a == 0:
                    continue
                for k in range(N + 1 - i):
                    row = o.c[k]
                    orow = out[i + k]
                    for l in range(M + 1 - j):
                        b = row[l]
                        if b:
                            orow[j + l] += a * b
        return B(N, M, out)

    __radd__ = __add__
    __rmul__ = __mul__

    def __rsub__(self, o):
        return _liftB(o, self.N, self.M) - self

    def qshift(self, k):
        """x -> q^k x."""
        out = [[0] * (self.M + 1) for _ in range(self.N + 1)]
        for i in range(self.N + 1):
            for j in range(self.M + 1):
                a = self.c[i][j]
                if a and i + k * j <= self.N:
                    out[i + k * j][j] = a
        return B(self.N, self.M, out)

    def is_zero(self):
        return all(a == 0 for r in self.c for a in r)

    def __eq__(self, o):
        return (self - o).is_zero()

    def xcoeff(self, j):
        return S([self.c[i][j] for i in range(self.N + 1)], self.N)

    def at_x_power(self, k):
        """Evaluate at x = q^k (k >= 0): sum of q^{kj} * coefficient of x^j."""
        out = S.const(0, self.N)
        for j in range(self.M + 1):
            out = out + self.xcoeff(j).shift(k * j)
        return out

    def div_x(self):
        """Divide by x; the x-order drops by one."""
        assert all(self.c[i][0] == 0 for i in range(self.N + 1))
        return B(self.N, self.M - 1, [[row[j + 1] for j in range(self.M)] for row in self.c])

    def trunc_x(self, M2):
        return B(self.N, M2, [row[: M2 + 1] for row in self.c])


def _liftB(o, N, M):
    if isinstance(o, B):
        assert (o.N, o.M) == (N, M), "mixed truncation orders"
        return o
    if isinstance(o, S):
        b = B(N, M)
        b.add_xterm(o, 0)
        return b
    return B.const(o, N, M)


# --------------------------------------------------------------------------
# Double sums over the quadrant
# --------------------------------------------------------------------------


def qsum(N, inv1, inv3, exp_fn, sign_fn=lambda m, n: 1, keep=lambda m, n: True):
    """sum_{m,n>=0, keep} sign(m,n) q^{exp(m,n)} / ((q;q)_m (q^3;q^3)_n), truncated at N.

    No early termination: every quadratic form used here satisfies
    exp(m,n) > N outside the box 0 <= m, n <= 2N+2.
    """
    out = S.const(0, N)
    for m in range(2 * N + 3):
        for n in range(2 * N + 3):
            if not keep(m, n):
                continue
            e = exp_fn(m, n)
            if e < 0:
                raise ValueError("negative exponent %d at (%d,%d)" % (e, m, n))
            if e > N:
                continue
            term = inv1[m] * inv3[n]
            out = out + (-term if sign_fn(m, n) < 0 else term).shift(e)
    return out


def qxsum(N, M, inv1, inv3, exp_fn, xpow, sign_fn=lambda m, n: 1, keep=lambda m, n: True):
    """Bivariate version: also multiplies by x^{xpow(m,n)}."""
    out = B(N, M)
    for m in range(2 * N + 3):
        for n in range(2 * N + 3):
            if not keep(m, n):
                continue
            j = xpow(m, n)
            if j > M:
                continue
            e = exp_fn(m, n)
            if e < 0:
                raise ValueError("negative exponent %d at (%d,%d)" % (e, m, n))
            if e > N:
                continue
            term = inv1[m] * inv3[n]
            out.add_xterm((-term if sign_fn(m, n) < 0 else term).shift(e), j)
    return out


def theta_series(N, exp_fn):
    """sum_{k in Z} q^{exp(k)} for a form growing to +infinity in both directions."""
    out = [0] * (N + 1)
    for k in range(-2 * N - 3, 2 * N + 4):
        e = exp_fn(k)
        if 0 <= e <= N:
            out[e] += 1
    return S(out, N)


def check(name, ok, failures):
    print(("PASS " if ok else "FAIL ") + name)
    if not ok:
        failures.append(name)


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--order", type=int, default=40, help="truncation order in q")
    ap.add_argument("--xorder", type=int, default=12, help="truncation order in x")
    args = ap.parse_args()
    N, M = args.order, args.xorder
    NT = 4 * N
    failures = []
    one = S.const(1, N)
    Qf = lambda m, n: m * m + 3 * m * n + 3 * n * n
    Gf = lambda m, n: m * m - 3 * m * n + 3 * n * n
    Phi4 = lambda m, n: m * m + 6 * m * n + 3 * n * n + 6 * n
    altm = lambda m, n: -1 if m % 2 else 1
    even = lambda m, n: (m - n) % 2 == 0
    odd = lambda m, n: (m - n) % 2 == 1
    inv1 = poch_inv_table(1, N, 2 * N + 3)
    inv3 = poch_inv_table(3, N, 2 * N + 3)

    # ---- the six series of the main theorem --------------------------------
    A = qsum(N, inv1, inv3, Qf)
    Bs = qsum(N, inv1, inv3, lambda m, n: Qf(m, n) + m + 3 * n)
    C = qsum(N, inv1, inv3, lambda m, n: Qf(m, n) + 2 * m + 3 * n)

    def kprod(residues):
        out = one
        for r in residues:
            out = out * poch_inf(r, 9, N)
        return out.inv()

    K1, K2, K3 = kprod([1, 3, 6, 8]), kprod([2, 3, 6, 7]), kprod([3, 4, 5, 6])
    check("KR_1: A = K1 (the theorem; sanity)", A == K1, failures)
    check("KR_2: B = K2 (the theorem; sanity)", Bs == K2, failures)
    check("KR_3: C = K3 (the theorem; sanity)", C == K3, failures)
    check("constant terms are 1", all(s.c[0] == 1 for s in (A, Bs, C, K1, K2, K3)), failures)
    check("lower bounds A-K1, B-K2, C-K3 >= 0 coefficientwise (Pending input; sanity)",
          all(all(a >= 0 for a in (X - Y).c) for X, Y in ((A, K1), (Bs, K2), (C, K3))), failures)

    # ---- Euler products, theta functions, a(q) -----------------------------
    E = lambda d: poch_inf(d, d, N)
    E1, E2, E3, E4, E9 = E(1), E(2), E(3), E(4), E(9)
    theta = theta_series(N, lambda k: k * k)
    phi = theta_series(N, lambda k: k * (k - 1))
    theta3, phi3 = theta.subs_pow(3), phi.subs_pow(3)
    a2 = S([0] * (N + 1), N)
    for r in range(-N - 1, N + 2):
        for s in range(-N - 1, N + 2):
            e = r * r + r * s + s * s
            if e <= N:
                a2.c[e] += 1
    check("a(q) = theta(q) theta(q^3) + q phi(q) phi(q^3)  [eq:a2-parity]",
          a2 == theta * theta3 + (phi * phi3).shift(1), failures)
    check("phi(q) = 2 E4^2 / E2  (JTP form; not needed for KR)",
          phi * E2 == S.const(2, N) * E4 * E4, failures)
    check("theta(q) = E2^5 / (E1^2 E4^2)  (JTP form; not needed for KR)",
          theta * E1 * E1 * E4 * E4 == E2 * E2 * E2 * E2 * E2, failures)

    # ---- cubic norm ----------------------------------------------------------
    def norm(X, Y, Z):
        return X * X * X + (Y * Y * Y).shift(1) - (Z * Z * Z).shift(2) + (X * Y * Z).shift(1) * 3

    check("source norm: E1 E3 N(A,B,C) = a(q)  [lem:equal-norms]", norm(A, Bs, C) * E1 * E3 == a2, failures)
    check("product norm: E1 E3 N(K1,K2,K3) = a(q)  [lem:equal-norms]", norm(K1, K2, K3) * E1 * E3 == a2, failures)

    # ---- G values and the quadratic bridge ----------------------------------
    G11 = qsum(N, inv1, inv3, Gf)
    Gq1 = qsum(N, inv1, inv3, lambda m, n: Gf(m, n) + m)
    Gqinv = qsum(N, inv1, inv3, lambda m, n: Gf(m, n) - m + 3 * n)
    U, V, W = A * A + (Bs * C).shift(1), Bs * Bs + A * C, A * Bs - (C * C).shift(1)
    check("G(1,1) = A^2 + q B C  [eq:app-quadratic-bridge]", G11 == U, failures)
    check("G(q^-1,q^3) = B^2 + A C", Gqinv == V, failures)
    check("G(q,1) = A B - q C^2", Gq1 == W, failures)
    check("W^2 - U V = -C N(A,B,C)  [eq:norm-determinant-factorization]",
          W * W - U * V == -(C * norm(A, Bs, C)), failures)

    # ---- parity rows with integral exponents --------------------------------
    check("Phi4(m,n) = 0 mod 4 iff m = n mod 2",
          all((Phi4(m, n) % 4 == 0) == even(m, n) and (Phi4(m, n) % 4 in (0, 1))
              for m in range(14) for n in range(14)), failures)
    A1 = qsum(N, inv1, inv3, lambda m, n: Phi4(m, n) // 4, altm, even)
    B1 = qsum(N, inv1, inv3, lambda m, n: (Phi4(m, n) - 1) // 4, altm, odd)
    A2 = qsum(N, inv1, inv3, lambda m, n: Phi4(m, n) // 4 + m, altm, even)
    B2 = qsum(N, inv1, inv3, lambda m, n: (Phi4(m, n) - 1) // 4 + m, altm, odd)

    # ---- the four theta functionals and the Casoratian ---------------------
    check("short 1: phi A1 + theta B1 = E1 G(q,1)  [eq:source-short]", phi * A1 + theta * B1 == E1 * Gq1, failures)
    check("short 2: phi A2 + theta B2 = E1 G(q^-1,q^3)", phi * A2 + theta * B2 == E1 * Gqinv, failures)
    check("long 1: theta3 A1 - q phi3 B1 = E3 G(1,1)  [eq:source-long]",
          theta3 * A1 - (phi3 * B1).shift(1) == E3 * G11, failures)
    check("long 2: theta3 A2 - q phi3 B2 = E3 G(q,1)", theta3 * A2 - (phi3 * B2).shift(1) == E3 * Gq1, failures)
    check("Casoratian M12 = A1 B2 - A2 B1 = C  [eq:source-minors]", A1 * B2 - A2 * B1 == C, failures)
    check("determinant: M12 a(q) = E1 E3 (U V - W^2)",
          (A1 * B2 - A2 * B1) * a2 == E1 * E3 * (U * V - W * W), failures)

    # ---- D-Euler: the functionals via Euler's identity instead of Morita ---
    # Cleared vanishing Euler (Q generic): sum_n (-1)^n Q^{(n-nu)(n-nu+1)/2}/(Q;Q)_n = 0 (nu >= 1).
    ok = True
    for nu in range(1, 7):
        tot = S.const(0, N)
        for n in range(2 * N + 3):
            e = (n - nu) * (n - nu + 1) // 2
            if e <= N:
                tot = tot + (-inv1[n] if n % 2 else inv1[n]).shift(e)
        ok = ok and tot.is_zero()
    check("cleared vanishing Euler: sum_n (-1)^n Q^{(n-nu)(n-nu+1)/2}/(Q;Q)_n = 0 for nu >= 1", ok, failures)
    ok = True
    for nu in range(0, 6):
        tot = S.const(0, N)
        for n in range(2 * N + 3):
            e = n * (n - 1) // 2 + (1 + nu) * n
            if e <= N:
                tot = tot + (-inv1[n] if n % 2 else inv1[n]).shift(e)
        ok = ok and tot == poch_inf(1 + nu, 1, N)
    check("Euler: sum_n (-1)^n Q^{n(n-1)/2 + (1+nu) n}/(Q;Q)_n = (Q^{1+nu};Q)_inf for nu >= 0", ok, failures)

    # Long functional, fixed m, in the t-world (q = t^4), Q = q^3 = t^12:
    #   sum_{n>=0} sum_{ell = m+n (2)} (-1)^n t^{m^2+6mn+3n^2+6n+3 ell^2} / (Q;Q)_n
    #   = q^{m^2} E3 sum_{n>=0} q^{3n^2-3mn} / (Q;Q)_n .
    inv3t = [s.lift4(NT) for s in inv3]
    E3t = E3.lift4(NT)
    ok = True
    for m in range(0, 6):
        lhs = S.const(0, NT)
        for n in range(2 * N + 3):
            base = m * m + 6 * m * n + 3 * n * n + 6 * n
            if base > NT:
                continue
            ell = (m + n) % 2
            while base + 3 * ell * ell <= NT:
                mult = 1 if ell == 0 else 2
                term = inv3t[n].shift(base + 3 * ell * ell) * mult
                lhs = lhs + (-term if n % 2 else term)
                ell += 2
        rhs = S.const(0, NT)
        for n in range(2 * N + 3):
            e = 4 * (m * m + 3 * n * n - 3 * m * n)
            if e <= NT:
                rhs = rhs + inv3t[n].shift(e)
        ok = ok and lhs == rhs * E3t
    check("long functional, fixed-m inner identity in t (Euler route)", ok, failures)

    # Short functional, fixed n, in the t-world, base q = t^4:
    #   sum_{m>=0} sum_{k = m+n+1 (2)} (-1)^m t^{k^2 + m^2+6mn+3n^2+6n} / (q;q)_m
    #   = t^{?}: the odd part of theta(t) U_1(t) collects k + m + n odd.  Checked globally below.

    # ---- t-world formulation of the functionals (parity recombination) -----
    inv1t = [s.lift4(NT) for s in inv1]

    def Ut(k):
        out = S.const(0, NT)
        for m in range(2 * N + 3):
            for n in range(2 * N + 3):
                e = Phi4(m, n) + 4 * k * m
                if e <= NT:
                    term = inv1t[m] * inv3t[n]
                    out = out + (-term if m % 2 else term).shift(e)
        return out

    U1t, U5t = Ut(0), Ut(1)
    L = lambda s: s.lift4(NT)
    check("U_1(t) = A_1(q) + t B_1(q)  [eq:parity-recombination]", U1t == L(A1) + L(B1).shift(1), failures)
    check("U_5(t) = A_2(q) + t B_2(q)", U5t == L(A2) + L(B2).shift(1), failures)
    thetat = theta_series(NT, lambda k: k * k)
    theta3t = theta_series(NT, lambda k: 3 * k * k)
    check("theta(t) = theta(q) + t phi(q)", thetat == L(theta) + L(phi).shift(1), failures)
    check("theta(t^3) = theta(q^3) + t^3 phi(q^3)", theta3t == L(theta3) + L(phi3).shift(3), failures)
    NT4 = NT - 4  # odd_part_div loses the top coefficient
    check("S1: odd part of theta(t) U_1(t) = t E1 G(q,1)",
          (thetat * U1t).odd_part_div().truncate(NT4) == L(E1 * Gq1).truncate(NT4), failures)
    check("S2: odd part of theta(t) U_5(t) = t E1 G(q^-1,q^3)",
          (thetat * U5t).odd_part_div().truncate(NT4) == L(E1 * Gqinv).truncate(NT4), failures)
    check("L1: even part of theta(-t^3) U_1(t) = E3 G(1,1)",
          (theta3t.neg_var() * U1t).even_part() == L(E3 * G11), failures)
    check("L2: even part of theta(-t^3) U_5(t) = E3 G(q,1)",
          (theta3t.neg_var() * U5t).even_part() == L(E3 * Gq1), failures)

    # ---- addition theorem and difference systems in (q, x) ------------------
    def F2(a, b, cx, dx):
        """F(q^a x^cx, q^b x^dx)."""
        return qxsum(N, M, inv1, inv3, lambda m, n: Qf(m, n) + a * m + b * n,
                     lambda m, n: cx * m + dx * n)

    def G2(a, b, cx, dx):
        return qxsum(N, M, inv1, inv3, lambda m, n: Gf(m, n) + a * m + b * n,
                     lambda m, n: cx * m + dx * n)

    x = B.mono(0, 1, N, M)
    q = B.mono(1, 0, N, M)
    a_x = F2(0, 0, 1, 0)          # a(x) = F(x,1)
    b_x = F2(1, 3, 1, 0)          # b(x) = F(qx,q^3)
    p_x = F2(1, 0, 1, 3)          # p(x) = F(qx,x^3)
    Fxx3 = F2(0, 0, 1, 3)         # F(x,x^3)
    Fqxq3x3 = F2(1, 3, 1, 3)      # F(qx,q^3x^3)
    Fq2xq3x3 = F2(2, 3, 1, 3)     # F(q^2x,q^3x^3)
    g_x = G2(0, 0, 1, 0)          # g(x) = G(x,1)
    Gminus = G2(-1, 3, 1, 0)      # G(q^-1 x, q^3)
    check("addition 0: G(x,1) = F(x,1)F(x,x^3) + q x^2 F(qx,q^3)F(q^2x,q^3x^3)  [eq:app-addition-0]",
          g_x == a_x * Fxx3 + q * x * x * b_x * Fq2xq3x3, failures)
    check("addition +: G(qx,1) = F(x,1)F(qx,q^3x^3) - q x F(q^2x,q^3)F(q^2x,q^3x^3)",
          g_x.qshift(1) == a_x * Fqxq3x3 - q * x * b_x.qshift(1) * Fq2xq3x3, failures)
    check("addition -: G(q^-1x,q^3) = x F(qx,q^3)F(qx,q^3x^3) + F(q^2x,q^3)F(x,x^3)",
          Gminus == x * b_x * Fqxq3x3 + b_x.qshift(1) * Fxx3, failures)
    scalar = lambda r: (q * r - (1 + q + q * q * x * x) * r.qshift(1) + (1 - q * q * x) * r.qshift(2)
                        + q * q * x * r.qshift(3))
    check("scalar equation E(g) = 0  [eq:app-scalar-equation]", scalar(g_x).is_zero(), failures)
    check("contiguity 1 at y=1: a(x) - a(qx) = q x b(qx)", a_x - a_x.qshift(1) == q * x * b_x.qshift(1), failures)
    check("L-system row 3: b(q^2x) = x b(x) + b(qx) - x a(qx)",
          b_x.qshift(2) == x * b_x + b_x.qshift(1) - x * a_x.qshift(1), failures)
    check("p-recurrence  [eq:app-p-recurrence]",
          p_x == (1 - q * x) * p_x.qshift(1) + q * x * (1 + q + q * q * x * x) * p_x.qshift(2)
          + q * q * q * q * x * x * p_x.qshift(3), failures)
    check("bridge: F(x,x^3) = p(x) + q x p(qx)  [eq:app-p-bridges]", Fxx3 == p_x + q * x * p_x.qshift(1), failures)
    check("bridge: F(qx,q^3x^3) = p(qx) + q^2 x p(q^2x)",
          Fqxq3x3 == p_x.qshift(1) + q * q * x * p_x.qshift(2), failures)
    check("bridge: F(q^2x,q^3x^3) = p(qx)", Fq2xq3x3 == p_x.qshift(1), failures)
    check("q x G(q^-1x,q^3) = g(x) - g(qx) - q x g(q^2x)",
          q * x * Gminus == g_x - g_x.qshift(1) - q * x * g_x.qshift(2), failures)
    check("initial data: g(0) = a(0), [x]g = [x](F(x,1)F(x,x^3))  [eq:app-g-initial]",
          g_x.xcoeff(0) == a_x.xcoeff(0) and g_x.xcoeff(1) == (a_x * Fxx3).xcoeff(1), failures)

    # Full bilinear check of the certificate (eq:app-bilinear-certificate) in the
    # denominator-free form used by the plan: with f = (a, b, b(qx)) and the
    # p-basis (p(q^2x), p(q^3x), p(q^4x)), the 4-term combination of h is 0.
    h_x = a_x * Fxx3 + q * x * x * b_x * Fq2xq3x3
    check("E(h) = 0 for the right side h of addition 0", scalar(h_x).is_zero(), failures)

    # ---- Casoratian in x -----------------------------------------------------
    Acal = qxsum(N, M, inv1, inv3, lambda m, n: Phi4(m, n) // 4, lambda m, n: m, altm, even)
    Bcal = qxsum(N, M, inv1, inv3, lambda m, n: (Phi4(m, n) - 1) // 4, lambda m, n: m, altm, odd)
    D = min(N, (M + 1) * (M + 1) // 4 - 1)  # x-truncation is invisible below q-degree D
    check("A_1 = Acal(1), A_2 = Acal(q) (through degree %d)" % D,
          Acal.at_x_power(0).truncate(D) == A1.truncate(D) and Acal.at_x_power(1).truncate(D) == A2.truncate(D),
          failures)
    check("B_1 = Bcal(1), B_2 = Bcal(q) (through degree %d)" % D,
          Bcal.at_x_power(0).truncate(D) == B1.truncate(D) and Bcal.at_x_power(1).truncate(D) == B2.truncate(D),
          failures)
    check("scalar equation E(Acal) = 0", scalar(Acal).is_zero(), failures)
    check("scalar equation E(Bcal) = 0", scalar(Bcal).is_zero(), failures)
    W01 = Acal * Bcal.qshift(1) - Acal.qshift(1) * Bcal
    check("Casoratian W01(x) = x p(qx)  [eq:app-Casoratian]", W01 == x * p_x.qshift(1), failures)
    # exterior equation for H = W01 / x at x-order M-1
    H = W01.div_x()
    q1, x1 = B.mono(1, 0, N, M - 1), B.mono(0, 1, N, M - 1)
    Hres = (H - (1 - q1 * q1 * x1) * H.qshift(1)
            - q1 * q1 * x1 * (1 + q1 + q1 * q1 * q1 * q1 * x1 * x1) * H.qshift(2)
            - q1 * q1 * q1 * q1 * q1 * q1 * x1 * x1 * H.qshift(3))
    check("H(0) = 1 and exterior equation for H  [eq:app-exterior-equation]",
          H.xcoeff(0) == one and Hres.is_zero(), failures)
    check("[x^1] W01 = 1 (parity initial determinant)  [eq:app-parity-initial-determinant]",
          W01.xcoeff(1) == one, failures)

    # q-Airy Wronskian (eq:app-Ai-Wronskian) at p = t^6, X = t^9: omega = 2.
    inv12t = [s.lift4(NT) for s in inv3]  # (t^12;t^12)_n^{-1}

    def Ai(xexp, sign):
        out = S.const(0, NT)
        for n in range(2 * N + 3):
            e = 3 * n * (n - 1) + xexp * n
            if e <= NT:
                out = out + (-inv12t[n] if (sign < 0 and n % 2) else inv12t[n]).shift(e)
        return out

    omega = Ai(9, 1) * Ai(15, -1) + Ai(9, -1) * Ai(15, 1)
    check("q-Airy Wronskian omega = 2 at p = t^6, X = t^9", omega == S.const(2, NT), failures)

    # ---- product side (lem:product-comparison) ------------------------------
    P36 = lambda j: poch_inf(j, 36, N) * poch_inf(36 - j, 36, N)

    def Pset(js):
        out = one
        for j in js:
            out = out * P36(j)
        return out

    a1 = Pset([1, 3, 5, 6, 8, 9, 12, 13, 15, 17]).inv()
    a2p = Pset([3, 4, 5, 6, 7, 9, 11, 12, 13, 15]).inv()
    b1 = -Pset([1, 3, 4, 6, 9, 10, 12, 14, 15, 17]).inv()
    b2 = -Pset([2, 3, 5, 6, 9, 12, 13, 14, 15, 16]).inv().shift(1)
    alpha, beta = phi * E1.inv(), theta * E1.inv()
    gamma, delta = theta3 * E3.inv(), -(phi3 * E3.inv()).shift(1)
    check("product short 1", alpha * a1 + beta * b1 == K1 * K2 - (K3 * K3).shift(1), failures)
    check("product short 2", alpha * a2p + beta * b2 == K2 * K2 + K1 * K3, failures)
    check("product long 1", gamma * a1 + delta * b1 == K1 * K1 + (K2 * K3).shift(1), failures)
    check("product long 2", gamma * a2p + delta * b2 == K1 * K2 - (K3 * K3).shift(1), failures)
    check("product minor a1 b2 - a2 b1 = K3", a1 * b2 - a2p * b1 == K3, failures)
    check("A_1 = a_1, B_1 = b_1, A_2 = a_2, B_2 = b_2 (consequence; sanity)",
          A1 == a1 and B1 == b1 and A2 == a2p and B2 == b2, failures)

    # Reformulation used by plan option S1 for the product norm.
    Jr = lambda r: poch_inf(r, 9, N) * poch_inf(9 - r, 9, N) * E9
    J1, J2, J4 = Jr(1), Jr(2), Jr(4)
    check("K_i = E9^2 / (E3 J_r), r = 1, 2, 4",
          K1 * E3 * J1 == E9 * E9 and K2 * E3 * J2 == E9 * E9 and K3 * E3 * J4 == E9 * E9, failures)
    check("J1 J2 J4 = E1 E9^3 / E3", J1 * J2 * J4 * E3 == E1 * E9 * E9 * E9, failures)
    lhs = (J2 * J2 * J2 * J4 * J4 * J4 + (J1 * J1 * J1 * J4 * J4 * J4).shift(1)
           - (J1 * J1 * J1 * J2 * J2 * J2).shift(2) + (J1 * J1 * J2 * J2 * J4 * J4).shift(1) * 3)
    check("product norm, theta form: J2^3J4^3 + qJ1^3J4^3 - q^2J1^3J2^3 + 3q(J1J2J4)^2 = a(q) E1^2 E9^3/E3",
          lhs * E3 == a2 * E1 * E1 * E9 * E9 * E9, failures)

    # P6 research reductions: finite checks, not Lean theorems or a product-norm proof.
    check("P6 cubic reduction: a E3 = E1^3 + 9q E9^3",
          a2 * E3 == E1 * E1 * E1 + (E9 * E9 * E9).shift(1) * 9, failures)
    inv1, inv2, inv4, inv9 = J1.inv(), J2.inv(), J4.inv(), E9.inv()
    reduced = J2 * J4 * inv1 * inv1 + (J1 * J4 * inv2 * inv2).shift(1) - (J1 * J2 * inv4 * inv4).shift(2)
    check("P6 remaining theta ratio: J2J4/J1^2 + qJ1J4/J2^2 - q^2J1J2/J4^2 = E1^3/E9^3 + 6q",
          reduced == E1 * E1 * E1 * inv9 * inv9 * inv9 + S.mono(1, N, 6), failures)

    # Lambert trace route. These checks do not assert any infinite identity.
    def lambert_filter(keep):
        coeffs = [0] * (N + 1)
        for k in range(1, N + 1):
            if keep(k):
                for m in range(1, N // k + 1):
                    coeffs[k * m] += m
        return S(coeffs, N)

    L = lambert_filter(lambda k: True)
    residues = {r: lambert_filter(lambda k, r=r: k % 9 in (r, 9-r))
                for r in (1, 2, 3, 4)}
    B9 = E9 * E9 * E9 * E9 * E9 * E9 * E3.inv() * E3.inv()
    check("P6 Weierstrass difference r=1",
          residues[1] - residues[3] == (B9 * J2 * J4 * inv1 * inv1).shift(1), failures)
    check("P6 Weierstrass difference r=2",
          residues[2] - residues[3] == (B9 * J1 * J4 * inv2 * inv2).shift(2), failures)
    check("P6 Weierstrass difference r=4",
          residues[4] - residues[3] == -(B9 * J1 * J2 * inv4 * inv4).shift(3), failures)
    trace = L - 4 * L.subs_pow(3) + 3 * L.subs_pow(9)
    check("P6 residue trace (unconditionally formalized)",
          residues[1] + residues[2] + residues[4] - 3 * residues[3] == trace, failures)
    check("P6 cubic theta square Lambert expansion",
          a2 * a2 == 1 + 12 * L - 36 * L.subs_pow(3), failures)
    check("P6 cubic theta trisection",
          a2 - a2.subs_pow(3) == 6 * (E9 * E9 * E9 * E3.inv()).shift(1), failures)
    check("P6 eta-product Lambert trace",
          trace == (E1 * E1 * E1 * E9 * E9 * E9 * E3.inv() * E3.inv()).shift(1)
                   + 6 * B9.shift(2), failures)

    print()
    if failures:
        print("%d FAILURE(S):" % len(failures))
        for f in failures:
            print("  " + f)
        return 1
    print("all checks passed at q-order N=%d, x-order M=%d" % (N, M))
    return 0


if __name__ == "__main__":
    sys.exit(main())
