"""Exact arithmetic in K = Q(sqrt2, sqrt3): an element is a tuple (a, b, c, d) of Fractions meaning
a + b*sqrt2 + c*sqrt3 + d*sqrt6.  Includes an exact sign test using only rational arithmetic."""
from fractions import Fraction as Fr
from math import isqrt

ZERO = (Fr(0), Fr(0), Fr(0), Fr(0))
ONE = (Fr(1), Fr(0), Fr(0), Fr(0))


def k(a=0, b=0, c=0, d=0):
    return (Fr(a), Fr(b), Fr(c), Fr(d))


def add(x, y):
    return tuple(p + q for p, q in zip(x, y))


def sub(x, y):
    return tuple(p - q for p, q in zip(x, y))


def scale(x, r):
    return tuple(p * r for p in x)


def mul(x, y):
    a, b, c, d = x; e, f, g, h = y
    # sqrt2^2 = 2, sqrt3^2 = 3, sqrt6^2 = 6, sqrt2 sqrt3 = sqrt6, sqrt2 sqrt6 = 2 sqrt3, sqrt3 sqrt6 = 3 sqrt2
    return (a * e + 2 * b * f + 3 * c * g + 6 * d * h,
            a * f + b * e + 3 * c * h + 3 * d * g,
            a * g + c * e + 2 * b * h + 2 * d * f,
            a * h + d * e + b * g + c * f)


def _sign_q2(x, y):
    """sign of x + y*sqrt2 (x, y rational)."""
    if x == 0 and y == 0: return 0
    if x >= 0 and y >= 0: return 1
    if x <= 0 and y <= 0: return -1
    d = x * x - 2 * y * y          # nonzero since sqrt2 is irrational and (x, y) != 0
    return (1 if d > 0 else -1) if x > 0 else (-1 if d > 0 else 1)


def sign(z):
    """exact sign of a + b sqrt2 + c sqrt3 + d sqrt6 = P + sqrt3 Q with P = a + b sqrt2, Q = c + d sqrt2."""
    a, b, c, d = z
    sP, sQ = _sign_q2(a, b), _sign_q2(c, d)
    if sQ == 0: return sP
    if sP == 0: return sQ
    if sP == sQ: return sP
    # opposite signs: compare P^2 with 3 Q^2 (both in Q(sqrt2))
    s = _sign_q2(a * a + 2 * b * b - 3 * c * c - 6 * d * d, 2 * a * b - 6 * c * d)
    return s if sP > 0 else -s


def to_float(z):
    return float(z[0]) + float(z[1]) * 2 ** 0.5 + float(z[2]) * 3 ** 0.5 + float(z[3]) * 6 ** 0.5


def sqrt_bounds(n, digits=60):
    """rational lo < sqrt(n) < hi with hi - lo = 10^-digits (exact check)."""
    D = 10 ** digits
    r = isqrt(n * D * D)
    lo, hi = Fr(r, D), Fr(r + 1, D)
    assert lo * lo < n < hi * hi
    return lo, hi
