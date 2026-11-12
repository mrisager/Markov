#!/usr/bin/env python3
"""Enclose the modular McShane--Rivin unit-ball area and its counting constant.

Uses the Farey area series in Appendix A, with f(m) = acosh(3m/2).
The two exceptional triples have weight 1/2. No value of Zagier's
constant is supplied as input.

The first omitted triples form a frontier. Zagier's Lemma 2 gives
0 < f(p)+f(q)-f(r) < 1/r**2. Descendants at depth n have largest entry
at least 2**n*r and coordinatewise larger entries, so their total area
contribution is at most 3/(r**2*f(p)*f(q)*f(r)).

Decimal interval arithmetic includes rounding errors; pi is enclosed
independently using Machin's formula and alternating rational series.

Run: python3 numerics/unit_ball_volume.py --cutoff 1000000000000
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR, getcontext, localcontext
from fractions import Fraction
from functools import cache


@dataclass(frozen=True)
class Interval:
    lo: Decimal
    hi: Decimal

    @classmethod
    def exact(cls, value):
        value = Decimal(value)
        return cls(value, value)

    @classmethod
    def rational(cls, lo: Fraction, hi: Fraction):
        with localcontext() as ctx:
            ctx.rounding = ROUND_FLOOR
            lower = Decimal(lo.numerator) / Decimal(lo.denominator)
            ctx.rounding = ROUND_CEILING
            upper = Decimal(hi.numerator) / Decimal(hi.denominator)
        return cls(lower, upper)

    def __add__(self, other):
        with localcontext() as ctx:
            ctx.rounding = ROUND_FLOOR
            lo = self.lo + other.lo
            ctx.rounding = ROUND_CEILING
            hi = self.hi + other.hi
        return Interval(lo, hi)

    def __sub__(self, other):
        with localcontext() as ctx:
            ctx.rounding = ROUND_FLOOR
            lo = self.lo - other.hi
            ctx.rounding = ROUND_CEILING
            hi = self.hi - other.lo
        return Interval(lo, hi)

    def __mul__(self, other):
        with localcontext() as ctx:
            ctx.rounding = ROUND_FLOOR
            lo = min(a * b for a in (self.lo, self.hi)
                     for b in (other.lo, other.hi))
            ctx.rounding = ROUND_CEILING
            hi = max(a * b for a in (self.lo, self.hi)
                     for b in (other.lo, other.hi))
        return Interval(lo, hi)

    def __truediv__(self, other):
        if other.lo <= 0 <= other.hi:
            raise ValueError("Division by an interval containing zero")
        with localcontext() as ctx:
            ctx.rounding = ROUND_FLOOR
            lo = min(a / b for a in (self.lo, self.hi)
                     for b in (other.lo, other.hi))
            ctx.rounding = ROUND_CEILING
            hi = max(a / b for a in (self.lo, self.hi)
                     for b in (other.lo, other.hi))
        return Interval(lo, hi)

    def sqrt(self):
        # Decimal.sqrt and Decimal.ln are correctly rounded to nearest.
        return Interval(self.lo.sqrt().next_minus(), self.hi.sqrt().next_plus())

    def ln(self):
        return Interval(self.lo.ln().next_minus(), self.hi.ln().next_plus())


def pi_interval(precision):
    def atan_inverse_bounds(m):
        total = Fraction(0)
        k = 0
        threshold = Fraction(1, 10 ** (precision + 5))
        while True:
            total += Fraction((-1) ** k, (2 * k + 1) * m ** (2 * k + 1))
            k += 1
            next_term = Fraction((-1) ** k, (2 * k + 1) * m ** (2 * k + 1))
            if abs(next_term) < threshold:
                return min(total, total + next_term), max(total, total + next_term)

    a, b = atan_inverse_bounds(5)
    c, d = atan_inverse_bounds(239)
    return Interval.rational(16 * a - 4 * d, 16 * b - 4 * c)


def compute(cutoff, precision):
    getcontext().prec = precision
    number = Interval.exact
    zero, two, three = number(0), number(2), number(3)

    @cache
    def f(m):
        return ((number(3 * m) + number(9 * m * m - 4).sqrt()) / two).ln()

    def term(p, q, r):
        return (f(p) + f(q) - f(r)) / (f(p) * f(q) * f(r))

    series = (term(1, 1, 1) + term(1, 1, 2)) / two
    remainder = zero
    retained, frontier = 2, 0
    stack = [(1, 2, 5)]
    while stack:
        p, q, r = stack.pop()
        if r > cutoff:
            remainder += three / (number(r * r) * f(p) * f(q) * f(r))
            frontier += 1
            continue
        series += term(p, q, r)
        retained += 1
        stack.extend(((p, r, 3 * p * r - q), (q, r, 3 * q * r - p)))

    partial_area = three * series / two
    area = Interval(partial_area.lo, (partial_area + remainder).hi)
    pi = pi_interval(precision)
    constant = two * area / (pi * pi)
    return retained, frontier, remainder.hi, area, constant


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cutoff", type=int, default=10**12)
    parser.add_argument("--precision", type=int, default=100)
    args = parser.parse_args()
    if args.cutoff < 2 or args.precision < 40:
        parser.error("cutoff must be at least 2 and precision at least 40")
    retained, frontier, tail, area, constant = compute(args.cutoff, args.precision)
    print(f"cutoff={args.cutoff}; precision={args.precision}")
    print(f"retained triples={retained}; frontier triples={frontier}")
    print(f"area truncation error <= {tail}")
    print(f"area lower = {area.lo}")
    print(f"area upper = {area.hi}")
    print(f"C lower = {constant.lo}")
    print(f"C upper = {constant.hi}")


if __name__ == "__main__":
    main()
