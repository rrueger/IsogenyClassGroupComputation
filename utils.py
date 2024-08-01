#!/usr/bin/env python

# Silence warnings for now
# https://stackoverflow.com/a/15778297
from warnings import simplefilter

import sage.all
from sage.arith.misc import (
    divisors,
    factor,
    gcd,
    is_prime_power,
    is_square,
    jacobi_symbol,
    kronecker_symbol,
    xgcd,
)
from math import prod
from sage.all import pari
from sage.arith.misc import is_power_of_two
from sage.functions.other import ceil, floor
from sage.matrix.constructor import Matrix
from sage.misc.functional import sqrt
from sage.modules.free_module_element import vector
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.rings.integer import Integer
from sage.rings.integer_ring import ZZ
from sage.rings.number_field.number_field import QuadraticField
from sage.schemes.elliptic_curves.cm import hilbert_class_polynomial
from sage.schemes.elliptic_curves.constructor import EllipticCurve
from sage.sets.primes import Primes
from sage.structure.factorization_integer import IntegerFactorization

from math import log

from random import randint
from itertools import product, cycle, islice

# Silence warnings about slow implementations in the pre-processing step e.g.
#     verbose 0 (4176: multi_polynomial_ideal.py, groebner_basis)
#     Warning: falling back to very slow toy implementation.
try:
    from sage.misc.verbose import set_verbose
    set_verbose(-1)
except ImportError:
    try:
        from sage.misc.misc import set_verbose
        set_verbose(-1)
    except ImportError:
        pass

simplefilter(action='ignore', category=FutureWarning)
simplefilter(action='ignore', category=DeprecationWarning)


def padicval(p, N):
    if N == 0:
        return 0

    if N == 1:
        return 0

    k = 0
    while N % p**k == 0:
        k += 1
    return k - 1


class Cideal():
    def __init__(self, O, a, b, m):
        self.O = O
        self.a = a
        self.b = b % a
        self.m = m
        self.f = O.conductor()
        self.D = O.ambient().discriminant()

        if (self.b**2 + self.f**2*(self.D**2 - self.D)//4 + self.f*self.b*self.D) % self.a != 0:
            print(f"{a}, {b} not good choices")
            raise ValueError

    def norm(self):
        return self.m**2 * self.a

    def discriminant(self):
        return self.D

    def gens(self):
        return [self.m*self.a, self.m*(self.b % self.a)]

    def __mul__(self, other):
        if isinstance(other, int) or isinstance(other, sage.rings.integer.Integer):
            return Cideal(self.O, self.a, self.b, other*self.m)

        if isinstance(other, list) or isinstance(other, tuple) or isinstance(other, sage.modules.vector_integer_dense.Vector_integer_dense):
            assert len(other) == 2

            # We expect other to be in the [1, fw] basis!

            if other[1] == 0:
                # In other words, we are multiplying by a + 0*f*w
                return self.__mul__(other[0])

            assert other in Cideal(self.O, 1, 0, 1)

            f, D = self.f, self.D
            K = (D**2 - D)//4

            a, b = self.a, self.b
            c, d = other

            f, D = self.f, self.D
            K = (D**2 - D)//4

            # Generators of product written as rows in the basis [fw, 1]
            # i.e. a + b*fw is written as [b, a]
            # The hermite row reduced matrix with no zero rows will have the
            # form
            #     [ C, B ]
            #     [ 0, A ]
            # This is because Sage's hermite form does row reduction
            G = Matrix(ZZ, [
                            [a*d,             a*c],
                            [c + b*d + d*D*f, c*b - d*f**2*K],
                        ])

            G = G.hermite_form(include_zero_rows=False)
            # print()
            # print(G)
            # print(f"Multiplying ideal I = [{a}, {b} + f*w] by ({c}, {d//f}*f*w)")
            A = G[1, 1]
            B = G[0, 1]
            C = G[0, 0]
            # print(G)
            M = self.m

            # alpha = a*c
            # beta = a*d
            # gamma = c*b - d*f**2*K
            # delta = b*d + c + d*D*f

            # C, u, v = xgcd(beta, delta)
            # A = gcd(alpha*delta, beta*gamma)/C
            # B = u*alpha + v*gamma
            # M = self.m

            if C != 1:
                if A % C != 0 or B % C != 0:
                    print("There has been an error in the representation of the ideal")
                    exit(148)
                A = A//C
                B = B//C
                M = M*C

            assert G[1, 0] == 0

            return Cideal(self.O, A, B, M)

        if isinstance(other, Cideal):
            assert self.O == other.O

            a1, b1 = self.a, self.b
            a2, b2 = other.a, other.b
            f, D = self.f, self.D
            K = (D**2 - D)//4

            # Generators of product written as rows in the basis [fw, 1]
            # i.e. a + b*fw is written as [b, a]
            # This is because Sage's hermite form does row reduction
            # (we want columns, so transposing the bases gives the "right"
            # result)
            G = Matrix(ZZ, [
                            [0,             a1*a2         ],
                            [a1,            a1*b2         ],
                            [a2,            a2*b1         ],
                            [b1 + b2 + f*D, b1*b2 - f**2*K],
                        ])

            G = G.hermite_form(include_zero_rows=False)

            if G.dimensions() != (2, 2):
                print("Ideal multiplication failed")

            C = G[0, 0]
            B = G[0, 1]
            A = G[1, 1]
            M = self.m * other.m

            if C != 1:
                if A % C != 0 or B % C != 0:
                    print("There has been an error in the representation of the ideal")
                A = A//C
                B = B//C
                M = M*C

            return Cideal(self.O, A, B, M)

    __rmul__ = __mul__


    def __pow__(self, other):
        if isinstance(other, int) or isinstance(other, sage.rings.integer.Integer):
            if other == 0:
                return Cideal(self.O, 1, 0, 1)
            # Use double and add method
            result = Cideal(self.O, 1, 0, 1)
            power = self
            while other >= 1:
                # print(other)
                if other %2 == 1:
                    result = result * power
                    other = other - 1
                power = power*power
                other = other //2
            return result

    def __repr__(self):
        # b_str = f"{self.b} + " if self.b != 0 else ""
        # m_str = f"{self.m}*" if self.m != 1 else ""
        # return f"{m_str}[{self.a}, {b_str}{self.f}*w]"

        # True repr
        def _factor(n): return 0 if n == 0 else factor(n)
        return f"Cideal(QuadraticField({self.D}).order_of_conductor({_factor(self.f)}), {_factor(self.a)}, {_factor(self.b)}, {_factor(self.m)})"

    def __shortrepr__(self):
        b_str = f"{self.b} + " if self.b != 0 else ""
        m_str = f"{self.m}*" if self.m != 1 else ""
        return f"{m_str}[{self.a}, {b_str}{self.f}*w]"

    def __eq__(self, other):
        return self.a == other.a \
                and self.b == other.b \
                and self.m == other.m \
                and self.O == other.O

    def __hash__(self):
        return hash((self.O, self.a, self.b, self.m))

    def __contains__(self, other):

        # Cast lists, tuples, vectors all as lists
        other = list(other)

        if len(other) == 2:
            # In the [1, fw] basis!
            c, d = other
            # So mathematically
            #   other = c + dfw
            # This lies in O = m[a, b + fw] = [ma, m(b + fw)] if and only if
            #   c + dfw = mxa + myb + myfw
            # for some integers x, y. In other words,
            #   (i)  d = my for some integer y
            #        <=> d \in m\Z
            #   (ii) c = mxa + myb for some  integer x (and same y from (i))
            #        <=> c = mxa + db
            #        <=> c - db = mxa
            #        <=> c - db \in ma\Z
            return (d % self.m == 0) and (c - self.b*d) % (self.m*self.a) == 0

    def new_basis(self, other):

        # Cast lists, tuples, vectors all as lists
        other = list(other)

        if len(other) == 2:
            # In the [1, fw] basis!
            c, d = other

            # So mathematically
            #   other = c + dfw
            #
            #   this lies in m[a, b + fw] if and only if c and d are multiples
            #   of m and (c/m) + (d/m) fw lies in [a, b + fw]

            assert c % self.m == 0  and d % self.m == 0

            c = c // self.m
            d = d // self.m

            # Now we check that c + d fw lies in [a, b + fw]
            #
            # c + d fw = c + d (b + fw) - db = (c - db)/a * a + d (b + fw)
            assert (c - self.b*d) % self.a == 0

            alpha = (c - self.b*d) // self.a
            beta = d

            print(f"{c} + {d} fw = {self.m} * [{alpha} * {self.a} + {beta} * ({self.b} + fw)]")

    def __floordiv__(self, other):
        if isinstance(other, int) or isinstance(other, sage.rings.integer.Integer):
            if self.m % other == 0:
                return Cideal(self.O, self.a, self.b, self.m // other)
            print("Could not divide exactly!")
            exit(123)

    def conjugate(self):
        return Cideal(self.O, self.a, -(self.b + self.f*self.D), self.m)

    def scalar_product(self, v, u):
        # In the [1, fw] basis!
        a, b = v
        c, d = u
        return ((2*a + b*self.f*self.D)*(2*c + d*self.f*self.D) - b*d*self.f**2*self.D)/4

    def norm_sq(self, v):
        x, y = v
        return x**2 + x*y*self.f*self.D + y**2 * self.f**2 * (self.D**2-self.D)//4
        # return self.scalar_product(v, v)

    def reduced_basis(self):

        def scalar_product(v, w): return self.scalar_product(v, w)
        def norm_sq(v): return self.norm_sq(v)

        def rround(n):
            return -1*round(-n) if n < 0 else round(n)

        # Using Galbraith's Algorithm 23 to compute a minimal basis
        # In the [1, fw_D] basis!
        A = self.m*vector(ZZ, [self.a, 0])
        B = self.m*vector(ZZ, [self.b, 1])

        b_1 = A
        b_2 = B

        B_1 = norm_sq(b_1)
        mu = scalar_product(b_1, b_2)/B_1
        b_2 = b_2 - rround(mu)*b_1
        B_2 = norm_sq(b_2)

        while B_2 < B_1:
            b_1, b_2 = b_2, b_1
            B_1 = norm_sq(b_1)
            mu = scalar_product(b_1, b_2) / B_1
            b_2 = b_2 - rround(mu)*b_1
            B_2 = norm_sq(b_2)

        # # Wikipedia's variant
        # if norm_sq(b_1) <= norm_sq(b_2):
        #     b_1, b_2 = b_2, b_1

        # # b_2 has the smaller norm here
        # while norm_sq(b_2) <= norm_sq(b_1):
        #     # Get the projection factor of b_2 on b_1
        #     mu = rround(scalar_product(b_2, b_1)/norm_sq(b_2))
        #     r = b_1 - mu*b_2
        #     b_1 = b_2
        #     b_2 = r

        if b_1 not in self:
            print(self.a, self.b, self.m)
            print(b_1)
            assert b_1 in self

        if b_2 not in self:
            print(self.a, self.b, self.m)
            print(b_2)
            assert b_2 in self

        if b_1 != b_2:
            # Some easy sanity checks
            assert norm_sq(b_1) <= norm_sq(b_2)
            assert norm_sq(b_1) <= norm_sq(A)
            assert norm_sq(b_1) <= norm_sq(B)
            assert norm_sq(b_1 - b_2) >= norm_sq(b_1)
            assert norm_sq(b_1 + b_2) >= norm_sq(b_1)

        return b_1, b_2

    def is_principal(self):
        # if self.a == 1 and self.b == 0:
        #     # This is an integer multiple of the whole ring
        #     return True

        b_1, b_2 = self.reduced_basis()

        # print(f"Shortest vector in {self}: {b_1}, self.m = {self.m}")
        # Now b_1 is the element of the lattice with the smallest norm
        # Now we check whether this element generates the whole ring

        return self == b_1 * Cideal(self.O, 1, 0, 1)

    def is_equivalent(self, other):
        return (self.conjugate()*other).is_principal()


def find_ideals(O, norm, equivalent_to=None):
    f = O.conductor()
    D = O.ambient().discriminant()
    n_w_D = (D**2 - D) // 4
    for a in divisors(norm):
        if Integer(norm//a).is_square():
            for b in range(a):
                if (b**2 + b*f*D + f**2*n_w_D) % a == 0:
                    m = Integer(sqrt(norm//a))
                    I = Cideal(O, a, b, m)
                    if not equivalent_to:
                        yield I
                    else:
                        if I.is_equivalent(equivalent_to):
                            yield I


def find_ideal(O, norm, equivalent_to=None):
    ideals_iterator = find_ideals(O, norm, equivalent_to=equivalent_to)
    return next(ideals_iterator)


def qfbsolve(a, b, c, enn, nonzero=False, not2power=False, flag=3):
    if isinstance(enn, list):
        enn = IntegerFactorization(enn)
    # From Pari's documentation (Page 218)
    # https://pari.math.u-bordeaux.fr/pub/pari/manuals/2.15.5/users.pdf
    # The flag is a bitmask
    # Bit 1: decides if all solutions (1) or only one solution (0) are returned
    # Bit 2: decides if the returned solutions are primitive (0) or not (1)
    # That is
    # flag=0, Return only one primitive solution
    # flag=1, Return all primitive solutions
    # flag=2, Return only one (possibly imprimitive) solution
    # flag=3, Return all primitive and imprimitive solutions
    #
    # qfbsolve returns objects of type
    #   <class 'cypari2.gen.Gen'> <class 'cypari2.gen.Gen'>
    # ...

    if flag == 0 or flag == 2:
        # Pari returns a single pair in this case (_not_ a 1 element list)
        _solutions = pari.qfbsolve(pari.Qfb(a, b, c), enn, flag=flag)
        if _solutions:
            solutions = [_solutions]
        else:
            solutions = []
    else:
        # Here pari returns a list of pairs
        solutions = pari.qfbsolve(pari.Qfb(a, b, c), enn, flag=flag)

    # ... we want them as integers

    if b == 0:
        # Some normalisation
        solutions = [(abs(int(x)), abs(int(y))) for (x, y) in solutions]
    else:
        solutions = [(int(x), int(y)) for (x, y) in solutions]

    if nonzero:
        solutions = [(x, y) for (x, y) in solutions if x != 0 and y != 0]

    if not2power:
        solutions = [(x, y) for (x, y) in solutions if not is_power_of_two(x) and not is_power_of_two(y)]

    # Stupid dedupe
    solutions = list(set(solutions))

    return solutions


def has_torsion(E, n=2, card=False):
    # Try to avoid counting points multiple times by calling abelian_group once
    Eab = E.abelian_group()
    invs = Eab.invariants()
    if len(invs) == 2:
        m1, m2 = invs
        if card:
            cardinality = Eab.cardinality()
            return min(padicval(n, m1), padicval(n, m2)), cardinality
        return min(padicval(n, m1), padicval(n, m2))
    else:
        # E is cyclic
        if card:
            return 0, Eab.cardinality()
        return 0


def get_point(E, order):
    while True:
        P = E.random_point()
        if P == E.zero:
            continue
        if P.order() % order == 0:
            yield (P.order()//order)*P


def info(E, D=None, N=None, T=None, name=None, tries=None, indent=-1):
    """Pretty prints information about Elliptic Curves"""
    # N is the target torsion
    # T is the actual torsion
    # D is the discriminant (of End(E))

    ret_str = []

    C = E.cardinality()
    p = E.base_field().characteristic()
    q = E.base_field().cardinality()
    k = padicval(p, q)

    if not name:
        name = 'E'

    if N:
        (n, l) = is_prime_power(N, get_data=True)

    q_str = f"{p}^{k}" if k != 1 else f"{p}"

    E_str = f"{name} = EllipticCurve(GF({q_str}), {E.a_invariants()})"
    ret_str += [E_str]

    C_str = f"card({name}) = {factor(C)}"
    ret_str += [C_str]

    if N:
        if not T:
            t = has_torsion(E, n)
        else:
            t = padicval(n, T)

        tors_str = f"{n}-Torsion: {n}^{t} (Target {n}^{l})"
        ret_str += [tors_str]

    if tries:
        ret_str += [f"Iterations to find {name}: {tries}"]

    if N and D:
        v = int(sqrt(((q+1-C)**2 - 4*q)/D))
        v_val = padicval(-D, v)
        two_val = padicval(2, v)
        # if two_val < l:
        #     print("Found one!")
        #     exit(3)
        v_str = f"v = {factor(v)}, Torsion losses: v_{-D}(v) = {v_val}, v_2(v) = {two_val}"

        # cls_no = Integer(D).class_number()
        # ret_str += [f"{D = }, h(D) = {cls_no}"]

        ret_str += [v_str]

    if indent == -1:
        return " | ".join(ret_str)
    else:
        return " "*indent + ("\n"+" "*indent).join(ret_str)


def find_E(D, N, cls_no=None, cls_poly=None, max_multiple=None, rand=False):
    """Finds ordinary curve E whose N-torsion is rational

    Assumes N % 4 == 0

    Since the N-torsion is a subgroup of order N^2, our general strategy is to
    first find curves with cardinality m*N^2 and then check whether this
    constitutes the N-torsion

    Passing cls_no and cls_poly is useful when finding many curves with a fixed
    discriminant.

    Passing rand may be beneficial when the method gets "stuck" on smaller
    cardinality attempts.
    """

    if not max_multiple:
        max_multiple = N**4

    if not cls_no:
        # Must cast as sage integer for the class_number() method to exist
        cls_no = Integer(D).class_number()

    if not cls_poly:
        cls_poly = hilbert_class_polynomial(D)

    if rand:
        # Generator expression for lazy sampling
        # There is probably a better inbuilt solution for this
        ms = (randint(1, max_multiple) for x in range(1, max_multiple))
    else:
        ms = range(1, max_multiple)

    for m in ms:
        # If the N-torsion is to be rational, the curve must have
        # F_q-cardinality that is a multiple of N^2
        C = m*N**2

        # Now searching for prime powers q that are of the form
        #     q = C + 1 \pm sqrt(4C + v^2 D)
        # We do this by first finding v's so that 4C - v^2 D is a square
        # In other words,
        #     x^2 = 4C + v^2 D    <=>    4C = x^2 - v^2 D
        for x, v in qfbsolve(1, 0, -D, 4*C):
            for sign in [-1, 1]:
                q = C + 1 + sign * x
                # Verify that this is a prime power
                (p, k) = is_prime_power(q, get_data=True)
                if k == 0:
                    continue

                # Ensure the resulting curve is ordinary
                if jacobi_symbol(D, p) != 1:
                    continue

                # Get roots over F_q (listed as pairs (root, multiplicity))
                for j, _ in cls_poly.roots(GF(q)):
                    E = EllipticCurve(GF(q), j=j)

                    assert E.is_ordinary()

                    M = E.cardinality()

                    if M % N**2 != 0:
                        # Got the wrong twist! Choose the other...
                        # (assume j != 0, 1728)
                        E = E.quadratic_twist()

                    if not has_torsion(E, N):
                        continue

                    # Because there is a point of order 4, there should be a
                    # montgomery model for this curve
                    E = E.montgomery_model()
                    return E


def positive_bezout_coefficients(x, y, N, squares=False, allowzero=False):
    """Compute all positive integer pairs (a, b) so that ax + by = N

    Assumes that x, y, N > 0
    """

    if x == 0 and y == 0:
        return ()

    if y == 0:
        if allowzero:
            return ((N // x, 0)) if N % x == 0 else ()
        return ()

    if x == 0:
        if allowzero:
            return ((0, N // y)) if N % y == 0 else ()
        return ()

    (g, a, b) = xgcd(x, y)

    if N % g != 0:
        return ()

    _N = N // g
    _y = y // g
    _x = x // g

    coeffs = ((N*a + k*y, N*b - k*x) for k in range(ceil(float(-N*a/y)), floor(float(N*b/x))+1))

    for A, B in coeffs:

        if squares and not is_square(A) and not is_square(B):
            continue

        if not allowzero and (A == 0 or B == 0):
            continue

        yield A, B


def compute_good_norms(O, T, prime_at_least=2):
    f = O.conductor()
    D = O.discriminant()//f**2

    P = Primes()
    good_primes = []
    p = P.first()  # p = 2
    # Not allowing even numbers for now, getting next prime
    p = P.next(p)  # p = 3

    while p < T:
        if f % 2 == 0:
            if kronecker_symbol(f**2*D//4, p) != -1:
                good_primes += [p]
        else:
            if kronecker_symbol(f**2*D, 4*p) != -1:
                good_primes += [p]

        p = P.next(p)

    print(f"There are {len(good_primes)} good primes to choose from")
    # This could be done way, way faster using some "reverse sieving" technique
    # For now, our numbers are small enough that it doesn't make a big
    # difference
    good_primes = set(good_primes)
    good_norms = reverse_sieve(good_primes, T, prime_at_least=prime_at_least)
    good_norms = sorted(good_norms)
    print(f"This gives us {len(good_norms)} many possible norms")

    return good_norms


def get_interesting_ideals(O, T, at_most_ideals=0, prime_at_least=2):
    """Return pairs of coprime integers (m, j) for which there exist (x, y) such
    that m*x^2 + j*y^2 = T
    """
    good_norms = compute_good_norms(O, T)

    ideal_combinations = []

    for i, m in enumerate(good_norms):
        if i % 50 == 0:
            print(f"\rFinding an ideal for every possible norm up to {T}: {i/(len(good_norms))*100:.2f}% Done", end='')

        ideals_norm_m = list(find_ideals(O, m))

        if len(ideals_norm_m) == 0:
            print("No ideals found, even though {m = } was a good norm!")
            continue

        for j in good_norms:
            if j >= m:
                break

            if gcd(m, j) != 1:
                continue

            sols = qfbsolve(m, 0, j, T, nonzero=True, not2power=True)

            if not sols:
                continue

            ideals_norm_j = list(find_ideals(O, j))

            if len(ideals_norm_m) == 0:
                print("No ideals found, even thought {j = } was a good norm!")
                continue

            success = False
            for I, J in product(ideals_norm_m, ideals_norm_j):
                assert I.norm() == m and J.norm() == j
                if I.is_equivalent(J):
                    success = True
                    break

            if not success:
                continue

            print("Success!")

            # print(f"norm(I) = {I.norm()}, I = {I}")
            # print(f"norm(J) = {J.norm()}, J = {J}")
            # print(f"I.conjugate()*J = {I.conjugate()*J}")
            # print(f"Are equivalent = {I.is_equivalent(J)}")
            # print(f"Smallest elements of I.conjugate()*J = {(I.conjugate()*J).reduced_basis()}")

            for x, y in sols:
                ideal_combinations += [(I, x, J, y)]
                if at_most_ideals != 0 and len(ideal_combinations) >= at_most_ideals:
                    print()
                    return ideal_combinations

    print()
    return ideal_combinations



# def sample(a, b, c, D, f):


# def get_interesting_ideals(O, T, at_most_ideals=0, prime_at_least=1):
#     """Return pairs of coprime integers (m, j) for which there exist (x, y) such
#     that m*x^2 + j*y^2 = T
#     """
#     f = O.conductor()
#     D = O.discriminant()//f**2

#     P = Primes()
#     good_primes = []
#     p = P.first()  # p = 2
#     # Not allowing even numbers for now, getting next prime
#     p = P.next(p)  # p = 3

#     while p < T:
#         if f % 2 == 0:
#             if kronecker_symbol(f**2*D//4, p) != -1:
#                 good_primes += [p]
#         else:
#             if kronecker_symbol(f**2*D, 4*p) != -1:
#                 good_primes += [p]

#         p = P.next(p)

#     print(f"There are {len(good_primes)} good primes to choose from")
#     good_primes = set(good_primes)
#     good_primes = sorted(list(good_primes))
#     print(good_primes[-1])
#     good_norms = reverse_sieve(good_primes, 10*T, prime_at_least=prime_at_least)
#     good_norms = sorted(good_norms)
#     print(good_norms[-1])
#     exit(123)
#     print(f"This gives us {len(good_norms)} many possible norms")

#     for _m in range(len(good_norms)):
#         for _j in range(_m):
#             m = good_norms[_m]
#             j = good_norms[_j]

#             if not is_square(4*m*j + f**2*D):
#                 print(f"{4*m*j + f**2*D} is not a square")
#                 continue

#             # Since f is even, b is even
#             b = int(sqrt(4*m*j + f**2*D))

#             I = Cideal(O, a, -(b + f**2*D)//2, 1)
#             J = Cideal(O, c, (b - f**2*D)//2, 1)

#             print("The ideals are equivalent:", I.is_equivalent(J))
#             print("{I.norm()}, {J.norm()}")
#             assert I.is_equivalent(J)

#     ideal_combinations = []

#     return ideal_combinations


def reverse_sieve(primes, bound, prime_at_least=1):
    if prime_at_least >= bound:
        print("Starting point is greater than the upper bound")
        raise ValueError
    # This is very dumb
    # Could be done nicer with some constructive (recusive even) algorithm to
    # multiply numbers together from the primes
    # The hard part is to know when to terminate
    return [m for m in range(prime_at_least, bound) if set([p for p, _ in factor(m)]).issubset(set(primes))]


def prod(it):
    result = 1
    for i in it:
        result = result * i
    return result


def wD(E, D):
    """Computing the isogeny corresponding to w_D, i.e. the generator of the
    endomorphism ring with conductor f
    """
    q = E.base_field().cardinality()
    C = E.cardinality()
    t = q + 1 - C
    # Throws error if not coercable to int
    v = ZZ(sqrt((t**2 - 4*q)/D))

    assert (v*D - t) % 2 == 0
    assert gcd(v, D) == 1

    deg_wD = (D**2 - D)//4

    # Try smaller extensions first, before going to the full extension
    for extension in [deg_wD - 1, deg_wD + 1, deg_wD**2 - 1]:
        base_field = E.base_field()
        irr_element = base_field['x'].irreducible_element(extension)
        extension_field = base_field.extension(modulus=irr_element, names='v')

        R = E.change_ring(extension_field)

        pi_E = E.frobenius_endomorphism()
        pi_R = R.frobenius_endomorphism()

        wD_kernel = []
        for P in R.zero().division_points(deg_wD):
            if P.order() == deg_wD and (v*D - t)//2 * P + pi_R(P) == R.zero():
                wD_kernel = [P]
                wD_R = R.isogeny(wD_kernel)
                if wD_R.codomain().j_invariant() == E.j_invariant():
                    break

        if len(wD_kernel) == 0:
            continue

        wD_R = wD_R.codomain().isomorphism_to(R) * wD_R

        if wD_R.degree() != deg_wD:
            continue

        # Cheap method to restrict wD_R to E
        def wD(P):
            # Assumes P lies in E
            return E(wD_R(R(P)))

        # Ensure the map we created is the correct one. Mathematically
        #   wD = ((vD - t)/2 + \pi)/v
        if not all([v*wD(P) == (v*D - t)//2 * P + pi_E(P) for P in [E.random_point() for _ in range(100)]]):
            continue

        # w_D satisfies w_D^2 - D w_D + (D^2 - D)/4 = 0
        if not all([wD(wD(P)) - D * wD(P) + (D**2 - D)//4 * P == E.zero() for P in [E.random_point() for _ in range(100)]]):
            continue

        return wD


def good_coprime_norm_pairs(n, D, f):
    for norm_I in range(2, f**2 * (int(1 + sqrt(-D)))):
        if norm_I % D == 0 or norm_I % f == 0:
            continue
        for norm_J in range(2, min(norm_I, 2**n - norm_I)):
            if norm_J % D == 0 or norm_J % f == 0:
                continue
            if gcd(norm_I, norm_J) != 1:
                continue

            # If
            #   norm_I*a^2 + norm_J*b^2 = 2^m for some m <= n with m + 2k = n
            # then
            #   norm_I*(2^k a)^2 + norm_J*(2^k b)^2 = 2^m * 2^(2k) = 2^n
            # Conversely
            #   norm_I*a^2 + norm_J*b^2 = 2^m for some m <= n with m + 2k + 1 = n
            # then
            #   norm_I*(2^k a)^2 + norm_J*(2^k b)^2 = 2^m * 2^(2k) = 2^{n - 1}
            #
            # So by finding a solution for
            #   norm_I*a^2 + norm_J*b^2 = 2^n
            # or
            #   norm_I*a^2 + norm_J*b^2 = 2^{n-1}
            # we have verified that there exists a solution to (*)

            # Use flag=2 to return after finding one solution
            # We only care that there is one solution

            sols = qfbsolve(norm_I, 0, norm_J, [(2, n)], flag=2)

            if not sols:
                sols = qfbsolve(norm_I, 0, norm_J, [(2, n - 1)], flag=2)

            if sols:
                a, b = sols[0]
                yield norm_I, a, norm_J, b


def find_class_group(d, f):
    D = d if d % 4 == 1 else 4 * d
    K = QuadraticField(D, names="i")
    O = K.order_of_conductor(f)
    (_f, e_f) = is_prime_power(f, get_data=True)
    class_number = f - (f // _f) * kronecker_symbol(D, _f)
    assert class_number == Integer(D * f**2).class_number()

    # int() rounds down, which is what we want here
    maxnorm = f * int(sqrt(-D))
    class_group = [Cideal(O, 1, 0, 1)]
    for norm in range(1, maxnorm):
        for I in find_ideals(O, norm):
            # For simplicity, only find ideals with m = 1
            # (Means coprimality conditions are easier to meet later on)
            if I.m > 1:
                continue

            alpha = I.a
            beta = 2 * I.b + I.f * I.D
            gamma = (I.b**2 + I.b * I.f * I.D + I.f**2 * (I.D**2 - I.D) // 4) // I.a

            if gcd([alpha, beta, gamma]) > 1:
                continue

            if not any([I.is_equivalent(_) for _ in class_group]):
                class_group += [I]
                print(f"Found ideal: {len(class_group)}/{class_number} norm = {I.norm()} (maxnorm: {maxnorm})")
                if len(class_group) >= class_number:
                    break
            if len(class_group) >= class_number:
                break
        if len(class_group) >= class_number:
            break

    assert len(class_group) == class_number

    print(f"Computed class group of size {class_number}")
    return class_group


def roundrobin(*iterables):
    # https://docs.python.org/3/library/itertools.html#recipes
    "Visit input iterables in a cycle until each is exhausted."
    # roundrobin('ABC', 'D', 'EF') → A D E B F C
    # Algorithm credited to George Sakkis
    iterators = map(iter, iterables)
    for num_active in range(len(iterables), 0, -1):
        iterators = cycle(islice(iterators, num_active))
        yield from map(next, iterators)


def find_pairs_squares(d, n, f):
    D = d if d % 4 == 1 else 4*d
    K = QuadraticField(D, names='i')
    (i, ) = K._first_ngens(1)
    O = K.order_of_conductor(f)

    found = []
    count_pairs = 0
    (_f, e_f) = is_prime_power(f, get_data=True)
    class_number = f - (f//_f)*kronecker_symbol(D, _f)

    for norm_I, a, norm_J, b in good_coprime_norm_pairs(n, D, f):
        count_pairs += 1
        if len(found) >= class_number:
            return found

        # Iter over the ideals with norm_I and find J with norm(J) = norm_J
        # Since norm(m[a, b + fw]) = m^2a == norm_I, there are only
        # finitely many such ideals
        for I in find_ideals(O, norm_I):
            # We are only interested in finding classes of ideals
            if any([I.is_equivalent(_) for _ in found]):
                continue

            alpha = I.a
            beta = 2*I.b + f*D
            gamma = (I.b**2 + I.b*I.f*I.D + I.f**2*(I.D**2 - I.D)//4) // I.a

            # This returns the coefficients of beta, if they exist
            # We only care if there is one solution (flag=2)
            equiv_sol = qfbsolve(alpha, beta, gamma, norm_J, flag=2)

            if equiv_sol:
                (x, y) = equiv_sol[0]

                # Recall that conjugate(w) = D - w. Hence
                #   conjugate(x + yfw) = x + yfD - yfw
                # so in the [1, fw] basis  we get
                #   conjugate([x, y]) = [x + yfD, -y]
                beta = I.m*vector(ZZ, [x*I.a + y*I.b, y])
                beta_conj = vector(ZZ, [beta[0] + beta[1]*I.f*I.D, -beta[1]])
                J = (beta_conj*I) // I.norm()

                # I or J, doesn't matter. We are interested in the class
                found += [I]

                kani_endo = (J.conjugate()*I).reduced_basis()[0]
                vstring = []
                vstring += [f"(v1)"]
                vstring += [f"Norm pairs tried: {count_pairs:>10}"]
                vstring += [f"Distinct classes: {len(found)}/{class_number}"]
                vstring += [f"2^{padicval(2, a**2*norm_I + b**2*norm_J)} == {a}^2*{norm_I} + {b}^2*{norm_J}"]
                vstring += [f"kani_endo == {kani_endo[0]} + {kani_endo[1]} fw"]
                print(" | ".join(vstring))

    print("Could not find pairs for the whole class group")
    return found

def find_pairs_full(class_group, d, n, f):

    D = d if d % 4 == 1 else 4 * d

    found = []
    for n_H, H in enumerate(class_group):
        tries = 0

        # Norm form of equivalent ideals to H
        alpha = H.a
        beta = 2 * H.b + H.f * H.D
        gamma = (H.b**2 + H.b * H.f * H.D + H.f**2 * (H.D**2 - H.D) // 4) // H.a

        # Should already be true, because of how the class group was computed
        assert gcd([alpha, beta, gamma]) == 1

        # Norm form of O = [1, fw]
        delta = 1
        epsilon = f * D
        phi = f**2 * (D**2 - D) // 4

        finish = False

        while True:

            if finish:
                break

            upper_bound = 2 ** (n // 6)

            x_I = randint(-upper_bound, upper_bound)
            y_I = randint(-upper_bound, upper_bound)
            norm_I = alpha * x_I**2 + beta * x_I * y_I + gamma * y_I**2

            x_J = randint(-upper_bound, upper_bound)
            y_J = randint(-upper_bound, upper_bound)
            norm_J = alpha * x_J**2 + beta * x_J * y_J + gamma * y_J**2

            if gcd(norm_I, norm_J) > 1:
                continue

            tries += 1
            # print(f"{tries} Coprime pair")

            if tries > 2**12:
                # Don't get stuck in infinite loop
                print(f"Class {n_H+1:>2}/{len(class_group)} ({len(found)/(n_H+1):.1%}): Giving up...")
                finish = True
                break

            bezout_coefficients = 0
            for a, b in roundrobin(
                positive_bezout_coefficients(norm_I, norm_J, 2 ** (n - 1)),
                positive_bezout_coefficients(norm_I, norm_J, 2**n),
            ):
                bezout_coefficients += 1

                # g = gcd(a, b)
                # a, b = a//gcd(a, b), b//gcd(a, b)

                if finish:
                    break

                if bezout_coefficients > 2**10:
                    break

                if gcd(a*norm_I, b*norm_J) > 1:
                    continue

                if is_square(a):
                    end_a = (int(sqrt(a)), 0)
                    end_a_str = f"{end_a[0]}^2"
                elif sols := qfbsolve(delta, epsilon, phi, a, flag=2):
                    end_a = sols[0]
                    end_a_str = f"deg({end_a[0]} + {end_a[1]} fw)"
                else:
                    continue

                # Assert that the degree of the endmorphism is correct
                assert delta*end_a[0]**2 + epsilon*end_a[0]*end_a[1] + phi*end_a[1]**2 == a

                if is_square(b):
                    end_b = (int(sqrt(b)), 0)
                    end_b_str = f"{int(sqrt(b))}^2"
                elif sols := qfbsolve(delta, epsilon, phi, b, flag=2):
                    end_b = sols[0]
                    end_b_str = f"deg({end_b[0]} + {end_b[1]} fw)"
                else:
                    continue

                # Assert that the degree of the endmorphism is correct
                assert delta*end_b[0]**2 + epsilon*end_b[0]*end_b[1] + phi*end_b[1]**2 == b

                finish = True

                # Recover the ideals
                beta_I_conj = H.m * vector(
                    ZZ, [x_I * H.a + y_I * (H.b + H.f * H.D), -y_I]
                )
                I = beta_I_conj * H
                I = I // H.norm()

                assert norm_I == I.norm()

                # beta_J = H.m*vector(ZZ, [x_J*H.a + y_J*H.b, y_J])
                beta_J_conj = H.m * vector(
                    ZZ, [x_J * H.a + y_J * (H.b + H.f * H.D), -y_J]
                )
                J = beta_J_conj * H
                J = J // H.norm()

                assert norm_J == J.norm()

                # assert gcd(a * norm_I, b * norm_J) == 1
                assert I.is_equivalent(H)
                assert J.is_equivalent(H)
                assert I.is_equivalent(J)
                assert J.is_equivalent(I)

                print()

                kani = (J.conjugate() * I).reduced_basis()[0]

                assert delta*kani[0]**2 + epsilon*kani[0]*kani[1] + phi*kani[1]**2 == J.norm()*I.norm()

                found += [(H, a, I, b, J, end_a, end_b, kani)]

                verb_str = []
                verb_str += [f"Class {n_H+1:>2}/{len(class_group)}"]
                verb_str += [f"({len(found)/(n_H+1):.1%})"]
                verb_str += [f"(tries: {tries:>4}, b_coefs: {bezout_coefficients:>4})"]
                # Class group computed so that H.m = 1
                verb_str += [f"Found for class [H] = [{H.a}, {H.b} + fw]"]
                verb_str += [f"{norm_I}*{end_a_str} + {norm_J}*{end_b_str} = 2^{padicval(2, norm_I*a + norm_J*b)}"]
                verb_str += [f"(Kani end = {kani[0]} + {kani[1]} fw)"]
                print(" ".join(verb_str))

    return found


def volcano_walk(d, n, _f, e_f):
    # # Chosen parameters
    # # Discriminant of the Elliptic curve we find
    # d = -7
    # # Available 2 torsion on middle curve
    # n = 32
    # # Conductor of endomorphism ring of middle curve
    # _f = 3
    # e_f = 5

    # Derived parameters
    # Discriminant, called \Delta_D in the thesis
    D = d if d % 4 == 1 else 4*d
    K = QuadraticField(D, names='i')
    (i, ) = K._first_ngens(1)
    f = _f**e_f
    N = f*2**n

    # print(f"Pre-computing class polynomial and class number of {D}...")
    cls_no = Integer(D).class_number(proof=False)
    cls_poly = hilbert_class_polynomial(D)
    # print("Done")
    # print()

    sim_cls_no = f - (f//_f)*kronecker_symbol(D, _f)

    cases = {1: 'Elkies', -1: 'Atikin', 0: 'Ramified'}

    print("Setup:")
    print(f"    {d = }, ({log(-d, 2):.2f} bits)")
    print(f"    {D = }, Discriminant of {K = }")
    print(f"    h(D) = {cls_no} ({log(cls_no, 2):.2f} bits)")
    print(f"    h(f**2D) = {sim_cls_no} ({log(sim_cls_no, 2):.2f} bits)")
    print(f"    N = {factor(N)}, Target rational torsion of curve")
    print(f"    In the {cases[kronecker_symbol(D, 2)]} case")
    print()

    print("Looking for curve...")
    print()
    result = find_E(D, N, cls_no=cls_no, cls_poly=cls_poly)
    if result:
        E = result
        print(info(E))
    else:
        print()
        print("No curve found!")
        exit(1)

    q = E.base_field().cardinality()
    p, k = q.is_prime_power(get_data=True)
    q_str = f"{p}^{k}" if k != 1 else f"{p}"

    assert has_torsion(E, 2) >= n
    assert has_torsion(E, _f) >= e_f

    # Walk down the _f-isogeny volcano to the floor.

    P, Q = E.torsion_basis(f)
    _P, _Q = (_f)**(e_f-1)*P, (_f)**(e_f-1)*Q

    one_away_success = False
    for kernel in [_P + k*_Q for kernel in range(_f)] + [_Q]:
        if E.isogeny(kernel).codomain().j_invariant() != E.j_invariant():
            one_away_success = True
            correct_torsion_point = P + k*Q
            break

    assert one_away_success

    phi = E.isogeny(correct_torsion_point, algorithm='factored')
    F = phi.codomain()

    assert has_torsion(F, _f) == 0

    assert E == phi.domain()
    assert F == phi.codomain()

    print(f"Found curve with conductor {f = } and rational 2^{has_torsion(F, 2)}-torsion")
    print(f"F = EllipticCurve(GF({q_str}), {F.a_invariants()})")

    assert has_torsion(F, 2) >= n

    return E, F, phi
