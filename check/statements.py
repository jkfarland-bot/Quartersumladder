# Numerical check of the Lean statements of QuarterSumLadder, exactly as formalized, for both
# quartic characters modulo every prime p = 1 (mod 8) below the bound. Exact integer arithmetic:
# chi(n) = i^r is represented by r in Z/4 (Gaussian integers as pairs where needed).
import sys
from math import gcd
from sympy import primerange, primitive_root, legendre_symbol, n_order

BOUND = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
fails = {}
def F(name):
    fails[name] = fails.get(name, 0) + 1

def v2(n):
    n = abs(n); k = 0
    while n % 2 == 0: n //= 2; k += 1
    return k

def gmul(a, b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
def gadd(*zs): return (sum(z[0] for z in zs), sum(z[1] for z in zs))
def gsc(k, z): return (k*z[0], k*z[1])
IP = [(1,0),(0,1),(-1,0),(0,-1)]

nprimes = 0
for p in primerange(17, BOUND):
    if p % 8 != 1: continue
    nprimes += 1
    g = primitive_root(p); Q = (p-1)//4
    ind = [0]*p; x = 1
    for j in range(p-1): ind[x] = j; x = x*g % p
    fourth = {pow(y, 4, p) for y in range(1, p)}
    kap = sum(int(legendre_symbol(n, p)) for n in range(1, Q+1))
    rho = n_order(2, p)
    for sgn in (1, 3):                      # chi and its conjugate
        cls = lambda n: (sgn*ind[n % p]) % 4
        w = 1 if cls(2) == 0 else (-1 if cls(2) == 2 else None)
        # setting
        if cls(p-1) != 0 or w is None or ((w == 1) != (2 in fourth)): F('even_quartic_setting')
        size = [sum(1 for m in range(1, p) if cls(m) == r) for r in range(4)]
        R = [sum(1 for n in range(1, Q+1) if cls(n) == r) for r in range(4)]
        if any(s != Q for s in size) or sum(R) != Q: F('class_sizes')
        U = [sum(m*m for m in range(1, p) if cls(m) == r) for r in range(4)]
        if any(u % p for u in U): F('weight_two_integrality')
        c0 = (U[0]-U[2])//p; c1 = (U[1]-U[3])//p
        T2 = gadd(*[gsc(m*m, IP[cls(m)]) for m in range(1, p)])
        if T2 != (p*c0, p*c1): F('weight_two_integrality')
        E = [sum(1 for m in range(1, p) if m % 4 == 2 and cls(m) == r) for r in range(4)]
        if (c0-4*(E[0]+E[2])) % 8 or (c1-4*(E[1]+E[3])) % 8 or (c0+c1-(p-1)) % 8:
            F('weight_two_coefficient_congruence')
        if ((c0 % 8 == 0 and c1 % 8 == 0) != (w == 1)) or (c0-4*(R[1]+R[3])) % 8 or (c1-4*(R[1]+R[3])) % 8:
            F('weight_two_mod_eight')
        if pow(2, Q, p) != (1 if (R[1]+R[3]) % 2 == 0 else p-1) or w != (-1)**(R[1]+R[3]):
            F('quartic_gauss_lemma')
        if kap != Q-2*(R[1]+R[3]) or ((w == 1) != (kap % 4 == Q % 4)): F('quarter_interval_formula')
        if w == 1 and len({r % 2 for r in R}) != 1: F('doubling_orbit_parity')
        par = tuple(r % 2 for r in R)
        if par in ((1,0,1,0), (0,1,0,1)): F('parity_patterns')
        Om = (R[0]-R[2], R[1]-R[3]); xx, yy = Om; N = xx*xx+yy*yy
        z = (-1, 1)
        rhs = gadd((Q,0), gsc(R[1]+2*R[2]+3*R[3], z), gsc(R[2]+3*R[3], gmul(z,z)), gsc(R[3], gmul(z,gmul(z,z))))
        if rhs != Om: F('quarter_sum_expansion')
        dv = lambda n, k: n % (2**k) == 0
        NB = c0*c0+c1*c1
        if w == -1:
            if not (dv(N,1) and not dv(N,2)): F('ladder_bottom')
            if v2(N) != 1: F('ladder_bottom_valuation')
            if not (dv(NB,5) and not dv(NB,6)): F('weight_two_trichotomy')
            if v2(NB) != 5: F('weight_two_trichotomy_valuation')
        elif p % 16 == 9:
            if not (dv(N,2) and not dv(N,3)): F('ladder_bottom')
            if v2(N) != 2: F('ladder_bottom_valuation')
            if not (dv(NB,6) and not dv(NB,7)): F('weight_two_trichotomy')
            if v2(NB) != 6: F('weight_two_trichotomy_valuation')
        else:
            if not dv(N,3): F('ladder_bottom')
            if N and v2(N) < 3: F('ladder_bottom_valuation')
            if not dv(NB,7): F('weight_two_trichotomy')
            if NB and v2(NB) < 7: F('weight_two_trichotomy_valuation')
            if dv(N,4) != ((R[1]+2*R[2]+R[3]) % 4 == 0): F('ladder_fourth')
            ind_rho = (p-1)//(4*rho) if rho % 2 == 0 else 0
            if kap % 4 or dv(N,4) != (((Q-kap)//4 + (p-1)//8 + ind_rho) % 2 == 0): F('ladder_fourth_classical')
        if w == 1:
            d = 1 if pow(2, (p-1)//8, p) == p-1 else 0
            ind_rho = (p-1)//(4*rho) if rho % 2 == 0 else 0
            if (R[2]-(p-1)//8-d) % 2 or (d-ind_rho) % 2: F('second_quarter_parity')
        if dv(2*N,6) != (dv(2*N,5) and (R[2]+R[3]) % 4 == (Q//2) % 4): F('ladder_fifth')
        if dv(2*N,5) and dv(2*N,6) != ((xx+yy) % 8 == 0): F('ladder_fifth')
        if (p*(c0-c1)+4*(xx-yy)) % 16: F('weight_two_comparison')
        # the Gauss-Lehmer product on the half system and on its classes
        gm = lambda a: (2*a) % p if 4*a < p else (-2*a) % p
        for A in [set(range(1, (p-1)//2+1))] + [{a for a in range(1, (p-1)//2+1) if cls(a) in (r, (r+2) % 4)} for r in range(2)]:
            if all(gm(a) in A for a in A):
                val = pow(2, len(A), p) * (1 if sum(1 for a in A if not 4*a < p) % 2 == 0 else p-1) % p
                if val != 1: F('gauss_lehmer_product')
for a in range(-60, 61):
    for b in range(-60, 61):
        if a and b and v2(a*a+b*b) != 2*min(v2(a), v2(b)) + (1 if v2(a) == v2(b) else 0):
            F('coordinate_valuation_formula')
print(f"{nprimes} primes p = 1 (mod 8) in [17, {BOUND}), both quartic characters")
print("failures:", fails or "none")
