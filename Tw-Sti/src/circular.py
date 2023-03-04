# Code in support of ePrint:2021/1384
# Copyright 2021, Olivier Bernard
# GPL-3.0-only (see LICENSE file)

from sage.all    import *

from characters  import *
from cyclotomics import *


# --------------------------------------------------------------------------------------------------
# Cyclotomic units

# Denote U = O_K^{x}, U+ = O_{K+}^{x} unit groups of resp. cyclotomic and maximal real subfield.
#        mu = \mu_K                   torsion subgroup of units in K, ie. mu = < -\z_m >.
# Cyclotomic units are defined as C = V \cap U, where G is the multiplicative group generated by:
#         V = < +/- \z_m, { 1-\z^a_m for 1 \leq a \leq m-1 } >     (see [Was97, §8.1])
# NB: An explicit family of generators for C is *not* necessarily known when m is not a prime power.
#
# Index of real units [Was97, Th.4.12 and Cor.4.13]:
#         [U: mu.U+] = 1    if m is a prime power,
#                      2    otherwise.
# Best possible outcome for (real) cyclotomic units C+ [Was97, Th.8.2 and Rem. after Th.8.3 on Sinnott]:
#         [U+: C+] = h_{K+}        if m is a prime power,
#                    2^b.h_{K+}    otherwise, where b = 2^{g-2}+1-g where g >= 2 is #{p|m}
# Explicit families: (first family is mispelled as "canonical units")
#         C'+ = "Kummer units" (see wording in [Kuc92])
#             = { +/- \z_m^{(1-a)/2} . (1-\z_m^a) / (1-\z_m) for 1 < a < m/2 where (a,m)=1 }
#             = { +/- sin(pi.a/m) / sin(pi/m)                for 1 < a < m/2 where (a,m)=1 }
#         C"+ = "Ramachandra units" (see [Was97, Th.8.3]
#
# If m is a prime power:
#         [C+: C'+]   = [C: mu.C'+] = 1  [Was97, Lem.8.1]
#         [U: mu.C'+] = h_{K+}           (hence).
# Otherwise, it is hard to explicit [C+:C'+] or [C+:C"+] but (m=prod p_i^e_i):
#         [U+: C'+] = h+. prod_{chi mod m} prod_{p_i} (1-chi(p_i)) [ +\infty if 0 ]
#         [U+: C"+] = h+. prod_{chi mod m} prod_{p_i \not| f_chi} (phi(p_i^e_i) + 1 - chi(p_i))
# NB: These formula are valid in any case.
#     [U: C] = [U+: C+], see [Was97, Ex.8.5]
def cf_kummer_units(K, m):
    z  = K.gen();
    n  = K.degree(); assert(n == euler_phi(m));
    
    X  = cf_galois_exponents(K)[1:n/2]; # Want all 1 < _k < m/2 st. (_k,m)=1
    Uc = [ z**mod((1-_k)/ZZ(2),m) * (1-z**_k)/(1-z) for _k in X]; # Torsion part just maps to K+

    return Uc;


# [OLD] Not in use, since Kucera units solve the general case.
# Computes [U+: C'+] / h_{K+} = prod_{chi mod m} prod_{p_i} (1-chi(p_i)) [ +\infty if 0 ]
def cf_kummer_index(m):
    # Only non-trivial factors are for chi st. chi mod m is of conductor f strictly dividing m
    # Product is also limited to even characters
    # TODO: use our custom character implementation.
    D   = [ _chi.primitive_character() for _chi in DirichletGroup(m)
            if 1 < _chi.conductor() and _chi.conductor() < m and _chi.is_even()];
    
    # Prime factors of m
    m_p = [ _f[0] for _f in factor(m) ];

    # Could improve the computation by not computing terms where (p,f_chi) > 1
    idx = prod( prod(1-_chi(_p) for _p in m_p) for _chi in D );
    idx = Integers()(idx) if idx != 0 else +Infinity;

    return idx;


# 1. Washington's definition uses subsets of prime factors -> 2^g-2 terms
# 2. This gives a fundamental basis of cardinal (phi(m)/2-1),
#    but generally of (a lot) larger index than Kummer's
# Instead, switch to Kucera units
def cf_ramachandra_units(K, m):
    print ("Ramachandra units: not implemented.");
    return [];


# [OLD] Not used, because Kucera units solve everything.
def cf_ramachandra_index(m):
    # Prime factors of m
    m_fact = [ (_f[0], _f[1]) for _f in factor(m) ];
    # Only non-trivial factors are for chi st. chi mod m is of conductor f strictly dividing m
    # Product is also limited to even characters
    # TODO: use our custom character implementation.
    D   = [ _chi.primitive_character() for _chi in DirichletGroup(m)
            if 1 < _chi.conductor() and _chi.conductor() < m and _chi.is_even()];
    # Apply magic formula [Was97, Th.8.3]
    idx = prod(prod(euler_phi(_f[0]**_f[1]) + 1 - _chi(_f[0])
                    for _f in m_fact if not _f[0].divides(_chi.conductor()))
               for _chi in D );
    idx = Integers()(idx);
    
    return idx;


# Kucera units, as defined in [Kuc92]
# - The set "M+" is given in [Kuc92, p.293, before Th.4.1]
#   "It is easy to see that #(M+ \ {0}) = \phi(m)/2 - 1" (...)
# - The v_a are from [Kuc92, p.296, before Th.4.2]; for a \in M+:
#         (1-\z^a)               if for all m_i = m/p_i^e_i, m_i \not| a.
#         (1-\z^a)/(1-\z^{m_i})  if there is m_i | a (and obviously there is only one). 
# NB: in the prime power case, this exactly matches Kummer's units, ie.:
#         M+  = { 1 < a < p^k/2 st. gdc(a,p^k) == 1 }.
#         v_a = (1-\z^a)/(1-\z)   [indeed, m_1 = m/p^k = 1]

# This is a pedestrian implementation of the M+ definition in [Kuc92, p.293, before Th.4.1]
def kucera_get_Mplus(m):
    # m = prod q_i, where q_i = p_i^e_i
    m_p = [ _f[0]        for _f in factor(m) ]; # Cheap anyway.
    m_q = [ _f[0]**_f[1] for _f in factor(m) ]; # Cheap anyway.
    g   = ZZ(len(m_q));
    # Start from X = all [1, m-1] prime to m, plus multiples of p_i^e_i (not of p_i, ... only)
    Mplus = [ ZZ(_a) for _a in range(1,m) if
              all( not m_p[_i].divides(_a) or m_q[_i].divides(_a) for _i in range(g)) ];
    # Remove N+
    Nplus = { _a for _a in Mplus
              if _a.divides(m) and is_odd(len([_q for _q in m_q if not _q.divides(_a)])) };
    Mplus = [ _a for _a in Mplus if _a not in Nplus ];
    # Remove all a/(m,a)=-1 [q_i] for some q_i
    res_q = { _a for _a in Mplus
            if any([ _q.divides(_a+gcd(m,_a)) for _q in m_q if not _q.divides(_a)]) };
    Mplus = [ _a for _a in Mplus if _a not in res_q ];
    # Remove B_k = { q_k \not| a and {a/q_k/(a,m)} > 1/2 and for i > k, a = (m,a) mod [q_i] }
    for i in range(g):
        q_i = m_q[i];
        B_i = { _a for _a in Mplus if
                not q_i.divides(_a)
                and 2 * Integers()(mod(_a/gcd(_a,m), q_i)) > q_i
                and all( _q.divides(_a-gcd(m,_a)) for _q in m_q[i+1:] ) };
        Mplus = [ _a for _a in Mplus if _a not in B_i ];

    assert (len(Mplus) == euler_phi(m)/2-1);
    return Mplus;


def cf_kucera_units(K, m):
    # The magic set
    Mplus = kucera_get_Mplus(m);
    
    # Establish the m_i (if m=p^k, mi=[1])
    m_q = [ _f[0]**_f[1] for _f in factor(m) ]; # Cheap anyway.
    mi  = [ m / _q for _q in m_q ];
    # Use set [Kuc92, p.296, before Th.4.2] using property: m_i | a <=> gcd(a,m) == m_i (for a \in X)
    z   = K.gen();
    Uc  = [ (1-z**_a)/(1-z**gcd(_a,m)) if gcd(_a,m) in mi else (1-z**_a) for _a in Mplus ];
    
    return Uc;


# Kucera units generate all cyclotomic units [Kuc92, Th.6.1], so we are back to a theorem of Sinnott:
#         [U: C] = [U+: C+] = h_{K+} .2^b, where b=0           if g=1,
#                                                b=2^{g-2}-g+1 otherwise (g is #{p|m}).
def cf_kucera_index(m):
    m_p = [ _f[0] for _f in factor(m) ];
    g   = len(m_p);
    b   = 0 if g == 1 else 2**(g-2)-g+1;

    return 2**b;


# Returns a description of the cyclotomic units C,
# ie. an independent set of phi(m)/2-1 multiplicative generators
def cf_cyclotomic_units(K):
    m  = cf_get_conductor(K); assert(K.degree() == euler_phi(m));
    if (is_prime_power(m)):
        Uc = cf_kummer_units(K,m); # Just because in this case, it returns totally real elements
    else:
        Uc = cf_kucera_units(K,m); 
        
    return Uc;


# The index of cyclotomic units; more precisely, [U:C] / h_{K+} is returned.
def cf_cyclotomic_units_index(m):
    return cf_kucera_index(m);


# Torsion units are always generated by (-\zeta_m)
# [NB] If m is odd, \zeta_m is of order m, but -\zeta_m is \in K and has order 2m.
def cf_get_torsion_units(K):
    return [-K.gen()];