# Code in support of ISSAC'23 Submission #7564
# Copyright 2023, <anonymous-roots-crt>
# GPL-3.0-only (see LICENSE file)

proof.number_field(False); 
proof.arithmetic(False);   # Essentially, use pseudo-primality tests everywhere


# Primes above p in K
def my_primes_above(K, p, __idx_start=0):
    r"""
    compute primes above ideal p : output them as two-elements representation
    """
    assert(is_prime(p));
    
    Fp_y   = PolynomialRing(GF(p), name='y');      y = Fp_y.gen();
    Z_x    = PolynomialRing(Integers(), name='x'); x = Z_x.gen();
    f      = Fp_y(K.defining_polynomial());
    f_fact = f.factor();
    return [(p, Z_x(_fact[0])) for _fact in f_fact]


# Does the m-th cyclotomic contain inert primes ?
def cf_can_inert(m):
    r"""
    compute whether one can find an inert prime in Q(zeta_m)
    """
    f = factor(m)
    if len(f)>2:
        return False
    elif len(f)==2 and (f[0][0] > 2 or f[0][1] > 1):
        return False
    elif f[0][0]==2 and f[0][1] > 2:
        return False;
    else:
        return True;


def get_conductor(K): # K.conductor() is very inefficient, in our case we know K.pol() = some cyclotomic polynomial
    return K.gen().multiplicative_order();
    
    
# returns next prime = res mod M greater than "next"
def __prime_mod_m(M, res, next=2**24):
    _p0 = ZZ(next);
    _p0 = _p0 - ZZ(_p0.mod(M)) + ZZ(res);
    if (_p0 <= ZZ(next)): # Could even test only == 
        _p0 += M;
    while not is_prime(_p0):
        _p0 += M;
    return _p0;


    
### ---------------------------------------------------------------------------
### p-adic lifting

# We compute the "inverse" e-th root: a^(1/e - 1)
# So Let g(x) = a^{e-1} x^e - 1
#        xi+1 = xi - (1/e).xi.g(xi)
# --> Converges to a^{1/e-1}
# --> a.xk = a^{1/e} mod p^k
def cf_padic_lifting(elts, exps, e, B):
    Zx.<x> = PolynomialRing(ZZ);
    
    K = elts[0].parent();
    m = get_conductor(K);
    pp, ee = is_prime_power(m, get_data=True); 
    assert(ee!=0)  # wants inert primes or cyclic ZZ/mZZ*
    # An element of order phi(m) ?
    r = ZZ(IntegerModRing(m).multiplicative_generator());
    # => inert primes are = r [m] (many choices)
    _d = 0
    p = randint(2**60, 2**61)
    p = p - p%m + 1 # not needed
    if ee==1:                    # 1/e does exist mod (p^n - 1)/e
        while _d!=1:
            p = __prime_mod_m(m, r, next=p);   print("inert p: ", p, "m: ", m, "r: ", r);
            Fp = GF(p, proof=False);
            q = ZZ(p**K.degree()); Fq = GF(q, proof=False, modulus=K.polynomial(), name='u'); # if modulus not given, takes forever
            _d = gcd(e,(q-1)//e); 
    else:                         # 1/e cannot exist mod (p^n - 1)/e
        while _d==0:
            p = __prime_mod_m(m, r, next=p);   print("inert p: ", p, "m: ", m, "r: ", r);
            Fp = GF(p, proof=False);
            q = ZZ(p**K.degree()); Fq = GF(q, proof=False, modulus=K.polynomial(), name='u'); # if modulus not given, takes forever
            _d = gcd(e,(q-1)//e); 
    print("ff done", flush=True);
    Fpy.<y> = PolynomialRing(Fp); gp = Fpy(K.polynomial());
    Fqz.<z> = PolynomialRing(Fq);
    print("poly done",flush=True);

    # Hensel's height
    log2_k = ceil(max(log(ln(2*B)/ln(p), 2),0)); # protection against small cases
    k = 2**log2_k;
    # print("Hensel's height: {} iterations".format(log2_k));
    Rpk     = IntegerModRing(p**k);
    Rpk.<t> = PolynomialRing(Rpk);
    gt      = Rpk(K.polynomial());
    
    # Prod mod p^k
    t = cputime();
    se_Pk = prod( power_mod(Rpk(_u.polynomial()), _e, gt) for _u,_e in zip(elts,exps) ).mod(gt); # Could do better
    a_Pk  = power_mod(se_Pk, e-1, gt); # Say, a = se^{e-1}
    t = cputime(t);
    # print("time se^{{e-1}} mod P^k: {:.2f}".format(t)); 
    # print("se^{{e-1}} mod P^k:", a_Pk);

    # Root in base residue field: first approximation
    t = cputime(); a_P = Fq(Fpy(a_Pk)); t = cputime(t);
    if ee!=1:
        pol_pow = a_P*z**e - 1; # should compute this mod gt (if e is about not small)
        t = cputime(); is_P  = pol_pow.roots()[0][0]; t = cputime(t); print("roots: {:.2f}".format(t)); # cheating
    else:
        inv_e = ZZ(-mod(1/e, (q-1)//e)); # careful, this is not mod(-1/e,(q-1)//e) if e not prime
        is_P  = a_P**inv_e;
    # assert(is_P**e * a_P == 1); # Takes time
    # print("a^{{1/e-1}}:", is_P);
    
    # Want to lift root mod P to root mod P^2 etc.
    is_P = is_P.polynomial();
    _k   = 1; # Just in case log2_k = 0
    for _i in range(log2_k):
        # print("\n"+"-"*15+"Lift stage {}".format(_i)+"-"*15);
        _k = 2**(_i+1);
        Fpky.<yk> = PolynomialRing(IntegerModRing(p**_k));
        gp  = Fpky(gt); # Fpky(K.polynomial()); 
        is_P = Fpky(is_P);
        a_P  = Fpky(a_Pk);
        # print("old sol: {}".format(is_P));
        # xi+1 = xi - 1/e xi f(xi)
        eval_isP = a_P * power_mod(is_P, e, gp) - 1;
        # print("f(xi) mod p^{} = {}".format(_k, eval_isP));
        new_isP = is_P - mod(1/e, p**_k) * (is_P * eval_isP).mod(gp);
        # print("xi+1 = ", new_isP);
        # assert( (power_mod(new_isP, e, gp) * a_P).mod(gp) == 1 ); # Takes time
        is_P = new_isP;
    assert(_k == k);
    s_P = (Rpk(is_P)*se_Pk).mod(gt);
    
    # print("\n"+"-"*15+"End of p-adic lifting" + "-"*15);
    # assert(power_mod(s_P, e, gt) == se_Pk); # Takes time
    s_P = Zx(s_P);
    s   = K([ (_s if _s < p**k/2. else _s - p**k) for _s in s_P ]);
    # print("SOLUTION: ", s);

    return s;


### ---------------------------------------------------------------------------
### pohst / fieker / belabas / roblot
def __eval_rmax(La):
    _d = La.nrows();
    GLa,PLa = gram_schmidt_ortho(La);
    iPLa = rc_mat_inverse(PLa);
    rmax = min( 1/2/sqrt(sum(iPLa[_j][_i]**2/(GLa[_j].norm())**2 for _j in range(_d))) for _i in range(_d));
    return rmax;

def belabas(elts, exps, e, lurs=[]):
    red_fct = lll_ZZ;
    K = elts[0].parent();
    la_se = logarg_mpow(lurs, exps);
    la_s  = logarg_pow(la_se, 1/e); # Any argument is fine for pinf[0] (/!\ not consistent with pinf[i])
    m    = get_conductor(K);
    n    = K.degree();

    if cf_can_inert(m): # call p-adic lifting
        print("can use hensel")
        Be = sum(exps[j]* log(vector(ComplexField(300), elts[j].complex_embeddings(prec=300)).norm(infinity),2) for j in range(len(elts)));
        # print("log h(s^e) = {:.2f}".format(Be));
        B  = Be / e;
        # print("log h(s) = {:.2f}".format(B));
        B =  2**B;
        return cf_padic_lifting(elts, exps, e, B)

    
    # Eval prec (depends on la_se?)
    b_sol  = log(logarg_t2_norm_cf(la_s),2); print("log2 t2(sol): {:.2f}".format(b_sol));
    # Find biggest possible inertia degree
    Zm = IntegerModRing(m);
    fp = max([ _a.multiplicative_order() for _a in Zm if _a.is_unit()]);
    # print("Inertia degree fp={}".format(fp));
    resp = [ _a for _a in Zm if _a.is_unit() and _a.multiplicative_order() == fp ]; assert(len(resp)>0); resp=resp[0];
    p = __prime_mod_m(m, resp, next=m); 
    # print("some prime : {}, fp={}".format(p,fp));
    # ---> Consider Lenstra bound on rmax ([Bel03, end p.17]) and plug in min bi ~ N(P^a)^{1/n}.(1.022)
    #      Condition rmax > min bi / .. > coeff_norm(x) yields:
    #         a > n/ln(N(p)) (ln |x| + ln 2 + (n(n-1)/4-1).ln g_lll ) [ NB: for cyclo, |x| ~ t2(x)/sqrt(n) ]
    g_lll  = 1.022; # Could use a more optimistic value, eg. 1.016
    p_prec = ceil(n/fp/ln(p)*(ln(2)*(1+b_sol)-1/2*ln(n)+(n*(n-1)/4.-1)*ln(g_lll)));
    # next power of 2 is faster to compute (pid^a, lifting).
    print("1st eval: {}".format(p_prec));
    p_prec = 2**(ceil(log(p_prec,2.)));
    print("1st round mod p^a, a={}".format(p_prec));
    # Compute LLL HNF(p^a)
    pid = K.ideal(my_primes_above(K,p)[0]);
    # [Sage] Costly version in Sage
    # print("pid:", pid);
    # t = cputime(); pid_a = pid**p_prec; t = cputime(t); print("Calcul pid^{}: {:.2f}".format(p_prec, t));
    # t = cputime(); HP_A  = matrix(ZZ, [_a.list() for _a in pid_a.basis()]); t = cputime(t); HP_A  = row_lower_hermite_form(HP_A);
    # print("mat(pid^{}): {:.2f}".format(p_prec, t));
    # //--- [END Sage]
    # [Pari] We want to use Pari for the computation of pid^a, otherwise it takes forever
    Kb = pari.nfinit(K);
    ppid = pari(pid);
    t = cputime(); HP_a = Kb.idealpow(ppid, p_prec); HP_A = matrix(HP_a).transpose(); t = cputime(t);
    print("Calcul pid^{} + HNF: {:.2f}".format(p_prec, t));
    # Convert to HNF in z^i basis
    t = cputime();
    HP_A = row_lower_hermite_form(matrix(ZZ,[ vector(K(Kb.nfbasistoalg(pari(_u).Col()))) for _u in HP_A ]))
    t = cputime(t);
    print("Convert to inc basis {:.2f}".format(t));
    # //--- [END Pari]

    # LLL Reduction of the HNF
    t = walltime(); L_A, _ = red_fct(HP_A); t = walltime(t); print("LLL: {:.2f}".format(t));
    rmax = __eval_rmax(L_A);
    print("ln rmax: {:.2f}, ln target: {:.2f}".format(ln(rmax), ln(RealField()(2**(b_sol)/sqrt(n)))));
    while (rmax < 2**(b_sol)/sqrt(n)):
        p_prec = p_prec*2;
        print("--> increase a={}".format(p_prec));
        # [Sage] version
        # pid_a  = pid_a^2;
        # HP_A = row_lower_hermite_form(matrix(ZZ, [_a.list() for _a in pid_a.basis()]));
        # [Pari] (silly) version
        HP_a = Kb.idealpow(HP_a, 2); HP_A = matrix(HP_a).transpose();
        HP_A = row_lower_hermite_form(matrix(ZZ,[ vector(K(Kb.nfbasistoalg(pari(_u).Col()))) for _u in HP_A ]));
        # //--- [END Pari]
        L_A, _ = red_fct(HP_A);
        rmax = __eval_rmax(L_A);
        print("ln rmax: {:.2f}, ln target: {:.2f}".format(ln(rmax), ln(RealField()(2**(b_sol)/sqrt(n)))));
    # Target
    # 1. Obtain s mod P
    # 2. Obtain s mod P^a or (s mod p) mod P^a , by Hensel lifting
    # 3. CVP(P^a, s mod P^a) gives s (or s mod p)
    Fp = GF(p, proof=False); Fpy.<yp> = PolynomialRing(Fp); gp = (pid.gens()[1]).polynomial();
    q  = p**fp; Fq = GF(q, proof=False, modulus=gp, name='u');
    se_p = prod( Fq(Fpy(_u.polynomial()).mod(Fpy(gp)))**_e for _u,_e in zip(elts,exps) );
    ae_p = se_p**(e-1); ##### pulls out of subgroup of order (q-1)/e ?
    # Find an e-th root in Fq:
    if (gcd((q-1)/e, e) == 1): # see [BV04] Efficient computation of roots in finite fields
        assert(e.divides(q-1));
        inv_e = ZZ(-mod(1/e,(q-1)/e)); # WARN: if e is not prime, mod(-1/e, (q-1)/e) != - mod(1/e, (q-1)/e)
        # We want the latter
        x0   = ae_p**inv_e; # x0 = prod^{(1-e)/e} mod Pid
    else: # For now, resort to factorization algo
        # Could be costly, should try to use that we need only one solution to cut the exploration tree in Cantor-Z
        # Or use [AMM77] On taking roots in finite fields
        print("Problem gcd((q-1)/e,e) > 1");
        Fqy.<yq> = PolynomialRing(Fq);
        t=cputime(); x0   = (yq**e * ae_p - 1).roots()[0][0]; t=cputime(t);
        print("Roots mod q using Coppersmith in {:.2f}".format(t));
        # assert(x0**e * ae_p == 1), "Fq:{}\nsp:{}\nx0:{}\nae_p:{}".format(Fq.modulus(),se_p,x0,ae_p);

    # Need product at precision p_prec
    Rpk = IntegerModRing(p**p_prec); Rpk.<t> = PolynomialRing(Rpk);
    gt  = Rpk(HP_A[fp].list()); assert(Fpy(gt) == Fpy(gp));
    se_pk  = prod( power_mod(Rpk(_u.polynomial()), _e, gt) for _u,_e in zip(elts,exps) ).mod(gt);
    ae_pk  = power_mod(se_pk, e-1, gt); # NB:  Fpy(ae_pk) !=  ae_p, since P^a \not| p

    # A small Hensel lifting to prec a
    x0 = x0.polynomial();
    for _i in range(ceil(log(p_prec,2))):
        _k = min(2**(_i+1), p_prec); print("Lift to prec {}".format(_k));
        Fpky.<yk> = PolynomialRing(IntegerModRing(p**_k));
        gp = Fpky(gt);
        x0 = Fpky(x0);
        ae_p = Fpky(ae_pk);
        eval_f = ae_p*power_mod(x0,e,gp)-1;
        xi = (x0 - mod(1/e,p**_k)*(x0 * eval_f)).mod(gp);
        # assert( (power_mod(xi,e,gp)*ae_p).mod(gp) == 1);
        x0 = xi;
        xpa = (Rpk(x0)*se_pk).mod(gt);
        # print("sol mod P^a ? ", xpa); # So far, seems good

    v,y=cvp_babai_NP(L_A, vector(ZZ,K(xpa).list()));
    s = K((vector(K(xpa).list()) - v).list());
    return s;


### ---------------------------------------------------------
#### CRT-based
def root_mod_p(elts, exps, p, eth):
    assert(mod(p, eth)!=1);
    K = elts[0].parent();
    # Define Fp/[y]/1/e mod p
    Fp  = GF(p);
    Fpy = PolynomialRing(Fp, name='y');
    inv_e  = ZZ(mod(1/eth, p-1));
    # Orbit above p, plus CRT stuff
    orb_p = my_primes_above(K, p);
    gx_p  = [ Fpy(_pid[1]) for _pid in orb_p ];

    # Residue of the root mod each pid
    res_idp = [];
    for _gx in gx_p:
        _res_elts  = [ Fp( Fpy(_su.polynomial()).mod(_gx)) for _su in elts ];
        _res_se    = prod(_res_elts[j]**exps[j] for j in range(len(elts)));
        _res_s     = _res_se**inv_e;
        # assert(_res_s^eth == _res_se);
        res_idp.append(Fpy(_res_s));
        # -- End for

    # CRT dans K --> sol mod p
    res_p = CRT(res_idp, gx_p); 
    return res_p;


# computation of e-th roots through CRT in number field L
# Q(zeta_e) should not be a subfield of L
def cf_root_crt(elts, exps, e, L, m):
    r"""
    Computes B^(1/e) in OL where B = prod U[i] ^ Exps[i]
    
    Input:
    - 'elts': number field elements; belongs to L
    - 'exps': list of integers; prod elts[i]^exps[i] is of the form A^e
    - 'e': integer; e is the exponent
    - 'L': number field; field where we want to retrieve a e-th root;
    Q(zeta_e) is *not* a subfield of L
    """
    Zx.<x> = PolynomialRing(ZZ)
    bound = sum([abs(exps[i]) * abs(log(vector(elts[i]).norm(2), 2))
                 for i in range(len(elts))])
    bound = 2**(2.5*(bound/e).round());
    crt_p = [];
    _p0 = next_prime(2**60);
    _p0 = _p0 + m - _p0.mod(m) + 1; # = 1 mod m
    while (prod(crt_p) < 2 * bound): # factor 2 because of \pm signs
        while ((not is_prime(_p0)) or (_p0%e ==1)):
            _p0 += m;
        crt_p.append(_p0);
        _p0 += m;
    Pp = prod(crt_p); # we need it to map into -P/2, P/2

    t = cputime(); crt_root = [ Zx(root_mod_p(elts, exps, _p, e)) for _p in crt_p ]; t = cputime(t);
    t = cputime();
    root_big = CRT(crt_root, crt_p) if len(crt_p)>1 else crt_root[0]; # Weird Sage bug if lists have only one element
    root =  L([(_s if _s < Pp/2. else _s - Pp) for _s in root_big ]); # Mapping dans -P/2, P/2 à \pm 1 près
    t = cputime(t);

    return root;


### --------------------------------------------------------------------------
### functions for generalised Couveignes' CRT-based method

### choice for primes
def cf_couveignes_good_prime(L, K, m, q=1, e=1):
    r"""
    Find a good prime for couveignes' method relative to L / K

    INPUT:

    - ''L'' -- cyclotomic number field;
    
    - ''K'' -- cyclotomic number field; K is a subfield of L
    
    - ''m'' -- integer; m is the pair [mK, mL] of conductors of K and L resp.

    OUTPUT: a tuple p, Ip, Jp such that

    - p is a prime interger such that all prime ideals of K above it are inert
      in L/K
    
    - Ip is the list of prime ideals of K above p
    
    - Jp is the list of prime ideals of L above p
    """
    mK = m[0]
    mL = m[1]
    mLK = mL / mK
    my_t = cputime()
    
    a   = ZZ(IntegerModRing(mLK).multiplicative_generator());
    res = CRT([1,a],[mK,mLK]); # target residue mod mL: split in Q(zmK), inert mod mLK)
    p = __prime_mod_m(mL, res, next=q);
    if (e != 1) and (mod(mK,e**2) != 0):
        while (mod(p-1,e**2) == 0):
            p = __prime_mod_m(mL,res,next=p);
    
    Ip = my_primes_above(K, p);
    Jp = my_primes_above(L, p);
    len_K = len(Ip); assert(len_K == K.degree());
    len_L = len(Jp); assert(len_L == len_K);

    Fpy.<y> = PolynomialRing(GF(p))
    Jp1 = []
    for _ip in Ip:
        _gK = _ip[1]
        _gLK = _gK(L.gen()**mLK).polynomial() # generators of ideals in L
        for i in range(len(Jp)):
            _jp = Jp[i]
            _gL = _jp[1]
            if Fpy(_gLK.mod(_gL)) == 0:
                Jp1 += [_jp]
                _a = Jp.pop(i)
                break;
    Jp = Jp1
    return p, Ip, Jp


### relative norm map in number field
## NB: crt_p, crt_Ip, crt_Jp (and bound) are useless + unused
def cf_relative_norms(A, L, K, crt_p=[], crt_Ip=[], crt_Jp=[], bound=0):
    r"""
    Computes N_{L/K}(a)
    
    Input:
    - 'U': number field element; belongs to L
    - 'L': number field;
    - 'K': number field; subfield of L verifying good properties
    ( gcd([L:K], e) == 1, zeta_e belongs to K)
    """
    

    Zx.<x> = PolynomialRing(ZZ);
    my_t = cputime()
    mK = get_conductor(K)
    mL = get_conductor(L)
    mLK = mL//mK;

    phiL = Zx(L.defining_polynomial());
    my_t = cputime()    
    embLK = [ CRT([i,1],[mLK,mK]) for i in range(1,mLK) if gcd(i,mLK)==1 ]; # sigma_s with s mod mLK invertible, s mod mK= 1
    
    Ky.<y> = PolynomialRing(K);
    Lz.<z> = PolynomialRing(L);
    ext_pol = prod(z - L.gen()**i for i in embLK);
    ext_pol = Ky( { _key: K(_val) for (_key,_val) in ext_pol.dict().items()} );
    # print("ext_pol", ext_pol);
    xml_pol = x**mL-1;
    
    #NA = [ prod(Zx(_a.polynomial())(x^i).mod(x^mL-1)) for i in embLK))[::mLK]) for _a in A];
    NA = [ ];
    t = cputime();
    for _a in A:
        _na = Zx(1);
        _ax = _a.list();
        in_t = cputime();
        for _i in embLK: # Necessary to apply mod x^mL-1 at each step
            _axi = Zx(sum( [ _ax[_k]*x**ZZ(mod(_k*_i,mL)) for _k in range(len(_ax)) ] ));
            _na  = (_na*_axi).mod(xml_pol);
        in_t = cputime(in_t); # print("inner ", in_t);
        _na = _na.mod(phiL);
        _na = _na(y).mod(ext_pol); 
        assert(_na.degree() == 0);
        
        NA.append(K(_na));
    t = cputime(t);
    print("all relative norms: {:.2f} [{:.2f}/elt]".format(t, t/len(A)));

    # [Test] Resultants --------------------------------------------------------------
    # t = cputime();
    # ZZut.<u,v> = PolynomialRing(ZZ,2);
    # Ext_pol = [ _c.polynomial()(v) for _c in ext_pol.list() ]; assert(len(Ext_pol) == euler_phi(mLK)+1);
    # Ext_pol = ZZut(sum( u**_i*Ext_pol[_i] for _i in range(len(Ext_pol)) ));
    # NA2 = [ ZZut(_a.polynomial()(u)).resultant(Ext_pol,u).mod(K.defining_polynomial()(v)) for _a in A ];
    # NA2 = [ K(_na(1,x)) for _na in NA2 ];
    # t = cputime(t);
    # print("all relative norms using resultants: {:.2f} [{:.2f}/elt]".format(t, t/len(A)));
    # assert(NA == NA2);
    # //--- [END Resultants] Only works for small values, and always twice slower anyway. Does not scale at all.

    return NA;


### couveignes for one prime and *cyclotomic fields*
def cf_couveignes_mod_p(U, Exps, e, NA, L, K, m, p, PI_p, BL=0, zm=0, ze = 0):
    r"""
    Computes B^(1/e) in OL/(p) where B = prod_i U[i]^Exps[i]

    Input:
    
    - 'B': number field element; belongs to L and is of the form A^e
    
    - 'e': integer; e is the exponent
    
    - 'NA': number field element; norm of A relative to L/K times zeta_e, where zeta_e is a primitive e-th root of unity in K
    
    - 'L': number field; field where we want to retrieve a e-th root of B
    
    - 'K': number field; subfield of L verifying good properties (gcd([L:K], e) == 1,
      zeta_e belongs to K)
    
    - 'p', integer; computations done modulo p
    
    - 'Ip', list of number field ideals; prime ideals of K above p
    
    - 'Jp', list of number field ideals; prime ideals of L above p
    """
    MY_T = cputime()
    mK = m[0]
    mL = m[1]
    mLK = mL / mK
    
    Fp  = GF(p, proof=False);
    Fpy = PolynomialRing(Fp, name='y'); y = Fpy.gen();

    gx_p_K = [Fpy(_ip[1]) for _ip in PI_p[0]]  # generators of ideals in K
    gx_p_L = [Fpy(_jp[1]) for _jp in PI_p[1]]  # generators of ideals in L

    
    # print("before computing residue field in:", cputime(MY_T))
    # residue fields
    my_t = cputime()
    q  = p**gx_p_L[0].degree();
    Lp = [GF(q, modulus=_gx, name='A', proof=False) for _gx in gx_p_L];

    # embed norm in residue fields
    NAp = [Fp (Fpy(NA.polynomial()).mod(_gx)) for _gx in gx_p_K];     

    gt = Fpy(L.polynomial())
    BL = prod( power_mod(   Fpy(_u.polynomial()), _e, gt ) for _u,_e in zip(U,Exps) ).mod(gt);
    BLp = [ _lp(BL) for _lp in Lp ];

    my_t = cputime()
    assert(ZZ(e).divides(p-1));
    Fp_gen = Fp.multiplicative_generator();
    ze_p   = [ Fp_gen**(_k*(p-1)/e) for _k in range(e) ];
    # print("time for ze mod p: ", cputime(my_t));

    my_t = cputime();
    # eth roots of embeddings of B in residue fields
    if (gcd(e, (p-1)//e) == 1):
        print("e-th root in Fq using inversions");
        inv_e  = ZZ(mod(1/e, (q-1)/e));
        BLp_e  = [ _blp**inv_e for _blp in BLp ]; # Could just apply ^1/e ***before*** mapping in Lp
    else:
        print("WARN: e-th root in Fq using generic methods", end="\t");
        BLp_e = []
        if e < 10:         # factorisation of polynomials z^e - A in residue fields if e is small
            print("Calling eq.roots()");
            for i in range(len(BLp)):
                Q.<z> = PolynomialRing(Lp[i])
                eq = z**e - BLp[i]
                pr = eq.roots()
                pr = pr[0][0]#[_pr[0] for _pr in pr]
                BLp_e += [pr]
        else:
            print("Calling nth_root");
            BLp_e = [_blp.nth_root(e, all=False) for _blp in BLp];
    # print("time taken for eth roots is: ", cputime(my_t));

    my_t = cputime()
    # norms of previous roots
    frob  = (q-1)//(p-1); 
    NB_mod_ze = [ Fp(_blp_e**frob)/_na for _blp_e, _na in zip(BLp_e, NAp) ];
    # print("time for relative norms mod ze in Fp: ", cputime(my_t));
    
    # for each residue field, test which norm is good
    ze_pow_idx = [ ze_p.index(_ze) for _ze in NB_mod_ze ];
    # print("time afer index: ", cputime(my_t));
    inv_nLK = mod(1/euler_phi(mLK),e); # normally guaranteed to be invertible
    ALp = [ _blp*ze_p[( -_idx*inv_nLK )] for _blp, _idx in zip(BLp_e,ze_pow_idx) ];

    # reconstruction via CRT
    Ap = CRT([Fpy(_alp.polynomial()) for _alp in ALp], gx_p_L);
    # print("time after CRT: ", cputime(my_t));
    
    return Ap;



# -------------------------------------------------------------------------------------
# The main recursive function
def cf_roots_rec(U, Exps, e, L, mL, size_primes=60):
    r"""
    Computes B^(1/e) in OL where B = prod U[i] ^ Exps[i]
    Recursive version
    
    Input:
    - 'U': number field elements; belongs to L
    - 'Exps': list of integers; prod U[i]^Exps[i] is of the form A^e
    - 'e': integer; e is the exponent
    - 'L': number field; field where we want to retrieve a e-th root of B
    """

    if mL%e != 0:               # good case : we can do a CRT à la Thomé
        print("can do crt")
        return cf_root_crt(U, Exps, e, L, mL), 0;
    else:                       # bad case : factor the conductor to know what to do
        if cf_can_inert(mL): # len(fL)==1:          # mL=e^k for some k : we can use plain Hensel
            print("can use hensel")
            # Fits well with real measurements for cyclotomics
            Be = sum(Exps[j]* log(vector(ComplexField(300), U[j].complex_embeddings(prec=300)).norm(infinity),2)
                     for j in range(len(U)));
            # print("log h(s^e) = {:.2f}".format(Be));
            B  = Be / e;
            # print("log h(s) = {:.2f}".format(B));
            B =  2**B;
            return cf_padic_lifting(U, Exps, e, B), 0
        else:                   # can we use couveignes then ?
            fK = []
            mK = 1
            fL = factor(mL)
            for _f in fL:
                if (_f[0]==e) or (euler_phi(_f[0])%e == 0):
                    fK.append(_f)
                    mK *= _f[0]**_f[1]
            mLK = mL // mK
            # print(mLK)
            if mK==mL or (not cf_can_inert(mLK)):
                # /!\ WORST CASE : we use p-adic reconstruction by [Bel03]
                print("using custom Belabas")
                phi = get_inf_places(L,300);
                lurs = [ logarg_set(_u, phi) for _u in U ];
                return belabas(U, Exps, e, lurs), 0;
            else: # start Couveignes' process
                print("using couveignes' method")
                K = CyclotomicField(mK)
                m = [mK,mL]
                Zx.<x> = PolynomialRing(ZZ);
                nL = L.degree()
                nK = K.degree()
                nLK = ZZ(nL / nK)
                zL = L.gen()
                ze = zL**(m[1]/e)
                        
                my_t = cputime()

                Re = RealField(300);
                bound_u = [abs(log(vector(Re,_u).norm(2), 2)) for _u in U];
                bound_basis = max(bound_u) # much faster if not in symb ring
                # bound_norm = round(2**(bound_basis*nLK)/2 +  log(sqrt(Re(nL))*nLK, 2) /2)
                print("calcul des bornes: {:.2f}".format(cputime(my_t)));

                NU = cf_relative_norms(U,L,K,[],[],[],0); # relative norm computation
                print("relative norm computed in: ", cputime(my_t));
                t_norm = cputime(my_t)
                
                my_t = cputime()
                NA, _ = cf_roots_rec(NU, Exps, e, K, mK) # recursive e-th root of relative norm
                print("root of norm computed in: ", cputime(my_t));

                # now will start CRT process
                A_crt = [];
                my_t = cputime();
                bound = sum([ abs(_e)*_bu for _e, _bu in zip(Exps,bound_u) ]);
                bound = 2**(1.3*(bound/e).round());
                print("bounds for couveignes: ", cputime(my_t));
                p = randint(2**size_primes, 2**(size_primes+1));
                # p = p- p%mK + 1
                crt_Ip = [];
                crt_p = [];
                crt_Jp = [];
                crt_Ap = [];
                prod_crt_p = 1;
                
                my_t = cputime();
                while prod_crt_p < bound: # computation of suitable primes 
                    p, Ip, Jp = cf_couveignes_good_prime(L, K, m, q=p, e=e);
                    prod_crt_p *= p;
                    crt_p.append(p);
                    crt_Ip.append(Ip);
                    crt_Jp.append(Jp);
                print("primes for couv computed in: ", cputime(my_t));
                for i in range(len(crt_p)): # now we'll find the root mod p for each p
                    my_int = cputime();
                    print("treating ", crt_p[i], flush=True);
                    crt_Ap += [cf_couveignes_mod_p(U, Exps, e, NA, L, K, m, crt_p[i],
                                                   [crt_Ip[i], crt_Jp[i]], zL, ze)];
                    print("one couveignes mod p computed in: ", cputime(my_int));
                crt_Ap = [Zx(_ap) for _ap in crt_Ap];

                my_t = cputime();
                A_big = CRT(crt_Ap, crt_p) if len(crt_p)>1 else crt_Ap[0]; # reconstruction through CRT
                print("CRT for couveignes in: ", cputime(my_t));

                A = L([(_a if _a < prod_crt_p/2. else _a - prod_crt_p) for _a in A_big]);
                return A, t_norm;                
