import random
from libnum import has_sqrtmod_prime_power, sqrtmod_prime_power
from py_ecc.bn128 import is_on_curve, FQ, multiply, add, eq, neg, Z1, curve_order as p
from py_ecc.fields import field_properties
from functools import reduce


field_mod = field_properties["bn128"]["field_modulus"]

# Test cases
a1 = [808, 140, 166, 209]
b1 = [88, 242, 404, 602]

a2 = [433, 651]
b2 = [282, 521]

a3 = [222]
b3 = [313]

# Prove you know the inner product of a and b using a combination of the algorithm from Chapter 5 and Chapter 7.
# Your interactive proof should transmit no more than logarithmic size data and be zero knowledge even if n = 1.
# Use a random elliptic curve basis based on the algorithm from Chapter 1.

####################### EC & VECTOR OPERATIONS ###########################

# Adds up multiple EC points
def add_points(*points):
    return reduce(add, points, Z1)

# Inner product of an EC point vector and a scalar vector
def vector_commit(points, scalars):
    return reduce(add, [multiply(P, i) for P, i in zip(points, scalars)], Z1)

# Inner product of two scalar vectors mod curve order p
def mod_inner(a, b, p):
    return sum((x * y) % p for x, y in zip(a, b)) % p

# Scalar multiplication of a scalar vector by some factor mod curve order p
def mod_scalar_mul(arr, scalar, p):
    return [(x * scalar) % p for x in arr]

# Scalar vector addition mod curve order p
def mod_vec_add(a, b, p):
    return [(x + y) % p for x, y in zip(a, b)]

# Element-wise scalar vector multiplication mod curve order p
def mod_vec_mul(a, b, p):
    return [(x * y) % p for x, y in zip(a, b)]

# Returns a random element from the scalar field of the bn128 elliptic curve.
def random_field_element():
    return random.randint(0, p)

# Returns a random scalar vector of length n
def random_scalar_vector(n):
    return [random_field_element() for _ in range(n)]

# Generates a random EC point vector of length n
def generateRandomECPointVec(n):
    b = 3 # for bn128, y^2 = x^3 + 3

    x = random_field_element()

    entropy = 0
    vector_basis = []

    while len(vector_basis) < n:
        while not has_sqrtmod_prime_power((x**3 + b) % field_mod, field_mod, 1):
            # increment x, so hopefully we are on the curve
            x = (x + 1) % field_mod
            entropy = entropy + 1

        # pick the upper or lower point depending on if entropy is even or odd
        y = list(sqrtmod_prime_power((x**3 + b) % field_mod, field_mod, 1))[entropy & 1 == 0]
        point = (FQ(x), FQ(y))
        assert is_on_curve(point, b), "sanity check"
        vector_basis.append(point)

        # new x value
        x = random_field_element()
    
    return vector_basis

####################### HELPERS ###########################

# Generate commitments vector polynomials
def commit(a, sL, b, sR, alpha, beta, gamma, tau_1, tau_2, G_vec, H_vec, Q, B):

    A = add_points(vector_commit(G_vec, a), vector_commit(H_vec, b), multiply(B, alpha))
    S = add_points(vector_commit(G_vec, sL), vector_commit(H_vec, sR), multiply(B, beta))
    V = add_points(multiply(Q, mod_inner(a,b, p)), multiply(B, gamma))

    T1 = add_points(multiply(Q, (mod_inner(a, sR, p) + mod_inner(b, sL, p)) % p), multiply(B, tau_1))
    T2 = add_points(multiply(Q, mod_inner(sR, sL, p)), multiply(B, tau_2))

    return (A, S, V, T1, T2)

# Fold a scalar vector
def fold(scalar_vec, u):
    i = 0
    vec = []
    while i < len(scalar_vec):
        vec.append((mod_inner([scalar_vec[i]], [u], p) + mod_inner([scalar_vec[i+1]], [pow(u, -1, p)], p)) % p)
        i += 2
    
    assert len(vec) == len(scalar_vec) / 2
    return vec

# Fold an EC points vector
def fold_points(point_vec, u):
    i = 0
    vec = []
    while i < len(point_vec):
        vec.append(add_points(multiply(point_vec[i], u), multiply(point_vec[i+1], pow(u, -1, p))))
        i += 2
    
    return vec

# Compute the secondary diagonal L,R for a scalar vector and EC point vector
def compute_secondary_diagonal(G_vec, a):
    R = Z1
    L = Z1

    for i in range(len(a)):
        if i % 2 == 0:
            R = add_points(R, multiply(G_vec[i], a[i+1]))
        else:
            L = add_points(L, multiply(G_vec[i], a[i-1]))

    return L, R

# Compute the secondary diagonal L,R for a scalar vectors
def compute_secondary_diagonal_scalar(b, a):
    R = 0
    L = 0

    for i in range(len(a)):
        if i % 2 == 0:
            R = (R + (b[i] * a[i+1] % p)) % p
        else:
            L = (L + (b[i] * a[i-1] % p)) % p

    return L, R

def verify(a, b, b_inv, P, G_vec, H_vec, Q):

    assert len(a) == len(b) == len(b_inv) == len(G_vec) == len(H_vec), "vectors must be of same length"

    if len(a) > 1:
        # Compute L and R    
        L_a, R_a = compute_secondary_diagonal(G_vec, a)
        L_b, R_b = compute_secondary_diagonal(H_vec, b)
        L_q, R_q = compute_secondary_diagonal_scalar(b_inv, a)

        L = add_points(L_a, L_b, multiply(Q, L_q))
        R = add_points(R_a, R_b, multiply(Q, R_q))

        # Verifier provided randomness
        u = random_field_element()

        # Compute P'
        Pprime = add_points(multiply(L, pow(u, 2, p)), P, multiply(R, pow(u, -2, p)))

        # Fold
        aprime = fold(a, u)
        bprime = fold(b, u)
        bprime_inv = fold(b_inv, pow(u, -1, p))

        Gprime = fold_points(G_vec, pow(u, -1, p))
        Hprime = fold_points(H_vec, pow(u, -1, p))

        return verify(aprime, bprime, bprime_inv, Pprime, Gprime, Hprime, Q)
    else:
        return eq(P, add_points(vector_commit(G_vec, a), vector_commit(H_vec, b), multiply(Q, mod_inner(a, b_inv, p))))

####################### PROVE AND VERIFY ###########################

def proveAndVerify(a, b):
    assert len(a) == len(b), "vectors must be of same length"
    assert len(a) == 1 or len(a) % 2 == 0, "vector length must be 1 or even"
    
    # Get vector length
    n = len(a)
    
    # Generate random EC point basis vectors G,H and a random EC point Q
    G_vec = generateRandomECPointVec(n)
    H_vec = generateRandomECPointVec(n)
    Q = generateRandomECPointVec(1)[0]
    B = generateRandomECPointVec(1)[0]

    # Compute P: commitment to a,b and <a,b> = v
    P = add_points(vector_commit(G_vec, a), vector_commit(H_vec, b), multiply(Q, mod_inner(a, b, p)))

    verification = False

    if n == 1:
        verification = eq(P, add_points(vector_commit(G_vec, a), vector_commit(H_vec, b), multiply(Q, mod_inner(a, b, p))))
    else:
        # Prover blinding terms
        alpha = random_field_element()
        beta = random_field_element()
        gamma = random_field_element()
        tau_1 = random_field_element()
        tau_2 = random_field_element()

        sL = random_scalar_vector(n)
        sR = random_scalar_vector(n)

        # Prover creates the commitments
        A, S, V, T1, T2 = commit(a, sL, b, sR, alpha, beta, gamma, tau_1, tau_2, G_vec, H_vec, Q, B)

        # Verifier picks u
        u = random_field_element()

        # Compute l(u), r(u), t(u) and creates evaluation proofs
        l_u = mod_vec_add(a, mod_scalar_mul(sL, u, p), p)
        r_u = mod_vec_add(b, mod_scalar_mul(sR, u, p), p)
        t_u = (mod_inner(a, b, p) + (((mod_inner(a, sR, p) + mod_inner(b, sL, p)) % p) * u) % p + ((mod_inner(sR, sL, p) * pow(u, 2, p))) % p) % p

        pi_lr = alpha + (beta * u % p) % p
        pi_t = (gamma + (tau_1 * u % p) + (tau_2 * u**2 % p)) % p

        # Generate proof and verify
        C = add_points(vector_commit(G_vec, l_u), vector_commit(H_vec, r_u));

        verification = verify(l_u, r_u, r_u, add_points(C, multiply(Q, t_u)), G_vec, H_vec, Q) 
        verification = verification and eq(C, add_points(A, multiply(S, u), neg(multiply(B, pi_lr))))
        verification = verification and eq(multiply(Q, t_u), add_points(V, multiply(T1, u), multiply(T2, pow(u, 2, p)), neg(multiply(B, pi_t))))
    
    return verification

assert proveAndVerify(a1, b1), "invalid proof"
assert proveAndVerify(a2, b2), "invalid proof"
assert proveAndVerify(a3, b3), "invalid proof"

print("accepted")