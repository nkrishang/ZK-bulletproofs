import random
from libnum import has_sqrtmod_prime_power, sqrtmod_prime_power
from py_ecc.bn128 import is_on_curve, FQ, multiply, add, eq, neg, G1, Z1, curve_order as p
from py_ecc.fields import field_properties
from functools import reduce


field_mod = field_properties["bn128"]["field_modulus"]

####################### EC & VECTOR OPERATIONS ###########################

# Adds up multiple EC points
def add_points(*points):
    return reduce(add, points, Z1)

# Inner product of an EC point vector and a scalar vector
def vector_commit(points, scalars):
    return reduce(add, [multiply(P, i) for P, i in zip(points, scalars)], Z1)

# Element-wise scalar and point vector multiplication mod curve order p
def points_vec_mul(points, scalars):
    return [multiply(x, y) for x, y in zip(points, scalars)]

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

# Returns an array of the binary representation (little endian) of n
def getBinaryAsArray(n):
    if n < 0:
        raise ValueError("Input must be a positive integer")
    if n == 0:
        return [0]
        
    binary = []
    while n > 0:
        binary.append(n & 1)  # Get least significant bit
        n >>= 1              # Right shift by 1 (divide by 2)
    return binary

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

# Prove that v < 2^n
def rangeProofAndVerify(v, n):

    # Public factors
    vec_1n = [1] * n
    
    vec_2n = []
    for i in range(n):
        vec_2n.append(pow(2, i, p))
    
    # Get binary representation of v
    a_L = getBinaryAsArray(v)
    a_R = mod_vec_add(a_L, mod_scalar_mul(vec_1n, -1, p), p)

    # Generate random EC point basis vectors G,H and a random EC point Q
    G_vec = generateRandomECPointVec(n)
    H_vec = generateRandomECPointVec(n)
    Q = generateRandomECPointVec(1)[0]
    B = generateRandomECPointVec(1)[0]

    # Prover blinding terms
    alpha = random_field_element()
    beta = random_field_element()
    gamma = random_field_element()
    tau_1 = random_field_element()
    tau_2 = random_field_element()

    sL = random_scalar_vector(n)
    sR = random_scalar_vector(n)

    # Prover commitments
    A = add_points(vector_commit(G_vec, a_L), vector_commit(H_vec, a_R), multiply(B, alpha))
    S = add_points(vector_commit(G_vec, sL), vector_commit(H_vec, sR), multiply(B, beta))
    V = add_points(multiply(Q, v), multiply(B, gamma))

    # Verifier sends randomness y,z and u
    y = random_field_element()
    z = random_field_element()
    u = random_field_element()

    vec_yn = []
    vec_yn_inv = []
    for i in range(len(a_L)):
        vec_yn.append(pow(y, i, p))
        vec_yn_inv.append(pow(y, -i, p))

    # Compute l(u), r(u), t(u)
    
    l_u_term1 = mod_vec_add(a_L, mod_scalar_mul(vec_1n, -z, p), p)
    l_u_term2 = sL
    l_u = mod_vec_add(l_u_term1, mod_scalar_mul(l_u_term2, u, p), p)

    r_u_term1 = mod_vec_add(mod_vec_add(mod_vec_mul(vec_yn, a_R, p), mod_scalar_mul(vec_yn, z, p), p), mod_scalar_mul(vec_2n, pow(z, 2, p), p), p)
    r_u_term2 = mod_vec_mul(vec_yn, sR, p)
    r_u = mod_vec_add(r_u_term1, mod_scalar_mul(r_u_term2, u, p), p)

    tu_term1 = mod_inner(l_u_term1, r_u_term1, p)
    tu_term2 = (mod_inner(l_u_term1, r_u_term2, p) + mod_inner(l_u_term2, r_u_term1, p)) % p
    tu_term3 = mod_inner(l_u_term2, r_u_term2, p)
    t_u = (tu_term1 + tu_term2 * u + tu_term3 * pow(u, 2, p)) % p

    pi_lr = alpha + (beta * u % p) % p
    pi_t = ((gamma * pow(z, 2, p) % p) + (tau_1 * u % p) + (tau_2 * pow(u, 2, p) % p)) % p

    T1 = add_points(multiply(Q, tu_term2), multiply(B, tau_1))
    T2 = add_points(multiply(Q, tu_term3), multiply(B, tau_2))

    # Verifier computes new basis vector H.y^-1
    H_y_inv = points_vec_mul(H_vec, vec_yn_inv)

    # Generate proof and verify
    C = add_points(vector_commit(G_vec, l_u), vector_commit(H_y_inv, r_u))

    verification = verify(l_u, r_u, r_u, add_points(C, multiply(Q, t_u)), G_vec, H_y_inv, Q) 

    j = vector_commit(G_vec, mod_scalar_mul(vec_1n, -z, p))
    k = vector_commit(H_y_inv, mod_vec_add(mod_scalar_mul(vec_yn, z, p), mod_scalar_mul(vec_2n, pow(z, 2, p), p), p))

    verification = verification and eq(C, add_points(A, multiply(S, u), j, k, neg(multiply(B, pi_lr))))

    # Then combine with the z terms
    delta = (
        # (z - z^2)⟨1^n, y^n⟩
        mod_inner([((z - pow(z, 2, p)) % p)], [mod_inner(vec_1n, vec_yn, p)], p) - 
        # z^3⟨1^n, 2^n⟩
        mod_inner([pow(z, 3, p)], [mod_inner(vec_1n, vec_2n, p)], p)
    ) % p

    verification = verification and eq(add_points(multiply(Q, t_u), multiply(B, pi_t)), add_points(multiply(V, pow(z, 2, p)), multiply(Q, delta), multiply(T1, u), multiply(T2, pow(u, 2, p))))

    return verification


assert rangeProofAndVerify(246, 8), "invalid range proof"

print("accepted")