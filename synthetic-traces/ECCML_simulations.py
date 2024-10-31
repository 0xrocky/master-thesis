#!/usr/bin/env python
# coding: utf-8
import hashlib
import datetime
import ecdsa
import random
import numpy as np
import sys
import os
import pathlib

# MACRO
CONT = str(sys.argv[1])
BASE_PATH = str(pathlib.Path(__file__).parent.resolve())
TRACES_PATH = BASE_PATH + '/traces'
K_PATH = BASE_PATH + '/Ks'
Z_PATH = BASE_PATH + '/Zs'
SIZE_SIMULATION_TRACES = 1  # number of synthetic traces
TAG_ADD = 1
TAG_SUB = 2
TAG_MUL = 3
TAG_END = 0  # tag of a delimitator of a modular operation
SUB = 153  # time duration of a single sub
ADD = SUB  # time duration of a single sub
MUL = 2648  # time duration of a single multiplication
MAX_SUB = 255
MAX_MUL = 2804
MODULO_SUB = MAX_SUB - SUB  # time duration of a modulo
MODULO_MUL = MAX_MUL - MUL  # time duration of a modulo
CONT_ADDS = 0
CONT_ADDS_OF = 0
CONT_SUBS = 0
CONT_SUBS_OF = 0
gen = ecdsa.SECP160r1.generator
order = gen.order()
curve = gen.curve()
p = curve.p()
inv_two_p = pow(2, p-2, p)
Zs = []
K_LENGTH = len(str(bin(order))) - 2
Z_LENGTH = len(str(bin(order))) - 3
########################################################################################################################
###################################################### SIMULATOR #######################################################
########################################################################################################################

# add a power consumption to my trace with a tag: ( weight, tag )
def add_consumption_tag(trace, consumption, tag):
    trace += [(consumption, tag)]


# Hamming weight models the consumption of a chip
# def hamming_weight(n):
#     return bin(n).count("1")

m1  = 0x5555555555555555 #binary: 0101...
m2  = 0x3333333333333333 #binary: 00110011..
m4  = 0x0f0f0f0f0f0f0f0f #binary:  4 zeros,  4 ones ...
m8  = 0x00ff00ff00ff00ff #binary:  8 zeros,  8 ones ...
m16 = 0x0000ffff0000ffff #binary: 16 zeros, 16 ones ...
m32 = 0x00000000ffffffff #binary: 32 zeros, 32 ones
h01 = 0x0101010101010101 #the sum of 256 to the power of 0,1,2,3...

def hamming_weight(x: int) -> int:
    x -= (x>>1)&m1
    x = (x&m2) + ((x>>2)&m2)
    x = (x+(x>>4))&m4
    return ((x*h01)>>56)&0x7f


# The hamming weight in the index "position" of the trace
def get_weight(trace, position):
    return trace[position][0]


# The tag in the index "position" of the trace
def get_tag(trace, position):
    return trace[position][1]


# measure of a leakage
def leakage(trace, result, tag):
    if isinstance(result, int):
        add_consumption_tag(trace, hamming_weight(result), tag)


# ADD tag = 1
def add_modulo(x1, x2, trace, trace_ops):
    # global p
    global CONT_ADDS
    global CONT_ADDS_OF
    result = x1 + x2
    original_result = result
    is_long = False
    for i in range(ADD):
        trace += [(hamming_weight(original_result), TAG_ADD)]
        # leakage(trace, original_result, TAG_ADD)
    if result >= p:
        is_long = True
        # with open('output.txt', 'a') as f:
        #    f.write( '\tADD_OF\n' )
        for i in range(MODULO_SUB):
            trace += [(hamming_weight(original_result), TAG_ADD)]
            # leakage(trace, original_result, TAG_ADD)
        result -= p
        CONT_ADDS_OF += 1
    else:
        # with open('output.txt', 'a') as f:
        #    f.write( '\tADD\n' )
        CONT_ADDS += 1
    trace += [(hamming_weight(original_result), TAG_END)]
    if is_long:
        trace_ops += ['ADD_OF']
    else:
        trace_ops += ['ADD']
    # leakage(trace, original_result, TAG_END)
    return result


# SUB tag = 2
def sub_modulo(x1, x2, trace, trace_ops):
    # global p
    global CONT_SUBS
    global CONT_SUBS_OF
    result = x1 - x2
    original_result = result
    is_long = False
    for i in range(SUB):
        trace += [(hamming_weight(original_result), TAG_SUB)]
        # leakage(trace, original_result, TAG_SUB)
    if result < 0:
        is_long = True
        # with open('output.txt', 'a') as f:
        #    f.write( '\tSUB_OF\n' )
        result += p
        for i in range(MODULO_SUB):
            trace += [(hamming_weight(original_result), TAG_SUB)]
            # leakage(trace, original_result, TAG_SUB)
        CONT_SUBS_OF += 1
    else:
    #     # with open('output.txt', 'a') as f:
    #     #    f.write( '\tSUB\n' )
        CONT_SUBS += 1
    trace += [(hamming_weight(original_result), TAG_END)]
    # leakage(trace, original_result, TAG_END)
    if is_long:
        trace_ops += ['SUB_OF']
    else:
        trace_ops += ['SUB']
    return result


# MUL tag = 3
def mul_modulo(x1, x2, trace, trace_ops):
    # global p
    result = x1 * x2
    original_result = result
    is_long = False
    for i in range(MUL):
        trace += [(hamming_weight(original_result), TAG_MUL)]
        # leakage(trace, original_result, TAG_MUL)
    if result >= p:
        is_long = True
        result = result % p
        for i in range(MODULO_MUL):
            trace += [(hamming_weight(original_result), TAG_MUL)]
            # leakage(trace, original_result, TAG_MUL)
    trace += [(hamming_weight(original_result), TAG_END)]
    # leakage(trace, original_result, TAG_END)
    if is_long:
        trace_ops += ['MUL_OF']
    else:
        trace_ops += ['MUL']
    return result


# Inverse of the final Z-coordinate
# def FinalInvZ(R, Point, b, z):
def FinalInvZ(R, Point, b):
    global p
    Xb, Yb = R[b]
    XPoint = Point.x()
    YPoint = Point.y()
    z = XPoint * Yb * (R[1][0] - R[0][0])
    z = pow(z, p-2, p)
    z = (Xb * YPoint * z) % p
    return z


# Functions of Montgomery Ladder with consumption registration
# (X,Y)-only co-Z addition with update: computed (X,Y)-coordinates of P + Q and update (X,Y)-coordinates of P
# Algorithm 18
def XYCZ_ADD_modulo(R0, R1, trace, trace_ops):
    # input: ( X1, Y1 ) and ( X2, Y2 ) t.c. P = ( X1 : Y1 : Z ) and Q = ( X2 : Y2 : Z ) for some Z € Fq, P, Q € E( Fq )
    # output: ( X3, Y3 ) and ( X'1, Y'1 ) t.c. P = ( X'1: Y'1: Z3 ) and P + Q = ( X3 : Y3 : Z3 ) for some Z3 € Fq
    # T1 = X1, T2 = Y1, T3 = X2, T4 = Y2
    T1 = R0[ 0 ]
    T2 = R0[ 1 ]
    T3 = R1[ 0 ]
    T4 = R1[ 1 ]
    T5 = sub_modulo(T3, T1, trace, trace_ops)  # X2 - X1
    T5 = mul_modulo(T5, T5, trace, trace_ops)  # ( X2 - X1 )^2 = A
    T1 = mul_modulo(T1, T5, trace, trace_ops)  # X1 * A = B
    T3 = mul_modulo(T3, T5, trace, trace_ops)  # X2 * A = C
    T4 = sub_modulo(T4, T2, trace, trace_ops)  # Y2 - Y1
    T5 = mul_modulo(T4, T4, trace, trace_ops)  # ( Y2 - Y1 )^2 = D
    T5 = sub_modulo(T5, T1, trace, trace_ops)  # D - B
    T5 = sub_modulo(T5, T3, trace, trace_ops)  # X3
    T3 = sub_modulo(T3, T1, trace, trace_ops)  # C - B
    T2 = mul_modulo(T2, T3, trace, trace_ops)  # Y1 * ( C - B )
    T3 = sub_modulo(T1, T5, trace, trace_ops)  # B - X3
    T4 = mul_modulo(T4, T3, trace, trace_ops)  # ( Y2 - Y1 ) * ( B - X3 )
    T4 = sub_modulo(T4, T2, trace, trace_ops)  # Y3
    return ((T5, T4), (T1, T2))


# ADDC with modulo operations
# (X,Y)-only co-Z conjugate addition: computed (X,Y)-coordinates of P + Q and (X,Y)-coordinates of P - Q
# Algo 19
def XYCZ_ADDC_modulo(R0, R1, trace, trace_ops):
    # input: ( X1, Y1 ) and ( X2, Y2 ) t.c. P = ( X1 : Y1 : Z ) and Q = ( X2 : Y2 : Z ) for some Z € Fq, P, Q € E( Fq )
    # output: ( X3, Y3 ) and ( X'3, Y'3 ) t.c. P + Q = ( X3: Y3: Z3 ) and P - Q = ( X'3 : Y'3 : Z3 ) for some Z3 € Fq
    # T1 = X1, T2 = Y1, T3 = X2, T4 = Y2
    T1 = R0[0]
    T2 = R0[1]
    T3 = R1[0]
    T4 = R1[1]
    T5 = sub_modulo(T3, T1, trace, trace_ops)  # X2 - X1
    T5 = mul_modulo(T5, T5, trace, trace_ops)  # ( X2 - X1 )^2 = A
    T1 = mul_modulo(T1, T5, trace, trace_ops)  # X1 * A = B
    T3 = mul_modulo(T3, T5, trace, trace_ops)  # X2 * A = C
    T5 = add_modulo(T4, T2, trace, trace_ops)  # Y1 + Y2
    T4 = sub_modulo(T4, T2, trace, trace_ops)  # Y1 - Y2
    T6 = sub_modulo(T3, T1, trace, trace_ops)  # C - B
    T2 = mul_modulo(T2, T6, trace, trace_ops)  # Y1 * ( C - B )
    T6 = add_modulo(T3, T1, trace, trace_ops)  # B + C
    T3 = mul_modulo(T4, T4, trace, trace_ops)  # ( Y2 - Y1 )^2
    T3 = sub_modulo(T3, T6, trace, trace_ops)  # X3
    T7 = sub_modulo(T1, T3, trace, trace_ops)  # B - X3
    T4 = mul_modulo(T4, T7, trace, trace_ops)  # ( Y1 - Y2 ) * ( B - X3 )
    T4 = sub_modulo(T4, T2, trace, trace_ops)  # Y3
    T7 = mul_modulo(T5, T5, trace, trace_ops)  # ( Y2 + Y1 )^2 = F
    T7 = sub_modulo(T7, T6, trace, trace_ops)  # X'3
    T6 = sub_modulo(T7, T1, trace, trace_ops)  # X'3 - B
    T6 = mul_modulo(T6, T5, trace, trace_ops)  # ( Y2 + Y1 ) * ( X'3 - B )
    T6 = sub_modulo(T6, T2, trace, trace_ops)  # Y'3
    return ((T3, T4), (T7, T6))


# Algo 14
def double_jacobian(X1, Y1, Z1, trace, trace_ops):
    # input: P ≡ ( X1, Y1, Z1 )
    # output: 2P ≡ ( X3, Y3, Z3 )
    T1 = X1
    T2 = Y1
    T3 = Z1
    T4 = mul_modulo(T2, T2, trace, trace_ops)  # Y1^2
    T5 = mul_modulo(T1, T4, trace, trace_ops)  # X1Y1^2 = A
    T4 = mul_modulo(T4, T4, trace, trace_ops)  # Y1^4
    T2 = mul_modulo(T2, T3, trace, trace_ops)  # Y1Z1= Z3
    T3 = mul_modulo(T3, T3, trace, trace_ops)  # Z1^2
    T1 = add_modulo(T1, T3, trace, trace_ops)  # X1 + Z1^2
    T3 = add_modulo(T3, T3, trace, trace_ops)  # 2Z1^2
    T3 = sub_modulo(T1, T3, trace, trace_ops)  # X1 - Z1^2
    T1 = mul_modulo(T1, T3, trace, trace_ops)  # X1^2 - Z1^4
    T3 = add_modulo(T1, T1, trace, trace_ops)  # 2(X1^2 - Z1^4)
    T1 = add_modulo(T1, T3, trace, trace_ops)  # 3(X1^2 - Z1^4)
    T1 = (T1 * inv_two_p) % p
    T3 = mul_modulo(T1, T1, trace, trace_ops)  # B^2
    T3 = sub_modulo(T3, T5, trace, trace_ops)  # B^2 - A
    T3 = sub_modulo(T3, T5, trace, trace_ops)  # B^2 - 2A = X3
    T5 = sub_modulo(T5, T3, trace, trace_ops)  # A - X3
    T1 = mul_modulo(T1, T5, trace, trace_ops)  # B(A - X3)
    T1 = sub_modulo(T1, T4, trace, trace_ops)  # B(A - X3) - Y1^4 = Y3
    return (T3, T1, T2)

# To check
def apply_z(X, Y, Z, trace, trace_ops):
    # ( X, Y ) => ( X * Z^2, Y * Z^3 )
    T1 = mul_modulo(Z,  Z, trace, trace_ops)  # Z^2
    X  = mul_modulo(X, T1, trace, trace_ops)  # X * Z^2
    T1 = mul_modulo(T1, Z, trace, trace_ops)  # Z^3
    Y  = mul_modulo(Y, T1, trace, trace_ops)  # Y * Z^3
    return (X, Y)

# To check
def XYcZ_initial_double(P, Z, trace, trace_ops):
    # R0 = X2, Y2
    # R1 = X1, Y1
    X1 = P[0]
    Y1 = P[1]
    X1_P, Y1_P = apply_z(X1, Y1, Z, trace, trace_ops)
    X1_P, Y1_P, Z_P = double_jacobian(X1_P, Y1_P, Z, trace, trace_ops)
    X2_P, Y2_P = apply_z(X1, Y1, Z_P, trace, trace_ops)
    return ((X1_P, Y1_P), (X2_P, Y2_P), Z_P)


# micro-ecc version of Montgomery Ladder with double jacobian
def montgomery_ladder_coz_microecc(scal, Point, trace, trace_ops):
    # input: P € E(fq), k = [kn-1,...,k1,k0]2 t.c. Kn-1 = 1
    # output: Q = [k]*P
    global Zs
    # Padding
    digits = [int(x) for x in bin(scal)[2:]]
    # digits = list(reversed(digits+[0]*( 160 - len( digits ) )))
    # print("scalar: ", digits)
    z = 2
    while (len(str(bin(z))) - 2 != Z_LENGTH):
        z = random.getrandbits(Z_LENGTH)
    Zs += [ z ]
    R = [[0, 0], [0, 0]]
    P = [Point.x(), Point.y()]
    R[1], R[0], z = XYcZ_initial_double(P, z, trace, trace_ops)
    #for i in range(1, len(digits) - 1):
    for i in range(1, len(digits) - 155):
        b = digits[i]
        R[1-b], R[b] = XYCZ_ADDC_modulo(R[b], R[1 - b], trace, trace_ops)
        R[b], R[1 - b] = XYCZ_ADD_modulo(R[1 - b], R[b], trace, trace_ops)
        trace_ops += ['TAG_BIT {} = {}'.format(i, b)]
    b = digits[len(digits) - 1]
    R[1 - b], R[b] = XYCZ_ADDC_modulo(R[b], R[1 - b], trace, trace_ops)
    l = (FinalInvZ(R, Point, b))
    R[b], R[1 - b] = XYCZ_ADD_modulo(R[1 - b], R[b], trace, trace_ops)
    return (R[0][0] * l**2) % p, (R[0][1] * l**3) % p


########################################################################################################################
##################################################### ECDSA ############################################################
########################################################################################################################

def hashmsg(msg):
    encoded = msg.encode('utf-8')
    result = hashlib.sha1(encoded)
    return int(result.hexdigest(), 16)


def ecdsa_keygen():
    # d = randint( 1, n - 1 ) # private key
    # Q = d * G # public key
    # global order
    secret = random.randrange(1, order)
    pub_key = ecdsa.ecdsa.Public_key(gen, gen * secret)
    priv_key = ecdsa.ecdsa.Private_key(pub_key, secret)
    return pub_key, priv_key


def ecdsa_sign(d, m, trace, trace_ops):
    # d private key
    # m message to sign
    # global gen
    # global order
    r = 0
    s = 0
    while s == 0:
        while r == 0:
            k = random.randrange(1, order)
            C = montgomery_ladder_coz_microecc(k, gen, trace, trace_ops)  # k * G
            r = C[0] % order
        e = hashmsg(m) % order
        s = (pow(k, order - 2, order) * (e + r * d.secret_multiplier) ) % order
    return r, s, e, k


def ecdsa_verify(pub_key, m, r, s):
    # global order
    e = hashmsg(m)
    w = pow(s, order - 2, order)
    u1 = ((w * e) % order)
    u2 = ((w * r) % order)
    X = gen.mul_add(u1, pub_key.point, u2)
    v = X.x() % order
    return v == r


if __name__ == '__main__':
    #np.warnings.filterwarnings('ignore', category=np.VisibleDeprecationWarning)
    # MACRO
    parameters = []
    traces = []
    trace = []
    trace_ops = []
    # gen = ecdsa.SECP160r1.generator
    # order = gen.order()
    # curve = gen.curve()
    # p = curve.p()
    m = 'hello'
    today = datetime.datetime.now()

    # for i in range(2):
    #     # scalar = 133
    #     scalar = random.randrange( 1, order - 1 )
    #     A = montgomery_ladder_coz_microecc(scalar, gen, trace, trace_ops)
    #     B = (scalar * gen).to_affine()
    #     print("Montgomery:", A)
    #     print("Scal_Mult :", B)
    #     if A[0] != B.x() or A[1] != B.y():
    #         print("Error")
    #         print("Montgomery:", A)
    #         print("Scal_Mult :", B)
    #         break
    # print('Tests passed')

    # Q, d = ecdsa_keygen()
    # for i in range(SIZE_SIMULATION_TRACES):
    #    trace = []
    #    r, s, e, k = ecdsa_sign(d, m, trace, trace_ops)
    #    trace = np.array(trace, dtype=object)
    #    traces += [trace]
    #    params = np.array([ Q, d, e, k, r, s], dtype=object)
    #    parameters += [[params]]

    # debugging
    # r, s, e, k = ecdsa_sign( d, m, trace, trace_ops )
    # parameters = [ Q, d, r, s, e, k ]
    #keys = [
    #    int(0b100111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111),
    #    int(0b101111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111),
    #    int(0b110111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111),
    #    int(0b1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111),
    #   ]
    #temp = np.unique( np.array(keys) )
    #keys = np.sort( np.array( keys ) )
    #for i, key in enumerate(keys):
    #    print( i, ") Len:", len(bin(key)), "key:", key )
    #    print( i, ") Len:", len(bin(temp[i])), "key:", temp[i])
    #    if key != temp[i]:
    #        print("error")
    #        break
    print('start tests')
    outstr = ''
    i = 0
    number_of_simulated_traces = 500
    traces = []
    all_trace_ops = []
    keys = set()
    while (len(keys) != number_of_simulated_traces):
        key = random.getrandbits(K_LENGTH)
        if (len(str(bin(key))) - 2) >= K_LENGTH:
            keys.add(key)
    keys = list(keys)
    if len(keys) != 500:
        sys.exit("error number of keys")
    for key in keys:
        trace = []
        trace_ops = []
        CONT_ADDS = 0
        CONT_ADDS_OF = 0
        CONT_SUBS = 0
        CONT_SUBS_OF = 0
        i += 1
        _ = montgomery_ladder_coz_microecc(key, gen, trace, trace_ops)
        # print(key * gen)
        currstr = 'Key {}\n\tCONT_ADDS {}\n\tCONT_ADDS_OF {}\n\tCONT_SUBS {}\n\tCONT_SUBS_OF {}\n'.format(bin(key), CONT_ADDS, CONT_ADDS_OF, CONT_SUBS, CONT_SUBS_OF)
        outstr = '{}{}'.format(outstr, currstr)
        #print(currstr)
        traces.append(trace)
        all_trace_ops.append(trace_ops)
        # with open('output.txt', 'a') as f:
        #    f.write( 'k={k}\n'.format( k=bin(key) ) )
        #    f.write( 'montgomery_ladder_coz_microecc={C}\n'.format( C=montgomery_ladder_coz_microecc( key, G, trace ) ) )
        #    f.write( 'k * G                         ={result}\n'.format( result=key * G ) )
        #    f.write( 'ADD without OF = {c}\n'.format( c=CONT_ADDS ) )
        #    f.write( 'ADD with OF = {c}\n'.format( c=CONT_ADDS_OF ) )
        #    f.write( 'SUB without OF = {c}\n'.format( c=CONT_SUBS ) )
        #    f.write( 'SUB with OF = {c}\n'.format( c=CONT_SUBS_OF ) )
    traces = np.asanyarray(traces, dtype=object)
    all_trace_ops = np.asanyarray(all_trace_ops, dtype=object)
    name = 'traces_{a}'.format( a='_'.join(today.strftime("%c").split(' ')) )
    np.savez_compressed(os.path.join(TRACES_PATH, CONT+'.'+name), x=traces, y=all_trace_ops, dtype=object)

    #np.save(name, traces, allow_pickle=True)
    #[x == y for x, y in zip(all_trace_ops[0], all_trace_ops[1])]
    #print(all_trace_ops[0])
    #print(all_trace_ops[1])
    #print(all_trace_ops[2])
    #print(all_trace_ops[3])
    # training
    #trace = []
    #trace_ops = []
    #scalar = random.randrange( 1, order - 1 )
    #A = montgomery_ladder_coz_microecc(scalar, gen, trace, trace_ops)
    # np.savez( 'traces.npz', x=traces, y=parameters )
    # totals = [ traces, parameters ]
    # np.save( 'traces', totals, allow_pickle=True )
    # np.save( 'trace_single', trace, allow_pickle=True )
    # np.savez( 'trace_single.npz', x=trace, y=parameters, dtype=object )
    #name = 'trace_single_{a}'.format( a='_'.join( today.strftime("%c").split(' ') ) )
    #np.savez_compressed( name + '.npz', x=trace, y=trace_ops, dtype=object )
    # np.save( 'parameters_' + name, parameters, allow_pickle=True )
    np.save(os.path.join(Z_PATH, CONT+'.Zs_' + name), Zs, allow_pickle=True)
    np.save(os.path.join(K_PATH, CONT+'.Ks_' + name), keys, allow_pickle=True)
    print("keys: ", len(keys))
    print("Zs: ", len(Zs))
    print("traces: ", len(traces))
    print('Done')