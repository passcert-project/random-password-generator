
import random # obs: not secure! for test prupose only


# OBS: there is also a problem with rejection sampling with secret ranges
#  a solution might be to always sampling from the LCM of possible ranges: 1061260200



s_u = 26 # uppercase
s_l = 26 # lowercase
s_d = 10 # digits
s_s = 14 # special
charLUT = [ 65+x for x in range(s_u) ]
charLUT += [ 97+x for x in range(s_l) ]
charLUT += [ 48+x for x in range(10) ]
charLUT += [ 33, 35, 36, 37, 38, 42, 43, 45, 58, 59, 61, 63, 64, 95 ]

assert len(charLUT) == (s_u+s_l+s_d+s_s), "Wrong size `charLUT`"

def u32b(x, i):
    """ byte 'i' from 'x' """
    x >>= (8*i)
    x &= 255
    return x

def mk_u32(x0, x1, x2, x3):
    r = 0
    r += x3 & 255
    r <<= 8
    r += x2 & 255
    r <<= 8
    r += x1 & 255
    r <<= 8
    r += x0 & 255
    return r

def charLUT_lookup(cats, s):
    """ lookups a secret 's' char from the lookup table, from selected (secret) categories 'cats'
       'cats' is encoded in a 'u32' (a category per byte)"""
    c = 0     # char to be returned
    c_cat = 0 # category of c
    i = 0
    i_cat = -1
    s += 1
    decmask = 1
    while (i < len(charLUT)):
        if i == 0:
            dec = 1
            if not u32b(cats,0): dec = 0
            i_cat = 0
        if i == s_u:
            decmask <<= 8
            dec = 1
            if not u32b(cats,1): dec = 0
            i_cat = 1
        if i == s_u+s_l:
            decmask <<= 8
            dec = 1
            if not u32b(cats,2): dec = 0
            i_cat = 2
        if i == s_u+s_l+s_d:
            decmask <<= 8
            dec = 1
            if not u32b(cats,3): dec = 0
            i_cat = 3
        c_tmp = charLUT[i]
        s -= dec
        catsdec = 0
        if (s == 0):
            # print("i =", i)
            c = c_tmp
            c_cat = i_cat
            s = 255
            catsdec = decmask
        cats -= catsdec
        i += 1
    return cats, c

def rndChar(cats):
    """ 'cats' is a bitwise encoding of the intended categories
           bit 0 - uppercase
           bit 1 - lowercase
           bit 2 - digit
           bit 3 - special
        E.g. 'cats=5' would choose either an uppercase or digit. 
        Return the generated char, and corresponding category """
    print("%08x," % cats, end=' ')
    range = 0
    size = s_u
    if not u32b(cats,0): size = 0
    range += size
    size = s_l
    if not u32b(cats,1): size = 0
    range += size
    size = s_d
    if not u32b(cats,2): size = 0
    range += size
    size = s_s
    if not u32b(cats,3): size = 0
    range += size
    s = 0
    if range: s = random.randrange(range)
    cats, c = charLUT_lookup(cats, s)
    print("%08X(%d): " % (cats, range), s, "%d(%c)" % (c,c))
    return cats, c

# Policy: { 'len': int, 'mins': (min_u,min_l,min_d,min_s), 'max': (max_u,max_l,max_d,max_s) }
# Exemplo:
pol1 = {'len':12, 'mins':(1,2,3,2), 'maxs':(3,3,5,5)}
pol2 = {'len':12, 'mins':(10,2,3,4), 'maxs':(3,3,5,5)}

pw_max_len = 99 # max password size

def polSat(pol):
    """ checks if policy is satisfiable """
    v = True
    v = v and 0 < pol['len'] and pol['len'] <= pw_max_len
    v = v and len(pol['mins'])==4 and len(pol['maxs'])==4
    v = v and all([ 0 <= pol['mins'][k] and pol['mins'][k] <= pol['maxs'][k] for k in range(4)])
    v = v and sum(pol['mins']) <= pol['len']
    v = v and pol['len'] <= sum(pol['maxs'])
    return v

def genPwPol(pol):
    """ generates a random 'policy normalised' password """
    if not polSat(pol): return None
    p = []
    plen = 0
    allowed = list(pol['maxs'])
    # generate mins for each category
    for _ in range(pol['mins'][0]):
        _, c = rndChar(1)
        p.append(c)
        plen +=1
    for _ in range(pol['mins'][1]):
        _, c = rndChar(1 << 8)
        p.append(c)
        plen +=1
    for _ in range(pol['mins'][2]):
        _, c = rndChar(1 << 8*2)
        p.append(c)
        plen +=1
    for _ in range(pol['mins'][3]):
        _, c = rndChar(1 << 8*3)
        p.append(c)
        plen +=1
    # remaining chars
    cats = mk_u32(pol['maxs'][0]-pol['mins'][0],pol['maxs'][1]-pol['mins'][1],pol['maxs'][2]-pol['mins'][2],pol['maxs'][3]-pol['mins'][3])
    while (plen < pol['len']):
        cats, c = rndChar(cats)
        p.append(c)
        plen +=1
    return p


def cswap(l, pos1, pos2):
    """ constant-time swap of two elements of a vector.
        It swaps 's[pos1]' with 's[pos2]' (assumes pos1 <= pos2) """
    #print(pos1, "<->", pos2)
    c = l[pos2]
    c_new = c
    for i in range(pos2):
        c_i = l[i]
        if i==pos1:
            c_new = c_i
            c_i = c
        l[i] = c_i
    l[pos2] = c_new

def rndPerm(l):
    """ performs a random permutation (in constant-time) """
    i = len(l)
    while 0 < i:
        j = random.randrange(i)
        i -= 1
        cswap(l, j, i)
    return l


def genPw(pol):
    """ generate a random password for a given policy """
    p = genPwPol(pol)
    if p == None: return None
    rndPerm(p)
    return "".join(map(chr,p))


