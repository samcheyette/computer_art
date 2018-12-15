
from LOTlib.Primitives import primitive
from LOTlib.Miscellaneous import Infinity
from LOTlib.Grammar import Grammar
from collections import defaultdict

from LOTlib.Miscellaneous import attrmem
from LOTlib.Hypotheses.LOTHypothesis import LOTHypothesis
from LOTlib.Hypotheses.Likelihoods.BinaryLikelihood import BinaryLikelihood

from LOTlib.Miscellaneous import Infinity, beta, attrmem
from LOTlib.FunctionNode import FunctionNode

from math import log, exp
import numpy as np
import random
import itertools as it
import string


##########################################################################################


MAX = 15
INF = 30
let_to_dig={}
dig_to_let={}
alph=string.ascii_uppercase
highest = "E"


for i in xrange(len(alph)):
    let_to_dig[alph[i]] = i
    dig_to_let[i] = alph[i]



@primitive
def repeat(x, n=INF):
    if len(x) >= INF or len(x) < 1:
        return x
    else:
        i = 0
        out = ""
        while len(out) < INF and i < n:
            out += x
            i += 1
        return out[:INF]



@primitive
def append(x1, x2):
    return((x1 + x2)[:INF])


@primitive
def invert(x):
    inv = ""
    for i in x:
        if i == "A":
            inv += "B"
        elif i == "B":
            inv += "A"
        else:
            inv += str(int(10 - float(i)))
    return inv

@primitive
def delete(s1, n):
    if (len(s1) >= INF and (n == INF)) or (len(s1) <= n):
        return s1
    else:
        return s1[:n]


@primitive
def cut(x, lower, upper):
    if upper <= lower:
        return ""
    elif ((len(x) == INF) and (upper == INF)):
        return x
    else:
        return x[lower:upper]


@primitive
def upto(x,  upper):

    if ((len(x) == INF) and (upper == INF)):
        return x
    else:
        return x[0:upper]


@primitive
def after(x,  lower):

    if ((len(x) == INF) and (lower == 0)):
        return x
    else:
        return x[lower:INF]


@primitive
def weave(x, y):
    if len(x) == 0:
        return y
    elif len(y) == 0:
        return x
    else:
        out = ""
        ind = 0
        while ((ind < min(len(x), len(y))) and 
                    (len(out) < INF)):
            out += x[ind] + y[ind]
            ind += 1

        if len(out) >= INF:
            return out
        else:
            out += (x[ind:] + y[ind:])[:INF]    
            return out

@primitive
def n_times(x, y):
    return repeat(x,y)

@primitive
def alternate(x, y):
    return repeat(x+y)



#@primitive
#def flip():
    #return str(np.random.binomial(1, n/float(MAX)))
   # return  random.randint(0,1) == 1


@primitive
def rand_n(lower, upper):
    #return str(np.random.binomial(1, n/float(MAX)))
    return  random.randint(lower, upper)


@primitive
def max_rand(n):
    return str(np.random.binomial(INF, n/float(MAX)))

@primitive
def increment(x,y):
    out = ""
    add = ""
    if len(x) == 0 and len(y) == 0:
        return x

    while len(out) < MAX:
        add += y
        out += x + add
    return out[:MAX]

    
@primitive
def expand(x):
    out = ""
    last = ""
    for i in x:
        if i == last:
            out += i
        else:
            out += i*2
        last = i
    return out[:MAX]


@primitive
def mirror(x):
    return  x[::-1]

@primitive
def next_dig(x, highest="Z"):
    out=""
    for l in x: 
        dig = let_to_dig[l]+1
        dig = dig % (let_to_dig[highest]+1)
        out += dig_to_let[dig]
    return out
    


@primitive
def prev_dig(x, highest=highest):
    out=""
    for l in x: 
        dig = let_to_dig[l]-1
        dig = dig % (let_to_dig[highest])
        out += dig_to_let[dig]
    return out
    



@primitive
def index(x, i):
    if len(x) == 0:
        return x 
    return x[max(0, min(i, len(x)-1))]


@primitive
def length(a):
    return len(a)

@primitive
def eq(a,b):
    return a==b

@primitive
def gt(a,b):
    return a>b

@primitive
def or_(a,b):
    return (a | b)

@primitive
def and_(a,b):
    return (a & b)


@primitive
def if_else(tf, a, b):
    if tf: 
        return a
    else:
        return b



@primitive
def plus(a,b):
    return a+b



@primitive
def minus(a,b):
    return a-b


@primitive
def div(a,b):
    if b == 0:
        return 0
    else:
        return a/b


@primitive
def times(a,b):

    return a*b

@primitive
def mod(a,b):
    if b == 0:
        return 0
    return a % b


@primitive
def base_case(index,a,b,c):
    if index == 1:
        return a
    elif index == 2:
        return b
    else:
        return c





##########################################################################################


def get_rule_counts(grammar, t, add_counts ={}):
    """
            A list of vectors of counts of how often each nonterminal is expanded each way

            TODO: This is probably not super fast since we use a hash over rule ids, but
                    it is simple!
    """

    counts = defaultdict(int) # a count for each hash type

    for x in t:
        if type(x) != FunctionNode:
            raise NotImplementedError("Rational rules not implemented for bound variables")
        
        counts[x.get_rule_signature()] += 1 


    for k in add_counts:
        counts[k] += add_counts[k]

    # and convert into a list of vectors (with the right zero counts)
    out = []
    for nt in grammar.rules.keys():
        v = np.array([ counts.get(r.get_rule_signature(),0) for r in grammar.rules[nt] ])
        out.append(v)
    return out




def get_rule_key(grammar):
    rule_keys = []
    for z in grammar: 
        #print z.get_rule_signature()
        rs_orig = z.get_rule_signature()
        name = rs_orig[1].replace("'", "")
        name = name.replace("(", "")
        name = name.replace(")", "")
        name = name.replace(",","")
        name = name.replace("%s", "")
        name = name.replace(" ", "")

        rs = (rs_orig[0], name)

        rule_keys.append(rs)
    return rule_keys



##########################################################################################

def all_poss_upto(n, seqs = [""], max_len=0):
    if max_len == n:
        return seqs
    else:
        add_seqs = []
        for seq in seqs:
            if len(seq) == max_len:
                add_seqs.append(seq + "A")
                add_seqs.append(seq + "B")
        seqs = seqs + add_seqs
        return all_poss_upto(n, seqs, max_len+1)
    return -1



def output1(lst,out_f):
    o = "seq,p_B,p_Random\n"
    for l in lst:
        o += "%s,%f,%f\n" % l

    f = open(out_f, "w+")
    f.write(o)
    f.close()


def output2(lst, out_f):
    o = "seq,h_count,hyp_out,out_at_len,gr_type,gr_name,gr_typename,count_h,posterior,prior,likelihood,out\n"
    #o = ""
    for l in lst:
        o += ",".join(list(l)) + "\n"

    f = open(out_f, "w+")
    f.write(o)
    f.close()

def levenshtein(seq1, seq2):
    oneago = None
    thisrow = range(1, len(seq2) + 1) + [0]
    for x in xrange(len(seq1)):
        twoago, oneago, thisrow = oneago, thisrow, [0] * len(seq2) + [x + 1]
        for y in xrange(len(seq2)):
            delcost = oneago[y] + 1
            addcost = thisrow[y - 1] + 1
            subcost = oneago[y - 1] + (seq1[x] != seq2[y])
            thisrow[y] = min(delcost, addcost, subcost)
    return thisrow[len(seq2) - 1]



