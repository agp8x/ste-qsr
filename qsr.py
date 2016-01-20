#!/usr/bin/env python3
import heapq
from subprocess import Popen, PIPE
from random import random
from time import time
from io import StringIO


# beginning of an implementation of computing with relations


class Calculus:
    # we implement relations over domain {d1, d2, ..., dn} as bit vectors of length n,
    # which are just integers (current versions of Python except Integers of arbitrary length)
    # union and intersection can be realized as bitwise logic operations,
    # for complement we also need to store the universal relation 2**n - 1 (done in variable u)

    n_rels = 0  # number of base relations
    u = 1  # universal relation: 2^n_rels - 1
    baserels = []  # 1D array (sequence) of base relation symbols, e.g., baserels = ['<', '=', '>']
    converseTab = []  # 1D array (sequence) of mappings relation index -> code of relation
    compositionTab = [
        []]  # 2D array of mappings base relation index * base relation index -> code of relation resulting from composition

    def __init__(self, filename):
        f = open(filename, 'r')

        # read first line of specification file which contains base relations separated by spaces
        self.baserels = f.readline().strip().lower().split()
        self.n_rels = len(self.baserels)
        self.u = (2 ** self.n_rels) - 1
        print('reading calculus with ' + str(self.n_rels) + ' base relations: ' + str(self.baserels) + '...')

        # read converse operation and check for chapter label 'converse'
        if (f.readline().strip() != 'converse'):
            raise Exception('syntax error, was expecting "converse" on line before:\n', f.readline())
        self.converseTab = [0 for i in range(0, self.n_rels)]  # allocate 1D array of size n_rels
        # parse in all n_rels entries of format 'base relation' 'converse of the base relation'
        for i in range(0, self.n_rels):
            entry = f.readline().strip().split()
            r1 = self.baserel_idx(entry[0])
            r2 = self.code_rel(entry[1])
            print(str(entry) + ' -> converse[' + str(r1) + '] = ' + str(r2))
            self.converseTab[r1] = r2

        # read composition operation and check for chapter label 'composition'
        if (f.readline().strip() != 'composition'):
            raise Exception('syntax error, was expecting "composition" on line before:\n', f.readline())
        self.compositionTab = [[0 for i in range(0, self.n_rels)] for j in
                               range(0, self.n_rels)]  # allocate 2D array of size n_rels X n_rels
        for i in range(0, self.n_rels * self.n_rels):
            entry = f.readline().strip().split()  # entry needs to be of type 'base_relation' 'base_relation' 'base_relation,base_relation,...'
            r1 = self.baserel_idx(entry[0])
            r2 = self.baserel_idx(entry[1])
            rc = self.code_rel(entry[2])
            self.compositionTab[r1][r2] = rc
            # print str(entry) + ' -> composition[' + str(r1) + '][' + str(r2) + '] = ' + str(rc)

        print('done parsing\n')
        f.close()

    # returns the index number of a base relation given as string, used for lookup in converseTab and compositionTab
    def baserel_idx(self, str):
        return self.baserels.index(str.strip().lower())

    # codes a composition relation (notation without white space: b1,b2,b3) as binary value
    def code_rel(self, str):
        if (str.strip() == '0'):  # accept 0 as empty relation
            return 0
        else:
            r = 0
            for name in (str.strip().split(',')):
                if (name != ''):
                    r = r | (2 ** self.baserel_idx(name))
            return r

    # decodes a relation given as binary value as string
    def decode_rel(self, r):
        if (r == 0):
            return '0'
        str = ''
        for i in range(0, self.n_rels):
            if ((r & 2 ** i) != 0):
                str += self.baserels[i]
                if (r >= 2 ** (i + 1)):  # more to come?
                    str += ','
        return str

    # computes the converse of a relation r coded as binary
    def converse(self, r):
        rc = 0
        for i in range(0, self.n_rels):
            if (r & 2 ** i):
                rc = rc | self.converseTab[i]
        return rc

    # computes the composition of relations r1,r2 coded as binary value
    def composition(self, r1, r2):
        rc = 0
        for i in range(0, self.n_rels):
            if (r1 & 2 ** i):
                for j in range(0, self.n_rels):
                    if (r2 & 2 ** j):
                        rc = rc | self.compositionTab[i][j]
        return rc

    # operations of a Boolean set algebra (self-explanatory)
    def empty_rel(self):
        return 0

    def universal_rel(self):
        return self.u

    def unite_rels(self, r1, r2):
        return r1 | r2

    def intersect_rels(self, r1, r2):
        return r1 & r2

    def complement_rel(self, r):
        return self.u ^ r

    def is_empty_rel(self, r):
        return r == 0

    def is_universal_rel(self, r):
        return r == self.u


class CSP:
    matrix = None
    n = 0
    c = None

    def __init__(self, c, filename):
        if type(filename) is StringIO:
            f = filename
        else:
            f = open(filename, 'r')
        self.c = c
        n = 1 + int(f.readline().split('#')[0])  # Anzahl Variablen
        self.n = n
        u = c.universal_rel()
        row = [u for i in range(n)]
        self.matrix = [row for i in range(n)]
        reading = True
        while reading:
            l = f.readline().strip()
            if (l == '.'):
                reading = False
            else:
                entry = l.split()
                print(entry)
                self.matrix[int(entry[0])][int(entry[1])] = self.c.code_rel(entry[2])
                self.matrix[int(entry[1])][int(entry[0])] = self.c.converse(self.c.code_rel(entry[2]))
        f.close()

    def __str__(self):
        out = "CSP with " + str(self.n) + " vars:\n"
        for i in range(self.n):
            for j in range(i):
                out += str(i) + "," + str(j) + " : " + self.c.decode_rel(self.matrix[i][j])
        return out

    def dot_src(self):
        dot = 'digraph {\n'
        for i in range(self.n):
            for j in range(i):
                dot += str(i) + "->" + str(j) + "[label=\"" + self.c.decode_rel(self.matrix[i][j]) + "\"]\n"
        dot += '}\n'
        return dot

    def dot(self, filename):
        out = open(filename, 'w')
        out.write(self.dot_src())
        out.close()

    def render(self, filename, dottype='png'):
        with open(filename + '.' + dottype, 'w+b') as out:
            p = Popen(["dot -T" + dottype], shell=True, stdin=PIPE, stdout=out)
            p.communicate(self.dot_src().encode())

    def refinement(self, i, j, k):
        if type(self.matrix[i][j]) == str:
            self.matrix[i][j] = self.c.code_rel(self.matrix[i][j])
        if type(self.matrix[i][k]) == str:
            self.matrix[i][k] = self.c.code_rel(self.matrix[i][k])
        if type(self.matrix[k][j]) == str:
            self.matrix[k][j] = self.c.code_rel(self.matrix[k][j])
        old_r = self.matrix[i][j]
        new_r = self.c.intersect_rels(self.matrix[i][j], self.c.composition(self.matrix[i][k], self.matrix[k][j]))
        self.matrix[i][j] = new_r
        return (old_r != new_r)

    def aclosure10(self):
        looping = True
        while looping:
            looping = False
            for i in range(self.n):
                for j in range(self.n):
                    for k in range(self.n):
                        looping |= self.refinement(i, j, k)

    def aclosure15(self):
        q = [(i, j) for i in range(self.n) for j in range(self.n)]
        heapq.heapify(q)

        while q:
            (i, j) = heapq.heappop(q)
            for k in range(self.n):
                if (self.refinement(i, k, j)):
                    if ((i, k) not in q):
                        heapq.heappush(q, (i, k))
                if (self.refinement(k, j, i)):
                    if ((k, j) not in q):
                        heapq.heappush(q, (k, j))

    def isConsistent(self):
        pass

    # asg08: aclosure15 already has ENQUEQE_NEW implemented and therefore is already aclosure20

    # asg09
    def aclosure20(self, heuristic=True):
        self.aclosure15()

    def refinementSearch10(self) -> bool:
        self.aclosure20()
        consistent = True
        for i in range(self.n):
            for j in range(self.n):
                r = self.matrix[i][j]
                if self.c.is_empty_rel(r):
                    return False
                if bin(r).count("1") == 1:
                    consistent = consistent and True
                else:
                    refined_consistency = False
                    for b in self.c.baserels:
                        old_matrix = self.matrix
                        self.matrix[i][j] = b
                        if self.refinementSearch10():
                            refined_consistency = True
                        else:
                            # TODO: is this really needed?
                            # self.matrix = old_matrix
                            pass
                    consistent = consistent and refined_consistency
            return consistent and self.n > 1


def randomQCSP(n, d, l, c, filename=None):
    if filename is None:
        filename = "data/random_generated.csp"
    with open(filename, "w") as out:
        out.write("{}\n".format(n))
        for i in range(1, n):
            for j in range(d):
                j = int(random() * n)
                rel = c.empty_rel()
                while rel == c.empty_rel():
                    rel = int(random() * len(c.baserels))
                for x in range(int(random() * l)):
                    rel = c.unite_rels(rel, int(random() * len(c.baserels)))
                out.write("{} {} {}\n".format(i, j, c.decode_rel(rel)))
        out.write(".\n")


def benchmark(calculus, resultfile, range_n=range(10, 100, 10), d=6, l=6.5):
    with open(resultfile, 'w') as out:
        for n in range_n:
            print("start {}...".format(n))
            name = "data/bench{}.qcsp".format(n)
            randomQCSP(n, d, l, calculus, name)
            result = benchmark_aclosure(calculus, name, n, d, l)
            print(result)
            out.write(result + "\n")
            out.flush()


def benchmark_aclosure(calc, filename, n, d, l) -> str:
    csp = CSP(calc, filename)
    start = time()
    csp.aclosure20()
    duration = time() - start
    return "{},{},{},{}".format(n, duration, d, l)


def batch_load(calculus, filename) -> [CSP]:
    csps = []
    with open(filename) as input:
        lines = []
    for line in input:
        lines.append(line)
        if line.strip() == '.':
            csps.append(CSP(calculus, StringIO("".join(lines))))
            lines = []
    return csps


# testing
"""
print('testing with point calculus\n')
pc = Calculus('data/pc.txt')
print('converse of <,= is =,>: ' + pc.decode_rel(pc.converse(pc.code_rel('<,='))))
print('converse of empty relation is empty relation: ' + pc.decode_rel(pc.converse(pc.code_rel(''))))
print('composition of < and < is <: ' + pc.decode_rel(pc.composition(pc.code_rel('<'), pc.code_rel('<'))))
print('composition of < and <,= is <: ' + pc.decode_rel(pc.composition(pc.code_rel('<'), pc.code_rel('<,='))))
print('composition of < and > is <,=,>: ' + pc.decode_rel(pc.composition(pc.code_rel('<'), pc.code_rel('>'))))

csp1 = CSP(pc, 'data/linear.csp')
csp1.render("linear0")
csp1.aclosure15()
print(csp1)
csp1.render("linear")
print(csp1)
print("consistent:", csp1.refinementSearch10())
csp1.render("linear2")
print(csp1)
randomQCSP(4, 2, 4, pc)
csp2=CSP(pc, "data/random_generated.csp")
print(csp1.matrix)
print(csp2.matrix)
csp2.render("foo")
print(csp2)
print("consistend:",csp2.refinementSearch10())
csp2.render("foo2")
print(csp2)"""

# pc=Calculus("data/allen.txt")
# benchmark(pc,'test_allen',range(10,200,10))

rcc = Calculus("data/rcc8.txt")
csp = CSP(rcc, "data/scale_free_rcc.qcsp")
print("rendering...")
csp.render("rcc")
print("benchmarking...")
print(benchmark_aclosure(rcc, "data/scale_free_rcc.qcsp",0,0,0))
