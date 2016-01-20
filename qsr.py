#!/usr/bin/env python3
import heapq


# beginning of an implementation of computing with relations
import subprocess


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
        self.baserels = f.readline().strip().split()
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
        return self.baserels.index(str.strip())

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
        f = open(filename, 'r')
        self.c = c
        n = 1 + int(f.readline())  # Anzahl Variablen
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

    def dot(self, filename):
        out = open(filename, 'w')
        out.write('digraph {\n')
        for i in range(self.n):
            for j in range(i):
                out.write(str(i) + "->" + str(j) + "[label=\"" + self.c.decode_rel(self.matrix[i][j]) + "\"]\n")
        out.write('}\n')
        out.close()

    def render(self, filename):
        self.dot(filename + '.dot')
        with open(filename + '.png', 'w+b') as out:
            dot = subprocess.call(["dot", "-Tpng", filename + ".dot"], stdout=out)
           # out.write(dot.stdout)

    def refinement(self, i, j, k):
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


# testing

print('testing with point calculus\n')
pc = Calculus('data/pc.txt')
print('converse of <,= is =,>: ' + pc.decode_rel(pc.converse(pc.code_rel('<,='))))
print('converse of empty relation is empty relation: ' + pc.decode_rel(pc.converse(pc.code_rel(''))))
print('composition of < and < is <: ' + pc.decode_rel(pc.composition(pc.code_rel('<'), pc.code_rel('<'))))
print('composition of < and <,= is <: ' + pc.decode_rel(pc.composition(pc.code_rel('<'), pc.code_rel('<,='))))
print('composition of < and > is <,=,>: ' + pc.decode_rel(pc.composition(pc.code_rel('<'), pc.code_rel('>'))))

csp1 = CSP(pc, 'data/linear.csp')
csp1.aclosure15()
print(csp1)
csp1.render("linear")