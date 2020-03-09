from enum import Enum
import sys

def error(lno, msg):
    if not lno:
        print("Error: {}".format(msg), file=sys.stderr)
    else:
        print("Error (line {}): {}".format(lno, msg), file=sys.stderr)
    sys.exit(1)

class Manifest:
    def __init__(self, job):
        self.job = job
        self.vars    = (-1, [])
        self.consts  = (-1, [])
        self.preds   = (-1, {})
        self.eq      = (-1, "")
        self.conns   = (-1, [])
        self.quants  = (-1, [])
        self.formula = [-1, -1, ""]

    def __str__(self):
        out = "Manifest for {}\n".format(self.job)
        out += "-> vars L{}: {}\n".format(*self.vars)
        out += "-> consts L{}: {}\n".format(*self.consts)
        out += "-> preds L{}: {}\n".format(*self.preds)
        out += "-> eq L{}: {}\n".format(*self.eq)
        out += "-> conns L{}: {}\n".format(*self.conns)
        out += "-> quants L{}: {}\n".format(*self.quants)
        out += "-> formula L{}-{}: {}\n".format(*self.formula)
        return out

    @classmethod
    def from_file(cls, path):
        def chunk(rval):
            return rval.strip().split(" ")

        man = cls(path)
        expect = {"variables", "constants", "predicates", "equality",
                  "connectives", "quantifiers", "formula"}
        seen = set()
        with open(path) as inf:
            exp_form = False
            for lind, line in enumerate(inf):
                lno = lind + 1
                parts = line.split(":", 1)
                if len(parts) != 1:
                    if exp_form:
                        man.formula[1] = lno-1
                    exp_form = False
                    lval, rval = parts
                    seen.add(lval)
                    if lval == "variables":
                        man.vars = (lno, chunk(rval))
                    elif lval == "constants":
                        man.consts = (lno, chunk(rval))
                    elif lval == "predicates":
                        preds = {}
                        for spec in chunk(rval):
                            pname = None
                            bptr = -1
                            for i, c in enumerate(spec):
                                if pname is not None and bptr == -1:
                                    if c == ']':
                                        pass # err
                                    bptr = i
                                if c == '[':
                                    pname = spec[:i]
                            if c != ']':
                                pass # err
                            if bptr != -1:
                                try:
                                    preds[pname] = int(spec[bptr:-1])
                                except IndexError:
                                    pass # err
                        man.preds = (lno, preds)
                    elif lval == "equality":
                        man.eq = (lno, rval.strip())
                    elif lval == "connectives":
                        man.conns = (lno, chunk(rval))
                    elif lval == "quantifiers":
                        man.quants = (lno, chunk(rval))
                    elif lval == "formula":
                        man.formula = [lno, -1, rval]
                        exp_form = True
                    else:
                        error(lno, "Unrecognised label name")
                elif exp_form:
                    man.formula[2] += line
                else:
                    error(lno, "Unrecognised input syntax")
        if exp_form:
            man.formula[1] = lno
        if seen != expect:
            error(0, "Did not see expected label set")
        return man

class Connective(Enum):
    AND  = 0
    OR   = 1
    IMPL = 2
    IFF  = 3
    NEG  = 4

class Quantifier(Enum):
    EXISTS = 0
    FORALL = 1

class Name(Enum):
    VAR   = 1
    CONST = 2
    PRED  = 3

class Symbol(Enum):
    COMMA  = 1
    LPAREN = 2
    RPAREN = 3

class Equality:
    def __str__(self):
        return "Equality"

class Token:
    def __init__(self, t, v):
        self.t = t
        self.v = v

    def __str__(self):
        return "[{}: {}]".format(self.t, self.v)

class Tokeniser:
    def __init__(self, man):
        self.man = man
        self.toks = []

    def tokenise(self):
        lptr = 0
        rptr = 0
        source = self.man.formula[2]
        eof = False
        while not eof:
            sym_t = None
            while True:
                if rptr >= len(source):
                    eof = True
                    break

                c = source[rptr]

                if c.isspace():
                    if rptr != lptr:
                        break
                    else:
                        lptr += 1
                        rptr += 1
                        continue
                elif c == ',':
                    sym_t = Symbol.COMMA
                    break
                elif c == '(':
                    sym_t = Symbol.LPAREN
                    break
                elif c == ')':
                    sym_t = Symbol.RPAREN
                    break
                elif c.isalnum or c == '_' or c == '\\' or c == '=':
                    rptr += 1
                    continue
                # ERR

            if lptr != rptr:
                v = source[lptr:rptr]
                if v in self.man.vars[1]:
                    t = Name.VAR
                elif v in self.man.consts[1]:
                    t = Name.CONST
                elif v in self.man.preds[1]:
                    t = Name.PRED
                elif v == self.man.eq[1]:
                    t = Equality()
                elif v in self.man.conns[1]:
                    t = Connective(self.man.conns[1].index(v))
                elif v in self.man.quants[1]:
                    t = Quantifier(self.man.quants[1].index(v))
                self.toks.append(Token(t, v))
                lptr = rptr

            if sym_t is not None:
                self.toks.append(Token(sym_t, source[rptr]))
                lptr = rptr = rptr + 1
                sym_t = None

    def __str__(self):
        s = ""
        for i, t in enumerate(self.toks):
            s += "{} = {}\n".format(i, t)
        return s

class Rule(Enum):
    PARENS    = 1
    EQUALITY  = 2
    BINARY    = 3
    NEGATION  = 4
    QUANTIFY  = 5
    PREDICATE = 6

def parse_predicate(psr, tree, parent):
    # assume first tok predicate name
    tree.add_node(parent, psr.tok())
    args = psr.tkr.man.preds[1][psr.tok().v]

    if not psr.next(): pass #err
    if psr.tok().t != Symbol.LPAREN: pass #err
    if not psr.next(): pass #err

    for i in range(args):
        if psr.tok().t != Name.VAR:
            pass #err
        tree.add_node(parent, psr.tok())
        if not psr.next():
            pass #err
        if i+1 == args:
            if psr.tok().t != Symbol.RPAREN:
                pass #err
        else:
            if psr.tok().t != Symbol.COMMA:
                pass #err
            if not psr.next():
                pass #err


def parse_equality(psr, tree, parent):
    if psr.tok().t == Name.VAR or psr.tok().t == Name.CONST:
        tree.add_node(parent, psr.tok())
    else:
        pass #err

    if not psr.next():
        pass #err

    if type(psr.tok().t) != Equality:
        pass #err

    if not psr.next():
        pass #err

    if psr.tok().t == Name.VAR or psr.tok().t == Name.CONST:
        tree.add_node(parent, psr.tok())
    else:
        pass #err

def parse_binary(psr, tree, parent):
    parse_formula(psr, tree, parent)
    if not psr.next():
        pass #err
    if psr.tok().t in {Connective.AND, Connective.OR, Connective.IMPL, Connective.IFF}:
        tree.add_node(parent, psr.tok())
    else:
        pass #err
    if not psr.next():
        pass #err
    parse_formula(psr, tree, parent)

def parse_parens(psr, tree, parent):
    if psr.next():
        lval = psr.tok()
        if lval.t == Name.VAR or lval.t == Name.CONST:
            equality = tree.add_node(parent, Rule.EQUALITY)
            parse_equality(psr, tree, equality)
        else:
            binary = tree.add_node(parent, Rule.BINARY)
            parse_binary(psr, tree, binary)
        if psr.next():
            rparen = psr.tok()
            if rparen.t != Symbol.RPAREN:
                pass #err
    else:
        pass #err

def parse_quantify(psr, tree, parent):
    # assuming first tok is quant
    tree.add_node(parent, psr.tok())
    if psr.next():
        if psr.tok().t != Name.VAR:
            pass #err
        tree.add_node(parent, psr.tok())
        if not psr.next():
            pass #err
        parse_formula(psr, tree, parent)
    else:
        pass #err


def parse_negation(psr, tree, parent):
    # assuming first tok is negation
    if psr.next():
        parse_formula(psr, tree, parent)
    else:
        pass #err

def parse_formula(psr, tree, parent):
    tok = psr.tok()
    if tok.t == Connective.NEG:
        negation = tree.add_node(parent, Rule.NEGATION)
        parse_negation(psr, tree, negation)
    elif type(tok.t) == Quantifier:
        quantify = tree.add_node(parent, Rule.QUANTIFY)
        parse_quantify(psr, tree, quantify)
    elif tok.t == Symbol.LPAREN:
        parens = tree.add_node(parent, Rule.PARENS)
        parse_parens(psr, tree, parens)
    elif tok.t == Name.PRED:
        predicate = tree.add_node(parent, Rule.PREDICATE)
        parse_predicate(psr, tree, predicate)

class Node:
    def __init__(self, nid, nval, parent):
        self.nid = nid
        self.nval = nval
        self.parent = parent
        self.children = []

class Tree:
    def __init__(self):
        self.nodes = [Node(0, None, 0)]

    def add_node(self, parent, nval):
        nid = len(self.nodes)
        self.nodes.append(Node(nid, nval, parent))
        self.nodes[parent].children.append(nid)
        return nid

    def _cat_node(self, nid, depth):
        s = "{} ({}) {}\n".format("  "*depth, nid, self.nodes[nid].nval)
        for cnid in self.nodes[nid].children:
            s += self._cat_node(cnid, depth+1)
        return s

    def __str__(self):
        return self._cat_node(0, 0)


class Parser:
    def __init__(self, tokeniser):
        self.tkr = tokeniser
        self.tptr = 0

    def tok(self):
        return self.tkr.toks[self.tptr]

    def peek(self):
        return self.tkr.toks[self.tptr+1]

    def next(self):
        self.tptr += 1
        if self.tptr < len(self.tkr.toks):
            return True
        else:
            return false

    def parse(self):
        tree = Tree()
        parse_formula(self, tree, 0)
        return tree

if __name__ == "__main__":
    if len(sys.argv) < 2:
        error(0, "Need a filepath argument")
    path = sys.argv[1]
    man = Manifest.from_file(path)
    tkr = Tokeniser(man)
    tkr.tokenise()
    psr = Parser(tkr)
    tree = psr.parse()
    print(tree)

