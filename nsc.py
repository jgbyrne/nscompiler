from enum import Enum
import sys

sys.stderr = sys.stdout

def err_fatal(lno, msg):
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
        def chunk(rval, lno, msg, also=""):
            items = rval.strip().split(" ")
            for item in items:
                for c in item:
                    if c.isalnum():
                        continue
                    if c == '_':
                        continue
                    if c not in also:
                        err_fatal(lno, msg.format(item))
            return items


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

                    if lval in seen:
                        err_fatal(lno, "Duplicate label name")

                    seen.add(lval)
                    if lval == "variables":
                        man.vars = (lno, chunk(rval, lno, "'{}' is not a valid variable name"))
                    elif lval == "constants":
                        man.consts = (lno, chunk(rval, lno, "'{}' is not a valid variable name"))
                    elif lval == "predicates":
                        preds = {}
                        for spec in rval.strip().split(" "):
                            pname = None
                            bptr = -1
                            for i, c in enumerate(spec):
                                if pname is not None and bptr == -1:
                                    if c == ']':
                                        err_fatal(lno, "Predicate definition '{}' has no arity specified".format(pname))
                                    bptr = i
                                if c == '[':
                                    pname = spec[:i]
                                    if not all(c.isalnum() or c == "_" for c in pname):
                                        err_fatal(lno, "'{}' is not a valid predicate name".format(pname))
                            if c != ']':
                                err_fatal(lno, "Predicate definition did not conclude with ']'")
                            if bptr != -1:
                                try:
                                    preds[pname] = int(spec[bptr:-1])
                                    if preds[pname] < 0:
                                        err_fatal(lno, "Predicate definition arity is not positive")
                                except ValueError:
                                    err_fatal(lno, "Predicate definition arity is not an integer")
                        man.preds = (lno, preds)
                    elif lval == "equality":
                        eq = rval.strip()
                        if not all(c.isalnum() or c in "_=\\" for c in eq):
                            err_fatal(lno, "'{}' is not a valid equality symbol".format(eq))
                        man.eq = (lno, rval.strip())
                    elif lval == "connectives":
                        man.conns = (lno, chunk(rval, lno, "'{}' is not a valid connective name", also="\\"))
                    elif lval == "quantifiers":
                        man.quants = (lno, chunk(rval, lno, "'{}' is not a valid quantifier name", also="\\"))
                    elif lval == "formula":
                        man.formula = [lno, -1, rval]
                        exp_form = True
                    else:
                        err_fatal(lno, "Unrecognised label name")
                elif exp_form:
                    man.formula[2] += line
                else:
                    err_fatal(lno, "Unrecognised input syntax")
        if exp_form:
            man.formula[1] = lno
        if seen != expect:
            err_fatal(0, "Did not see expected label set")
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
    def __init__(self, t, v, lptr, rptr):
        self.t = t
        self.v = v
        self.lptr = lptr
        self.rptr = rptr

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
                elif c.isalnum() or c == '_' or c == '\\' or c == '=':
                    rptr += 1
                    continue
                else:
                    err_fatal(0, "'{}' is not a valid character in any identifier".format(c))

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
                else:
                    err_fatal(0, "No such identifier ''".format(v))
                self.toks.append(Token(t, v, lptr, rptr-1))
                lptr = rptr

            if sym_t is not None:
                self.toks.append(Token(sym_t, source[rptr], rptr, rptr))
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
    name = psr.tok().v
    args = psr.tkr.man.preds[1][name]

    if not psr.next(): psr.err_fatal(psr.tok(), "Unexpected end of formula after predicate name")
    if psr.tok().t != Symbol.LPAREN: psr.err_fatal(psr.tok(), "Expected left parenthesis, found '{}'".format(psr.tok().v))
    if not psr.next(): psr.err_fatal(psr.tok(), "Unexpected end of formula instead of predicate arguments")

    for i in range(args):
        if psr.tok().t != Name.VAR:
            psr.err_fatal(psr.tok(), "Expected variable, found '{}'".format(psr.tok().v))
        tree.add_node(parent, psr.tok())
        if not psr.next():
            psr.err_fatal(psr.tok(), "Unexpected end of formula within predicate arguments")
        if i+1 == args:
            if psr.tok().t != Symbol.RPAREN:
                psr.err_fatal(psr.tok(), "Expected right parenthesis ({} has {} args), found '{}'".format(name, args, psr.tok().v))
        else:
            if psr.tok().t != Symbol.COMMA:
                psr.err_fatal(psr.tok(), "Expected comma ({} has {} args), found '{}'".format(name, args, psr.tok().v))
            if not psr.next():
                psr.err_fatal(psr.tok(), "Unexpected end of formula within predicate arguments")


def parse_equality(psr, tree, parent):
    if psr.tok().t == Name.VAR or psr.tok().t == Name.CONST:
        tree.add_node(parent, psr.tok())
    else:
        psr.err_fatal(psr.tok(), "Expected variable or constant, found '{}'".format(psr.tok().v))

    if not psr.next():
        psr.err_fatal(psr.tok(), "Unexpected end of formula while parsing equality expression")

    if type(psr.tok().t) != Equality:
        psr.err_fatal(psr.tok(), "Expected equality operator, found '{}'".format(psr.tok().v))

    if not psr.next():
        psr.err_fatal(psr.tok(), "Unexpected end of formula while parsing equality expression")

    if psr.tok().t == Name.VAR or psr.tok().t == Name.CONST:
        tree.add_node(parent, psr.tok())
    else:
        psr.err_fatal(psr.tok(), "Expected variable or constant, found '{}'".format(psr.tok().v))

def parse_binary(psr, tree, parent):
    parse_formula(psr, tree, parent)
    if not psr.next():
        psr.err_fatal(psr.tok(), "Unexpected end of formula while parsing binary expression")
    if psr.tok().t in {Connective.AND, Connective.OR, Connective.IMPL, Connective.IFF}:
        tree.add_node(parent, psr.tok())
    else:
        psr.err_fatal(psr.tok(), "Expected binary connective, found '{}'".format(psr.tok().v))
    if not psr.next():
        psr.err_fatal(psr.tok(), "Unexpected end of formula while parsing binary expression")
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
                psr.err_fatal(psr.tok(), "Expected ')', found '{}'".format(rparen.v))
        else:
            psr.err_fatal(psr.tok(), "Unexpected end of formula while looking for closing parenthesis")
    else:
        psr.err_fatal(psr.tok(), "Unexpected end of formula while beginning to parse expression")

def parse_quantify(psr, tree, parent):
    # assuming first tok is quant
    tree.add_node(parent, psr.tok())
    if psr.next():
        if psr.tok().t != Name.VAR:
            psr.err_fatal(psr.tok(), "Expected variable, found '{}'".format(psr.tok().v))
        tree.add_node(parent, psr.tok())
        if not psr.next():
            psr.err_fatal(psr.tok(), "Unexpected end of formula while parsing quantifier")
        parse_formula(psr, tree, parent)
    else:
        psr.err_fatal(psr.tok(), "Unexpected end of formula while parsing quantifier")


def parse_negation(psr, tree, parent):
    # assuming first tok is negation
    if psr.next():
        parse_formula(psr, tree, parent)
    else:
        psr.err_fatal(psr.tok(), "Unexpected end of formula while parsing negation")

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
    else:
        psr.err_fatal(tok, "Expected formula, found '{}'".format(tok.v))

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

    def err_fatal(self, tok, msg):
        print("Error: {}".format(msg), file=sys.stderr)
        if tok:
            source = self.tkr.man.formula[2]
            lbuf = tok.lptr
            rbuf = 20
            prefix = "   | "
            if tok.lptr > 20:
                lbuf = 20
                prefix = ".... "
            print(prefix + source[tok.lptr - lbuf : tok.rptr + rbuf].rstrip())
            print(" " * (5 + lbuf) + "^" * (tok.rptr - tok.lptr + 1))
        sys.exit(1)

    def tok(self):
        return self.tkr.toks[self.tptr]

    def next(self):
        if self.tptr+1 < len(self.tkr.toks):
            self.tptr += 1
            return True
        else:
            return False

    def parse(self):
        tree = Tree()
        parse_formula(self, tree, 0)
        if self.next():
            self.err_fatal(self.tok(), "Finished parsing but did not reach end of formula")
        return tree

if __name__ == "__main__":
    if len(sys.argv) < 2:
        err_fatal(0, "Need a filepath argument")
    path = sys.argv[1]
    man = Manifest.from_file(path)
    tkr = Tokeniser(man)
    tkr.tokenise()
    psr = Parser(tkr)
    tree = psr.parse()
    print("Parsed Successfully")

