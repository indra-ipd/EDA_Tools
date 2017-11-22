"""
    EDA Tools SS-17
    Implementation of a Netlist Equivalence Checker using a SAT approach.

    Authors:
        Raul Beltran B.

    ICS - TU-Chemnitz
    Python 2.7.10
"""
import sys

##
# Print controller in 4 bits:
# 0 : Full CNF
# 1 : Guessing/Heuristic vars
# 2 : CNF applied heuristics
# 3 : Empty Clause list
PRN = sys.argv[3] if len(sys.argv) == 4 else []

class MemoizeHash(object):
    """ Memoization decorator for a function taking one or more arguments. """
    def __init__(self, _fn):
        self._fn = _fn
        self.memo = {}
    def __call__(self, *args, **kwds):
        import cPickle
        str_hash = cPickle.dumps(args, 1)+cPickle.dumps(kwds, 1)
        # Search for calculated functions.
        if not self.memo.has_key(str_hash):
            self.memo[str_hash] = self._fn(*args, **kwds)

        return self.memo[str_hash]

def read_netlist(_file, _plusnet):
    """ Load the info from the files given in the arguments' script. """
    nets = int(_file.readline())
    inputs = _file.readline().split()
    inputs.sort()
    outputs = _file.readline().split()
    outputs.sort()

    # read mapping
    mapping = {}
    while True:
        line = _file.readline().strip()
        if not line:
            break

        net, name = line.split()
        # Re-enumeration of wires on second circuit.
        mapping[name] = int(net) + _plusnet

    # read gates
    gates = []
    for line in _file.readlines():
        bits = (line.split())
        gate = bits.pop(0)
        ports = map(int, bits)
        # Re-enumeration of wires on second circuit.
        ports = [p+_plusnet for p in ports]
        gates.append((gate, ports))

    return nets, inputs, outputs, mapping, gates

# read netlists
NETS_1, INPUTS_1, OUTPUTS_1, MAPPING_1, GATES_1 = read_netlist(open(sys.argv[1], "r"), 0)
NETS_2, INPUTS_2, OUTPUTS_2, MAPPING_2, GATES_2 = read_netlist(open(sys.argv[2], "r"), NETS_1)

# add your code here!
def and_f(_s):
    """ AND: (a V -c)(b V -c)(-a V -b V c) """
    expr1 = "( %d V -%d )" % (_s[0], _s[2])
    expr2 = "( %d V -%d )" % (_s[1], _s[2])
    expr3 = "( -%d V -%d V %d )" % (_s[0], _s[1], _s[2])
    return [expr1, expr2, expr3]
def or_f(_s):
    """ OR: (-a V c)(-b V c)(a V b V -c) """
    exp3 = "( %d V %d V -%d )" % (_s[0], _s[1], _s[2])
    return ["( -%d V %d )" % (_s[0], _s[2]), "( -%d V %d )" % (_s[1], _s[2]), exp3]
def inv_f(_s):
    """ INV: (a V b)(-a V -b) """
    return ["( %d V %d )" % (_s[0], _s[1]), "( -%d V -%d )" % (_s[0], _s[1])]
def xor_f(_s):
    """ XOR: (a V b V -c)(-a V -b V -c)(-a V b V c)(a V -b V c) """
    expr1 = "( %d V %d V -%d )" % (_s[0], _s[1], _s[2])
    expr2 = "( -%d V -%d V -%d )" % (_s[0], _s[1], _s[2])
    expr3 = "( -%d V %d V %d )" % (_s[0], _s[1], _s[2])
    expr4 = "( %d V -%d V %d )" % (_s[0], _s[1], _s[2])
    return [expr1, expr2, expr3, expr4]
def one_f(_s):
    """ ONE: (a) """
    return ["( %d )" % (_s[0])]
def zero_f(_s):
    """ ZERO: (-a) """
    return ["( -%d )" % (_s[0])]
def join_f(_s):
    """ JOIN: (a V -b)(-a V b) """
    return ["( %d V -%d )" % (_s[0], _s[1]), "( -%d V %d )" % (_s[0], _s[1])]
CHARACTERISTIC_F = {
    "and" : and_f,
    "inv" : inv_f,
    "xor" : xor_f,
    "or"  : or_f,
    "one" : one_f,
    "zero": zero_f,
    "join": join_f
}

@MemoizeHash
def heuristics(_cnf, _var, _unicl_track):
    """ Apply the Unite Clause and Pure Literal rules to CNF. """
    _cnf = [cl for cl in _cnf if " %d "%(_var) not in cl] # Remove all satisfied clauses.
    # Negation to removing 'false' literals from the clauses.
    _cnf = [cl.replace("V %d "%(-_var), "").replace(" %d V"%(-_var), "") for cl in _cnf]

    _unicl_track.append((abs(_var), "=1" if _var > 0 else "=0"))
    if PRN and PRN[1] == '1':
        print "\nGUESSING:" if len(_unicl_track) == 1 else "\nHEURISTICS:", _unicl_track
    if PRN and PRN[2] == '1':
        print "CNF:", [cl.replace("( ", "(").replace(" )", ")") for cl in _cnf]

    unicl_lst = [cl for cl in _cnf if len(cl) < 9] # The shortest elements => Unite Clauses.
    if unicl_lst: # Takes the rightmost and apply the heuristics again.
        ucl_var = int(unicl_lst[-1].replace("( ", "").replace(" )", ""))
        # Empty Clause marker.
        if not ("( "+str(ucl_var)+" )" in _cnf and "( "+str(-ucl_var)+" )" in _cnf):
            _cnf, _unicl_track = heuristics(_cnf, ucl_var, _unicl_track)
        else:
            if PRN and PRN[3] == '1':
                print "EMPTY CLAUSE: ", unicl_lst[-1]
            _unicl_track = []

    return _cnf, _unicl_track

@MemoizeHash
def dpa(_cnf, _var):
    """ The Davis Putnam Algorithm. """
    unicl_track = []

# Heuristics:
    _cnf, unicl_track = heuristics(_cnf, _var, unicl_track)

# Terminal conditions:
    if not unicl_track: # Check for Empty Clause.
        return False, [] # No solution possible.

    if not _cnf: # Check for empty CNF.
        return True, unicl_track # Terminate algorithm, solution found.

# Backtracking:
    var = abs(int(_cnf[-1].split()[-2])) # Rightmost literal from the last clause.
    is_solution, unicl_lst = dpa(_cnf, -var) # Guessing with 0.

    if not is_solution:
        is_solution, unicl_lst = dpa(_cnf, var) # Guessing with 1.

    unicl_track += unicl_lst
    return is_solution, unicl_track


def add_or(_gates, _first_in, _last_out):
    """ Iterator to join the XOR outputs with OR gates. """
    j = 0 # Penultimate (odd case) or ultimate (even case) line used.
    for j in range(_first_in, _last_out, 2):
        _last_out += 1 # To add OR outputs to the miter.
        _gates.append(("or", [j, j+1, _last_out]))

    if j+2 < _last_out:
        _gates, _last_out = add_or(_gates, j+2, _last_out)

    return _gates, _last_out


# --- Code's Body ---

if len(INPUTS_1) == len(INPUTS_2) and len(OUTPUTS_1) == len(OUTPUTS_2):
    GATES_ALL = [] # To join the two nets.

    for in1, in2 in zip(INPUTS_1, INPUTS_2): # Adding input connections.
        GATES_ALL.append(("join", [MAPPING_1[in1], MAPPING_2[in2]]))

    GATES_ALL += GATES_1 + GATES_2

    NETS_ALL = NETS_1+NETS_2
    for out1, out2 in zip(OUTPUTS_1, OUTPUTS_2):
        NETS_ALL += 1 # To add XOR outputs to the miter circuit.
        GATES_ALL.append(("xor", [MAPPING_1[out1], MAPPING_2[out2], NETS_ALL]))

    if len(OUTPUTS_1) > 1: # To join with OR's the XOR outputs.
        GATES_ALL, NETS_ALL = add_or(GATES_ALL, NETS_1+NETS_2+1, NETS_ALL)

    GATES_ALL.append(("one", [NETS_ALL])) # The last out.

    CNF = [] # To create a CNF from all netlist.
    for gate_l in GATES_ALL:
        CNF += CHARACTERISTIC_F[gate_l[0]](gate_l[1])

    if PRN and PRN[0] == '1': # 0 : Full CNF
        print "CNF:", [x.replace("( ", "(").replace(" )", ")") for x in CNF]

    SOLUTION, UNIT_CLS = dpa(CNF, NETS_ALL)

    if not SOLUTION:
        print "\nEquivalent!"
    else:
        print "\nNot equivalent! Counter example:\nInputs:"
        for i in INPUTS_1:
            print ["%s: %s"%(i, u[1].replace("=", "")) for u in UNIT_CLS if u[0] == MAPPING_1[i]]
        print "Outputs netlist 1:"
        for o in OUTPUTS_1:
            print ["%s: %s"%(o, u[1].replace("=", "")) for u in UNIT_CLS if u[0] == MAPPING_1[o]]
        print "Outputs netlist 2:"
        for o in OUTPUTS_2:
            print ["%s: %s"%(o, u[1].replace("=", "")) for u in UNIT_CLS if u[0] == MAPPING_2[o]]

else:
    print "The circuits inputs and outputs differ."
