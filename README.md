# EDA_Tools
This implementation performs the formal equivalence checking given two netlists using a SAT-based approach. The method reads the two netlist files in a specific format. If the netlists are functionally equivalent, the program displays “OK”. If not, it  prints an input assignment which leads to different output values (*counter example*).

To achieve this, the following steps are necessary:
- Create an appropriate miter circuit,
- Convert the miter circuit to a formula in CNF, and 
- Check the CNF for satisfiability.


## Input format

- Line 1: Number of nets.
- Line 2: Names of all input nets.
- Line 3: Names of all output nets.
- Line 4-6: Mapping from net numbers to port names (for all inputs and outputs).
- Line 7: Empty line.
- Line 8 to end of file: Gate instantiations in the form: <Gate type> <input nets> <output nets>. Depending on the gate type, there number of parameters may vary. e.g. *and* has three parameters, while *not* has only two parameters.


## Gate types

There are six gate types which are allowed in a netlist:

**Gate type   Input ports   Output ports**
  and           2             1
  or            2             1
  inv           1             1
  xor           2             1
  one           0             1
  zero          0             1


## --

To have 4 levels of printing is included a third optional argument (sys.argv[3]) that acts as 4-bit selector. e.g. To get a complete CNF and the successive reductions we can put 1010 at the end of command calling. The levels are described in the  program header.

In the first version the CNF is implemented with a string manipulation strategy, wich provoques that the searching and replacing take a little more time going over chains of characters. To improve this behaviour is used a Memoization technic (as a decorator class for the recursive functions).

In the second version is used 2-dimensional vectors of integers to improve the velocity, although the if statements to check the printing flags consumes a considerable time...
