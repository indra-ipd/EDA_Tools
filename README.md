# EDA_Tools

Implementation of a Netlist Equivalence Checker using a SAT approach.

To have 4 levels of printing is included a third optional argument (sys.argv[3]) that acts as 4-bit selector. e.g. To get a complete CNF and the successive reductions we can put 1010 at the end of command calling. The levels are described in the  program header.

In the first version the CNF is implemented with a string manipulation strategy, wich provoques that the searching and replacing take a little more time going over chains of characters. To improve this behaviour is used a Memoization technic (as a decorator class for the recursive functions).

In the second version is used 2-dimensional vectors of integers to improve the velocity, although the if statements to check the printing flags consumes a considerable time...
