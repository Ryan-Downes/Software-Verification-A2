'''
=== INPUT ===
Takes as input a text file that is a partially completes hidato grid of the form:
An N x M grid (lines sep by newlines) of single space separated characters:
> a number
> a * representing a blocked (unfillable) cell
> a - representing a blank (to be filled) cell

=== OUTPUT ===
> hidato-output.txt
Outputs another text file of the same form, containing the corresponding solved problem.

> hidato-formula.smt2
Outputs a z3 formula file that was run against z3 to generate the solution.
'''
import os
import sys
import time # For naming output files
import numpy as np # For pretty printing the matrix
import subprocess as sp # For running z3
import re # For matching output strings
import copy

# Symbol constants in hidato grid files
BLOCKED_CELL = '*'
BLANK_CELL = '-'

# Path to Z3 executable
#Z3 = '/u/csc410h/fall/pub/dafny/Binaries/z3/bin/z3' # For CDF machines
Z3 = '/u/csc410h/fall/pub/z3/bin/z3' # For CDF Machines (updated Oct 12, 2017)

# Name of output files
#formulasFile = 'hidato-formula-' + time.strftime('%Y%m%d-%H%M%S') + '.smt2'
#solutionFile = 'hidato-output-'  + time.strftime('%Y%m%d-%H%M%S') + '.txt'
formulasFile = 'hidato-formula.smt2'
solutionFile = 'hidato-output.txt'


'''
Return string name of cell i, j
'''
def cell(i, j):
    return 'h_{X}_{Y}'.format(X = str(i), Y = str(j))

'''
Given cell string, return coordinates
'''
def uncell(c):
    return int(c.split('_')[1]), int(c.split('_')[2])

'''
Given hidato grid; return list of <cell, [nbr1, nbr2, ...]> pairs. Each
pair is a cell and all unblocked neighbouring cells of that cell.

A cell is either a string 'hXY', where XY is index into grid for that cell,
or the cell is the integer number located at that cell.
'''
def get_neighbours(grid):
    # Helper functions for finding neighbours
    def top_left(matrix, x, y):
        try:
            assert x - 1 >= 0
            assert y - 1 >= 0
            return matrix[x - 1][y - 1]
        except (AssertionError, IndexError):
            return None
    def top(matrix, x, y):
        try:
            assert y - 1 >= 0
            return matrix[x][y - 1]
        except (AssertionError, IndexError):
            return None
    def top_right(matrix, x, y):
        try:
            assert y - 1 >= 0
            return matrix[x + 1][y - 1]
        except (AssertionError, IndexError):
            return None
    def right(matrix, x, y):
        try:
            return matrix[x + 1][y]
        except (AssertionError, IndexError):
            return None
    def bot_right(matrix, x, y):
        try:
            return matrix[x + 1][y + 1]
        except (AssertionError, IndexError):
            return None
    def bot(matrix, x, y):
        try:
            return matrix[x][y + 1]
        except (AssertionError, IndexError):
            return None
    def bot_left(matrix, x, y):
        try:
            assert x - 1 >= 0
            return matrix[x - 1][y + 1]
        except (AssertionError, IndexError):
            return None
    def left(matrix, x, y):
        try:
            assert x - 1 >= 0
            return matrix[x - 1][y]
        except (AssertionError, IndexError):
            return None
    
    neighbours = []
    for i in range(0, len(grid)):
        for j in range(0, len(grid[i])):
            # For all unblocked cells...
            if (grid[i][j] == BLANK_CELL) or (grid[i][j].isdigit()):
                # Get the cell's neighbours...
                all_n = [[ top_left(grid, i, j), cell(i-1,j-1)],
                         [      top(grid, i, j), cell(i  ,j-1)],
                         [top_right(grid, i, j), cell(i+1,j-1)],
                         [    right(grid, i, j), cell(i+1,j  )],
                         [bot_right(grid, i, j), cell(i+1,j+1)],
                         [      bot(grid, i, j), cell(i  ,j+1)],
                         [ bot_left(grid, i, j), cell(i-1,j+1)],
                         [     left(grid, i, j), cell(i-1,j  )]]

                val_n = []
                for n in all_n:
                    # This neighbour is also an unblocked cell...
                    if (n[0] is not None) and (n[0] != BLOCKED_CELL):
                        # Neighbour might be a digit or blank cell...
                        val_n.append(n[0]) if n[0] != BLANK_CELL else val_n.append(n[1])
                
                # Cell might be a digit or blank cell...
                neighbours.append([cell(i, j) if grid[i][j] == BLANK_CELL else grid[i][j],
                                   val_n])

    return neighbours


'''
Return all digit cells in N x M grid
'''
def get_digits(grid):
    digits = []
    for i in range(0, len(grid)):
        for j in range(0, len(grid[i])):
            if grid[i][j].isdigit():
                digits.append(grid[i][j])
    return digits


'''
DEFINE Z3 HELPER FUNCTIONSQW2
'''
# Return '(= 1 (- a b))'
def z3_diff_one(a, b):
    return '(= 1 (- {A} {B}))'.format(A = str(a), B = str(b))

# Return '(> a 0)'
def z3_positive(a):
    return '(> {A} 0)'.format(A = str(a))

# Return '(assert (and (> array[0] 0) (> array[1] 0) ...))'
def z3_all_positive(array):
    f = '(assert (and \n'
    for a in array:
        f += '     ' + z3_positive(a) + '\n'
    return f + '))\n\n'

# Return (min array[0] (min array[1] (min array[2] ...)))
def z3_min(array):
    if len(array) == 2:
        return '(min {A} {B})'.format(A = array[0], B = array[1])
    elif len(array) > 2:
        return '(min {A} {B})'.format(A = array[0], B = z3_min(array[1:]))

# Return '(assert (distinct array[0] array[1] ...))'
def z3_all_distinct(array):
    return '(assert (distinct ' + ' '.join(array) + '))\n'

# Return z3 definition of min function
def z3_min_def():
    return '(define-fun min ((x Int) (y Int)) Int (ite (> x y) y x))\n\n'


'''
Writes SMT formula for hidato puzzle defined by grid into formulasFile
'''
def generate_hidato_formula(grid):
    # Get all unblocked cells (blanks or digits)
    unblocked_cells_and_neighbours = get_neighbours(grid)
    unblocked_cells = [c_and_n[0] for c_and_n in unblocked_cells_and_neighbours]
   
    f = open(formulasFile, 'w')

    # Define min function
    f.write(z3_min_def())

    # Define variables
    for c in unblocked_cells:
        if not c.isdigit():
            f.write('(declare-const ' + c + ' Int)\n')
   
    # Encode Hidato inc property
    z3_min_str = z3_min(unblocked_cells)
    f.write('\n(assert (and \n')
    for c_and_ns in unblocked_cells_and_neighbours:
        c = c_and_ns[0]  # The Blank Cell/ Digit
        ns = c_and_ns[1] # The Blank Cell/ Digit's 'Blank' and 'Digit' neighbours
        
        f.write('     (or \n')
        f.write('          (= ' + c + ' ' + z3_min_str + ')\n') # Either global min
        for n in ns:
            f.write('          ' + z3_diff_one(c, n) + '\n') # Or, -1 neighbour
        f.write('     )\n')
    f.write('))\n\n')
   
    # Encode all positive
    f.write(z3_all_positive(unblocked_cells))

    # Encode that all values (blank, or digit) are distinct 
    f.write(z3_all_distinct(unblocked_cells))

    # Finish
    f.write('(check-sat)\n(get-model)')

    f.close()


'''
Given Z3 output (each line in a separate element),
return the variable assignments only.
'''
def extract_results(z3out):
    res = []
    pattern = re.compile("(.*)define-fun h(.*)Int")
    for i in range(0, len(z3out)):
        if pattern.match(z3out[i]):
            res.append([z3out[i].split()[1], # the variable name
                        z3out[i + 1].split()[0].split(')')[0]]) # the assigned value
    return res


'''
Run formula in formulasFile against Z3, save output to solutionFile,
and return solved grid or None if unsat
'''
def run_formula():
    args = [Z3, formulasFile]
    proc = sp.Popen(args, stdout=sp.PIPE)
    sol = proc.communicate()[0].split('\n')
    if sol[0] == 'unsat':
        return None
    return extract_results(sol)


'''
Return solved version of input grid
Writes solution to solutionFile
'''
def solve_hidato(grid):
    solved_grid = copy.deepcopy(grid)
    sat_assignments = run_formula()
    
    if sat_assignments is not None:
        # Set Z3's assignments to solved grid
        for assignment in sat_assignments:
            i, j = uncell(assignment[0])
            assigned_val = assignment[1]
        
            solved_grid[i][j] = assigned_val

    f = open(solutionFile, 'w')
    # UNSAT
    if sat_assignments is None:
        f.write('unsat\n')
    # SAT
    else:
        for i in range(0, len(solved_grid)):
            for j in range(0, len(solved_grid[i])):
                f.write(' ' + solved_grid[i][j])
            f.write('\n')
    f.close()

    return solved_grid


if __name__ == '__main__':
    if len(sys.argv) == 2:
        # Get N x M array from input file
        with open(sys.argv[1], 'r') as inputFile:
            grid = [row.split() for row in inputFile]
        print("\nInput grid:\n")
        print(np.matrix(grid))


        # Generate corresponding solution formula into formulasFile
        generate_hidato_formula(grid)        
        print("\nSaved SMT formula to: " + formulasFile + "\n")

        # Run formula against Z3, save output to hidato-output.txt
        solved_grid = solve_hidato(grid)
        print("\nSaved solution to: " + solutionFile + "\n")
        
        print("\nOutput grid:\n")
        print(np.matrix(solved_grid))
        print("\n")

    else:
        print("Expected usage: $ python hidato-solver.py input-file")
