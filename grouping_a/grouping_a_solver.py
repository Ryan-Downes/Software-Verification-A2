'''
=== GROUPING Method A ===
Only using propositional logic in the Z3 formula

=== INPUT ===
Takes as input a text file that contains student's partner preferences.
Student 1's preferences on line 1, Student 2's on line 2, etc.
Empty line N => Student N has no preferences.
Preferences are positive integers referencing other student's (assumed well-formed)

=== OUTPUT ===
> groupinga-output.txt
Outputs lines of student pairs; maximum pairs must be chosen, satisfying the most student preferences

> groupinga-formula.smt2
Outputs z3 formula file that was run against z3 to generate the solution.
'''
import os
import sys
import numpy as np # For pretty printing the matrix
import subprocess as sp # For running z3
import re # For matching output strings
import copy
import itertools

# Path to Z3 executable
Z3 = '/u/csc410h/fall/pub/z3/bin/z3' # For CDF machines

# Name of output files
formulasFile = 'groupinga-formula.smt2'
solutionFile = 'groupinga-output.txt'


'''
Return encoding of group formed by student 1 and student 2
'''
def group(student1, student2):
    return 'g_{X}_{Y}'.format(X = str(student1), Y = str(student2))


'''
Given list of (SID_1, SID_2) tuples, return 
'''
def group_all(pairings):
    return [group(pair[0], pair[1]) for pair in pairings]


'''
Given representation of group, return individual students, as integers
'''
def ungroup(group):
    return int(group.split('_')[1]), int(group.split('_')[2])


'''
Given group, reverse the encoding: input g_1_2 => return g_2_1
'''
def reverse_group(g):
    s1, s2 = ungroup(g)
    return group(s2, s1)


'''
Return true if g1 and g2 are reverses (e.g. g_1_2 and g_2_1 are reverses)
'''
def is_reverse(g1, g2):
    return g2 == reverse_group(g1)


'''
Return list of tuples, where a tuple is (SID_1, SID_2)
Given number of students, returns all groupings (pairings)
'''
def get_all_pairs(num_students):
    students = range(1, num_students + 1)
    return [pair for pair in itertools.combinations(students, 2)]


'''
Return true if s1 prefers working with s2
'''
def prefers(s1, s2, prefs):
   return str(s2) in prefs[s1 - 1]


'''
Return true if s1 prefers working with s2, and s2 prefers working with s1
'''
def mutual_preference(s1, s2, prefs):
    return prefers(s1, s2, prefs) and prefers(s2, s1, prefs)

'''
Return true if s1 prefers working with s2, or s2 prefers working with s1
'''
def oneway_preference(s1, s2, prefs):
    return prefers(s1, s2, prefs) or prefers(s2, s1, prefs)

'''
Return subset of pairs that satisfy at least a one-way preference
'''
def get_all_ow_pairs(pairs, prefs):
    return [pair for pair in pairs if oneway_preference(pair[0], pair[1], prefs)]


'''
Return subset of pairs that satisfy two-way (mutual) preference
'''
def get_all_tw_pairs(pairs, prefs):
    return [pair for pair in pairs if mutual_preference(pair[0], pair[1], prefs)]
 

'''
Return Z3 formula of form:
(assert (or (and var (not var_dep1) (not var_dep2) ...) (not var))
'''
def z3_group(g, pairs):
    s1, s2 = ungroup(g)
    other_pairs = []
    for pair in pairs:
        if (s1 in pair) ^ (s2 in pair):
            other_pairs.append(pair)
    
    ret = '(assert (or (and ' + g
    for pair in other_pairs:
        ret += ' (not ' + group(pair[0], pair[1]) + ')'
    
    return ret + ') (not ' + g + ')))'


'''
Return Z3 formula of form:
(assert-soft var :weight w)
'''
def z3_assert_soft(g, w):
    return '(assert-soft {var} :weight {weight})'.format(var = g, weight = w)


'''
Return disjunction of all groups containing person p; z3 formula of the form:
(or g1 g2 g3...)
'''
def z3_in_group(p, pairs):
    ret = '(or'
    for pair in pairs:
        if p in pair:
            ret += ' ' + group(pair[0], pair[1])
    return ret + ')'


'''
Return exclusionary conjuntions of disjunctions, excluding person p from a group
(and (or ...) (or ...))
'''
def z3_exclude_from_group(excluded_p, num_students, pairs):
    ret = '     (and\n'
    for p in range(1, num_students + 1):
        if p != excluded_p:
            ret += '          ' + z3_in_group(p, pairs) + '\n'
    return ret + '     )'


'''
Write the SMT formula for Grouping A method into formulasFile
'''
def generate_groupinga_formula(prefs):
    num_students = len(prefs)
    
    # List of all possible student pairings (ignoring preferences)
    pairs   = get_all_pairs(num_students)            # List of tuples
    f_pairs = group_all(pairs)                       # List of strings

    # List of all one way prefs (two way prefs are a subset)
    ow_pairs   = get_all_ow_pairs(pairs, prefs)      # List of tuples
    f_ow_pairs = group_all(ow_pairs)                 # List of strings

    # List of all two way prefs (mutual preferences)
    tw_pairs   = get_all_tw_pairs(pairs, prefs)      # List of tuples
    f_tw_pairs = group_all(tw_pairs)                 # List of strings

    # Test - this is what the parser is seeing:
    """
    print("\nAll pairs: \n")
    print(pairs)
    print("\nAll pairs (formatted):\n")
    print(f_pairs)
    print("\nAll one-way pairs: \n")
    print(ow_pairs)
    print("\nAll one-way pairs (formatted):\n")
    print(f_ow_pairs)
    print("\nAll two-way pairs: \n")
    print(tw_pairs)
    print("\nAll two-way pairs (formatted):\n")
    print(f_tw_pairs)
    print("\n")
    """

    f = open(formulasFile, 'w')

    # Define boolean variables
    for var in f_pairs:
        f.write('(declare-const ' + var + ' Bool)\n')    
    f.write('\n')

    # Define group constraints (no student can belong to two groups)
    for var in f_pairs:
        f.write(z3_group(var, pairs) + '\n')
    f.write('\n')

    # Define two-way pref pair weighting (prioritize these groups)
    for tw_var in f_tw_pairs:
       f.write(z3_assert_soft(tw_var, '4') + '\n')
    f.write('\n')

    # Define one-way pref pair weighting (prioritize these groups next)
    for ow_var in f_ow_pairs:
        f.write(z3_assert_soft(ow_var, '2') + '\n')
    f.write('\n')

    # Define that at most 1 person is not in a group
    f.write('(assert (or\n')
    for excluded_person in range(1, num_students + 1):
        f.write(z3_exclude_from_group(excluded_person, num_students, pairs) + '\n')
    f.write('))\n\n')

    # Get Model
    f.write('(check-sat)\n(get-model)')

    f.close()


'''
Given Z3 output (each line in a separate element),
return the variable assignments only.
'''
def extract_results(z3out):
    res = []
    pattern = re.compile("(.*)define-fun g_(.*)Bool")
    for i in range(0, len(z3out)):
        if pattern.match(z3out[i]):
            res.append([z3out[i].split()[1], # the variable name
                        z3out[i + 1].split()[0].split(')')[0]]) # the assigned value

    return res


'''
Run formula in formulasFile against Z3, return result
'''
def run_formula():
    args = [Z3, formulasFile]
    proc = sp.Popen(args, stdout=sp.PIPE)
    sol = proc.communicate()[0].split('\n')
    if sol[0] == 'unsat':
        return None
    return extract_results(sol)

'''
Write solution to solutionFile
'''
def solve_groupinga():
    assignments = run_formula()
    f = open(solutionFile, 'w')

    # UNSAT
    if assignments is None:
        f.write('unsat\n')

    # SAT
    else:
        f.write(str(len([sat_a for sat_a in assignments if sat_a[1] == 'true'])) + " groups formed:\n")
        for sat_a in assignments:
            if sat_a[1] == 'true':
                s1, s2 = ungroup(sat_a[0])
                f.write(str(s1) + ', ' + str(s2) + '\n')

    f.close()


if __name__ == '__main__':
    if len(sys.argv) == 2:
        # Get preferences from input file
        with open(sys.argv[1], 'r') as inputFile:
            prefs = [row.split() for row in inputFile]
        
        # Generate corresponding solution formula into formulasFile
        generate_groupinga_formula(prefs)
        print("\nSaved SMT formula to: " + formulasFile + "\n")

        # Run formula against Z3, save output to solutionFile
        solve_groupinga()
        print("\nSaved solution to: " + solutionFile + "\n")
    
    else:
        print("Expected usage: $ python groupinga.py input-file")
