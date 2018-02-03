'''
=== GROUPING Method B ===
Use user defined variables and function logic in z3 to solve Q2b
f(x) = y implies student x and y are a group
f(y) = x also implies x and y are a group

=== INPUT ===
Takes as input a text file that contains student's partner preferences.
Student 1's preferences on line 1, Student 2's on line 2, etc.
Empty line N => Student N has no preferences.
Preferences are positive integers referencing other student's (assumed well-formed)

=== OUTPUT ===
> groupingb-output.txt
Outputs lines of student pairs; maximum pairs must be chosen, satisfying the most student preferences

> groupingb-formula.smt2
Outputs z3 formula file that was run against z3 to generate the solution.
'''

import os
import sys
import subprocess as sp # For running z3
import re # For matching output strings
import copy

# Path to Z3 executable
Z3 = '/u/csc410h/fall/pub/z3/bin/z3' # For CDF machines

# Name of output files
formulasFile = 'groupingb-formula.smt2'
solutionFile = 'groupingb-output.txt'

'''
Returns a string corresponding to initialization of variables in z3
'''
def z3_declare(num):

    # user defined data type A
    ret = '(declare-sort A)\n'
    #declare all variables are type A
    for i in range(1, num+1):
        ret = ret + '(declare-const x' + str(i) + ' A)\n'
    ret =  ret + '(declare-const xnull A)\n\n'
    return ret 


'''
Returns a string corresponding to restrictions on size of student groups in z3
'''
def z3_restrictions(num):

    # assertion that each student group contains at most 2 elements
    ret = '(assert (forall ((x A)) (or '
    for i in range(1, num+1):
        ret = ret + '(= x x' + str(i) + ') ' 
    ret = ret + '(= x xnull))))\n\n' 
   
    # assert that each student group contains at least 2 elements
    ret = ret + '(assert (and\n\t'
    for i in range(1, num+1):
        for j in range (i+1, num+1):
            ret = ret +'(not (= x' + str(i) + ' x' + str(j) + ')) '
        ret = ret +  '(not (= x' + str(i) + ' xnull))' +  '\n\t'
    ret = ret + '))\n\n'
    return ret


'''
Returns a string corresponding to the definition of range of variables in z3
'''
def z3_define_range(num):

    # declaration of identity function    
    ret = '(declare-fun f (A) A)\n\n'

    for i in range(1, num+1):
        ret = ret + '(assert (exists ((x A)) (= (f x' + str(i) + ') x )))\n'
    ret = ret + '(assert (exists ((x A)) (= (f xnull) x )))\n\n'
    return ret 


'''
Returns a string corresponding to the function constraints and the 
student preference constraints
'''
def z3_preference(prefs, num):

    # assert function constraints
    # when f(x) = y it implies that x and y are a group
    # assert that f(y) = x also holds if f(x) = y 
    ret = '(assert (forall ((x A)) (= (f (f x)) x )))\n'
    ret = ret + '(assert (forall ((x A) (y A)) (=> (and (not (= x xnull)) (= (f x) y)) (not (= x y)))))\n\n'
    for i in range(1, num+1):

        # assert the student preferences if they have any
        if prefs[i-1] != []:
            ret = ret + '(assert-soft (or '
            for value in prefs[i-1]:       
                ret = ret + '(= (f x' + str(i) + ') x'+ value + ') ' 
            ret = ret + '))\n'
    ret = ret + '\n'
    return ret 


'''
Write the SMT formula for Grouping B method into formulasFile
'''
def z3_create(prefs):
    f = open(formulasFile, 'w')
    num_students = len(prefs)

    # Declares set and variables in z3
    f.write(z3_declare(num_students))

    # asserts that sets contain 2 and only 2 elements 
    f.write(z3_restrictions(num_students))

    # define the range of the set and functions in z3
    f.write(z3_define_range(num_students))

    #represent the student constraints/preferences in z3
    f.write(z3_preference(prefs, num_students)) 

    f.write('(check-sat)\n(get-model)')
    f.close()


'''
Given the Z3 output (each line in a separate element),
return the list of matched student groups 
'''
def extract_results(z3out):
    student_map = []
    pairings = []

    # search for the lines of data we need to get using regex
    pattern1 = re.compile("(.*)define-fun x([0-9]+)")
    pattern2 = re.compile("(.*)define-fun f\!")

    for i in range(0, len(z3out)):

        # once the pattern matches, extract the data we need
        if pattern1.match(z3out[i]):
            num1 = z3out[i].split()[1][1:]
            num2 = (z3out[i+1].split("!")[2].split(")")[0])
            student_map.append((num1, num2))
        else: 
            if pattern2.match(z3out[i]):
                for j in range (1, len(student_map)+1):
                    value = z3out[i+j].split("!")
                    value1 = (value[3].split(")"))[0]
                    value2 = (value[5].split("\n"))[0]
                    pairings.append((value1, value2))
    return combine_mapping(student_map, pairings)


'''
Given two sets of variable mappings from the z3 output,
return the list of matched student groups
'''
def combine_mapping(student_map, pairings):
    answer = []
    student_dict = dict(student_map)
    key_pair = dict(pairings)
    complete_key_pair = {}

    # collect all of the function pairings
    for first, second in key_pair.iteritems():
        complete_key_pair[second] = first
        complete_key_pair[first] = second

    # iterate over all of the function pairings and compare them with a
    # mapping of the student variables to find the matching functions
    # f(x) = y and f(y) = x which is our student pairing
    for student, key in student_dict.iteritems():
        search = complete_key_pair.get(key)
        if search != None:
            for sec_student, sec_key in student_dict.iteritems():
                if sec_key == search and (not((sec_student, student) in answer)):
                        answer.append((student, sec_student))
    return answer


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
def solve_groupingb():
    assignments = run_formula()
    f = open(solutionFile, 'w')

    # UNSAT
    if assignments is None:
        f.write('0 groups formed:\n')

    # SAT
    else:
        f.write(str(len(assignments)) + ' groups formed:\n')
        for sat_b in assignments:
            f.write(sat_b[0] + ', ' + sat_b[1] + '\n')

    f.close()


if __name__ == '__main__':
    if len(sys.argv) == 2:

        # Get preferences from input file
        with open(sys.argv[1], 'r') as inputFile:
            prefs = [row.split() for row in inputFile]

        # Generate corresponding solution formula into formulasFile
        z3_create(prefs)
        print("\nSaved SMT formula to: " + formulasFile + "\n")

        # Run formula against Z3, save output to solutionFile
        solve_groupingb()
        print("\nSaved solution to: " + solutionFile + "\n")
    else:
        print("Expected usage: $ python groupingb.py input-file")