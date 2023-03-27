from lark import Lark, Token, Tree
from hyperprob.utility import common
import re


class Property:
    def __init__(self, initial_property_string):
        self.parsed_grammar = None
        self.property_string = initial_property_string
        self.parsed_property = None

    def parseGrammar(self):
        turtle_grammar = """
                        start:    "AS" NAME "." quantifiedformulastate -> forall_scheduler
                            | "ES" NAME "." quantifiedformulastate -> exist_scheduler
                            
                        quantifiedformulastate:  "A" NAME "." quantifiedformulastate -> forall_state  
                            | "E" NAME "." quantifiedformulastate -> exist_state
                            | quantifiedformulastutter
                            | formula
                            
                        quantifiedformulastutter:  "AT" NAME "(" with ")" "." quantifiedformulastutter -> forall_stutter  
                            | "ET" NAME "(" with ")" "." quantifiedformulastutter -> exist_stutter
                            | formula
                        
                        formula: proposition "(" with ")"  -> atomic_proposition
                            | "(" formula "&" formula ")"-> and
                            | "(" formula "|" formula ")"-> or
                            | "(" formula "->" formula ")"-> implies
                            | "(" formula "<->" formula ")"-> biconditional
                            | "~(" formula ")" -> not
                            | "true" -> true
                            | "(" p "<" p ")" -> less_probability
                            | "(" p "=" p ")" -> equal_probability
                            | "(" p ">" p ")" -> greater_probability
                            | "(" p ">=" p ")" -> greater_and_equal_probability
                            | "(" p "<=" p ")" -> less_and_equal_probability
                            | "(" r "<" r ")" -> less_reward
                            | "(" r "=" r ")" -> equal_reward
                            | "(" r ">" r ")" -> greater_reward
                            | "(" r ">=" r ")" -> greater_and_equal_reward
                            | "(" r "<=" r ")" -> less_and_equal_reward

                        p: "P" phi  -> probability
                            | p "+" p -> add_probability
                            | p "-" p -> subtract_probability
                            | p "." p -> multiply_probability
                            | NUM -> constant_probability

                        r: "R" NAME phi  -> reward
                            | r "+" r -> add_reward
                            | r "-" r -> subtract_reward
                            | r "." r -> multiply_reward
                            | NUM -> constant_reward

                        phi:  "(X" formula ")" -> next
                            | "(" formula "U" formula ")"-> until_unbounded
                            | "(" formula "U["NUM "," NUM"]" formula ")"-> until_bounded
                            | "(F" formula ")" -> future
                            | "(G" formula ")" -> global

                        proposition: NAME 
                        with: NAME

                        %import common.CNAME -> NAME
                        %import common.NUMBER ->NUM
                        %import common.WS_INLINE
                        %ignore WS_INLINE
                    """
        self.parsed_grammar = Lark(turtle_grammar)

        # "ES sh . A s1 . A s2 . AT t1 (s1). ET t2. ET t3. ((start0(s1) & start1(s2)) -> (P (X end(s1)) = P (X end(s2))))"

    def parseProperty(self, print_property):
        try:
            self.parseGrammar()
            self.parsed_property = self.parsed_grammar.parse(self.property_string)
            if print_property:
                self.printProperty()
        except Exception as err:
            common.colourerror("Encountered error in property: " + str(err))

    def printProperty(self):
        print(self.parsed_property.pretty())


'''
def findToken(formula, token):
    no_of_children = len(formula.children)
    result_for_child1 = False
    result_for_child2 = False
    if no_of_children == 0:
        return False

    if formula.children[0] == token:
        result_for_child1 = True
    elif formula.children[0] != token and type(formula.children[0]) != Token:
        result_for_child1 = findToken(formula.children[0], token)

    if no_of_children > 1 and not result_for_child1:
        if formula.children[1] == token:
            result_for_child2 = True
        elif formula.children[1] != token and type(formula.children[1]) != Token:
            result_for_child2 = findToken(formula.children[1], token)

    return result_for_child1 or result_for_child2


def renameQuantifierVariable(formula_inp, old, new):
    no_of_children = len(formula_inp.children)
    if no_of_children == 0:
        return formula_inp

    if formula_inp.children[0] == old:
        formula_inp.children[0] = new
    elif formula_inp.children[0] != old and type(formula_inp.children[0]) != Token:
        formula_inp.children[0] = renameQuantifierVariable(formula_inp.children[0], old, new)

    if no_of_children > 1:
        if formula_inp.children[1] == old:
            formula_inp.children[1] = new
        elif formula_inp.children[1] != old and type(formula_inp.children[1]) != Token:
            formula_inp.children[1] = renameQuantifierVariable(formula_inp.children[1], old, new)

    return formula_inp


def editFormula(formula_inp):
    formula_inp_copy = None
    formula_inp_duplicate = formula_inp
    previous_head = None
    nos_of_quantifier = 0
    quantifier_change = []  # false indicates the quantifier was deleted, true indicates it'll stay but might need name change
    while len(formula_inp_duplicate.children) > 0 and type(formula_inp_duplicate.children[0]) == Token:
        if formula_inp_duplicate.data in ['exist_scheduler', 'forall_scheduler']:
            formula_inp_duplicate = formula_inp_duplicate.children[1]
        elif formula_inp_duplicate.data in ['exist_state', 'forall_state']:
            tok = formula_inp_duplicate.children[0]
            res = findToken(formula_inp_duplicate.children[1], tok)
            if not res:
                if previous_head is None:
                    formula_inp_copy = formula_inp_duplicate.children[1]
                else:
                    previous_head.children[1] = formula_inp_duplicate.children[1]
                    formula_inp_copy = previous_head
            else:
                nos_of_quantifier += 1
                previous_head = formula_inp_copy
            quantifier_change.append(not res)
            formula_inp_duplicate = formula_inp_duplicate.children[1]

    quantifier_index = 1
    for quant in range(len(quantifier_change)):
        if quantifier_change[quant] and quantifier_index < (quant + 1):
            old = Token('NAME', 's' + str(quant + 1))
            new = Token('NAME', 's' + str(quantifier_index))
            formula_inp_copy = renameQuantifierVariable(formula_inp_copy, old, new)
            quantifier_index += 1
    #print(formula_inp)
    #formula_inp_duplicate = formula_inp
    if formula_inp.data in ['exist_scheduler', 'forall_scheduler']:
        formula_inp.children[1] = formula_inp_copy
    
    while len(formula_inp_duplicate.children) > 0 and type(formula_inp_duplicate.children[0]) == Token:
        if formula_inp_duplicate.data in ['exist_scheduler', 'forall_scheduler', 'exist_state', 'forall_state']:
            formula_inp_duplicate = formula_inp_duplicate.children[1]
    
    return formula_inp_duplicate, formula_inp, nos_of_quantifier
'''


def findNumberOfStateQuantifier(hyperproperty):
    formula_duplicate = hyperproperty
    no_of_quantifier = 0
    variable_names = set() # list of state variable names/indices in order of quantification
    while len(formula_duplicate.children) > 0:
        if formula_duplicate.data in ['exist_scheduler', 'forall_scheduler']:
            formula_duplicate = formula_duplicate.children[1]
        elif formula_duplicate.data in ['exist_state', 'forall_state']:
            no_of_quantifier += 1
            variable_names.add(int(formula_duplicate.children[0].value[1:]))
            formula_duplicate = formula_duplicate.children[1]
        else:
            break
    if set(range(1,len(variable_names)+1)) != variable_names:
        raise ValueError("The state variables are not named s1, ..., sn.")
    return formula_duplicate, no_of_quantifier


def findNumberOfStutterQuantifier(hyperproperty):
    formula_duplicate = hyperproperty
    no_of_quantifier = 0
    quant_stutter_state_quantifier = dict() # mapping quantified variables, dict of the form {stutter : state}, i.e. dict[stutter quantifier] = state_quantifier
    variable_names = []
    while len(formula_duplicate.children) > 0 and type(formula_duplicate.children[0]) == Token:
        if formula_duplicate.data in ['exist_scheduler', 'forall_scheduler', 'exist_state', 'forall_state']:
            formula_duplicate = formula_duplicate.children[1]
        elif formula_duplicate.data in ['forall_stutter', 'exist_stutter']:
            no_of_quantifier += 1
            quant_stutter_state_quantifier[int(formula_duplicate.children[0].value[1:])] = int(formula_duplicate.children[1].children[0].value[1:])
            variable_names.append(int(formula_duplicate.children[0].value[1:]))
            formula_duplicate = formula_duplicate.children[2]
    # check all quantified stutter-sched variables are named correctly and occur in the correct order
    if list(range(1,len(variable_names)+1)) != variable_names:
        raise ValueError("The stutter variables are not named t1, ..., tn (or are not quantified in this order).")
    # check that all quantified stutter-vars are used:
    rel_quant = set() # set of stutter quantifiers occurring in the formula
    tokens = formula_duplicate.scan_values(lambda v: isinstance(v, Token))
    for name in tokens:
        if (re.search("t[1-9]+", name)) is not None:
            rel_quant.add(int(name[1:]))
    real_stutter_state_quantifier = {key: quant_stutter_state_quantifier[key] for key in list(rel_quant)} # only those pairs where the stutter-variable occurs in the formula
    if quant_stutter_state_quantifier != real_stutter_state_quantifier:
        raise ValueError("The variables used in the formula do not match the quantified variables.")
    return formula_duplicate, real_stutter_state_quantifier


def checkQuantifiersMatch():
    # TODO: check if every state quantifier has at least one matching stutter quantifier. If not, raise error.
    # extra TODO: add handling for missing stutter quantifiers (for all state, no stuttering)
    pass


def negateForallProperty(parsed_property):
    temp_traversed_property = parsed_property
    index_for_child = -1
    while len(temp_traversed_property.children) > 0:
        if temp_traversed_property.data == 'forall_scheduler':
            temp_traversed_property.data = 'exist_scheduler'
            index_for_child = 1
        elif temp_traversed_property.data == 'exist_state':
            temp_traversed_property.data = 'forall_state'
            index_for_child = 1
        elif temp_traversed_property.data == 'forall_state':
            temp_traversed_property.data = 'exist_state'
            index_for_child = 1
        elif temp_traversed_property.data == 'exist_stutter':
            temp_traversed_property.data = 'forall_stutter'
            index_for_child = 2
        elif temp_traversed_property.data == 'forall_stutter':
            temp_traversed_property.data = 'exist_stutter'
            index_for_child = 2
        elif temp_traversed_property.data == 'not':
            pass
        if temp_traversed_property.children[index_for_child].data in ['exist_state', 'forall_state', 'exist_stutter',
                                                                      'forall_stutter']:
            temp_traversed_property = temp_traversed_property.children[index_for_child]
        elif temp_traversed_property.children[index_for_child].data in ['quantifiedformulastate']:
            temp_traversed_property = temp_traversed_property.children[1].children[0]
        elif temp_traversed_property.children[index_for_child].data in ['quantifiedformulastutter']:
            temp_traversed_property = temp_traversed_property.children[index_for_child]
            break
    if temp_traversed_property.children[0].data == 'not':
        temp_traversed_property.children[0] = temp_traversed_property.children[0].children[0]
    else:
        temp_traversed_property.children[0] = Tree('not', [temp_traversed_property.children[0]])

    return temp_traversed_property.children[0]
