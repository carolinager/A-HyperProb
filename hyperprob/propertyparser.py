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

def checkStateQuantifiers(hyperproperty):
    """
    Traverses and checks state quantifiers
    :param hyperproperty: AHyperPCTL formula
    :return: stutter-quantified property, no. of state quantifiers, list of state variables in order of quantification
    """
    formula_duplicate = hyperproperty
    no_of_quantifier = 0
    variable_indices = set() # list of state variable names/indices in order of quantification
    while len(formula_duplicate.children) > 0:
        if formula_duplicate.data in ['exist_scheduler']: # , 'forall_scheduler'
            formula_duplicate = formula_duplicate.children[1]
        elif formula_duplicate.data in ['exist_state', 'forall_state']:
            no_of_quantifier += 1
            variable_indices.add(int(formula_duplicate.children[0].value[1:]))
            formula_duplicate = formula_duplicate.children[1]
        else:
            break
    if set(range(1,len(variable_indices)+1)) != variable_indices:
        raise ValueError("The state variables are not named s1, ..., sn.")
    return formula_duplicate, no_of_quantifier, variable_indices


def checkStutterQuantifiers(hyperproperty, state_indices):
    """
    Traverses and checks stutter quantifiers
    :param hyperproperty: quantified formula
    :param state_indices: list of state variable indices
    :return: stutter-quantified property, no. of state quantifiers, list of state variables in order of quantification
    """
    formula_duplicate = hyperproperty
    no_of_quantifier = 0
    quant_stutter_state_quantifier = dict() # mapping quantified variables, dict of the form {stutter : state}, i.e. dict[stutter quantifier] = state_quantifier
    variable_indices = []
    while len(formula_duplicate.children) > 0 and type(formula_duplicate.children[0]) == Token:
        if formula_duplicate.data in ['exist_scheduler', 'exist_state', 'forall_state']: # , 'forall_scheduler'
            formula_duplicate = formula_duplicate.children[1]
        elif formula_duplicate.data in ['exist_stutter']: # , 'forall_stutter'
            no_of_quantifier += 1
            quant_stutter_state_quantifier[int(formula_duplicate.children[0].value[1:])] = int(
                formula_duplicate.children[1].children[0].value[1:])
            variable_indices.append(int(formula_duplicate.children[0].value[1:]))
            formula_duplicate = formula_duplicate.children[2]
        else:
            break
    associated_state_indices = quant_stutter_state_quantifier.values()

    # check there exists a stutter-var for every state quantifier
    for i in state_indices:
        if i not in associated_state_indices:
            raise ValueError(f"State s{i} is not associated with a stutter-scheduler")
    # check that for each stutter-quantifier the associated state belongs to a state quantifier
    for i in associated_state_indices:
        if i not in state_indices:
            raise ValueError(f"State s{i} is not quantified")

    # check all quantified stutter-sched variables are named correctly and occur in the correct order
    if list(range(1, len(variable_indices)+1)) != variable_indices:
        raise ValueError("The stutter variables are not named t1, ..., tn (or are not quantified in this order).")
    # check that all quantified stutter-vars are used:
    rel_quant = set() # set of stutter quantifiers occurring in the formula
    tokens = formula_duplicate.scan_values(lambda v: isinstance(v, Token))
    for name in tokens:
        if (re.search("t[1-9]+", name)) is not None:
            rel_quant.add(int(name[1:]))
    if rel_quant != quant_stutter_state_quantifier.keys():
        raise ValueError("The variables used in the formula do not match the quantified variables.")

    return formula_duplicate, quant_stutter_state_quantifier
