import copy
import time
import itertools

from lark import Tree
# from z3 import Solver, Bool, Real, Int, Or, sat, And, Implies, RealVal, Sum

from cvc5.pythonic import *

from hyperprob.utility import common
from hyperprob import propertyparser
from hyperprob.sementicencoder import SemanticsEncoder


class ModelChecker:
    def __init__(self, model, hyperproperty, lengthOfStutter, dontRestrictSched=False):
        self.model = model
        self.initial_hyperproperty = hyperproperty  # object of property class
        self.solver = Solver()
        self.stutterLength = lengthOfStutter  # default value 1 (no stutter)
        self.list_of_subformula = []
        self.dictOfReals = dict()
        self.dictOfBools = dict()
        self.dictOfInts = dict()
        self.no_of_subformula = 0
        self.no_of_state_quantifier = 0
        self.no_of_stutter_quantifier = 0
        self.stutter_state_mapping = None  # value at index of stutter variable is the corresponding state variable
        self.dict_pair_index = dict() # dictionary mapping all state-action-pairs to their index in the tuples representing the stutter-schedulers
        self.dontRestrictSched = dontRestrictSched

    def modelCheck(self):
        non_quantified_property, self.no_of_state_quantifier, state_indices = propertyparser.checkStateQuantifiers(
            copy.deepcopy(self.initial_hyperproperty.parsed_property))
        non_quantified_property, self.stutter_state_mapping = propertyparser.checkStutterQuantifiers(
            non_quantified_property.children[0], state_indices)
        self.no_of_stutter_quantifier = len(self.stutter_state_mapping.keys())
        self.no_of_state_quantifier = len(set(self.stutter_state_mapping.values()))
        non_quantified_property = non_quantified_property.children[0]
        start_time = time.perf_counter()
        self.encodeActions()
        self.encodeStuttering()
        list_of_states_with_initial_stutter = list(itertools.product(self.model.getListOfStates(), [0]))
        combined_list_of_states_with_initial_stutter = list(
            itertools.product(list_of_states_with_initial_stutter, repeat=self.no_of_stutter_quantifier))

        if self.initial_hyperproperty.parsed_property.data == 'exist_scheduler':
            self.addToSubformulaList(non_quantified_property) # todo dont really need nq property here anymore
            self.truth(combined_list_of_states_with_initial_stutter)
            encoding_end_time = time.perf_counter() - start_time
            self.printResult(encoding_end_time, 'exists')

        elif self.initial_hyperproperty.parsed_property.data == 'forall_scheduler':
            negated_non_quantified_property = propertyparser.negateForallProperty(
                self.initial_hyperproperty.parsed_property)
            self.addToSubformulaList(negated_non_quantified_property)
            self.truth(combined_list_of_states_with_initial_stutter)
            encoding_end_time = time.perf_counter() - start_time
            print("Finished Checking")
            self.printResult(encoding_end_time, 'forall')

    def encodeActions(self):
        if self.dontRestrictSched:
            # probabilistic scheduler without extra restrictions:
            scheduler_probs = []
            for state in self.model.parsed_model.states:
                name = "a_" + str(state.id) + "_"  # a_s_x is probability of action x in state s
                sum_of_probs = RealVal(0)
                for act in state.actions:
                    name_a = name + str(act.id)
                    self.addToVariableList(name_a)
                    sum_of_probs += self.dictOfReals[name_a]
                scheduler_probs.append(sum_of_probs == RealVal(1))
            self.solver.add(And(scheduler_probs))
            self.no_of_subformula += 1
        else:
            # encode global, state-independent scheduler probabilities for the actions
            set_of_actionsets = {frozenset(x) for x in self.model.getDictOfActions().values()}
            scheduler_restrictions = []

            for A in set_of_actionsets:
                sum_over_probs = []
                if len(A) == 1:
                    action = list(A)[0]
                    name = "a_" + str(set(A)) + "_" + str(action)
                    self.addToVariableList(name)
                    scheduler_restrictions.append(self.dictOfReals[name] == RealVal(1))
                else:
                    for action in A:
                        name = "a_" + str(set(A)) + "_" + str(action)  # a_A_x is probability of action x at a state with enabled actions A
                        self.addToVariableList(name)
                        # probabilistic scheduler
                        scheduler_restrictions.append(self.dictOfReals[name] >= RealVal(0))
                        scheduler_restrictions.append(self.dictOfReals[name] <= RealVal(1))
                        # deterministic scheduler (inefficient to encode it like this?)
                        # scheduler_restrictions.append(Or(self.dictOfReals[name] == RealVal(0),
                        #                                  self.dictOfReals[name] == RealVal(1)))
                        sum_over_probs.append(self.dictOfReals[name])
                    scheduler_restrictions.append(Sum(sum_over_probs) == RealVal(1))

            # todo: if we remove dontRestrictSched then replace a_s_x by a_A_x everywhere in semantic encoding instead of doing the following
            for state in self.model.parsed_model.states:
                name_s = "a_" + str(state.id) + "_"  # a_s_x is probability of action x in state s
                name_A = "a_" + str(set([a.id for a in state.actions])) + "_"
                sum_of_probs = RealVal(0)
                for act in state.actions:
                    name_s_a = name_s + str(act.id)
                    name_A_a = name_A + str(act.id)
                    self.addToVariableList(name_s_a)
                    sum_of_probs += self.dictOfReals[name_s_a]
                    scheduler_restrictions.append(self.dictOfReals[name_s_a] == self.dictOfReals[name_A_a])

            if len(scheduler_restrictions) == 1:
                self.solver.add(scheduler_restrictions[0])
            else:
                self.solver.add(And(scheduler_restrictions))
            self.no_of_subformula += 1

        common.colourinfo("Encoded actions in the MDP...")

    def encodeStuttering(self):
        list_over_quantifiers = []
        for quantifier in range(0, self.no_of_stutter_quantifier):
            list_over_states = []
            for state in self.model.parsed_model.states:
                list_over_actions = []
                for action in state.actions:
                    # list_of_equations = []
                    # t_i_s_x means stutter duration for stutter quantifier i and state s and action x
                    name = "t_" + str(quantifier + 1) + "_" + str(state.id) + "_" + str(action.id)
                    self.addToVariableList(name)
                    # for stutter_length in range(0, self.stutterLength):
                    #    list_of_equations.append(self.dictOfInts[name] == int(stutter_length)) # todo do it like this do encode t_... as reals not ints?
                    lower_bound = self.dictOfInts[name] >= int(0)
                    upper_bound = self.dictOfInts[name] < int(self.stutterLength)
                    list_over_actions.append(And(lower_bound,
                                                 upper_bound))  # Or(list_of_equations),
                    self.no_of_subformula += 1
                if len(list_over_actions) == 1: # in case a state has just a single actions
                    list_over_states.append(list_over_actions[0])
                else:
                    list_over_states.append(And(list_over_actions))
                self.no_of_subformula += 1
            list_over_quantifiers.append(And(list_over_states))
            self.no_of_subformula += 1
        if len(list_over_quantifiers) == 1:
            self.solver.add(list_over_quantifiers[0])
        else:
            self.solver.add(And(list_over_quantifiers))
        self.no_of_subformula += 1
        common.colourinfo("Encoded stutter actions in the MDP...")


    def addToVariableList(self, name):
        if name[0] == 'h' and not name.startswith('holdsToInt'):  # holds_
            self.dictOfBools[name] = Bool(name)
        elif name[0] in ['p', 'd', 'r', 'a', 's'] or name.startswith('holdsToInt'):  # prob_, d_, rew_, a_s, sigma_a
            self.dictOfReals[name] = Real(name)
        elif name[0] in ['t']:  # t_
            self.dictOfInts[name] = Int(name)

    def addToSubformulaList(self, formula_phi):
    # add as you go any new subformula part as needed
    # also adds all subformulas of the formula to the list
    # todo could be made more efficient: test whether formula_phi is in list only once in the beginning?
        if formula_phi.data in ['exist_scheduler', 'forall_scheduler', 'exist_state', 'forall_state']:
            formula_phi = formula_phi.children[1]
            self.addToSubformulaList(formula_phi)
        elif formula_phi.data in ['and', 'or', 'implies', 'biconditional',
                                  'less_probability', 'equal_probability', 'greater_probability',
                                  'greater_and_equal_probability', 'less_and_equal_probability',
                                  'less_reward', 'equal_reward', 'greater_reward', 'greater_and_equal_reward',
                                  'less_and_equal_reward',
                                  'add_probability', 'subtract_probability', 'multiply_probability',
                                  'add_reward', 'subtract_reward', 'multiply_reward',
                                  'until_unbounded'
                                  ]:
            if formula_phi not in self.list_of_subformula:
                self.list_of_subformula.append(formula_phi)
            left_child = formula_phi.children[0]
            self.addToSubformulaList(left_child)
            right_child = formula_phi.children[1]
            self.addToSubformulaList(right_child)
        elif formula_phi.data in ['atomic_proposition', 'true', 'constant_probability', 'constant_reward']:
            if formula_phi not in self.list_of_subformula:
                self.list_of_subformula.append(formula_phi)
        elif formula_phi.data in ['next', 'not', 'future', 'global']:
            if formula_phi not in self.list_of_subformula:
                self.list_of_subformula.append(formula_phi)
            self.addToSubformulaList(formula_phi.children[0])
        elif formula_phi.data in ['probability']:
            if formula_phi not in self.list_of_subformula:
                self.list_of_subformula.append(formula_phi)
            self.addToSubformulaList(formula_phi.children[0])
        elif formula_phi.data in ['reward']:
            if formula_phi not in self.list_of_subformula:
                self.list_of_subformula.append(formula_phi)
                prob_formula = Tree('probability', [formula_phi.children[1]])
                self.list_of_subformula.append(prob_formula)
            self.addToSubformulaList(formula_phi.children[1])
        elif formula_phi.data in ['until_bounded']:
            if formula_phi not in self.list_of_subformula:
                self.list_of_subformula.append(formula_phi)
            left_child = formula_phi.children[0]
            self.addToSubformulaList(left_child)
            right_child = formula_phi.children[3]
            self.addToSubformulaList(right_child)

    def genComposedStutterscheds(self, possible_stutterings, rel_quant_stu):
        list_of_lists = []
        for i in range(self.no_of_stutter_quantifier):
            if i+1 in rel_quant_stu:
                list_of_lists.append(possible_stutterings)
            else:
                list_of_lists.append([possible_stutterings[0]])

        return list(itertools.product(*list_of_lists))


    def truth(self, combined_list_of_states_with_initial_stutter):
        # corresponds to Algo 5 "Truth"
        # encode quantifiers, i.e. translate forall to And and exists to Or
        list_of_state_AV = []  # will have the OR, AND according to the quantifier in that index in the formula
        list_of_stutter_AV = []  # placeholder to manage stutter quantifier encoding
        # TODO (optional): work to remove assumption of stutter schedulers named in order
        changed_hyperproperty = self.initial_hyperproperty.parsed_property
        while len(changed_hyperproperty.children) > 0:
            if changed_hyperproperty.data in ['exist_scheduler', 'forall_scheduler']:
                changed_hyperproperty = changed_hyperproperty.children[1]
            elif changed_hyperproperty.data == 'exist_state':
                if int(changed_hyperproperty.children[0].value[1:]) in self.stutter_state_mapping.values():
                    list_of_state_AV.append('V')
                changed_hyperproperty = changed_hyperproperty.children[1]
            elif changed_hyperproperty.data == 'forall_state':
                if int(changed_hyperproperty.children[0].value[1:]) in self.stutter_state_mapping.values():
                    list_of_state_AV.append('A')
                changed_hyperproperty = changed_hyperproperty.children[1]
            elif changed_hyperproperty.data == 'forall_stutter':
                if int(changed_hyperproperty.children[0].value[1:]) in self.stutter_state_mapping.keys():
                    list_of_stutter_AV.append('AT')
                changed_hyperproperty = changed_hyperproperty.children[2]
            elif changed_hyperproperty.data == 'exist_stutter':
                if int(changed_hyperproperty.children[0].value[1:]) in self.stutter_state_mapping.keys():
                    list_of_stutter_AV.append('VT')
                changed_hyperproperty = changed_hyperproperty.children[2]
            elif changed_hyperproperty.data in ['quantifiedformulastutter', 'quantifiedformulastate']:
                changed_hyperproperty = changed_hyperproperty.children[0]
            else:
                break
        common.colourinfo("Traversed all quantifiers", False)
        # TODO: read and track relevant quantifiers ->  Done in a way

        # changed_hyperproperty is now phi^nq, the outermost non-quantified formula
        index_of_phi = self.list_of_subformula.index(changed_hyperproperty)

        # create semantic encoding
        # todo move
        common.colourinfo("Create semantic encoding...", False)
        semanticEncoder = SemanticsEncoder(self.model, self.solver,
                                           self.list_of_subformula,
                                           self.dictOfReals, self.dictOfBools, self.dictOfInts,
                                           self.no_of_subformula,
                                           self.no_of_state_quantifier, self.no_of_stutter_quantifier,
                                           self.stutterLength,
                                           self.stutter_state_mapping, self.dict_pair_index)
        #_, rel_quant_stu, enc = semanticEncoder.encodeSemantics(changed_hyperproperty)
        common.colourinfo("Finished encoding non-quantified formula...", False)

        # todo move? or add explanation
        list_of_prob_restrict = []
        for name in self.dictOfReals.keys():
            if name[0] == 'p':
                list_of_prob_restrict.append(self.dictOfReals[name] >= RealVal(0))
                list_of_prob_restrict.append(self.dictOfReals[name] <= RealVal(1))
        self.solver.add(list_of_prob_restrict)
        self.no_of_subformula += 1

        # create all possible stutter-schedulers: assign one stutter-length to each state-action-pair
        # dict_pair_index = dict()  # dictionary mapping state-action-pairs to their index in an ordered enumeration of all state-action pairs
        i = 0
        for state in self.model.parsed_model.states:
            for action in state.actions:
                # list_of_state_action_pairs.append((state.id, action.id))
                self.dict_pair_index[(state.id, action.id)] = i
                i += 1
        possible_stutterings = list(itertools.product(list(range(self.stutterLength)),
                                                      repeat=i))  # list of all possible functions f : S x Act -> {0, ..., stutterLength - 1}, represented as tuples

        # create list of holds_(s1,0)_..._0 for all state combinations
        list_of_holds= []
        for state_tuple in combined_list_of_states_with_initial_stutter:
            name = "holds_"
            for j in range(self.no_of_stutter_quantifier):
                name += str(state_tuple[j]) + "_"
            name += str(index_of_phi)
            self.addToVariableList(name)
            list_of_holds.append(self.dictOfBools[name])
        self.no_of_subformula += 1

        # create list of preconditions for the encoding of stutter-quantifiers
        list_of_precondition = []
        for i in range(self.no_of_stutter_quantifier):  # todo vs len(list_of_stutter_AV)
            list_over_states = []
            for stutter_sched in possible_stutterings:  # range over possible stuttering-schedulers
                list_over_actions = []
                for state in self.model.parsed_model.states:
                    list_of_eqs = []
                    for action in state.actions:
                        name_tau = "t_" + str(i + 1) + "_" + str(state) + "_" + str(action.id)
                        index_of_pair = self.dict_pair_index[(state.id, action.id)]
                        list_of_eqs.append(self.dictOfInts[name_tau] == stutter_sched[index_of_pair])
                    if len(list_of_eqs) == 1:
                        list_over_actions.append(list_of_eqs[0])
                    else:
                        list_over_actions.append(And(list_of_eqs))
                    self.no_of_subformula += 1
                list_over_states.append(And(list_over_actions))
                self.no_of_subformula += 1
            list_of_precondition.append(list_over_states)

        # encode stutter scheduler quantifiers (for each possible assignment of the state variables)
        stutter_encoding_i = []
        stutter_encoding_ipo = list_of_holds
        for quant in range(self.no_of_stutter_quantifier, 0, -1):  # n, ..., 1
            # todo this needs to change
            for state_tuple in itertools.product(self.model.getListOfStates(),
                                                 repeat=self.no_of_stutter_quantifier): # len(self.stutter_state_mapping.keys())
                list_of_precond = list_of_precondition[quant - 1]
                postcond = self.fetch_value(stutter_encoding_ipo, state_tuple)
                if list_of_stutter_AV[quant - 1] == 'AT':
                    if self.stutterLength == 1: # then len(possible_stutterings) == 1
                        encoding = Implies(list_of_precond[0], self.dictOfBools[postcond])
                    else:
                        encoding = And([Implies(list_of_precond[i], postcond) for i in range(len(possible_stutterings))])
                elif list_of_stutter_AV[quant - 1] == 'VT':
                    if self.stutterLength == 1:
                        encoding = And(list_of_precond[0], postcond)
                    else:
                        encoding = Or([And(list_of_precond[i], self.dictOfBools[postcond]) for i in range(len(possible_stutterings))])
                stutter_encoding_i.append(encoding)
                self.no_of_subformula += 1
            stutter_encoding_ipo.clear()
            stutter_encoding_ipo = copy.copy(stutter_encoding_i) # todo deepcopy
            stutter_encoding_i.clear()
        common.colourinfo("Encoded stutter quantifiers", False)

        # iteratively encode state quantifiers
        state_encoding_i = []
        state_encoding_ipo = stutter_encoding_ipo
        for quant in range(self.no_of_state_quantifier, 0, -1):
            n = len(self.model.getListOfStates())
            len_i = int(len(state_encoding_ipo) / n)
            if list_of_state_AV[quant - 1] == 'A':
                state_encoding_i = [And(state_encoding_ipo[(j * n):((j + 1) * n)]) for j in range(len_i)]
            elif list_of_state_AV[quant - 1] == 'V':
                state_encoding_i = [Or(state_encoding_ipo[(j * n):((j + 1) * n)]) for j in range(len_i)]
            self.no_of_subformula += 1
            state_encoding_ipo.clear()
            state_encoding_ipo = copy.copy(state_encoding_i) # deepcopy
            state_encoding_i.clear()
        # the formula can now be accessed via state_encoding_ipo[0]
        self.solver.add(state_encoding_ipo[0])

        common.colourinfo("Encoded state quantifiers", False)

    def checkResult(self):
        starting_time = time.perf_counter()
        # f = open("solver1.txt", "w")
        # f.write(self.solver.to_smt2().__str__())
        # f.close()

        common.colourinfo("Checking...", False)
        truth = self.solver.check()
        common.colourinfo("Finished checking!", False)

        smt_time = time.perf_counter() - starting_time
        list_of_actions = None # todo change
        set_of_holds = set()
        if truth == sat:
            smt_model = self.solver.model()
            holds_candidates = [x for x in self.dictOfBools.keys() if x[0] == 'h']
            # list_of_actions = [None] * self.model.getNumberOfActions() # todo change?

            for varname in holds_candidates:
                parts = varname.split("_")
                # check if varname encodes the truth of the given formula and is satisfied in the model
                if parts[-2] == '0' and smt_model[self.dictOfBools[varname]]:
                    # check if varname belongs to a state with stutterLen 0
                    take_this = True
                    for i in range(self.no_of_stutter_quantifier):
                        if parts[1 + i][-2] != '0':
                            take_this = False
                    if take_this:
                        state_tuple_list = [parts[1 + i][1] for i in range(self.no_of_stutter_quantifier)]
                        set_of_holds.add(tuple(state_tuple_list))

            # looping through the whole model took a LOT of time for cvc5
            # for li in smt_model:
            #     if is_bool(li):
            #         varname = list(self.dictOfBools.keys())[list(self.dictOfBools.values()).index(li)]
            #     elif is_real(li):
            #         varname = list(self.dictOfReals.keys())[list(self.dictOfReals.values()).index(li)]
            #     elif is_int(li):
            #         varname = list(self.dictOfInts.keys())[list(self.dictOfInts.values()).index(li)]
            #     if varname[0] == 'h':
            #         parts = varname.split("_")
            #         if parts[-2] == '0' and smt_model[li]:
            #             take_this = True
            #             for i in range(self.no_of_stutter_quantifier):
            #                 if parts[1+i][-2] != '0':
            #                     take_this = False
            #             if take_this:
            #                 state_tuple_list = [parts[1+i][1] for i in range(self.no_of_stutter_quantifier)]
            #                 set_of_holds.add(tuple(state_tuple_list))
            #     elif varname[0] == 'a' and len(varname) == 3: # todo change!!
            #         list_of_actions[int(varname[2:])] = smt_model[li]
        return truth, list_of_actions, set_of_holds, self.solver.statistics().get(), smt_time

    def printResult(self, encoding_time, scheduler_quantifier):
        truth, actions, holds, statistics, smt_time = self.checkResult()

        if truth == unknown:
            print("Result unknown. Solver fails to solve constraints.")

        # todo  change outputs. output stuttering and action probabilities
        elif truth in [sat, unsat]:
            # todo dont distinguish output by scheduler_quantifier? since we have many alternating quantifiers
            if scheduler_quantifier == 'exists':
                if truth == sat:
                    # todo somehow also output stutter-scheduler?
                    common.colouroutput("The property HOLDS!")
                    print("\nThe values of variables of a witness are:") #todo mention more explicity that list mustnt be exhaustive?
                    #print("\nIf both actions are available at a state:")
                    #for i in range(0, len(actions)):
                    #    common.colouroutput("Choose action " + str(i) + " with probability " + str(actions[i]), False)
                    print(
                        "\nThe following state variable assignments satisfy the property "
                        "(tuples ordered by stutter quantification):")  # todo order of quantification? order of stutterquant ??
                    print(
                        holds)  # for each assignment: state associated with first stutter-sched var is listed first, and so on
                else:
                    common.colourerror("The property DOES NOT hold!")
            elif scheduler_quantifier == 'forall':
                if truth == sat:
                    common.colourerror("The property DOES NOT hold!")
                    print("\nThe values of variables of a counterexample are:")
                    #print("\nIf both actions are available at a state:")
                    #for i in range(0, len(actions)):
                    #    common.colouroutput("Choose action " + str(i) + " with probability " + str(actions[i]), False)
                    print(
                        "\nThe following state variable assignments do not satisfy the property (tuples ordered by stutter quantification):")  # todo order of quantification? order of stutterquant ??
                    print(
                        holds)  # for each assignment: state associated with first stutter-sched var is listed first, and so on
                else:
                    common.colouroutput("The property HOLDS!")
        common.colourinfo("\nTime to encode in seconds: " + str(round(encoding_time, 2)), False)
        common.colourinfo("Time required for smt checking in seconds: " + str(round(smt_time, 2)), False)
        common.colourinfo(
            "Number of variables: " +
            str(len(self.dictOfInts.keys()) + len(self.dictOfReals.keys()) + len(self.dictOfBools.keys())),
            False)
        common.colourinfo("Number of formula checked: " + str(self.no_of_subformula), False)
        # common.colourinfo("smt checking statistics:", False) # todo output number of constants or terms ?
        # common.colourinfo(statistics['global::totalTime']['value'], False)

    def fetch_value(self, list_with_value, value):
        # assuming value is a tuple
        res = 0
        for i in range(0, len(value)):
            res += value[i] * pow(len(self.model.getListOfStates()), len(value) - i - 1)
        return list_with_value[res]
