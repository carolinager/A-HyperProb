import copy
import time
import itertools

from lark import Tree
from z3 import SolverFor, Bool, Real, Or, sat, And, RealVal, Sum

import hyperprob.semanticencoder
from hyperprob.utility import common
from hyperprob import propertyparser
from hyperprob.semanticencoder import SemanticsEncoder

class ModelChecker:
    def __init__(self, model, hyperproperty, lengthOfStutter, maxSchedProb):
        self.model = model
        self.initial_hyperproperty = hyperproperty  # object of property class
        # set_param(proof=True)
        # ctx = Context()
        self.solver = SolverFor("QF_NRA")
        self.stutterLength = lengthOfStutter  # default value 1 equals no stuttering
        self.maxSchedProb = maxSchedProb
        self.list_of_subformula = []
        self.dictOfReals = dict()
        self.dictOfBools = dict()
        self.no_of_subformula = 0
        self.no_of_state_quantifier = 0
        self.no_of_stutter_quantifier = 0
        self.stutter_state_mapping = None  # value at index of stutter variable is the corresponding state variable

    def modelCheck(self):
        # parse property
        stutter_quantified_property, self.no_of_state_quantifier, state_indices = propertyparser.checkStateQuantifiers(
            copy.deepcopy(self.initial_hyperproperty.parsed_property))
        non_quantified_property, self.stutter_state_mapping = propertyparser.checkStutterQuantifiers(
            stutter_quantified_property.children[0], state_indices)
        self.no_of_stutter_quantifier = len(self.stutter_state_mapping.keys())
        self.no_of_state_quantifier = len(set(self.stutter_state_mapping.values()))
        non_quantified_property = non_quantified_property.children[0]
        self.addToSubformulaList(non_quantified_property)

        start_time = time.perf_counter()
        # encode scheduler and stutter-schedulers
        self.encodeScheduler()
        self.encodeStuttering()

        # encode the meaning of the quantifiers
        self.truth()

        # encode the non-quantified property
        common.colourinfo("\nEncoding non-quantified formula...", False)
        semanticEncoder = SemanticsEncoder(self.model, self.solver,
                                           self.list_of_subformula,
                                           self.dictOfReals, self.dictOfBools,
                                           self.no_of_subformula,
                                           self.no_of_state_quantifier, self.no_of_stutter_quantifier,
                                           self.stutterLength,
                                           self.stutter_state_mapping
                                           )
        semanticEncoder.encodeSemantics(non_quantified_property)

        # ensure that all variables encoding probabilities range in [0, 1]
        list_of_prob_restrict = []
        for name in self.dictOfReals.keys():
            if name[0] == 'p':
                list_of_prob_restrict.append(self.dictOfReals[name] >= RealVal(0))
                list_of_prob_restrict.append(self.dictOfReals[name] <= RealVal(1))
        self.solver.add(list_of_prob_restrict)
        self.no_of_subformula += 1

        encoding_time = time.perf_counter() - start_time

        self.printResult(encoding_time)

    def encodeScheduler(self):
        """
        Introduce variables encoding the probabilistic memoryless scheduler which satisfies the following:
        if Act(s) = Act(s'), then act(s, alpha) = act(s', alpha) for all alpha in Act(s).
        Variable a_A_x represents the probability of choosing action x at a state with enabled actions A
        """
        common.colourinfo("Encoding scheduler...")
        set_of_actionsets = {frozenset(x) for x in self.model.getDictOfActions().values()}
        scheduler_restrictions = []

        for A in set_of_actionsets:
            sum_over_probs = []
            # if only a single action is enabled at s, then that action will always be chosen with probability 1
            if len(A) == 1:
                action = list(A)[0]
                name = "a_" + str(set(A)) + "_" + str(action)
                self.addToVariableList(name)
                scheduler_restrictions.append(self.dictOfReals[name] == RealVal(1)) # .as_fraction()
            else:
                for action in A:
                    name = "a_" + str(set(A)) + "_" + str(action)
                    self.addToVariableList(name)
                    # probabilistic scheduler
                    maxVal = self.maxSchedProb
                    minVal = 1 - maxVal
                    scheduler_restrictions.append(self.dictOfReals[name] > RealVal(minVal)) # .as_fraction()
                    scheduler_restrictions.append(self.dictOfReals[name] < RealVal(maxVal)) # .as_fraction()
                    # deterministic scheduler (inefficient to encode it like this)
                    # scheduler_restrictions.append(Or(self.dictOfReals[name] == RealVal(0),
                    #                                  self.dictOfReals[name] == RealVal(1)))
                    sum_over_probs.append(self.dictOfReals[name])
                scheduler_restrictions.append(Sum(sum_over_probs) == RealVal(1)) #.as_fraction()

        # general probabilistic memoryless stutter-scheduler:
        """        for state in self.model.parsed_model.states:
            name_s = "a_" + str(state.id) + "_"  # a_s_x is probability of action x in state s
            sum_of_probs = RealVal(0)
            if len(state.actions) == 1: #
                action = list(state.actions)[0] #
                name = name_s + str(action.id) #
                self.addToVariableList(name) #
                scheduler_restrictions.append(self.dictOfReals[name] == RealVal(1)) #
            else:
                for act in state.actions:
                    name_s_a = name_s + str(act.id)
                    self.addToVariableList(name_s_a)

                    sum_of_probs += self.dictOfReals[name_s_a]

                    scheduler_restrictions.append(self.dictOfReals[name_s_a] > RealVal(0)) #
                    scheduler_restrictions.append(self.dictOfReals[name_s_a] < RealVal(1)) #
                scheduler_restrictions.append(Sum(sum_of_probs) == RealVal(1)) #"""

        self.solver.add(And(scheduler_restrictions))
        self.no_of_subformula += 1

    def encodeStuttering(self):
        """
        Introduce variables encoding the deterministic bounded-memory stutter-schedulers.
        Variable t_i_s_x represents the stutter duration for stutter quantifier i and state s and action x.
        """
        common.colourinfo("Encoding stutter-scheduler...", False)
        list_over_quantifiers = []
        for quantifier in range(0, self.no_of_stutter_quantifier):
            list_over_states = []
            for state in self.model.parsed_model.states:
                list_over_actions = []
                for action in state.actions:
                    list_of_equations = []
                    name = "t_" + str(quantifier + 1) + "_" + str(state.id) + "_" + str(action.id)
                    self.addToVariableList(name)
                    for stutter_length in range(0, self.stutterLength):
                        list_of_equations.append(self.dictOfReals[name] == RealVal(stutter_length))
                    list_over_actions.append(Or(list_of_equations))
                    self.no_of_subformula += 1
                list_over_states.append(And(list_over_actions))
                self.no_of_subformula += 1
            list_over_quantifiers.append(And(list_over_states))
            self.no_of_subformula += 1
        self.solver.add(And(list_over_quantifiers))
        self.no_of_subformula += 1

    def truth(self):
        """
        Encode the state and stutter quantifiers by translating "forall" to conjunction and "exists" to disjunction
        """
        # create list of state tuples of the induced DTMC
        list_of_states_with_initial_stutter = list(itertools.product(self.model.getListOfStates(), [0]))
        list_of_state_tuples = list(
            itertools.product(list_of_states_with_initial_stutter, repeat=self.no_of_state_quantifier))
        if self.no_of_stutter_quantifier != self.no_of_state_quantifier:
            combined_list_of_states_with_initial_stutter = [
                tuple([x[self.stutter_state_mapping[q] - 1] for q in range(1, self.no_of_stutter_quantifier + 1)])
                for x in list_of_state_tuples]
        else:
            combined_list_of_states_with_initial_stutter = list_of_state_tuples

        list_of_state_AV = []  # will have the OR, AND according to the quantifier in that index in the formula
        # TODO: work to remove assumption of stutter schedulers named in order
        common.colourinfo("Prepare encoding quantifiers...", False)
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
            elif changed_hyperproperty.data == 'exist_stutter':
                changed_hyperproperty = changed_hyperproperty.children[2]
            elif changed_hyperproperty.data in ['quantifiedformulastutter', 'quantifiedformulastate']:
                changed_hyperproperty = changed_hyperproperty.children[0]
            else:
                break

        index_of_phi = self.list_of_subformula.index(changed_hyperproperty)

        # create all possible stutter-schedulers: assign one stutter-length to each state-action-pair
        dict_pair_index = dict()  # dictionary mapping state-action-pairs to their index in an ordered enumeration of all state-action pairs
        i = 0
        for state in self.model.parsed_model.states:
            for action in state.actions:
                dict_pair_index[(state.id, action.id)] = i
                i += 1
        possible_stutterings = list(itertools.product(list(range(self.stutterLength)), repeat=i))

        print("Number of possible stutter-schedulers: " + str(len(possible_stutterings)))

        common.colourinfo("Create list of preconditions...", False)
        # create list of preconditions for the encoding of stutter-quantifiers
        list_of_precondition = []
        for i in range(self.no_of_stutter_quantifier):
            list_over_states = []
            for stutter_sched in possible_stutterings: # range over possible stuttering-schedulers
                list_over_actions = []
                for state in self.model.parsed_model.states:
                    list_of_eqs = []
                    for action in state.actions:
                        name_tau = "t_" + str(i + 1) + "_" + str(state) + "_" + str(action.id)
                        index_of_pair = dict_pair_index[(state.id, action.id)]
                        list_of_eqs.append(self.dictOfReals[name_tau] == RealVal(stutter_sched[index_of_pair]))
                    list_over_actions.append(And(list_of_eqs))
                    self.no_of_subformula += 1
                list_over_states.append(And(list_over_actions))
                self.no_of_subformula += 1
            list_of_precondition.append(list_over_states)

        # create list of holds_(s1,0)_..._0 for all state combinations
        list_of_holds = []
        for i in range(len(combined_list_of_states_with_initial_stutter)):
            name = "holds_"
            for j in range(self.no_of_stutter_quantifier):
                name += str(combined_list_of_states_with_initial_stutter[i][j]) + "_"
            name += str(index_of_phi)
            self.addToVariableList(name)
            list_of_holds.append(self.dictOfBools[name])

        # encode stutter scheduler quantifiers (for each possible assignment of the state variables)
        common.colourinfo("Encoding stutter quantifiers...", False)
        stutter_encoding_i = []
        stutter_encoding_ipo = list_of_holds
        for quant in range(self.no_of_stutter_quantifier, 0, -1):  # n, ..., 1
            for i in range(len(combined_list_of_states_with_initial_stutter)):
                list_of_precond = list_of_precondition[quant - 1]  # indexed starting from 0
                postcond = stutter_encoding_ipo[i]
                encoding = Or([And(list_of_precond[j], postcond) for j in range(len(possible_stutterings))])
                stutter_encoding_i.append(encoding)
                self.no_of_subformula += 1
            stutter_encoding_ipo.clear()
            stutter_encoding_ipo = copy.deepcopy(stutter_encoding_i)
            stutter_encoding_i.clear()

        # iteratively encode state quantifiers
        common.colourinfo("Encoding state quantifiers...", False)
        state_encoding_i = []
        state_encoding_ipo = copy.deepcopy(stutter_encoding_ipo)
        for quant in range(self.no_of_state_quantifier, 0, -1):
            n = len(self.model.getListOfStates()) # todo this wont work anymore?
            len_i = int(len(state_encoding_ipo) / n)
            if list_of_state_AV[quant - 1] == 'A':
                state_encoding_i = [And(state_encoding_ipo[(j * n):((j + 1) * n)]) for j in range(len_i)]
            elif list_of_state_AV[quant - 1] == 'V':
                state_encoding_i = [Or(state_encoding_ipo[(j * n):((j + 1) * n)]) for j in range(len_i)]
            self.no_of_subformula += len_i
            state_encoding_ipo.clear()
            state_encoding_ipo = copy.deepcopy(state_encoding_i)
            state_encoding_i.clear()
        self.solver.add(state_encoding_ipo[0])

    def addToVariableList(self, name):
        if name[0] == 'h' and not name.startswith('holdsToInt'):  # holds_
            self.dictOfBools[name] = Bool(name)
        elif name[0] in ['p', 'd', 'a', 't'] or name.startswith('holdsToInt'):  # prob_, d_, a_, t_
            self.dictOfReals[name] = Real(name)

    def addToSubformulaList(self, formula_phi):
        """
        Add formula and all its subformulas to a list of all subformulas.
        The position of a subformula in this list is used to index the variables encoding meaning of the formula.
        :param formula_phi: subformula to be added to list
        """
        if formula_phi.data in ['exist_scheduler', 'forall_scheduler', 'exist_state', 'forall_state']:
            formula_phi = formula_phi.children[1]
            self.addToSubformulaList(formula_phi)
        elif formula_phi.data in ['and', 'or', 'implies', 'equivalent',
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

    def checkResult(self):
        """
        Check whether the created SMT formula holds.
        :return:
            - truth: result of SMT solver
            - scheduler_assignments: list of variables encoding the scheduler and their assigned values
            - set_of_holds: set of state tuples that satisfy the formula
            - stuttersched_assignments: list of variables encoding the stutter-schedulers and their assigned values
            - statistics: statistics of the z3 solver
            - smt_time: time the SMT solver took to check the formula
        """
        common.colourinfo("Checking SMT-formula...", False)
        common.colourinfo(
            "Number of variables: " +
            str(len(self.dictOfReals.keys()) + len(self.dictOfBools.keys())),
            False)
        common.colourinfo("Number of formula to check: " + str(self.no_of_subformula), False)
        starting_time = time.perf_counter()
        truth = self.solver.check()
        #self.solver.proof()
        smt_time = time.perf_counter() - starting_time
        common.colourinfo("Finished checking!", False)
        scheduler_assignments = []
        set_of_holds = set()
        stuttersched_assignments = []
        if truth == sat:
            z3model = self.solver.model()
            list_of_corr_stutter_qs = [[k for k, v in self.stutter_state_mapping.items() if v == q + 1] for q in range(self.no_of_state_quantifier)]

            for li in z3model:
                if li.name()[0] == 'h' and z3model[li] and li.name().split("_")[-1] == '0':
                    state_tuples_list = li.name().split("_")[1:-1]
                    states_list = [elt.split(", ")[0][1:] for elt in state_tuples_list]
                    stutter_set = {elt.split(", ")[1][:-1] for elt in state_tuples_list}
                    states_by_state_qs = [[states_list[i-1] for i in x] for x in list_of_corr_stutter_qs]

                    if stutter_set == {'0'} and {len(set(x)) for x in states_by_state_qs} == {1}:
                        state_list = [x[0] for x in states_by_state_qs]
                        set_of_holds.add(tuple(state_list))
                elif li.name()[0] == 'a' and len(li.name()) == 5:
                    scheduler_assignments.append((li.name(), z3model[li]))
                elif li.name()[0] == 't':
                    stuttersched_assignments.append((li.name(), z3model[li]))
        return truth, scheduler_assignments, set_of_holds, stuttersched_assignments, self.solver.statistics(), smt_time

    def printResult(self, encoding_time):
        """
        Print the result of the model checking
        :param encoding_time: time it took to create the SMT encoding
        """
        smt_result, actions, holds, stuttersched_assignments, statistics, smt_time = self.checkResult()
        actions.sort()
        stuttersched_assignments.sort()

        if smt_result.r == 1:
            # todo adjust to more fine-grained output depending on different quantifier combinations?
            common.colouroutput("The property HOLDS!")
            print("\nThe values of variables of the witness are:")
            print("Choose scheduler probabilities as follows:")
            for act_prob in actions:
                common.colouroutput(
                    "At a state with enabled actions " + act_prob[0].split("_")[1] +
                    " choose action " + act_prob[0].split("_")[2] +
                    " with probability " + str(act_prob[1]),
                    False)
            print("\nChoose stutterschedulers as follows:")
            for stutter_step in stuttersched_assignments:
                common.colouroutput(
                    "For quantifier t" + stutter_step[0].split("_")[1] +
                    " : For state " + stutter_step[0].split("_")[2] +
                    " and action " + stutter_step[0].split("_")[3] +
                    " choose stuttering duration " + str(stutter_step[1]),
                    False)
            print("\nThe following state variable assignments (s1, ..., sn) satisfy the property:")
            print(holds)
        elif smt_result.r == -1:
            common.colourerror("The property DOES NOT hold!")
        else:
            common.colourerror("Solver returns unknown")
        common.colourinfo("\nTime to encode in seconds: " + str(round(encoding_time, 2)), False)
        common.colourinfo("Time required by z3 in seconds: " + str(round(smt_time, 2)), False)
        common.colourinfo("z3 statistics:", False)
        common.colourinfo(str(statistics), False)
